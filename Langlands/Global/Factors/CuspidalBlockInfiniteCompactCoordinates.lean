import Langlands.Global.AdelicBlockInfiniteCompactSections
import Langlands.Global.Factors.CuspidalBlockInfiniteEvaluation
import Langlands.Global.AdelicBlockCompactProduct

/-! # Compact Levi projection in the actual infinite place coordinates -/

noncomputable section

open scoped Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 90000

universe u

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic _root_.Langlands.Archimedean GeneralLinear
open AdelicBlockParabolic InfinitePlaceFamily ArchimedeanCompactBlocks PrimitiveAdelicHeight
open NumberField

variable {F : Type u} [Field F] [NumberField F]
variable {n : ℕ} (B : BlockShape n)

private def mapParabolic {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (p : B.parabolic R) : B.parabolic L :=
  ⟨Matrix.GeneralLinearGroup.map f p.val, (B.mem_parabolic_iff L _).mpr fun i j a b h => by
    change f (p.val (B.index i a) (B.index j b)) = 0
    rw [(B.mem_parabolic_iff R _).mp p.property i j a b h, map_zero]⟩

private theorem coordinates_of_factors (p : ArchimedeanCompactFactors F n) (v : Index F) :
    infiniteCompactCoordinates F n (ArchimedeanCompactFactors.toStandardCompact F n p) v =
      (match v with | .inl w => p.1 w | .inr w => p.2 w) := by
  let e := MulEquiv.ofBijective (ArchimedeanCompactFactors.toStandardCompact F n).toMonoidHom
    ⟨ArchimedeanCompactFactors.toStandardCompact_injective F n,
      ArchimedeanCompactFactors.toStandardCompact_surjective F n⟩
  cases v with
  | inl v => exact congrArg (fun q => q.1 v) (e.symm_apply_apply p)
  | inr v => exact congrArg (fun q => q.2 v) (e.symm_apply_apply p)

/-- A genuine compact inclusion is supported on its own infinite place. -/
theorem infiniteCompactCoordinates_inclusion (v : Index F) (d : Compact n v) :
    infiniteCompactCoordinates F n (compactInclusion n v d) =
      (Pi.mulSingle v d : ∀ w : Index F, Compact n w) := by
  classical
  funext w
  have h := coordinates_of_factors (compactFactor n v d) w
  refine h.trans ?_
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      change (Pi.mulSingle v d : ∀ q : {x : InfinitePlace F // x.IsReal}, Compact n (.inl q : Index F)) w = _
      by_cases h : w = v
      · subst w
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne (fun e => h (Sum.inl.inj e))]
    | inr w =>
      exact (Pi.mulSingle_eq_of_ne (by simp : (.inr w : Index F) ≠ .inl v) d).symm
  | inr v =>
    cases w with
    | inl w =>
      exact (Pi.mulSingle_eq_of_ne (by simp : (.inl w : Index F) ≠ .inr v) d).symm
    | inr w =>
      change (Pi.mulSingle v d : ∀ q : {x : InfinitePlace F // x.IsComplex}, Compact n (.inr q : Index F)) w = _
      by_cases h : w = v
      · subst w
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne (fun e => h (Sum.inr.inj e))]

/-- The infinite diagonal blocks of an element in the compact parabolic
intersection are elements of the actual infinite compact groups of the blocks. -/
def infiniteLeviCompact (p : infiniteCompactIntersection F B) (i : Fin B.length) :
    standardInfiniteCompact F (B.size i) :=
  infiniteCompactLeviProjection F B p i

theorem infiniteCompactCoordinates_levi_real (p : infiniteCompactIntersection F B)
    (v : {x : InfinitePlace F // x.IsReal}) :
    matrixUnitaryToCompact ℝ n
      (infiniteCompactCoordinates F n ⟨p.val.val, p.property⟩ (.inl v)) =
      compactLeviEmbedding ℝ B (fun i => matrixUnitaryToCompact ℝ (B.size i)
        (infiniteCompactCoordinates F (B.size i) (infiniteLeviCompact B p i) (.inl v))) := by
  let c := (realCoord v).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
  let g := mapParabolic B c p.val
  let q := matrixUnitaryToCompact ℝ n
    (infiniteCompactCoordinates F n ⟨p.val.val, p.property⟩ (.inl v))
  have hg : q.val = g.val :=
    Units.ext (infiniteCompactCoordinates_apply_real F n ⟨p.val.val, p.property⟩ v)
  have hgu : g.val ∈ unitaryCompact ℝ n := hg ▸ q.property
  have hblock (i : Fin B.length) :
      matrixUnitaryToCompact ℝ (B.size i)
        (infiniteCompactCoordinates F (B.size i) (infiniteLeviCompact B p i) (.inl v)) =
          ArchimedeanCompactBlocks.compactLeviProjection ℝ B g hgu i :=
    Subtype.ext (Units.ext (infiniteCompactCoordinates_apply_real F (B.size i)
      (infiniteLeviCompact B p i) v))
  exact (Subtype.ext hg).trans ((compactLeviEmbedding_projection ℝ B g hgu).symm.trans
    (congrArg (compactLeviEmbedding ℝ B) (funext hblock).symm))

theorem infiniteCompactCoordinates_levi_complex (p : infiniteCompactIntersection F B)
    (v : {x : InfinitePlace F // x.IsComplex}) :
    matrixUnitaryToCompact ℂ n
      (infiniteCompactCoordinates F n ⟨p.val.val, p.property⟩ (.inr v)) =
      compactLeviEmbedding ℂ B (fun i => matrixUnitaryToCompact ℂ (B.size i)
        (infiniteCompactCoordinates F (B.size i) (infiniteLeviCompact B p i) (.inr v))) := by
  let c := (complexCoord v).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
  let g := mapParabolic B c p.val
  let q := matrixUnitaryToCompact ℂ n
    (infiniteCompactCoordinates F n ⟨p.val.val, p.property⟩ (.inr v))
  have hg : q.val = g.val :=
    Units.ext (infiniteCompactCoordinates_apply_complex F n ⟨p.val.val, p.property⟩ v)
  have hgu : g.val ∈ unitaryCompact ℂ n := hg ▸ q.property
  have hblock (i : Fin B.length) :
      matrixUnitaryToCompact ℂ (B.size i)
        (infiniteCompactCoordinates F (B.size i) (infiniteLeviCompact B p i) (.inr v)) =
          ArchimedeanCompactBlocks.compactLeviProjection ℂ B g hgu i :=
    Subtype.ext (Units.ext (infiniteCompactCoordinates_apply_complex F (B.size i)
      (infiniteLeviCompact B p i) v))
  exact (Subtype.ext hg).trans ((compactLeviEmbedding_projection ℂ B g hgu).symm.trans
    (congrArg (compactLeviEmbedding ℂ B) (funext hblock).symm))

end Langlands.Global.CuspidalBlockInduction
