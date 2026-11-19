import Langlands.Global.AdelicEisensteinSeries
import Langlands.Global.AdelicGroupRationalTopology
import Langlands.Global.AdelicIwasawaOrbitHeight
import Langlands.GroupScheme.Rational.MaximalParabolicLineDominance

/-! # Projective embeddings of actual rational parabolic cosets -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
  {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)

omit [NumberField F] in
private theorem coordinateVector_ne_zero : (Pi.single j 1 : Fin n → F) ≠ 0 := by
  intro h
  have h' := congrFun h j
  simp at h'

omit [NumberField F] in
/-- On an affine test, the exact coordinate-line stabilizer is detected by affine matrices. -/
theorem mem_range_iff_affineMatrix_coordinateLine
    (hstab : ρ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j)
    (A : CommAlgCat.{u} (CommRingCat.of F)) (x : G.affinePoints A) :
    x ∈ (SubgroupFunctor.range p).carrier ((algSpec (CommRingCat.of F)).obj (op A)) ↔
      ∃ c : Aˣ, (ρ.affineMatrix A x).val *ᵥ Pi.single j 1 =
        (c : A) • (Pi.single j 1 : Fin n → A) := by
  classical
  let e := Corepresented.affineSectionsAlgEquiv A
  have hm (i : Fin n) :
      (ρ.pointMatrix ((algSpec (CommRingCat.of F)).obj (op A)) x).val i j =
        e.symm ((ρ.affineMatrix A x).val i j) := by
    rw [MatrixRepresentation.pointMatrix_eq_affineMatrix]
    rfl
  rw [hstab]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨Units.map e.toMonoidHom c, ?_⟩
    funext i
    have hi := congrArg e (congrFun hc i)
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul,
      hm, e.apply_symm_apply] at hi ⊢
    change _ = e c.val * _
    by_cases hij : i = j <;> simpa [hij, map_mul] using hi
  · rintro ⟨c, hc⟩
    refine ⟨Units.map e.symm.toMonoidHom c, ?_⟩
    funext i
    have hi := congrArg e.symm (congrFun hc i)
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul,
      hm] at hi ⊢
    change _ = e.symm c.val * _
    by_cases hij : i = j <;> simpa [hij, map_mul] using hi

variable [IsAffine G.X.left]

private theorem rationalOrbitPoint_inv_eq_iff
    (hstab : ρ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j)
    (x y : RationalGroupPoints F G) :
    rationalOrbitPoint ρ (coordinateVector_ne_zero j) x⁻¹ =
      rationalOrbitPoint ρ (coordinateVector_ne_zero j) y⁻¹ ↔
        (⟨rational F G y, ⟨y, rfl⟩⟩ : rationalSubgroup F G) *
          (⟨rational F G x, ⟨x, rfl⟩⟩ : rationalSubgroup F G)⁻¹ ∈
          parabolicRationalSubgroup F p := by
  let v : Fin n → F := Pi.single j 1
  let M := rationalMatrix F G ρ
  have hmul (w z : RationalGroupPoints F G) (b : Fin n → F) :
      (M w).val *ᵥ ((M z).val *ᵥ b) = (M (w * z)).val *ᵥ b := by
    rw [Matrix.mulVec_mulVec, map_mul, Units.val_mul]
  have hone (b : Fin n → F) : (M 1).val *ᵥ b = b := by simp
  have hs : (∃ a : Fˣ, a • ((M y⁻¹).val *ᵥ v) = (M x⁻¹).val *ᵥ v) ↔
      ∃ a : Fˣ, (M (y * x⁻¹)).val *ᵥ v = (a : F) • v := by
    constructor
    · rintro ⟨a, ha⟩
      have hh := congrArg (fun b => (M y).val *ᵥ b) ha
      change _ *ᵥ ((a : F) • _) = _ at hh
      rw [Matrix.mulVec_smul, hmul, hmul, mul_inv_cancel, hone] at hh
      exact ⟨a, hh.symm⟩
    · rintro ⟨a, ha⟩
      have hh := congrArg (fun b => (M y⁻¹).val *ᵥ b) ha
      change _ *ᵥ _ = _ *ᵥ ((a : F) • _) at hh
      rw [hmul, Matrix.mulVec_smul, ← mul_assoc, inv_mul_cancel, one_mul] at hh
      exact ⟨a, hh.symm⟩
  have hq : (y * x⁻¹ : RationalGroupPoints F G) ∈
      (SubgroupFunctor.range p).carrier ((algSpec (CommRingCat.of F)).obj
        (op (CommAlgCat.of F F))) ↔
      rational F G y * (rational F G x)⁻¹ ∈
        (rationalSubgroup F P).map (map F P G p).toMonoidHom := by
    have hnat (q : RationalGroupPoints F P) :
        rational F G (q ≫ p.hom.hom) = map F P G p (rational F P q) :=
      DFunLike.congr_fun (rational_naturality F P p) q
    constructor
    · rintro ⟨q, hq⟩
      change RationalGroupPoints F P at q
      change q ≫ p.hom.hom = y * x⁻¹ at hq
      refine ⟨rational F P q, ⟨q, rfl⟩, ?_⟩
      change map F P G p (rational F P q) = _
      rw [← hnat, hq, map_mul, map_inv]
    · rintro ⟨_, ⟨q, rfl⟩, hq⟩
      change map F P G p (rational F P q) = _ at hq
      refine ⟨q, rational_injective F G ?_⟩
      change rational F G (q ≫ p.hom.hom) = rational F G (y * x⁻¹)
      rw [hnat, hq, map_mul, map_inv]
  change _ ↔ rational F G y * (rational F G x)⁻¹ ∈
    (rationalSubgroup F P).map (map F P G p).toMonoidHom
  rw [← hq, mem_range_iff_affineMatrix_coordinateLine ρ j hstab]
  exact (Projectivization.mk_eq_mk_iff F _ _ _ _).trans hs

/-- The inverse projective orbit map embeds rational right cosets of the exact
line stabilizer into projective space. -/
def parabolicRationalProjectiveEmbedding
    (hstab : ρ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j) :
    ParabolicRationalCosets F p ↪ Projectivization F (Fin n → F) := by
  let e : RationalGroupPoints F G ≃* rationalSubgroup F G :=
    MonoidHom.ofInjective (rational_injective F G)
  let f : rationalSubgroup F G → Projectivization F (Fin n → F) := fun x =>
    rationalOrbitPoint ρ (coordinateVector_ne_zero j) (e.symm x)⁻¹
  have hf (x y : rationalSubgroup F G) : f x = f y ↔
      y * x⁻¹ ∈ parabolicRationalSubgroup F p := by
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    simp only [f, MulEquiv.symm_apply_apply]
    have he (z : RationalGroupPoints F G) : e z = ⟨rational F G z, ⟨z, rfl⟩⟩ :=
      Subtype.ext (MonoidHom.ofInjective_apply (rational_injective F G))
    rw [he y, he x]
    exact rationalOrbitPoint_inv_eq_iff ρ j hstab x y
  refine ⟨Quotient.lift f (fun x y h => (hf x y).2 (QuotientGroup.rightRel_apply.mp h)), ?_⟩
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | _ x y =>
    intro h
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr ((hf x y).1 h))

/-- Evaluation of the embedding on a principal rational representative. -/
theorem parabolicRationalProjectiveEmbedding_mk
    (hstab : ρ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j)
    (x : RationalGroupPoints F G) :
    parabolicRationalProjectiveEmbedding ρ j hstab (Quotient.mk _ ⟨rational F G x, ⟨x, rfl⟩⟩) =
      rationalOrbitPoint ρ (coordinateVector_ne_zero j) x⁻¹ := by
  change rationalOrbitPoint ρ (coordinateVector_ne_zero j)
    ((MonoidHom.ofInjective (rational_injective F G)).symm
      ((MonoidHom.ofInjective (rational_injective F G)) x))⁻¹ = _
  rw [MulEquiv.symm_apply_apply]

variable [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}

/-- The Chevalley line character controls the inverse-orbit projective height of
each rational coset. -/
theorem exists_height_le_sub_log_parabolicProjectiveEmbedding
    (hK : IsIwasawaCompact p K)
    (hstab : ρ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j) :
    ∃ (χ : rationalCharacters P) (D : ℝ), ∀ x : RationalGroupPoints F G,
      hK.height (rational F G x) χ ≤ D -
        (parabolicRationalProjectiveEmbedding ρ j hstab
          (Quotient.mk _ ⟨rational F G x, ⟨x, rfl⟩⟩)).logHeight := by
  let hline := hstab.preservesCoordinateLine_restrict p le_rfl
  let χ := (ρ.restrict p).coordinateLineRationalCharacter j hline
  have hrat : PrimitiveAdelicHeight.rational F n (Pi.single j 1) =
      (Pi.single j 1 : Fin n → Adeles F) := by
    funext i
    by_cases hij : i = j <;> simp [PrimitiveAdelicHeight.rational, hij]
  have ha (q : AdelicGroupPoints F P) :
      (adelicMatrix F G ρ (map F P G p q)).val *ᵥ
          PrimitiveAdelicHeight.rational F n (Pi.single j 1) =
        (character F P χ.toMul q).val •
          PrimitiveAdelicHeight.rational F n (Pi.single j 1) := by
    rw [hrat]
    exact (ρ.restrict p).affine_coordinateLineCharacter_action j hline
      (CommAlgCat.of F (Adeles F)) q
  obtain ⟨D, hD⟩ := exists_height_le_sub_log_mulHeight ρ
    (coordinateVector_ne_zero j) hK χ ha
  refine ⟨χ, D, fun x => ?_⟩
  rw [parabolicRationalProjectiveEmbedding_mk]
  exact hD x

end Langlands.Global.RepresentationGrowth
