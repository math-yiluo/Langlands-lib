import Langlands.Global.AdelicTruncationShellProduct
import Langlands.GroupScheme.Rational.RootKernelTorus

/-! # The characteristic chamber in the intrinsic standard Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open GroupScheme GroupScheme.RealTorusSpace ArthurRelative

variable {F : Type} [Field F]
  {G L : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom L.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} {iL : T.toGrp ⟶ L}
  [Mono i.hom.hom.left] [Mono iL.hom.hom.left]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hL : IsConnectedReductive L) (hiL : IsMaximalSplitTorus iL)
  (j : L ⟶ G) (hc : iL ≫ j = i)
  {ν : cocharacterLattice T} (hνL : IsGenericCocharacter iL ν)
  (D : RelativeRootReflectionData i) (DL : RelativeRootReflectionData iL)
  (J : StandardIndex F G i ν)

local notation "ΔL" => simpleRelativeRoots iL ν
local notation "proj" => levelProjection hG hi ν D J.val

include hc in
omit [IsAffineHom G.X.hom] [IsAffineHom L.X.hom] in
private theorem invariantForm_intrinsic (B : LinearMap.BilinForm ℝ (Vstar T))
    (hB : IsWeylInvariantInnerProduct i B) : IsWeylInvariantInnerProduct iL B := by
  refine ⟨hB.1, hB.2.1, ?_⟩
  intro w x y
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  let nG := normalizerPointsMap iL j i hc n
  have he : relativeWeylFullRealAction i (QuotientGroup.mk nG) =
      relativeWeylFullRealAction iL (QuotientGroup.mk n) := by
    change LinearEquiv.baseChange ℤ ℝ _ _ (weylAction i nG) =
      LinearEquiv.baseChange ℤ ℝ _ _ (weylAction iL n)
    rw [weylAction_normalizerPointsMap iL j i hc n]
  rw [← he]
  exact hB.2.2 (QuotientGroup.mk nG) x y

include hG hi hc in
/-- A shared relative root has the same real coroot in a Levi and the ambient group when both
use the same maximal split torus. -/
theorem sameTorus_realCoroot_eq (β : relativeRoots iL) (α : relativeRoots i)
    (h : β.val = α.val) : DL.realCoroot β = D.realCoroot α := by
  obtain ⟨B, hB⟩ := exists_isWeylInvariantInnerProduct hG hi
  have hBL := invariantForm_intrinsic j hc B hB
  apply (D.realCoroot_unique hi.isSplitSubtorus.1 B hB α _).mp
  intro x
  rw [← h]
  exact DL.coroot_mul_form iL B hBL β x

include hG hi hL hiL hνL hc in
private theorem intrinsicCorootSpan_eq (he : ΔL = J.val) :
    DL.realCorootSpan = corootSubspace D J.val := by
  obtain ⟨B, hB⟩ := exists_isWeylInvariantInnerProduct hL hiL
  have hspan : corootSubspace DL ΔL = DL.realCorootSpan :=
    (standardLeviRealDecomposition F L hL T iL hiL ν hνL DL).2.2.1.trans
      (DL.realCorootSpan_eq_annihilator hiL.isSplitSubtorus.1
        (isCompl_relativeRootSpanReal hL hiL) B hB).symm
  rw [← hspan]
  change Submodule.span ℝ (DL.realCorootsOf ΔL) = Submodule.span ℝ (D.realCorootsOf J.val)
  congr 1
  ext v
  constructor
  · rintro ⟨β, hβ, rfl⟩
    have hb : β.val ∈ J.val := he ▸ hβ
    let α : relativeRoots i := ⟨β.val, simpleRelativeRoots_subset_relativeRoots i ν (J.property hb)⟩
    exact ⟨α, hb, (sameTorus_realCoroot_eq hG hi j hc D DL β α rfl).symm⟩
  · rintro ⟨α, hα, rfl⟩
    have ha : α.val ∈ ΔL := he.symm ▸ hα
    let β : relativeRoots iL := ⟨α.val, simpleRelativeRoots_subset_relativeRoots iL ν ha⟩
    exact ⟨β, ha, sameTorus_realCoroot_eq hG hi j hc D DL β α rfl⟩

include hνL hc in
private theorem intrinsicWeight_eq (hν : IsGenericCocharacter i ν)
    (he : ΔL = J.val) (α : characterLattice T) (hα : α ∈ J.val)
    {x : V T} (hx : x ∈ corootSubspace D J.val) :
    weight hL hiL ν DL ΔL α x = weight hG hi ν D J.val α x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    have hb : β.val ∈ ΔL := he.symm ▸ hβ
    let v : relativeRoots iL := ⟨β.val, simpleRelativeRoots_subset_relativeRoots iL ν hb⟩
    rw [← sameTorus_realCoroot_eq hG hi j hc D DL v β rfl,
      weight_coroot hL hiL DL hνL subset_rfl (he.symm ▸ hα) v hb,
      sameTorus_realCoroot_eq hG hi j hc D DL v β rfl]
    rw [weight_coroot hG hi D hν J.property hα β hβ]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => simp only [map_smul, hx]

/-- A torus factorization through the lower group, genericity for both groups and the
Levi simple-root identification give the intrinsic chamber at the projected cutoffs. -/
def IntrinsicLeviChamberStatement : Prop :=
  iL ≫ j = i → IsGenericCocharacter iL ν → IsGenericCocharacter i ν →
  ΔL = J.val → ∀ T₀ Tp : V T,
    characteristicLeviChamber hG hi D J T₀ Tp =
      characteristicChamber ν hL hiL DL (T₀ - proj T₀) (Tp - proj Tp)

set_option maxHeartbeats 900000 in
/-- Compare both groups using the same invariant inner product and coroots, then compare
fundamental weights on their common Levi coroot span. -/
theorem intrinsicLeviChamber : IntrinsicLeviChamberStatement hG hi hL hiL j D DL J := by
  intro hc hνL hν he T₀ Tp
  have hspan := intrinsicCorootSpan_eq hG hi hL hiL j hc hνL D DL J he
  have hΔ : (simpleFinset ν hL hiL : Set (characterLattice T)) = J.val := by
    ext α
    exact (mem_simpleFinset _ _).trans (he ▸ Iff.rfl)
  ext x
  unfold characteristicLeviChamber characteristicChamber
  have hwt (α : characterLattice T) (ha : α ∈ J.val) (hx : x ∈ corootSubspace D J.val) :
      weight hL hiL ν DL (simpleFinset ν hL hiL : Set _) α (x - (Tp - proj Tp)) =
        weight hG hi ν D J.val α (x - (Tp - proj Tp)) := by
    have hF : (simpleFinset ν hL hiL : Set (characterLattice T)) = ΔL := hΔ.trans he.symm
    rw [hF]
    exact intrinsicWeight_eq hG hi hL hiL j hc hνL D DL J hν he α ha
      ((corootSubspace D J.val).sub_mem hx (sub_levelProjection_mem_span hG hi D J.val Tp))
  change (x ∈ corootSubspace D J.val ∧ _) ↔ (x ∈ DL.realCorootSpan ∧ _)
  rw [hspan]
  constructor
  · rintro ⟨hx, ha⟩
    refine ⟨hx, fun α hm => ?_⟩
    have hm' : α ∈ J.val := hΔ ▸ (show α ∈ (simpleFinset ν hL hiL : Set _) from hm)
    rw [hwt α hm' hx]
    exact ha α hm'
  · rintro ⟨hx, ha⟩
    refine ⟨hx, fun α hm => ?_⟩
    have hm' : α ∈ (simpleFinset ν hL hiL : Set (characterLattice T)) := hΔ.symm ▸ hm
    have hb := ha α hm'
    rwa [hwt α hm hx] at hb

end Langlands.Global.ArthurTruncation
