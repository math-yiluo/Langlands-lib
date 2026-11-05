import Langlands.Geometry.Building.KPLocalSplitNorm
import Langlands.GroupScheme.GaloisPointTowerBaseChange

/-! # Relative bounded norms on direct base changes -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

section Iso

variable {k : Type u} [Field k] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation k Γ) {G H : GroupScheme (Spec (CommRingCat.of k))}

private theorem rationalPoints_iso_inv_hom (e : G ≅ H) (x : rationalPoints H) :
    rationalPoints.map e.hom (rationalPoints.map e.inv x) = x := by
  change (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x
  rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id]
  rfl

/-- An actual group-scheme isomorphism identifies the character-valuation kernels. -/
def characterValuationKernelEquivOfIso (e : G ≅ H) :
    characterValuationKernel v G ≃* characterValuationKernel v H where
  toFun x := ⟨rationalPoints.map e.hom x,
    map_characterValuationKernel_le v e.hom ⟨x, x.property, rfl⟩⟩
  invFun x := ⟨rationalPoints.map e.inv x,
    map_characterValuationKernel_le v e.inv ⟨x, x.property, rfl⟩⟩
  left_inv x := Subtype.ext (by
    change (x.val ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = x.val
    rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id]
    rfl)
  right_inv x := Subtype.ext (by
    change (x.val ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x.val
    rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id]
    rfl)
  map_mul' x y := Subtype.ext ((rationalPoints.map e.hom).map_mul x.val y.val)

end Iso

section NormIso

variable (L M : Type u) [Field L] [Field M] [Algebra L M]
  [FiniteDimensional L M] [IsGalois L M]
  {ΓL ΓM : Type*} [LinearOrderedCommGroupWithZero ΓL]
  [LinearOrderedCommGroupWithZero ΓM]
  (vL : Valuation L ΓL) (vM : Valuation M ΓM) [vL.HasExtension vM]
  (hinv : ∀ (σ : M ≃ₐ[L] M) (z : M), vM (σ z) = vM z)
  (T : CommGroupScheme (Spec (CommRingCat.of L))) [IsAffine T.X.left]
  (G : GroupScheme (Spec (CommRingCat.of M)))
  (e : ((CommGroupScheme.baseChange (baseMap L M)).obj T).toGrp ≅ G)
  (N : rationalPoints G →* rationalPoints T.toGrp)
  (hN : ∀ y, N (rationalPoints.map e.hom y) = rationalNorm L M T y)

include hinv hN in
private theorem normKernel_transport_mem (x : characterValuationKernel vM G) :
    N x ∈ characterValuationKernel vL T.toGrp := by
  let y := rationalPoints.map e.inv x.val
  have hy : y ∈ characterValuationKernel vM
      ((CommGroupScheme.baseChange (baseMap L M)).obj T).toGrp :=
    map_characterValuationKernel_le vM e.inv ⟨x.val, x.property, rfl⟩
  have hn := hN y
  change N (rationalPoints.map e.hom (rationalPoints.map e.inv x.val)) = _ at hn
  rw [rationalPoints_iso_inv_hom] at hn
  rw [hn]
  exact torusNormIwahori_le_characterValuationKernel vL vM hinv T ⟨y, hy, rfl⟩

omit [vL.HasExtension vM] in
include hN in
private theorem normKernel_transport_lift
    (hunit : ∀ a : Lˣ, vL (a : L) = 1 →
      ∃ b : Mˣ, vM (b : M) = 1 ∧ Units.map (Algebra.norm L) b = a)
    (hT : IsSplitTorus T.toGrp) (t : characterValuationKernel vL T.toGrp) :
    ∃ x : characterValuationKernel vM G, N x = t.val := by
  obtain ⟨y, hy, hyt⟩ := (mem_torusNormIwahori L M).mp
    (split_kernel_le_torusNormIwahori L M vL vM hunit T hT t.property)
  let x := rationalPoints.map e.hom y
  have hx : x ∈ characterValuationKernel vM G :=
    map_characterValuationKernel_le vM e.hom ⟨y, hy, rfl⟩
  exact ⟨⟨x, hx⟩, (hN y).trans hyt⟩

end NormIso

section Tower

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  [FiniteDimensional L M] [IsGalois L M]
  {ΓL ΓM : Type*} [LinearOrderedCommGroupWithZero ΓL]
  [LinearOrderedCommGroupWithZero ΓM]
  (vL : Valuation L ΓL) (vM : Valuation M ΓM) [vL.HasExtension vM]
  (hinv : ∀ (σ : M ≃ₐ[L] M) (z : M), vM (σ z) = vM z)
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

private def commTowerIso :
    ((CommGroupScheme.baseChange (baseMap L M)).obj
      ((CommGroupScheme.baseChange (baseMap k L)).obj T)).toGrp ≅
        ((CommGroupScheme.baseChange (baseMap k M)).obj T).toGrp :=
  towerBaseChangeIso k L M T.toGrp

omit [FiniteDimensional L M] [IsGalois L M] [IsAffine T.X.left] in
private theorem commTowerIso_hom :
    (commTowerIso k L M T).hom = (towerBaseChangeIso k L M T.toGrp).hom := rfl

omit [FiniteDimensional L M] [IsGalois L M] [IsAffine T.X.left] in
private theorem commTowerIso_map
    (y : rationalPoints ((CommGroupScheme.baseChange (baseMap L M)).obj
      ((CommGroupScheme.baseChange (baseMap k L)).obj T)).toGrp) :
    rationalPoints.map (commTowerIso k L M T).hom y =
      rationalPoints.map (towerBaseChangeIso k L M T.toGrp).hom y :=
  by
    apply Over.OverMorphism.ext
    change y.left ≫ (commTowerIso k L M T).hom.hom.hom.left =
      y.left ≫ (towerBaseChangeIso k L M T.toGrp).hom.hom.hom.left
    rfl

private theorem relativeNorm_commTowerIso
    (y : rationalPoints ((CommGroupScheme.baseChange (baseMap L M)).obj
      ((CommGroupScheme.baseChange (baseMap k L)).obj T)).toGrp) :
    relativeRationalNorm k L M T (rationalPoints.map (commTowerIso k L M T).hom y) =
      rationalNorm L M ((CommGroupScheme.baseChange (baseMap k L)).obj T) y :=
  (congrArg (relativeRationalNorm k L M T) (commTowerIso_map k L M T y)).trans
    (relativeRationalNorm_towerBaseChangeIso k L M T y)

include hinv in
private theorem relativeRationalNorm_mem
    (x : characterValuationKernel vM
      ((CommGroupScheme.baseChange (baseMap k M)).obj T).toGrp) :
    relativeRationalNorm k L M T x ∈
      characterValuationKernel vL ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp :=
  normKernel_transport_mem L M vL vM hinv
    ((CommGroupScheme.baseChange (baseMap k L)).obj T)
    ((CommGroupScheme.baseChange (baseMap k M)).obj T).toGrp
    (commTowerIso k L M T) (relativeRationalNorm k L M T)
    (relativeNorm_commTowerIso k L M T) x

/-- The relative norm restricted to bounded points of the two direct base changes. -/
def relativeBoundedRationalNorm :
    characterValuationKernel vM ((CommGroupScheme.baseChange (baseMap k M)).obj T).toGrp →*
      characterValuationKernel vL ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp :=
  ((relativeRationalNorm k L M T).comp
    (characterValuationKernel vM
      ((CommGroupScheme.baseChange (baseMap k M)).obj T).toGrp).subtype).codRestrict _
        (relativeRationalNorm_mem k L M vL vM hinv T)

@[simp] theorem relativeBoundedRationalNorm_coe
    (x : characterValuationKernel vM
      ((CommGroupScheme.baseChange (baseMap k M)).obj T).toGrp) :
    (relativeBoundedRationalNorm k L M vL vM hinv T x :
      rationalPoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp) =
        relativeRationalNorm k L M T x := rfl

/-- Surjectivity for a split lower base change follows from scalar unit norms. -/
theorem relativeBoundedRationalNorm_surjective_of_split
    (hunit : ∀ a : Lˣ, vL (a : L) = 1 →
      ∃ b : Mˣ, vM (b : M) = 1 ∧ Units.map (Algebra.norm L) b = a)
    (hT : IsSplitTorus (baseChanged k L T.toGrp)) :
    Function.Surjective (relativeBoundedRationalNorm k L M vL vM hinv T) := by
  intro t
  obtain ⟨x, hxt⟩ := normKernel_transport_lift L M vL vM
    ((CommGroupScheme.baseChange (baseMap k L)).obj T)
    ((CommGroupScheme.baseChange (baseMap k M)).obj T).toGrp
    (commTowerIso k L M T) (relativeRationalNorm k L M T)
    (relativeNorm_commTowerIso k L M T) hunit hT t
  exact ⟨x, Subtype.ext hxt⟩

end Tower

section Local

open Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) E]
  (L : IntermediateField E (SeparableClosure F)) [FiniteDimensional E L] [IsGalois E L]
  (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffine T.X.left]

/-- The bounded relative norm for nested intermediate fields of the separable closure. -/
def relativeInertiaBoundedNorm :
    characterValuationKernel (nestedIntermediateValuation F E L)
        ((CommGroupScheme.baseChange (baseMap (UnramifiedClosure F) L)).obj T).toGrp →*
      characterValuationKernel (intermediateValuation F E)
        ((CommGroupScheme.baseChange (baseMap (UnramifiedClosure F) E)).obj T).toGrp :=
  relativeBoundedRationalNorm (UnramifiedClosure F) E L
    (intermediateValuation F E) (nestedIntermediateValuation F E L)
    (nestedIntermediateValuation_conjugate F E L) T

/-- A lower splitting field suffices for actual bounded relative norm surjectivity. -/
theorem relativeInertiaBoundedNorm_surjective_of_split
    (hT : IsSplitTorus (baseChanged (UnramifiedClosure F) E T.toGrp)) :
    Function.Surjective (relativeInertiaBoundedNorm F E L T) :=
  relativeBoundedRationalNorm_surjective_of_split (UnramifiedClosure F) E L
    (intermediateValuation F E) (nestedIntermediateValuation F E L)
    (nestedIntermediateValuation_conjugate F E L)
    T (nestedIntermediate_unit_norm_surjective F E L) hT

end Local

end Langlands.Geometry.Building
