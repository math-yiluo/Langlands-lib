import Langlands.Geometry.Building.KPLocalTorusCharacterFiltration
import Langlands.Geometry.Building.KPLocalWeilRestrictionCongruence

/-! # Normalized character depths in the coordinates of an induced torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalField Langlands.LocalGalois.Separable
open Langlands.Algebra.SeparableTensor
open scoped CategoryTheory.MonObj NNReal TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
set_option quotPrecheck false

namespace Langlands.BruhatTits.IntegralModels

private theorem mem_characterCongruence_map_iso {k : Type u} [Field k]
    (ω : AddValuation k (WithTop ℝ)) {G H : GroupScheme (Spec (CommRingCat.of k))}
    (e : G ≅ H) (r : ℝ≥0) (x : rationalPoints G) :
    rationalPoints.map e.hom x ∈ characterCongruence ω H r ↔
      x ∈ characterCongruence ω G r := by
  constructor
  · intro hx
    have h := map_characterCongruence_le ω e.inv r ⟨_, hx, rfl⟩
    simpa only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      e.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using h
  · intro hx
    exact map_characterCongruence_le ω e.hom r ⟨_, hx, rfl⟩

private theorem mem_gm_characterCongruence (k : Type u) [Field k]
    (ω : AddValuation k (WithTop ℝ)) (r : ℝ≥0)
    (x : rationalPoints (Gm (Spec (CommRingCat.of k))).toGrp) :
    x ∈ characterCongruence ω (Gm (Spec (CommRingCat.of k))).toGrp r ↔
      Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k))) x ∈ addValuationUnitFiltration ω r := by
  constructor
  · intro hx
    exact (mem_characterCongruence ω _ _ _).mp hx (Additive.ofMul (𝟙 _))
  · intro hx
    rw [mem_characterCongruence]
    intro χ
    let φ : Gm (Spec (CommRingCat.of k)) ⟶ Gm (Spec (CommRingCat.of k)) := χ
    change Gm.affinePointsEquiv (𝟙 _) (x ≫ (CommGroupScheme.groupHom φ).hom.hom) ∈ _
    rw [← (gmEndEquiv k).symm_apply_apply φ, gmEndEquiv_symm_comp, map_zpow]
    exact Subgroup.zpow_mem _ hx _

private theorem mem_split_characterCongruence (k : Type u) [Field k]
    (ω : AddValuation k (WithTop ℝ)) (r : ℝ≥0) (J : Type u) [Fintype J]
    (x : rationalPoints (splitTorus (Spec (CommRingCat.of k)) J)) :
    x ∈ characterCongruence ω _ r ↔
      ∀ j, splitTorus.affinePointsEquiv J (𝟙 (Spec (CommRingCat.of k))) x j ∈
        addValuationUnitFiltration ω r := by
  constructor
  · intro hx j
    exact (mem_gm_characterCongruence k ω r _).mp
      (map_characterCongruence_le ω
        (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) J j)) r
        ⟨x, hx, rfl⟩)
  · intro hx
    rw [splitPoint_decomposition k J x]
    apply Subgroup.prod_mem
    intro j _
    have hj := (mem_gm_characterCongruence k ω r
      (rationalPoints.map
        (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) J j)) x)).mpr (hx j)
    exact map_characterCongruence_le ω
      (CommGroupScheme.groupHom (splitTorus.single (Spec (CommRingCat.of k)) J j)) r
      ⟨_, hj, rfl⟩

namespace InducedTorusShallow

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "K" => inertiaFixedField F
local notation "Ω" => SeparableClosure F
local notation "ν" => algebraicExtensionAddValuation F Ω

variable {I : Type u} [Fintype I] (E : I → IntermediateField (inertiaFixedField F) (SeparableClosure F))
  [∀ i, FiniteDimensional (inertiaFixedField F) (E i)]

local instance : ∀ i, Algebra K (E i) := fun i => (E i).toSubalgebra.algebra
local instance : ∀ i, Module K (E i) := fun i =>
  @Algebra.toModule _ _ _ _ (E i).toSubalgebra.algebra
local instance : ∀ i, SMul K (E i) := fun i => (E i).toSubalgebra.algebra.toSMul

local instance productAlgebra : Algebra K (∀ i, E i) := Pi.algebra _ _
local instance : Module K (∀ i, E i) := @Algebra.toModule _ _ _ _ (productAlgebra F E)
local instance : SMul K (∀ i, E i) := (productAlgebra F E).toSMul

local instance : FiniteDimensional K (∀ i, E i) := Module.Finite.pi
local instance : Module.Projective K (∀ i, E i) :=
  Module.Projective.of_basis (Module.Basis.ofVectorSpace K (∀ i, E i))

local notation "B" => (∀ i, E i)
local notation "J" => (Σ i, E i →ₐ[K] Ω)
local notation "W" => WeilGm.commGroupScheme (CommRingCat.of K) B

/-- The product coefficient algebra splits in all its geometric embeddings. -/
def geometricCoefficientEquiv : Ω ⊗[K] B ≃ₐ[Ω] (J → Ω) := by
  classical
  exact ((Algebra.TensorProduct.piRight K Ω Ω (fun i => E i)).trans
    (AlgEquiv.piCongrRight fun i => WeilGm.separableEmbeddingDecomposition K (E i) Ω
      (WeilGm.separable_minpoly_splits K (E i) Ω))).trans
    { (Equiv.piCurry fun i (_ : E i →ₐ[K] Ω) => Ω).symm with
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

@[simp] theorem geometricCoefficientEquiv_tmul (c : Ω) (b : B) (j : J) :
    geometricCoefficientEquiv F E (c ⊗ₜ b) j = c * j.2 (b j.1) := rfl

omit [Fintype I] in
private theorem geometric_value_embedding (i : I) (τ : E i →ₐ[K] Ω) (z : E i) :
    ν (τ z) = ν (z : Ω) := by
  let h := MaximalUnramified.valuationSubring_isHenselian F
  rw [MaximalUnramified.coordinateEmbedding_preserves_value F (E i) h τ z]
  exact (MaximalUnramified.coordinateEmbedding_preserves_value F (E i) h (E i).val z).symm

/-- The full geometric-character test reduces to the normalized depth of each
unit coordinate of the rational Weil point. -/
theorem mem_geometricCharacterCongruence_iff (r : ℝ≥0) (hr : 0 < r)
    (x : rationalPoints (W).toGrp) :
    x ∈ localGeometricCharacterCongruence F W r ↔
      ∀ i, ((r : ℝ) : WithTop ℝ) ≤ ν
        (((WeilGm.rationalUnitsEquiv K B x : B) i : Ω) - 1) := by
  classical
  let e := geometricCoefficientEquiv F E
  let d := WeilGm.commDecompositionIso (CommRingCat.of K) (CommRingCat.of Ω) B J e
  let y := rationalExtend K Ω (W).toGrp x
  change y ∈ characterCongruence ν _ r ↔ _
  let d' : baseChanged K Ω (W).toGrp ≅ splitTorus (Spec (CommRingCat.of Ω)) J :=
    { hom := CommGroupScheme.groupHom d.hom
      inv := CommGroupScheme.groupHom d.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom d.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom d.inv_hom_id }
  rw [← mem_characterCongruence_map_iso ν d' r y,
    mem_split_characterCongruence]
  have hcoord (j : J) :
      (splitTorus.affinePointsEquiv J (𝟙 (Spec (CommRingCat.of Ω)))
        (rationalPoints.map d'.hom y) j : Ω) =
        j.2 ((WeilGm.rationalUnitsEquiv K B x : B) j.1) := by
    change (splitTorus.affinePointsEquiv J (𝟙 (Spec (CommRingCat.of Ω)))
      (rationalPoints.map (CommGroupScheme.groupHom d.hom) y) j : Ω) = _
    rw [WeilGm.decomposition_rational_coordinate K Ω B J e y j]
    dsimp only [y]
    rw [WeilGm.extensionUnitsEquiv_extend]
    change geometricCoefficientEquiv F E (1 ⊗ₜ (WeilGm.rationalUnitsEquiv K B x : B)) j = _
    rw [geometricCoefficientEquiv_tmul, one_mul]
  simp only [mem_addValuationUnitFiltration_of_pos ν hr, hcoord]
  constructor
  · intro h i
    exact h ⟨i, (E i).val⟩
  · intro h ⟨i, τ⟩
    rw [← map_one τ, ← map_sub, geometric_value_embedding F E i τ]
    exact h i

end InducedTorusShallow
end Langlands.BruhatTits.IntegralModels
