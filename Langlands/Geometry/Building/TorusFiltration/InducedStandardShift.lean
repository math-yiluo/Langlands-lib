import Langlands.Geometry.Building.TorusFiltration.InducedDepthPairs
import Langlands.Geometry.Building.TorusFiltration.Construction
import Langlands.Geometry.Building.KPInducedTorusIwahoriProof
import Langlands.GroupScheme.IntegralModel.CharacterValuationBound
import Langlands.Geometry.Building.UnramifiedStabilizerDescent

/-! # The first congruence shift of the induced standard filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalField
open Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
set_option quotPrecheck false

namespace Langlands.Geometry.Building

section Transport

variable {A k : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
  [Field k] [Algebra A k] [IsFractionRing A k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} (N : IntegralModel A k G) (d : G ≅ H)

private def modelWithGenericIso : IntegralModel A k H :=
  { N with genericIso := N.genericIso ≪≫ d }

omit [IsLocalRing A] in
private def modelWithGenericIso_iso : N.Iso (modelWithGenericIso N d) d where
  iso := Iso.refl _
  generic_comm := by simp [modelWithGenericIso]

omit [IsLocalRing A] in
private theorem modelWithGenericIso_integralPoints :
    (modelWithGenericIso N d).integralPoints = N.integralPoints.map (rationalPoints.map d.hom) :=
  (modelWithGenericIso_iso N d).map_integralPoints.symm

private theorem modelWithGenericIso_congruenceSubgroup :
    (modelWithGenericIso N d).congruenceSubgroup =
      N.congruenceSubgroup.map (rationalPoints.map d.hom) := by
  have h (x : N.integralSections) := (modelWithGenericIso_iso N d).integralPointMap_naturality x
  have hp (x : N.integralSections) :
      (modelWithGenericIso N d).integralPointMap x = rationalPoints.map d.hom (N.integralPointMap x) := by
    have hx := h x
    change (modelWithGenericIso N d).integralPointMap (rationalPoints.map (𝟙 N.group) x) = _ at hx
    rwa [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] at hx
  change N.congruenceKernel.map (modelWithGenericIso N d).integralPointMap =
    (N.congruenceKernel.map N.integralPointMap).map (rationalPoints.map d.hom)
  rw [Subgroup.map_map, show (modelWithGenericIso N d).integralPointMap =
    (rationalPoints.map d.hom).comp N.integralPointMap from MonoidHom.ext hp]

end Transport

section Coefficients

variable {k B B' : Type u} [Field k] [CommRing B] [Algebra k B] [Module.Finite k B]
  [Module.Projective k B] [CommRing B'] [Algebra k B'] [Module.Finite k B'] [Module.Projective k B']

private theorem rationalUnitsEquiv_congrIso (e : B ≃ₐ[k] B')
    (x : rationalPoints (WeilGm.groupScheme (CommRingCat.of k) B)) :
    (WeilGm.rationalUnitsEquiv k B'
      (rationalPoints.map (WeilGm.congrIso e).hom x) : B') =
      e (WeilGm.rationalUnitsEquiv k B x : B) := by
  let A := CommRingCat.of k
  let T := Over.mk (𝟙 (Spec A))
  rw [WeilGm.rationalUnitsEquiv_eq_sectionUnitsEquiv, WeilGm.rationalUnitsEquiv_eq_sectionUnitsEquiv]
  change WeilGm.sectionTensorEquiv A B'
    (WeilGm.pointsEquiv A B' T (x ≫ (WeilGm.congrIso e).hom.hom.hom)) =
      e (WeilGm.sectionTensorEquiv A B (WeilGm.pointsEquiv A B T x))
  rw [WeilGm.congrIso_hom_points, WeilGm.tensorUnitsEquiv_val]
  suffices h : ∀ z : B ⊗[A] ((algΓ A).obj T).unop,
      WeilGm.sectionTensorEquiv A B' (Algebra.TensorProduct.congr e AlgEquiv.refl z) =
        e (WeilGm.sectionTensorEquiv A B z) by
    exact h _
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
    rw [WeilGm.sectionTensorEquiv_tmul A B b a]
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.refl_toAlgHom, AlgHom.id_apply, AlgEquiv.coe_toAlgHom,
      WeilGm.sectionTensorEquiv_tmul]
    exact (e.toLinearEquiv.map_smul ((Scheme.ΓSpecIso A).hom a : k) b).symm
  | add x y hx hy => simp only [map_add, hx, hy]

end Coefficients

section Local

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "Ω" => SeparableClosure F
local notation "ν" => algebraicExtensionAddValuation F Ω

open InducedTorusShallow

/-- The standard positive terms on an induced torus are its geometric-character terms. -/
theorem localTorusFiltration_eq_geometric_of_induced
    (R : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine R.X.left]
    (hR : IsInducedTorus R) {r : ℝ≥0} (hr : 0 < r) :
    localTorusFiltration F R hR.isTorus r = localGeometricCharacterCongruence F R r := by
  let S := localTorusSplittingData F R hR.isTorus
  rw [localTorusFiltration_eq_of_splitting F S.L R hR.isTorus S.splits]
  exact localTorusFiltrationAtSplitting_eq_geometric_of_induced F S.L R S.splits hR hr

private theorem characterCongruence_map_iso
    {W R : CommGroupScheme (Spec (CommRingCat.of K))} (d : W.toGrp ≅ R.toGrp) (r : ℝ≥0) :
    (localGeometricCharacterCongruence F W r).map (rationalPoints.map d.hom) =
      localGeometricCharacterCongruence F R r := by
  apply le_antisymm (map_extendedCharacterCongruence_le K Ω ν W.toGrp d.hom r)
  intro x hx
  have h := map_extendedCharacterCongruence_le K Ω ν R.toGrp d.inv r ⟨x, hx, rfl⟩
  refine ⟨rationalPoints.map d.inv x, h, ?_⟩
  simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, d.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

set_option maxHeartbeats 4000000 in
private theorem exists_inducedStandardModel
    (R : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine R.X.left]
    (hR : IsInducedTorus R) (r : ℝ≥0) :
    ∃ N : IntegralModel O K R.toGrp, N.IsSmooth ∧
      N.integralPoints = localTorusFiltration F R hR.isTorus r ∧
      N.congruenceSubgroup = localTorusFiltration F R hR.isTorus (r + 1) := by
  classical
  let S := localTorusSplittingData F R hR.isTorus
  obtain ⟨n, E, ⟨e⟩⟩ := inducedTorusWeilDecomposition K S.L R S.splits hR
  let I := ULift.{u} (Fin n)
  let q : I ≃ Fin n := Equiv.ulift
  let E' (i : I) : IntermediateField K S.L := E (q i)
  let LtoOmega := IsScalarTower.toAlgHom K S.L Ω
  let D (i : I) : IntermediateField K Ω := (E' i).map LtoOmega
  let j (i : I) : E' i ≃ₐ[K] D i := (E' i).equivMap LtoOmega
  let : ∀ i, Algebra K (E i) := fun i => (E i).toSubalgebra.algebra
  let : ∀ i, Module K (E i) := fun i => @Algebra.toModule _ _ _ _ (E i).toSubalgebra.algebra
  let : ∀ i, SMul K (E i) := fun i => (E i).toSubalgebra.algebra.toSMul
  let : ∀ i, Algebra K (E' i) := fun i => (E' i).toSubalgebra.algebra
  let : ∀ i, Module K (E' i) := fun i => @Algebra.toModule _ _ _ _ (E' i).toSubalgebra.algebra
  let : ∀ i, SMul K (E' i) := fun i => (E' i).toSubalgebra.algebra.toSMul
  let : ∀ i, Algebra K (D i) := fun i => (D i).toSubalgebra.algebra
  let : ∀ i, Module K (D i) := fun i => @Algebra.toModule _ _ _ _ (D i).toSubalgebra.algebra
  let : ∀ i, SMul K (D i) := fun i => (D i).toSubalgebra.algebra.toSMul
  let B₀ := ∀ i, E i
  let B₁ := ∀ i, E' i
  let B₂ := ∀ i, D i
  let A₀ : Algebra K B₀ := Pi.algebra _ _
  let A₁ : Algebra K B₁ := Pi.algebra _ _
  let A₂ : Algebra K B₂ := Pi.algebra _ _
  let : Module K B₀ := @Algebra.toModule _ _ _ _ A₀
  let : Module K B₁ := @Algebra.toModule _ _ _ _ A₁
  let : Module K B₂ := @Algebra.toModule _ _ _ _ A₂
  let : SMul K B₀ := A₀.toSMul
  let : SMul K B₁ := A₁.toSMul
  let : SMul K B₂ := A₂.toSMul
  let : ∀ i, FiniteDimensional K (E i) := fun i => IntermediateField.finiteDimensional_left (E i)
  let : ∀ i, FiniteDimensional K (E' i) := fun i => IntermediateField.finiteDimensional_left (E' i)
  let : ∀ i, FiniteDimensional K (D i) := fun i => Module.Finite.equiv (j i).toLinearEquiv
  let : Module.Finite K B₀ := Module.Finite.pi
  let : Module.Finite K B₁ := Module.Finite.pi
  let : Module.Finite K B₂ := Module.Finite.pi
  let : Module.Projective K B₀ := Module.Projective.of_basis (Module.Basis.ofVectorSpace K B₀)
  let : Module.Projective K B₁ := Module.Projective.of_basis (Module.Basis.ofVectorSpace K B₁)
  let : Module.Projective K B₂ := Module.Projective.of_basis (Module.Basis.ofVectorSpace K B₂)
  let : Algebra K (∀ i : I, E (q i)) := A₁
  let reindex : B₀ ≃ₐ[K] B₁ := (AlgEquiv.piCongrLeft K (fun i : Fin n => E i) q).symm
  let eB : B₁ ≃ₐ[K] B₂ := AlgEquiv.piCongrRight j
  let W₁ := WeilGm.commGroupScheme (CommRingCat.of K) B₁
  let W₂ := WeilGm.commGroupScheme (CommRingCat.of K) B₂
  let e₁ : R ≅ W₁ := e ≪≫ WeilGm.commCongrIso reindex
  let e₂ : R ≅ W₂ := e₁ ≪≫ WeilGm.commCongrIso eB
  let d : W₂.toGrp ≅ R.toGrp :=
    { hom := CommGroupScheme.groupHom e₂.inv
      inv := CommGroupScheme.groupHom e₂.hom
      hom_inv_id := congrArg CommGroupScheme.groupHom e₂.inv_hom_id
      inv_hom_id := congrArg CommGroupScheme.groupHom e₂.hom_inv_id }
  let P (s : ℝ≥0) := depthModel F D s
  let N (s : ℝ≥0) := modelWithGenericIso (P s) d
  have hpoints (s : ℝ≥0) : (N s).integralPoints = localTorusFiltration F R hR.isTorus s := by
    by_cases hs : s = 0
    · subst s
      rw [localTorusFiltration_zero F S.L R hR.isTorus S.splits,
        inducedTorusIwahori F R S.L S.splits hR]
      apply le_antisymm
      · rw [← characterValuationKernel_eq_of_isEquiv (MaximalUnramified.valuation_isEquiv F)]
        exact (N 0).integralPoints_le_characterValuationKernel fun a =>
          ((MaximalUnramified.valuation_isEquiv F).le_one_iff_le_one).mpr a.property
      · intro x hx
        let y := rationalPoints.map (CommGroupScheme.groupHom e₁.hom) x
        have hy : y ∈ characterValuationKernel (fixedFieldValuation F) W₁.toGrp :=
          map_characterValuationKernel_le (fixedFieldValuation F)
            (CommGroupScheme.groupHom e₁.hom) ⟨x, hx, rfl⟩
        let z := rationalPoints.map (WeilGm.congrIso eB).hom y
        have hz (i : I) :
            intermediateValuation F (D i) ((WeilGm.rationalUnitsEquiv K B₂ z).val i) = 1 := by
          have h := WeilGm.product_coordinate_valuation_eq_one_of_mem K S.L E'
            (fixedFieldValuation F) (intermediateValuation F S.L)
            (intermediateValuation_conjugate F S.L) y hy i
          have hval := congrFun (rationalUnitsEquiv_congrIso eB y) i
          change (WeilGm.rationalUnitsEquiv K B₂ z).val i =
            j i ((WeilGm.rationalUnitsEquiv K B₁ y).val i) at hval
          rw [hval]
          exact h
        have hz₀ : z ∈ (P 0).integralPoints :=
          mem_depthModel_zero_of_coordinate_valuation F D z hz
        change x ∈ (modelWithGenericIso (P 0) d).integralPoints
        rw [modelWithGenericIso_integralPoints]
        refine ⟨z, hz₀, ?_⟩
        have hzi : z = rationalPoints.map d.inv x := by
          change (x ≫ (CommGroupScheme.groupHom e₁.hom).hom.hom) ≫
            (CommGroupScheme.groupHom (WeilGm.commCongrIso eB).hom).hom.hom =
              x ≫ (CommGroupScheme.groupHom (e₁.hom ≫ (WeilGm.commCongrIso eB).hom)).hom.hom
          rw [comp_groupHom_comp]
        rw [hzi]
        simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, d.inv_hom_id,
          Grp.id_hom_hom, Category.comp_id]
    · have hs' := pos_of_ne_zero hs
      change (modelWithGenericIso (depthModel F D s) d).integralPoints = _
      rw [modelWithGenericIso_integralPoints, depthModel_integralPoints_positive F D s hs',
        localTorusFiltration_eq_geometric_of_induced F R hR hs']
      exact characterCongruence_map_iso F d s
  refine ⟨N r, depthModel_smooth F D r, hpoints r, ?_⟩
  change (modelWithGenericIso (depthModel F D r) d).congruenceSubgroup = _
  rw [modelWithGenericIso_congruenceSubgroup, depthModel_congruenceSubgroup,
    ← modelWithGenericIso_integralPoints]
  exact hpoints (r + 1)

private theorem congruenceSubgroup_le_of_integralPoints_le
    {R : CommGroupScheme (Spec (CommRingCat.of K))} {M N : IntegralModel O K R.toGrp}
    (hM : M.IsSmooth) (h : M.integralPoints ≤ N.integralPoints) :
    M.congruenceSubgroup ≤ N.congruenceSubgroup := by
  have hp : M.integralPoints.map (rationalPoints.map (𝟙 R.toGrp)) ≤ N.integralPoints := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using h hx
  obtain ⟨f⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F hM rfl hp
  rw [← M.congruenceSubgroupAt_one, ← N.congruenceSubgroupAt_one]
  intro x hx
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
    f.map_mem_congruenceSubgroupAt 1 hx

/-- For a smooth model of an induced standard term, reduction to the identity
cuts out the next term one unit deeper. -/
theorem inducedStandardCongruence
    (R : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine R.X.left] (hR : IsInducedTorus R)
    (r : ℝ≥0) (M : IntegralModel O K R.toGrp)
    (hM : M.IsSmooth) (h : M.integralPoints = localTorusFiltration F R hR.isTorus r) :
    M.congruenceSubgroup = localTorusFiltration F R hR.isTorus (r + 1) := by
  obtain ⟨N, hN, hpoints, hshift⟩ := exists_inducedStandardModel F R hR r
  have heq := h.trans hpoints.symm
  exact (le_antisymm (congruenceSubgroup_le_of_integralPoints_le F hM heq.le)
    (congruenceSubgroup_le_of_integralPoints_le F hN heq.ge)).trans hshift

end Local

end Langlands.Geometry.Building
