import Langlands.GroupScheme.Reductive.TitsKernelIndexData
import Langlands.GroupScheme.Rational.NumberFieldTorusCyclotomicSplitting
import Langlands.GaloisCohomology.CyclotomicKilling.UnitsLatticeStatement
import Langlands.GroupScheme.CocycleBaseChangeFactor
import Langlands.GroupScheme.GaloisCocycleScalarExtension
import Langlands.GroupScheme.GaloisCocycleFiniteRecovery
import Langlands.GroupScheme.GaloisPointTransitivity
import Langlands.GroupScheme.Torus.SplitCoverCocycleVanishing
import Langlands.GroupScheme.Torus.LatticeGaloisContinuityProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Torus.MaximalAmbient
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Torus cocycles over number fields from the cocycles of `Ωˣ ⊗ X` -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.NumberFieldTorusCyclotomicSplittingReduction

set_option backward.isDefEq.respectTransparency false

open Langlands.GaloisCohomology Langlands.GroupScheme.TorusPointsTensorGalois

attribute [-instance] ULift.module

section Lattice

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  (T : CommGroupScheme (Spec (CommRingCat.of K)))

/-- Over a field where the torus splits, the cocharacter representation is finitely
generated. -/
theorem latticeRepresentation_finite (hT : IsSplitTorus (baseChanged K Ω T).toGrp) :
    Module.Finite (ULift.{u} ℤ) (latticeRepresentation K Ω T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let c := (TorusPointsTensor.latticeCongr
    (T := baseChanged K Ω T)
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of Ω)) I) e).trans
      (TorusPointsTensor.latticeCoordinates Ω I)
  exact Module.Finite.equiv c.symm

/-- Over an algebraic extension where the torus splits, the cocharacter representation is
smooth for the Krull topology. -/
theorem latticeRepresentation_isSmoothRep [Algebra.IsAlgebraic K Ω]
    (hT : IsSplitTorus (baseChanged K Ω T).toGrp) :
    IsSmoothRep (latticeRepresentation K Ω T) := by
  obtain ⟨L₀, hL₀, hfix⟩ := torusLatticeGaloisContinuity K Ω T hT
  refine IsSmoothRep.of_isOpen_stabilizer _ fun ν => ?_
  refine Subgroup.isOpen_mono (H₁ := L₀.fixingSubgroup) ?_ (L₀.fixingSubgroup_isOpen)
  intro σ hσ
  rw [mem_vectorStabilizer]
  have h := (hfix σ fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx).2
  change (cocharacterLattice.galoisRepresentation K Ω T σ) ν = ν
  rw [h]
  rfl

end Lattice

section Assembly

variable {K E₀ L M Ω : Type u} [Field K] [Field E₀] [Field L] [Field M] [Field Ω]
  [Algebra K E₀] [Algebra K L] [Algebra K M] [Algebra K Ω] [Algebra E₀ M] [Algebra L M]
  [Algebra M Ω] [Algebra L Ω]
  [IsScalarTower K E₀ M] [IsScalarTower K L M] [IsScalarTower K M Ω] [IsScalarTower K L Ω]
  [IsScalarTower L M Ω]
  (T : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left]

omit [Field E₀] [Algebra K E₀] [Algebra E₀ M] [IsScalarTower K E₀ M] in
/-- Extension of points along a tower of fields is transitive. -/
theorem relativeExtend_trans (x : affinePoints T.toGrp (CommAlgCat.of K L)) :
    GaloisPoint.relativeExtend K M Ω T.toGrp (GaloisPoint.relativeExtend K L M T.toGrp x) =
      GaloisPoint.relativeExtend K L Ω T.toGrp x := by
  apply (GaloisPoint.coordinates K T.toGrp Ω).injective
  ext a
  simp only [GaloisPoint.coordinates_relativeExtend]
  exact (IsScalarTower.algebraMap_apply L M Ω _).symm

omit [Field E₀] [Algebra K E₀] [Algebra E₀ M] [IsScalarTower K E₀ M] [IsAffine T.X.left] in
/-- Restricting a lift and then restricting further is the direct restriction. -/
theorem restrictNormal_restrictNormal [Normal K L] [Normal K M] (σ : Ω ≃ₐ[K] Ω) :
    (σ.restrictNormal M).restrictNormal L = σ.restrictNormal L := by
  ext x
  apply (algebraMap L Ω).injective
  rw [AlgEquiv.restrictNormal_commutes, IsScalarTower.algebraMap_apply L M Ω,
    IsScalarTower.algebraMap_apply L M Ω, AlgEquiv.restrictNormal_commutes,
    AlgEquiv.restrictNormal_commutes]

variable [FiniteDimensional E₀ M] [IsGalois E₀ M] [Normal K L] [Normal K M] [Normal K Ω]
  [IsGalois M Ω]

/-- A point of the torus over `Ω`, fixed by `Gal(Ω/M)`, whose coboundary on the automorphisms
fixing `E₀` is the inflated cocycle, trivializes the base change of the cocycle to `E₀`. -/
theorem isTrivial_baseChangePullback_of_point (τ : Cocycle T.toGrp (GaloisCocycle.cover K L))
    (a : affinePoints T.toGrp (CommAlgCat.of K Ω))
    (hfix : ∀ σ : Ω ≃ₐ[M] Ω, GaloisPoint.conjugate K Ω T.toGrp (σ.restrictScalars K) a = a)
    (hcob : ∀ σ : Ω ≃ₐ[K] Ω,
      (∀ x : E₀, σ (algebraMap M Ω (algebraMap E₀ M x)) = algebraMap M Ω (algebraMap E₀ M x)) →
      GaloisPoint.relativeExtend K L Ω T.toGrp (GaloisCocycle.value τ (σ.restrictNormal L)) =
        GaloisPoint.conjugate K Ω T.toGrp σ a * a⁻¹) :
    (τ.baseChangePullback (Spec.algebraMap K E₀)).IsTrivial := by
  apply GaloisCocycle.isTrivial_baseChange_of_scalarExtension (K := E₀) (M := M)
  rw [GaloisCocycle.isTrivial_iff]
  let aM := GaloisPoint.relativeAlgebraicDescend K M Ω T.toGrp ⟨a, fun σ => hfix σ⟩
  have haM : GaloisPoint.relativeExtend K M Ω T.toGrp aM = a :=
    GaloisPoint.relativeExtend_relativeAlgebraicDescend K M Ω T.toGrp _
  refine ⟨(GaloisCocycle.scalarExtensionPointsEquiv (K := E₀) (M := M) T.toGrp).symm (aM⁻¹),
    fun σ => ?_⟩
  apply (GaloisCocycle.scalarExtensionPointsEquiv (K := E₀) (M := M) T.toGrp).injective
  have hconj := GaloisCocycle.scalarExtensionPointsEquiv_conjugate (F := K) (K := E₀)
    (M := M) (G := T.toGrp)
    ((GaloisCocycle.scalarExtensionPointsEquiv (K := E₀) (M := M) T.toGrp).symm (aM⁻¹)) σ
  rw [GaloisCocycle.value_scalarExtension, map_mul,
    map_inv (GaloisCocycle.scalarExtensionPointsEquiv (K := E₀) (M := M) T.toGrp)
      (GaloisPoint.conjugate E₀ M _ σ _), hconj, MulEquiv.apply_symm_apply]
  apply GaloisPoint.relativeExtend_injective K M Ω T.toGrp
  set σK : M ≃ₐ[K] M := σ.restrictScalars K
  set σΩ : Ω ≃ₐ[K] Ω := σK.liftNormal Ω
  have hfixE : ∀ x : E₀, σΩ (algebraMap M Ω (algebraMap E₀ M x)) =
      algebraMap M Ω (algebraMap E₀ M x) := by
    intro x
    rw [AlgEquiv.liftNormal_commutes]
    congr 1
    exact σ.commutes x
  have hres : σΩ.restrictNormal L = σK.restrictNormal L := by
    rw [← restrictNormal_restrictNormal (M := M) σΩ, AlgEquiv.restrict_liftNormal]
  rw [relativeExtend_trans, map_mul, map_inv, map_inv]
  change _ = GaloisPoint.relativeExtend K M Ω T.toGrp aM⁻¹ *
    (GaloisPoint.relativeExtend K M Ω T.toGrp (GaloisPoint.conjugate K M T.toGrp σK aM⁻¹))⁻¹
  rw [GaloisPoint.relativeExtend_conjugate_lift, map_inv, map_inv, haM, ← hres, hcob σΩ hfixE,
    inv_inv, mul_comm]

end Assembly

section Cocycle

variable {K L Ω : Type u} [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
  [Algebra L Ω] [IsScalarTower K L Ω] [Normal K L]
  (T : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left]
  (τ : Cocycle T.toGrp (GaloisCocycle.cover K L))

/-- The values of a cocycle on the cover `Spec L → Spec K`, inflated to `Gal(Ω/K)` through
restriction to `L` and extended to points over `Ω`, written additively. -/
def pointCocycle (σ : Ω ≃ₐ[K] Ω) :
    ↑(GaloisCocycle.pointRepresentation (G := T.toGrp) (k := K) (L := Ω)) :=
  Additive.ofMul (GaloisPoint.relativeExtend K L Ω T.toGrp
    (GaloisCocycle.value τ (σ.restrictNormal L)))

/-- The inflated values form a `1`-cocycle for the Galois action on the points over `Ω`. -/
theorem pointCocycle_mul (σ σ' : Ω ≃ₐ[K] Ω) :
    pointCocycle (Ω := Ω) T τ (σ * σ') = pointCocycle T τ σ +
      (GaloisCocycle.pointRepresentation (G := T.toGrp) (k := K) (L := Ω)).ρ σ
        (pointCocycle T τ σ') := by
  have h : (σ * σ').restrictNormal L = σ.restrictNormal L * σ'.restrictNormal L :=
    map_mul (AlgEquiv.restrictNormalHom L) σ σ'
  unfold pointCocycle
  rw [h, GaloisCocycle.value_mul, map_mul, GaloisPoint.relativeExtend_conjugate K L Ω T.toGrp σ]
  rfl

omit [IsAffine T.X.left] in
/-- The inflated values are locally constant for the Krull topology. -/
theorem pointCocycle_isLocallyConstant [FiniteDimensional K L] :
    IsLocallyConstant (pointCocycle (Ω := Ω) T τ) := by
  let E : IntermediateField K Ω := (IsScalarTower.toAlgHom K L Ω).fieldRange
  have : FiniteDimensional K E :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L Ω)).toLinearEquiv
  rw [IsLocallyConstant.iff_eventually_eq]
  intro σ
  have hopen : IsOpen ((fun y => σ⁻¹ * y) ⁻¹' (E.fixingSubgroup : Set (Ω ≃ₐ[K] Ω))) :=
    E.fixingSubgroup_isOpen.preimage (continuous_const.mul continuous_id)
  filter_upwards [hopen.mem_nhds (by simp)] with y hy
  have h1 : (σ⁻¹ * y).restrictNormal L = 1 := by
    ext x
    apply (algebraMap L Ω).injective
    rw [AlgEquiv.restrictNormal_commutes]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hy _ ⟨x, rfl⟩
  have h2 : y.restrictNormal L = σ.restrictNormal L := by
    have h3 := map_mul (AlgEquiv.restrictNormalHom L) σ (σ⁻¹ * y)
    rw [mul_inv_cancel_left] at h3
    change y.restrictNormal L = σ.restrictNormal L * (σ⁻¹ * y).restrictNormal L at h3
    rw [h3, h1, mul_one]
  simp only [pointCocycle, h2]

/-- If the `m`-th power of the cocycle is trivial, `m` times the inflated cocycle is a
coboundary. -/
theorem pointCocycle_coboundary [FiniteDimensional K L] [IsGalois K L] (m : ℕ)
    (hτm : (τ.map (CommGroupScheme.groupHom (m • 𝟙 T))).IsTrivial) :
    ∃ b, ∀ σ : Ω ≃ₐ[K] Ω, m • pointCocycle (Ω := Ω) T τ σ =
      (GaloisCocycle.pointRepresentation (G := T.toGrp) (k := K) (L := Ω)).ρ σ b - b := by
  obtain ⟨f, hf⟩ := (GaloisCocycle.isTrivial_iff _).1 hτm
  set P := affinePoints T.toGrp (CommAlgCat.of K Ω)
  set ef : P := GaloisPoint.relativeExtend K L Ω T.toGrp f
  refine ⟨(Additive.ofMul ef⁻¹ : Additive P), fun σ => ?_⟩
  have hv : GaloisCocycle.value (τ.map (CommGroupScheme.groupHom (m • 𝟙 T)))
      (σ.restrictNormal L) = GaloisCocycle.value τ (σ.restrictNormal L) ^ m := by
    change GaloisCocycle.value τ _ ≫ (CommGroupScheme.groupHom (m • 𝟙 T)).hom.hom = _
    have h := congrArg Additive.toMul
      (map_nsmul (evalPoint (H := T) (GaloisCocycle.value τ (σ.restrictNormal L))) m (𝟙 T))
    exact h
  have h := hf (σ.restrictNormal L)
  rw [hv] at h
  have h' : GaloisPoint.relativeExtend K L Ω T.toGrp (GaloisCocycle.value τ (σ.restrictNormal L)) ^ m =
      GaloisPoint.conjugate K Ω T.toGrp σ ef⁻¹ / ef⁻¹ := by
    rw [← map_pow, h, map_mul, map_inv, GaloisPoint.relativeExtend_conjugate K L Ω T.toGrp σ,
      map_inv, div_eq_mul_inv, inv_inv, mul_comm]
  change m • (Additive.ofMul (GaloisPoint.relativeExtend K L Ω T.toGrp
      (GaloisCocycle.value τ (σ.restrictNormal L))) : Additive P) =
    (Additive.ofMul (GaloisPoint.conjugate K Ω T.toGrp σ ef⁻¹) : Additive P) -
      Additive.ofMul ef⁻¹
  rw [← ofMul_pow, h', ofMul_div]

end Cocycle

section IntermediateFields

variable {K L Ω : Type u} [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
  [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L] [IsGalois K Ω]
  (T : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left]

set_option maxHeartbeats 800000 in
/-- The point criterion of `isTrivial_baseChangePullback_of_point` for intermediate fields
`E₀ ≤ M` of `Ω/K`, with `M` finite and normal over `K` and containing `L`. -/
theorem isTrivial_baseChangePullback_of_intermediateField
    (τ : Cocycle T.toGrp (GaloisCocycle.cover K L)) (E₀ M : IntermediateField K Ω)
    [FiniteDimensional K M] [Normal K M] (hE₀M : E₀ ≤ M) (hLM : ∀ x : L, algebraMap L Ω x ∈ M)
    (a : affinePoints T.toGrp (CommAlgCat.of K Ω))
    (hfix : ∀ σ ∈ M.fixingSubgroup, GaloisPoint.conjugate K Ω T.toGrp σ a = a)
    (hcob : ∀ σ ∈ E₀.fixingSubgroup,
      GaloisPoint.relativeExtend K L Ω T.toGrp (GaloisCocycle.value τ (σ.restrictNormal L)) =
        GaloisPoint.conjugate K Ω T.toGrp σ a * a⁻¹) :
    (τ.baseChangePullback (algebraBaseMap K E₀)).IsTrivial := by
  have : Algebra.IsSeparable K M := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
  have : IsGalois K M := ⟨⟩
  let : Algebra E₀ M := (IntermediateField.inclusion hE₀M).toRingHom.toAlgebra
  let : Module E₀ M := Algebra.toModule
  have : IsScalarTower K E₀ M :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion hE₀M).comp_algebraMap.symm
  let jM : L →ₐ[K] M := (IsScalarTower.toAlgHom K L Ω).codRestrict M.toSubalgebra hLM
  let : Algebra L M := jM.toRingHom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' jM.comp_algebraMap.symm
  have : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have : FiniteDimensional E₀ M := FiniteDimensional.right K E₀ M
  have : IsGalois E₀ M := IsGalois.tower_top_of_isGalois K E₀ M
  have : IsGalois M Ω := IsGalois.tower_top_of_isGalois K M Ω
  refine isTrivial_baseChangePullback_of_point (E₀ := E₀) (M := M) T τ a (fun σ => ?_)
    (fun σ hσE => ?_)
  · refine hfix _ ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_)
    exact σ.commutes ⟨x, hx⟩
  · refine hcob σ ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_)
    exact hσE ⟨x, hx⟩

end IntermediateFields

section Points

variable {K L Ω : Type u} [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
  [Algebra L Ω] [IsScalarTower K L Ω] [FiniteDimensional K L] [IsGalois K L]
  (T : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left]

/-- From the Galois-cohomological statement: for some `N` and every intermediate field `E₀`
containing a primitive `N`-th root of unity, the inflated cocycle is, on `Gal(Ω/E₀)`, the
coboundary of a point of `T` over `Ω` that is fixed by the automorphisms fixing some finite
normal extension. -/
theorem exists_point_of_unitsLattice [NumberField K] [IsSepClosure K Ω]
    (hC : NumberFieldUnitsLatticeCyclotomicSplittingStatement.{u})
    (hTΩ : IsSplitTorus (baseChanged K Ω T).toGrp)
    (τ : Cocycle T.toGrp (GaloisCocycle.cover K L)) (m : ℕ) (hm : 0 < m)
    (hτm : (τ.map (CommGroupScheme.groupHom (m • 𝟙 T))).IsTrivial) :
    ∃ N : ℕ, 0 < N ∧ (∀ q : ℕ, q.Prime → q ∣ N → q ∣ m) ∧
      ∀ E₀ : IntermediateField K Ω, (∃ ζ : Ω, ζ ∈ E₀ ∧ IsPrimitiveRoot ζ N) →
        ∃ a : affinePoints T.toGrp (CommAlgCat.of K Ω),
          (∃ M₁ : IntermediateField K Ω, FiniteDimensional K M₁ ∧ Normal K M₁ ∧
            ∀ σ ∈ M₁.fixingSubgroup, GaloisPoint.conjugate K Ω T.toGrp σ a = a) ∧
          ∀ σ ∈ E₀.fixingSubgroup, GaloisPoint.relativeExtend K L Ω T.toGrp
            (GaloisCocycle.value τ (σ.restrictNormal L)) =
              GaloisPoint.conjugate K Ω T.toGrp σ a * a⁻¹ := by
  let X := latticeRepresentation K Ω T
  have : IsSmoothRep X := latticeRepresentation_isSmoothRep K Ω T hTΩ
  have : Module.Free (ULift.{u} ℤ) X := latticeRepresentation_free K Ω T hTΩ
  have : Module.Finite (ULift.{u} ℤ) X := latticeRepresentation_finite K Ω T hTΩ
  let e := tensorPointIso K Ω T hTΩ
  let A : Rep.{u} (ULift.{u} ℤ) (Ω ≃ₐ[K] Ω) := unitsModule K Ω ⊗ X
  let c : (Ω ≃ₐ[K] Ω) → A := fun σ => e.inv.hom (pointCocycle T τ σ)
  have hc_lc : IsLocallyConstant c := (pointCocycle_isLocallyConstant T τ).comp _
  have hc_mul : ∀ σ σ' : Ω ≃ₐ[K] Ω, c (σ * σ') = c σ + A.ρ σ (c σ') := by
    intro σ σ'
    simp only [c, pointCocycle_mul, map_add, Rep.hom_comm_apply]
    rfl
  have hc_cob : ∃ b : A, ∀ σ, m • c σ = A.ρ σ b - b := by
    obtain ⟨b, hb⟩ := pointCocycle_coboundary (Ω := Ω) T τ m hτm
    refine ⟨e.inv.hom b, fun σ => ?_⟩
    change m • e.inv.hom (pointCocycle T τ σ) = A.ρ σ (e.inv.hom b) - e.inv.hom b
    rw [← map_nsmul, hb σ, map_sub, Rep.hom_comm_apply]
  obtain ⟨N, hN, hNm, hE⟩ := hC K Ω X c hc_lc hc_mul m hm hc_cob
  refine ⟨N, hN, hNm, fun E₀ hE₀ => ?_⟩
  obtain ⟨b', hb'⟩ := hE E₀ hE₀
  set P := affinePoints T.toGrp (CommAlgCat.of K Ω)
  set v := e.hom.hom b'
  let a : P := Additive.toMul (show Additive P from v)
  have hpc : ∀ σ ∈ E₀.fixingSubgroup, pointCocycle (Ω := Ω) T τ σ =
      (GaloisCocycle.pointRepresentation (G := T.toGrp) (k := K) (L := Ω)).ρ σ v - v := by
    intro σ hσ
    have h1 := congrArg e.hom.hom (hb' σ hσ)
    change e.hom.hom (e.inv.hom _) = _ at h1
    rwa [Rep.hom_inv_apply, map_sub, Rep.hom_comm_apply] at h1
  have : IsSmoothRep (GaloisCocycle.pointRepresentation (G := T.toGrp) (k := K) (L := Ω)) :=
    IsSmoothRep.of_iso e
  have hopen := IsSmoothRep.isOpen_stabilizer
    (GaloisCocycle.pointRepresentation (G := T.toGrp) (k := K) (L := Ω)) v
  obtain ⟨M₁, hM₁fin, hM₁norm, hM₁U⟩ := (krullTopology_mem_nhds_one_iff_of_normal K Ω _).1
    (hopen.mem_nhds (vectorStabilizer _ v).one_mem)
  refine ⟨a, ⟨M₁, hM₁fin, hM₁norm, fun σ hσ => ?_⟩, fun σ hσ => ?_⟩
  · have h1 := hM₁U hσ
    rw [SetLike.mem_coe, mem_vectorStabilizer] at h1
    change (Additive.ofMul (GaloisPoint.conjugate K Ω T.toGrp σ a) : Additive P) =
      Additive.ofMul a at h1
    exact Additive.ofMul.injective h1
  · have h2 := hpc σ hσ
    change (Additive.ofMul (GaloisPoint.relativeExtend K L Ω T.toGrp
        (GaloisCocycle.value τ (σ.restrictNormal L))) : Additive P) =
      (Additive.ofMul (GaloisPoint.conjugate K Ω T.toGrp σ a) : Additive P) -
        Additive.ofMul a at h2
    rw [← ofMul_div] at h2
    exact (Additive.ofMul.injective h2).trans (div_eq_mul_inv _ _)

/-- A point as in `exists_point_of_unitsLattice` trivializes the base change of the cocycle
to a finite intermediate field `E₀`. -/
theorem isTrivial_baseChangePullback_of_fixedPoint [IsGalois K Ω]
    (τ : Cocycle T.toGrp (GaloisCocycle.cover K L)) (E₀ : IntermediateField K Ω)
    [FiniteDimensional K E₀] (a : affinePoints T.toGrp (CommAlgCat.of K Ω))
    (M₁ : IntermediateField K Ω) [FiniteDimensional K M₁]
    (hfix : ∀ σ ∈ M₁.fixingSubgroup, GaloisPoint.conjugate K Ω T.toGrp σ a = a)
    (hcob : ∀ σ ∈ E₀.fixingSubgroup,
      GaloisPoint.relativeExtend K L Ω T.toGrp (GaloisCocycle.value τ (σ.restrictNormal L)) =
        GaloisPoint.conjugate K Ω T.toGrp σ a * a⁻¹) :
    (τ.baseChangePullback (algebraBaseMap K E₀)).IsTrivial := by
  let L' : IntermediateField K Ω := (IsScalarTower.toAlgHom K L Ω).fieldRange
  have : FiniteDimensional K L' := LinearEquiv.finiteDimensional
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L Ω)).toLinearEquiv
  let M₀ : IntermediateField K Ω := E₀ ⊔ L' ⊔ M₁
  let M : IntermediateField K Ω := IntermediateField.normalClosure K M₀ Ω
  have hM₀M : M₀ ≤ M := M₀.le_normalClosure
  have hE₀M : E₀ ≤ M := le_trans (le_sup_left.trans le_sup_left) hM₀M
  have hL'M : L' ≤ M := le_trans (le_sup_right.trans le_sup_left) hM₀M
  have hM₁M : M₁ ≤ M := le_trans le_sup_right hM₀M
  have : FiniteDimensional K M := normalClosure.is_finiteDimensional K M₀ Ω
  have : Normal K M := normalClosure.normal K M₀ Ω
  exact isTrivial_baseChangePullback_of_intermediateField T τ E₀ M hE₀M
    (fun x => hL'M ⟨x, rfl⟩) a
    (fun σ hσM => hfix σ (IntermediateField.fixingSubgroup_antitone hM₁M hσM)) hcob

end Points

section Transfer

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]

/-- A cocycle that becomes trivial over the cyclotomic field `K(ζ₀) ⊆ Ω` generated by a
primitive `N`-th root of unity becomes trivial over every field containing a primitive `N`-th
root of unity. -/
theorem isTrivial_baseChangePullback_of_primitiveRoot {S : GroupScheme (Spec (CommRingCat.of K))}
    {U : Over (Spec (CommRingCat.of K))} (ξ : Cocycle S U) {N : ℕ} [NeZero N] {ζ₀ : Ω}
    (hζ₀ : IsPrimitiveRoot ζ₀ N) [Algebra.IsIntegral K Ω]
    (h₀ : (ξ.baseChangePullback (algebraBaseMap K (IntermediateField.adjoin K {ζ₀}))).IsTrivial)
    (E : Type u) [Field E] [Algebra K E] (ζ : E) (hζ : IsPrimitiveRoot ζ N) :
    (ξ.baseChangePullback (algebraBaseMap K E)).IsTrivial := by
  let E₀ : IntermediateField K Ω := IntermediateField.adjoin K {ζ₀}
  have : IsCyclotomicExtension {N} K E₀ := hζ₀.intermediateField_adjoin_isCyclotomicExtension K
  have := IsCyclotomicExtension.isSplittingField_X_pow_sub_one N K E₀
  have hsplit : ((Polynomial.X ^ N - 1 : Polynomial K).map (algebraMap K E)).Splits := by
    simpa using Polynomial.X_pow_sub_one_splits hζ
  let φ : E₀ →ₐ[K] E := Polynomial.IsSplittingField.lift E₀ (Polynomial.X ^ N - 1) hsplit
  refine Cocycle.isTrivial_baseChangePullback_of_factor (algebraBaseMap K E)
    (algebraBaseMap K E₀) (Spec.map (CommRingCat.ofHom φ.toRingHom)) ?_ ξ h₀
  change Spec.map (CommRingCat.ofHom (algebraMap K E)) =
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap K E₀))
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (φ.commutes x).symm

end Transfer

/-- The torus statement follows from its Galois-cohomological form for `Ωˣ ⊗ X`, applied with
`Ω` the separable closure of `K` and `X` the cocharacter lattice of the torus over `Ω`. -/
theorem numberFieldTorusCocycleCyclotomicSplitting_of_unitsLattice
    (hC : NumberFieldUnitsLatticeCyclotomicSplittingStatement.{u}) :
    NumberFieldTorusCocycleCyclotomicSplittingStatement.{u} := by
  intro K _ _ T hT L _ _ _ _ τ m hm hτm
  have : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hT
  let jL : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let : Algebra L (SeparableClosure K) := jL.toRingHom.toAlgebra
  have : IsScalarTower K L (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq' jL.comp_algebraMap.symm
  obtain ⟨N, hN, hNm, hE⟩ := exists_point_of_unitsLattice (Ω := SeparableClosure K) T hC
    (isSplitTorus_baseChange_separableClosure hT) τ m hm hτm
  refine ⟨N, hN, hNm, fun E _ _ ζ hζ => ?_⟩
  have : NeZero N := ⟨hN.ne'⟩
  have : NeZero (N : K) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure K) N
  have : FiniteDimensional K (IntermediateField.adjoin K {ζ₀}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ₀)
  obtain ⟨a, ⟨M₁, hM₁fin, -, hfix⟩, hcob⟩ :=
    hE _ ⟨ζ₀, IntermediateField.mem_adjoin_simple_self K ζ₀, hζ₀⟩
  exact isTrivial_baseChangePullback_of_primitiveRoot τ hζ₀
    (isTrivial_baseChangePullback_of_fixedPoint T τ _ a M₁ hfix hcob) E ζ hζ

end Langlands.GroupScheme.NumberFieldTorusCyclotomicSplittingReduction
