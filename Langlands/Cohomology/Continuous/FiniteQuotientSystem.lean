import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.Topology.Instances.Int

universe u

open CategoryTheory

namespace Langlands.Continuous

noncomputable section

variable (k G : Type u) [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G]

/-- A discrete module with a jointly continuous group action. -/
structure DiscreteModule where
  toTopRep : TopRep.{u} k G
  [isDiscrete : DiscreteTopology toTopRep]
  continuous_action :
    Continuous (fun p : G × toTopRep => toTopRep.ρ p.1 p.2)

attribute [instance] DiscreteModule.isDiscrete

variable {k G}

/-- The ordinary representation obtained by forgetting topology. -/
abbrev DiscreteModule.toRep (A : DiscreteModule k G) : Rep.{u} k G :=
  Rep.of A.toTopRep.ρ.toRepresentation

/-- An arbitrary-universe discrete additive action, with lifted integer scalars. -/
def DiscreteModule.ofAdditiveAction (A : Type u) [AddCommGroup A]
    [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
    [ContinuousSMul G A] : DiscreteModule (ULift.{u} ℤ) G where
  toTopRep := TopRep.of (X := A) <| ContRepresentation.ofMonoidHom
    { toFun g :=
        { toFun := fun a => g • a
          map_add' := smul_add g
          map_smul' c a := by
            change g • (c.down • a) = c.down • (g • a)
            exact (DistribSMul.toAddMonoidHom A g).map_zsmul c.down a
          cont := continuous_of_discreteTopology }
      map_one' := by
        ext a
        exact one_smul G a
      map_mul' g h := by
        ext a
        exact mul_smul g h a }
  isDiscrete := inferInstance
  continuous_action := continuous_smul

/-- Open normal subgroups ordered by reverse inclusion. -/
abbrev FiniteQuotientIndex := OrderDual (OpenNormalSubgroup G)

instance finiteQuotientIndex_nonempty : Nonempty (FiniteQuotientIndex (G := G)) :=
  ⟨OrderDual.toDual {
    toOpenSubgroup := ⊤
    isNormal' := by change (⊤ : Subgroup G).Normal; infer_instance }⟩

instance finiteQuotientIndex_filtered : IsFiltered (FiniteQuotientIndex (G := G)) :=
  inferInstanceAs (IsFiltered (OrderDual (OpenNormalSubgroup G)))

/-- Compactness makes every open-subgroup quotient finite. -/
theorem finite_quotient [SeparatelyContinuousMul G] [CompactSpace G]
    (N : OpenNormalSubgroup G) : Finite (G ⧸ N.toSubgroup) :=
  Subgroup.quotient_finite_of_isOpen N.toSubgroup N.toOpenSubgroup.isOpen

/-- The actual quotient representation on the fixed submodule. -/
abbrev finiteQuotientRep (A : Rep.{u} k G) (N : OpenNormalSubgroup G) :
    Rep.{u} k (G ⧸ N.toSubgroup) :=
  A.quotientToInvariants N.toSubgroup

/-- The quotient homomorphism for a refinement of open normal subgroups. -/
def quotientTransition {M N : OpenNormalSubgroup G} (h : M ≤ N) :
    G ⧸ M.toSubgroup →* G ⧸ N.toSubgroup :=
  QuotientGroup.map M.toSubgroup N.toSubgroup (MonoidHom.id G) h

/-- Inclusion of fixed submodules, equivariant for the quotient transition. -/
def fixedTransition (A : Rep.{u} k G) {M N : OpenNormalSubgroup G} (h : M ≤ N) :
    Rep.res (quotientTransition h) (finiteQuotientRep A N) ⟶ finiteQuotientRep A M :=
  Rep.ofHom
    { toLinearMap := Submodule.inclusion (fun _ hx s => hx ⟨s.1, h s.2⟩)
      isIntertwining' q := QuotientGroup.induction_on q fun g => by
        ext x
        rfl }

/-- Inflation along a finite quotient refinement, with the actual coefficient inclusion. -/
noncomputable def finiteInflation (A : Rep.{u} k G) (q : ℕ)
    {M N : OpenNormalSubgroup G} (h : M ≤ N) :
    groupCohomology (finiteQuotientRep A N) q ⟶
      groupCohomology (finiteQuotientRep A M) q :=
  groupCohomology.map (quotientTransition h) (fixedTransition A h) q

set_option backward.isDefEq.respectTransparency false in
/-- The directed diagram of actual inhomogeneous finite-quotient cochain complexes. -/
noncomputable def finiteQuotientCochainDiagram (A : Rep.{u} k G) :
    FiniteQuotientIndex (G := G) ⥤ CochainComplex (ModuleCat.{u} k) ℕ where
  obj N := groupCohomology.inhomogeneousCochains (finiteQuotientRep A (OrderDual.ofDual N))
  map {N M} f := groupCohomology.cochainsMap
    (quotientTransition (M := OrderDual.ofDual M) (N := OrderDual.ofDual N)
      (leOfHom (X := FiniteQuotientIndex (G := G)) f))
    (fixedTransition A (M := OrderDual.ofDual M) (N := OrderDual.ofDual N)
      (leOfHom (X := FiniteQuotientIndex (G := G)) f))
  map_id N := by
    calc
      _ = groupCohomology.cochainsMap (MonoidHom.id _)
          (𝟙 (finiteQuotientRep A (OrderDual.ofDual N))) := by
        apply groupCohomology.cochainsMap_congr
        · ext g
          rfl
        · rfl
      _ = _ := groupCohomology.cochainsMap_id
        (A := finiteQuotientRep A (OrderDual.ofDual N))
  map_comp f g := by
    rw [← groupCohomology.cochainsMap_comp]
    apply groupCohomology.cochainsMap_congr
    · ext x
      rfl
    · rfl

/-- The directed diagram of ordinary finite-quotient cohomology groups. -/
noncomputable def finiteQuotientDiagram (A : Rep.{u} k G) (q : ℕ) :
    FiniteQuotientIndex (G := G) ⥤ ModuleCat.{u} k :=
  finiteQuotientCochainDiagram A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) q

/-- The colimit of the actual finite-quotient cohomology diagram. -/
noncomputable abbrev finiteQuotientCohomology (A : Rep.{u} k G) (q : ℕ) :
    ModuleCat.{u} k :=
  Limits.colimit (finiteQuotientDiagram A q)

/-- The structural map from an ordinary finite stage to the directed colimit. -/
noncomputable def finiteStageToColimit (A : Rep.{u} k G) (N : OpenNormalSubgroup G)
    (q : ℕ) :
    groupCohomology (finiteQuotientRep A N) q ⟶ finiteQuotientCohomology A q :=
  Limits.colimit.ι (finiteQuotientDiagram A q) (OrderDual.toDual N)

/-- The quotient representation with the inherited discrete coefficient topology. -/
abbrev finiteQuotientTopRep (A : DiscreteModule k G) (N : OpenNormalSubgroup G) :
    TopRep.{u} k (G ⧸ N.toSubgroup) :=
  TopRep.of <| ContRepresentation.ofMonoidHom
    { toFun g := ⟨(finiteQuotientRep A.toRep N).ρ g, continuous_of_discreteTopology⟩
      map_one' := by
        apply ContinuousLinearMap.ext
        intro x
        exact LinearMap.congr_fun (map_one (finiteQuotientRep A.toRep N).ρ) x
      map_mul' g h := by
        apply ContinuousLinearMap.ext
        intro x
        exact LinearMap.congr_fun (map_mul (finiteQuotientRep A.toRep N).ρ g h) x }

/-- The quotient action is jointly continuous, since both factors are discrete. -/
def finiteQuotientModule [SeparatelyContinuousMul G]
    (A : DiscreteModule k G) (N : OpenNormalSubgroup G) :
    DiscreteModule k (G ⧸ N.toSubgroup) where
  toTopRep := finiteQuotientTopRep A N
  isDiscrete := inferInstance
  continuous_action := by
    let : DiscreteTopology (G ⧸ N.toSubgroup) :=
      QuotientGroup.discreteTopology_iff.mpr N.toOpenSubgroup.isOpen
    exact continuous_of_discreteTopology

/-- The continuous projection from the group to an open normal quotient. -/
def quotientProjection (N : OpenNormalSubgroup G) : G →ₜ* G ⧸ N.toSubgroup where
  toMonoidHom := QuotientGroup.mk' N.toSubgroup
  continuous_toFun := QuotientGroup.continuous_mk

/-- The continuous equivariant inclusion of fixed coefficients into the original module. -/
def fixedCoefficientInclusion (A : DiscreteModule k G) (N : OpenNormalSubgroup G) :
    TopRep.res (quotientProjection N) (finiteQuotientTopRep A N) ⟶ A.toTopRep :=
  TopRep.ofHom
    { toContinuousLinearMap :=
        { toLinearMap := Submodule.subtype _
          cont := continuous_subtype_val }
      isIntertwining' g := by
        ext x
        rfl }

/-- Inflation from the actual continuous cohomology of a finite quotient. -/
noncomputable def continuousFiniteInflation [IsTopologicalGroup G]
    (A : DiscreteModule k G) (N : OpenNormalSubgroup G) (q : ℕ) :
    continuousCohomology q (finiteQuotientTopRep A N) ⟶
      continuousCohomology q A.toTopRep :=
  ContinuousCohomology.map (quotientProjection N) (fixedCoefficientInclusion A N) q

/-- The continuous inclusion of a subgroup with its subspace topology. -/
def subgroupInclusion (H : Subgroup G) : H →ₜ* G where
  toMonoidHom := H.subtype
  continuous_toFun := continuous_subtype_val

/-- Restricting a jointly continuous discrete action to a subgroup. -/
abbrev DiscreteModule.restrict (A : DiscreteModule k G) (H : Subgroup G) :
    DiscreteModule k H where
  toTopRep := TopRep.res H.subtype A.toTopRep
  isDiscrete := inferInstance
  continuous_action :=
    A.continuous_action.comp (continuous_subtype_val.prodMap continuous_id)

/-- Restriction is precisely Mathlib's continuous cohomology map for subgroup inclusion. -/
noncomputable def continuousRestriction [IsTopologicalGroup G]
    (A : DiscreteModule k G) (H : Subgroup G) (q : ℕ) :
    continuousCohomology q A.toTopRep ⟶ continuousCohomology q (A.restrict H).toTopRep :=
  ContinuousCohomology.map (subgroupInclusion H) (𝟙 (A.restrict H).toTopRep) q

end

end Langlands.Continuous
