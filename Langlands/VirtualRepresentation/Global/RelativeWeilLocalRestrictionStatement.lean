import Langlands.ClassField.Global.LocalRelativeWeilMap
import Langlands.ClassField.Global.RelativeWeilTransfer
import Langlands.VirtualRepresentation.ExactInductionTwist
import Langlands.Weil.Representation.InductionContinuity
import Langlands.Global.AdelicFunctoriality.Norm

/-!
# Local restriction of induced representations of relative Weil groups

For `F ⊆ K ⊆ E` with `E / F` Galois and a local map `ι : W_{F_z} → W_{E/F}` at a
finite place `z`, the restriction along `ι` of a representation induced from
`W_{E/K}` is the sum over the places `u` of `K` above `z` of representations
induced along `W_{K_u} → W_{F_z}`, through local maps `W_{K_u} → W_{E/K}` whose
transfer to `C_K` is the inverse of geometric local reciprocity at `u`;
compare Tate (1979), (1.6.1) and (2.3.5). Apart from two topology lemmas and two
finite-index instances, nothing is proved; the formula is a proposition definition.
-/

noncomputable section

set_option autoImplicit false

universe uG uH uV u

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]

/-- Induction along an open embedding with finite-index range, on continuous exact
virtual groups: restriction along the inverse onto the range, followed by
finite-index induction from the range. -/
def continuousInduceAlong (φ : H →ₜ* G) (hφ : Topology.IsOpenEmbedding φ)
    [φ.toMonoidHom.range.FiniteIndex] :
    ExactGrothendieckGroup
        (fun A : FiniteRepresentation.{0, uH, uV} ℂ H => A.IsContinuous) →ₗ[ℤ]
      ExactGrothendieckGroup
        (fun A : FiniteRepresentation.{0, uG, max uG uV} ℂ G => A.IsContinuous) :=
  (continuousInduce φ.toMonoidHom.range
      (InductionAlong.isOpen_range φ.toMonoidHom hφ)).comp
    (continuousRestrict
      ⟨InductionAlong.rangeInverse φ.toMonoidHom hφ.injective,
        InductionAlong.continuous_rangeInverse φ.toMonoidHom hφ.isEmbedding⟩)

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField Langlands.VirtualRepresentation
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

/-- For a finite extension the Krull topology on `Gal(E/K)` is the discrete topology
`relativeGaloisTopology` used to topologize relative Weil groups. -/
theorem krullTopology_eq_relativeGaloisTopology (K E : Type u) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E] :
    krullTopology K E = relativeGaloisTopology K E :=
  DiscreteTopology.eq_bot

/-- A map into `W_{E/F}` continuous for the Krull topology on `Gal(E/F)` is continuous
for the discrete topology `relativeGaloisTopology`. -/
theorem continuous_of_krull (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    {X : Type*} [TopologicalSpace X] (f : X → RelativeWeilGroup c F E) (hf : Continuous f) :
    letI := relativeGaloisTopology F E
    Continuous f := by
  have key : ∀ t : TopologicalSpace (E ≃ₐ[F] E), krullTopology F E = t →
      letI := t
      Continuous f := by
    rintro t rfl
    exact hf
  exact key _ (krullTopology_eq_relativeGaloisTopology F E)

/-- A continuous map `W_{F_z} → W_{E/F}` for the Krull topology on `Gal(E/F)`, the
topology used by `IsLocalRelativeWeilMap`, read as a continuous map for the discrete
topology `relativeGaloisTopology`. The underlying homomorphism is unchanged. -/
def discreteLocalMap {c : FundamentalClass.ClassFamily.{u}} {F E : Type u}
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    {z : Langlands.Global.FinitePlace F}
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E) :
    letI := relativeGaloisTopology F E
    Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E :=
  let f := ι.toMonoidHom
  have hf : Continuous f := ι.continuous_toFun
  letI := relativeGaloisTopology F E
  { toMonoidHom := f
    continuous_toFun := continuous_of_krull c F E f hf }

section Discrete

attribute [local instance] relativeGaloisTopology

section Ranges

variable (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
  (K : Type u) [Field K] [NumberField K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
  (h : FundamentalClass.Restriction c)

/-- The image of `W_{E/K}` in `W_{E/F}` has finite index. -/
instance range_restrictionInclusion_finiteIndex :
    (restrictionInclusion c F E K h).toMonoidHom.range.FiniteIndex := by
  rw [range_restrictionInclusion]
  infer_instance

variable {F}

/-- The image of `W_{K_u}` in `W_{F_z}` has finite index. -/
instance completionWeilMap_range_finiteIndex (z : Langlands.Global.FinitePlace F)
    (u : Langlands.Global.FinitePlace K) [u.asIdeal.LiesOver z.asIdeal] :
    (completionWeilMap z u).toMonoidHom.range.FiniteIndex :=
  Weil.Local.extensionWeilMap_range_finiteIndex _ _ _

end Ranges

/-- Tate's local restriction formula at `z`, for the intermediate field `K` and the
local map `ι`, with `Gal(E/F)` and `Gal(E/K)` discrete: there are local maps
`ιᵤ : W_{K_u} → W_{E/K}`, one for each place `u` of `K` above `z`, such that the
transfer of `ιᵤ y` to `C_K` is the inverse of the image of `y` under every geometric
local reciprocity isomorphism of `K_u`, and the restriction along `ι` of every
continuous virtual representation induced from `W_{E/K}` is the sum over `u` of its
restrictions along the `ιᵤ`, induced along `W_{K_u} → W_{F_z}`. -/
def LocalInducedRestriction (c : FundamentalClass.ClassFamily.{u}) (F K E : Type u)
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [Field K] [NumberField K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    (h : FundamentalClass.Restriction c) (z : Langlands.Global.FinitePlace F)
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E) : Prop :=
  haveI : IsGalois K E := IsGalois.tower_top_of_isGalois F K E
  ∃ ιu : ∀ u : FinitePlacesAbove K z,
      Weil.Local.localWeilGroup (towerPadicField z u.1) →ₜ* RelativeWeilGroup c K E,
    (∀ (u : FinitePlacesAbove K z)
        (eu : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z u.1)),
      LocalClassField.GeometricWeilReciprocityRelation (towerPadicField z u.1)
          (towerPadicField z u.1).canonicalTopologicalData eu →
        ∀ y : Weil.Local.localWeilGroup (towerPadicField z u.1),
          transfer c K E (ιu u y) =
            (IdeleClassGroup.ofAdicCompletion (𝓞 K) K u.1
              (LocalFactor.RankOne.reciprocityUnits (towerPadicField z u.1) eu y))⁻¹) ∧
    ∀ x : ExactGrothendieckGroup
        (fun A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c K E) =>
          A.IsContinuous),
      ExactGrothendieckGroup.continuousRestrict ι
          (ExactGrothendieckGroup.continuousInduceAlong (restrictionInclusion c F E K h)
            (isOpenEmbedding_restrictionInclusion c F E K h) x) =
        ∑ u : FinitePlacesAbove K z,
          ExactGrothendieckGroup.continuousInduceAlong (completionWeilMap z u.1)
            (Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _)
            (ExactGrothendieckGroup.continuousRestrict (ιu u) x)

end Discrete

/-- Tate (1979), (2.3.5) with (1.6.1), for relative Weil groups: for every class
family satisfying the restriction compatibility, every tower `F ⊆ K ⊆ E` of number
fields with `E / F` Galois, and every local map `ι : W_{F_z} → W_{E/F}` for a place
`w` of `E` above a finite place `z` of `F`, the local restriction formula holds for
`ι` read with the discrete topology on `Gal(E/F)`. -/
def LocalInducedRestrictionStatement : Prop :=
  ∀ (c : FundamentalClass.ClassFamily.{u}) (F K E : Type u) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [Field K] [NumberField K]
    [Algebra F K] [Algebra K E] [IsScalarTower F K E] (h : FundamentalClass.Restriction c)
    (z : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
    [w.asIdeal.LiesOver z.asIdeal]
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w))
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E),
    IsLocalRelativeWeilMap z w e ι →
      LocalInducedRestriction.{uV, u} c F K E h z (discreteLocalMap ι)

end Langlands.ClassField.Global.RelativeWeilGroup
