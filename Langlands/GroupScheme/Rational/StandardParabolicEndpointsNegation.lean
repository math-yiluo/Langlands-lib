import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.ReflectionNegation
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.RootReflectionExistenceStatement
import Langlands.GroupScheme.Rational.StandardCocharacterReduction

/-! # The endpoints of standard parabolics from negation stability of relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Local

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- For every index set `J` and every cocharacter standard for `J` relative to `ν`,
the three standard subgroup functors of `J` equal the dynamic subgroup functors of
that cocharacter. This property includes no existence assertion. -/
def StandardSubgroupsDynamic : Prop :=
  ∀ (J : Set (characterLattice T)) (zeta : cocharacterLattice T),
    IsStandardCocharacter i ν J zeta →
      standardParabolic i ν J = Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ∧
      standardLevi i ν J = Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ∧
      standardUnipotent i ν J = Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)

end Local

/-- Intrinsic integral reflection data give negation stability of the actual
relative roots. The reflection-existence statement remains a premise. -/
theorem relativeRootNegationStatement_of_relativeRootReflectionExistence
    (hreflect : RelativeRootReflectionExistenceStatement.{u}) :
    RelativeRootNegationStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  obtain ⟨D, _⟩ := hreflect k G hG T i hi
  exact fun _ hα => D.neg_mem_relativeRoots i hα

/-- Under negation stability, for a generic `ν`, every standard subgroup functor
for a face `J` equals the dynamic subgroup functor of each standard cocharacter for
`J`. Existence of standard cocharacters is not asserted. -/
theorem standard_eq_dynamic_of_relativeRootNegation
    (hneg : RelativeRootNegationStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    haveI := hG.isAffineHom
    IsGenericCocharacter i ν → StandardSubgroupsDynamic i ν := by
  let := hG.isAffineHom
  intro hν J zeta hzeta
  have hcomparison : StandardCocharacterDynamicComparison i ν J :=
    fun xi hxi eta heta => relativeRootSignsDetermineDynamic k G hG T i hi xi eta
      (hxi.haveSameRelativeRootSigns i ν hν (hneg k G hG T i hi) heta)
  exact hcomparison.standard_eq_dynamic i ν J hzeta

/-- Under negation stability, the standard parabolic of the full simple-root
index is the whole group. -/
theorem standardParabolic_simple_eq_top_of_relativeRootNegation
    (hneg : RelativeRootNegationStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    haveI := hG.isAffineHom
    IsGenericCocharacter i ν → standardParabolic i ν (simpleRelativeRoots i ν) = ⊤ := by
  let := hG.isAffineHom
  intro hν
  simpa only [groupHom_zero_comp_eq_trivialCocharacter,
      Dynamic.parabolic_trivialCocharacter] using
    (standard_eq_dynamic_of_relativeRootNegation hneg k G hG T i hi ν hν _ 0
      (isStandardCocharacter_simple_zero i ν)).1

/-- Negation stability of the actual relative roots implies all five endpoint
clauses; the published theorems `genericCentralizer` and
`relativeRootSignsDetermineDynamic` supply the remaining inputs. -/
theorem standardParabolicEndpoints_of_relativeRootNegation
    (hneg : RelativeRootNegationStatement.{u}) :
    StandardParabolicEndpointsStatement.{u} := by
  intro k _ G hG T i hi ν hν
  let := hG.isAffineHom
  have hstandard := standard_eq_dynamic_of_relativeRootNegation hneg k G hG T i hi ν hν
  have hempty := hstandard ∅ ν (isStandardCocharacter_empty_self i ν)
  have hfull := hstandard _ 0 (isStandardCocharacter_simple_zero i ν)
  refine ⟨hempty.1, ?_, ?_, ?_, standardUnipotent_simple_eq_bot i ν⟩
  · exact standardLevi_empty_of_genericCentralizer i ν (genericCentralizer k G hG T i hi ν hν)
  · simpa only [groupHom_zero_comp_eq_trivialCocharacter,
      Dynamic.parabolic_trivialCocharacter] using hfull.1
  · simpa only [groupHom_zero_comp_eq_trivialCocharacter,
      Dynamic.centralizer_trivialCocharacter] using hfull.2.1

/-- The endpoints from intrinsic reflection existence, through negation stability. -/
theorem standardParabolicEndpoints_of_relativeRootReflectionExistence
    (hreflect : RelativeRootReflectionExistenceStatement.{u}) :
    StandardParabolicEndpointsStatement.{u} :=
  standardParabolicEndpoints_of_relativeRootNegation
    (relativeRootNegationStatement_of_relativeRootReflectionExistence hreflect)

end Langlands.GroupScheme
