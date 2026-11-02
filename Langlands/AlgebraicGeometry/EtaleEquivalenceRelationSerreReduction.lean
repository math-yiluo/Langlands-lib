import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationInvariantQuotient
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationRingFormStatement
import Langlands.AlgebraicGeometry.GroupoidCoactionNonzeroInvariantStatement
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationSerreCriterionStatement

/-! # Reduction of the Serre criterion to nonzero invariants -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

namespace GroupoidCoaction

/-- The nonzero-invariant assertion detects zero coactions, with exactly the
same module universe as the published assertion. -/
theorem subsingleton_of_nonzeroInvariant
    (hnonzero : GroupoidCoactionNonzeroInvariantStatement.{u})
    {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
    {t : B →+* C} (hE : RingEtaleEquivalenceRelation t) [IsNoetherianRing B]
    (hacyclic : ∀ (K : Type u) [AddCommGroup K] [Module B K]
      (θK : GroupoidCoaction t K), θK.IsAcyclic)
    {M : Type u} [AddCommGroup M] [Module B M] (θ : GroupoidCoaction t M)
    (hM : Subsingleton θ.invariantSubmodule) : Subsingleton M := by
  classical
  by_contra hn
  let : Nontrivial M := not_subsingleton_iff_nontrivial.mp hn
  obtain ⟨m, hm, hm0⟩ := hnonzero B C t hE inferInstance hacyclic M θ
  apply hm0
  exact congrArg Subtype.val (@Subsingleton.elim θ.invariantSubmodule hM
    (⟨m, hm⟩ : θ.invariantSubmodule) 0)

end GroupoidCoaction

namespace EtaleEquivalenceRelation

/-- The actual invariant-ring quotient certificate under the two remaining
statement inputs of the invariant-ring route to the Serre criterion. -/
noncomputable def noetherianInvariantRingQuotient
    (hform : EtaleEquivalenceRelationRingFormStatement.{u})
    (hnonzero : GroupoidCoactionNonzeroInvariantStatement.{u})
    (E : EtaleEquivalenceRelation.{u}) [IsAffine E.U] [IsNoetherian E.U]
    [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]
    (hacyclic : E.ComodulesAcyclic) : E.FaithfullyFlatRingQuotient := by
  letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  letI : IsNoetherianRing Γ(E.U, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top E.U⟩
  have hE : RingEtaleEquivalenceRelation E.t.appTop.hom :=
    hform E inferInstance inferInstance inferInstance
  exact invariantRingQuotient E hE hacyclic
    (fun _ _ _ θ hθ =>
      GroupoidCoaction.subsingleton_of_nonzeroInvariant hnonzero hE hacyclic θ hθ)

end EtaleEquivalenceRelation

/-- The ring-form and nonzero-invariant statements imply the exact published
Serre criterion, without any further hypothesis. -/
theorem serreCriterion_of_ringForm_of_nonzeroInvariant
    (hform : EtaleEquivalenceRelationRingFormStatement.{u})
    (hnonzero : GroupoidCoactionNonzeroInvariantStatement.{u}) :
    EtaleEquivalenceRelationSerreCriterionStatement.{u} := by
  intro E hU hN hR hj hacyclic
  let : IsAffine E.U := hU
  let : IsNoetherian E.U := hN
  let : IsAffine E.R := hR
  let : IsClosedImmersion (prod.lift E.t E.s) := hj
  exact (E.noetherianInvariantRingQuotient hform hnonzero hacyclic).hasAffineQuotient

end Langlands.AlgebraicGeometry
