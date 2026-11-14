import Langlands.GroupScheme.Reductive.DerivedCentralIsogenyStatement
import Langlands.GroupScheme.CentralIsogeny.QuotientPairing

/-! # Assembling derived central isogenies from existence and multiplication -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The existence and multiplication clauses of the derived central-isogeny target. -/
def ReductiveDerivedMultiplicationStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    let IsMaximalCentralTorus : ∀ {Z : GroupScheme S}, (Z ⟶ G) → Prop :=
      fun {Z} z => IsClosedSubgroup z ∧ IsCentral z ∧ RelativeTorus.IsTorus Z ∧
        ∀ (Z' : GroupScheme S) (z' : Z' ⟶ G), IsClosedSubgroup z' → IsCentral z' →
          RelativeTorus.IsTorus Z' → SubgroupFunctor.range z' ≤ SubgroupFunctor.range z
    (∃ (Z : GroupScheme S) (z : Z ⟶ G), IsMaximalCentralTorus z) ∧
    ∀ (D : GroupScheme S) (d : D ⟶ G), IsClosedSubgroup d →
      (SubgroupFunctor.range d).IsNormal → IsReductive D →
      (∀ s : S, IsSemisimple (geometricFiber D s)) →
      ∀ (Q : GroupScheme S) (q : G ⟶ Q), RelativeTorus.IsTorus Q →
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q →
      ∀ (Z : GroupScheme S) (z : Z ⟶ G) (hz : IsCentral z), IsMaximalCentralTorus z →
        IsCentralIsogeny (prodHom z d (hz.commute_values d))

/-- The pairing clause adds no further obligation once existence and multiplication hold. -/
def ReductiveDerivedCentralIsogenyReductionStatement : Prop :=
  ReductiveDerivedCentralIsogenyStatement.{u} ↔ ReductiveDerivedMultiplicationStatement.{u}

/-- Recover the unchanged full target using the two represented fppf quotient maps. -/
theorem reductiveDerivedCentralIsogeny_of_multiplication
    (h : ReductiveDerivedMultiplicationStatement.{u}) :
    ReductiveDerivedCentralIsogenyStatement.{u} := by
  intro S G hG
  obtain ⟨hex, hmul⟩ := h S G hG
  refine ⟨hex, ?_⟩
  intro D d hd hdn hD hDs Q q hQ hq Z z hz hZ
  have hm := hmul D d hd hdn hD hDs Q q hQ hq Z z hz hZ
  refine ⟨hm, ?_⟩
  intro P p hp
  have : IsClosedImmersion d.hom.hom.left := hd
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion z.hom.hom.left := hZ.1
  have : Mono z.hom.hom := Over.mono_of_mono_left _
  exact isCentralIsogeny_quotientPairing_of_prodHom z d hz (hz.commute_values d)
    q hq p hp hm

/-- Forgetting the pairing and the proved quotient transfer give the equivalence. -/
theorem reductiveDerivedCentralIsogenyReduction :
    ReductiveDerivedCentralIsogenyReductionStatement.{u} := by
  constructor
  · intro h S G hG
    obtain ⟨hex, hboth⟩ := h S G hG
    refine ⟨hex, ?_⟩
    intro D d hd hdn hD hDs Q q hQ hq Z z hz hZ
    exact (hboth D d hd hdn hD hDs Q q hQ hq Z z hz hZ).1
  · exact reductiveDerivedCentralIsogeny_of_multiplication

end Langlands.GroupScheme
