import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Group.RelativeWeyl

/-!
# Weyl conjugacy of induced exact-K0 classes

This is the separately named representation-theoretic input of Aubert (1.2)
and Ban–Jantzen Proposition 4.1(3). The parabolics and Levis are actual
subgroups; a Weyl lift lies in the actual normalizer, and the transport is the
actual inverse-conjugation pullback. No isomorphism of induced representations
is asserted. Neither target is a proof or an external structural axiom.
-/

noncomputable section

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (T : Subgroup G) (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))

/-- Aubert (1.2): `i_J ∘ Ad(n) = i_I` on exact finite-length K0 whenever
`n ∈ N_G(T)` conjugates the actual standard Levi `M I` onto `M J`.
Every actual lift is quantified; no lift-independence premise is hidden. -/
def inducedK0WeylConjugacy : Prop :=
  ∀ (I J : Finset ι) (n : Langlands.Group.RelativeWeyl.normalizer T)
    (hIJ : ∀ x : G, x ∈ M J ↔ (n : G)⁻¹ * x * (n : G) ∈ M I),
    (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1).comp
      (conjugationK0.{uG, max uG uV} (n : G) hIJ) =
        inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1

/-- The actual-class version of the same representation-theoretic target:
the two actual normalized induced modules have equal exact K0 classes.
The transported finite-length proof uses the published equivalence pullback
lemma, not a new representation-theoretic assumption. -/
def inducedClassWeylConjugacy : Prop :=
  ∀ (I J : Finset ι) (n : Langlands.Group.RelativeWeyl.normalizer T)
    (hIJ : ∀ x : G, x ∈ M J ↔ (n : G)⁻¹ * x * (n : G) ∈ M I)
    (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M I)),
    FiniteLengthGrothendieckGroup.ofRepresentation
      ((normalizedInductionFunctor (h J) (hU J)).obj
        ((conjugationFunctor (n : G) hIJ).obj σ.val))
      ((hfl J).1 _ (pullbackFunctor_preservesFiniteLength
        (conjugationEquiv (n : G) hIJ) σ.val σ.property)) =
    FiniteLengthGrothendieckGroup.ofRepresentation
      ((normalizedInductionFunctor (h I) (hU I)).obj σ.val)
      ((hfl I).1 σ.val σ.property)

end Langlands.Aubert.General
