# Temperedness and separate fixed-exponent conditions

Author: Worker 403.

`Langlands.TemperedLpStatement.{uG,uF,uV}` is a closed proposition consisting
of two equivalences. The first covers every group `G : Type uG` with a topology,
every algebraic complex carrier `V : Type uV`, an actual representation `ρ`,
a measurable space on the actual quotient `G / Z(G)`, and a Haar measure `μ`.
It states

```text
IsTemperedModCenter ρ μ ↔
  ∀ ε : ℝ, 0 < ε → IsLpModCenter ρ μ (2 + ε).
```

The second covers every prime, p-adic field `F : PadicField.{uF} p`, supplied
compatible realization `T`, every natural rank, and every actual GL
representation on an arbitrary `Type uV` carrier. It states

```text
T.IsTempered ρ ↔ ∀ ε : ℝ, 0 < ε → T.IsLp ρ (2 + ε).
```

Both canonical GL predicates use the same actual field topology and central
quotient, the same canonical Borel measurable space and every Haar measure.
The field, group and carrier universes are independent. No nontriviality,
irreducibility, finite dimension, positive rank, carrier countability, invariant
form or character-existence premise is introduced. The generic clause needs
only the topology and measurable-space hypotheses of the existing temperedness
predicate; it adds no Borel-space or topological group requirement.

This is an internal logical compatibility statement for already defined analytic
predicates. The forward implication should retain the character witness from
temperedness at each exponent. For the reverse implication, the instance at
`ε = 1` provides admissibility and one unitary central character. At any other
positive `ε`, the existing `UnitaryCentralCharacter.coefficientNorm_eq` equates
the coefficient norms from that exponent's witness with the chosen witness.
This supplies one witness for all exponents. The GL clause then interchanges
the two universal quantifiers over Haar measures and positive `ε`, applying
the generic equivalence for each measure.

The module defines the proposition only. This logical argument needs no external
literature theorem, integration estimate, change of Haar measure or tensor-dual
factorization. In particular this statement alone proves neither block tensor
comparison. It is intended to let their common finite-exponent proof feed the
unchanged temperedness target without adding a character certificate.
