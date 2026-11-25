# Integrality of the conductors of every presentation of a local Weil representation

This module states `Langlands.Henniart.WeilConductorIntegralityStatement`, a proposition
definition. Its proof is `Langlands.Henniart.weilConductorIntegrality`
(`HenniartWeilConductorIntegralityProof`).

## Statement

```lean
def WeilConductorIntegralityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)),
    (∀ (P : FiniteInertiaPresentation F A)
      (hP : Function.Surjective (weilInertiaRestriction F P.extension)),
      (∃ a : ℕ, P.artinConductor hP = (a : ℚ)) ∧ (∃ s : ℕ, P.swanConductor hP = (s : ℚ))) ∧
    (A.IsContinuous →
      ∃ (P : FiniteInertiaPresentation F A)
        (hP : Function.Surjective (weilInertiaRestriction F P.extension)) (a s : ℕ),
        P.artinConductor hP = (a : ℚ) ∧ P.swanConductor hP = (s : ℚ))
```

(name space `Langlands.Henniart`, with `Ramification.Padic` and `Weil.Local` open; level
parameters `uF uV`).

In words: let `F` be a p-adic field and `A` a finite-dimensional complex representation of the
local Weil group `W_F` (`Weil.Local.localWeilGroup F`), with carrier in universe `uV`.

1. For every finite inertia presentation `P` of `A` (`Ramification.Padic.FiniteInertiaPresentation`:
   a finite Galois subextension `L = P.extension` of the algebraic closure such that the kernel of
   the restriction `I_F → I(L/F)` of Weil inertia to the inertia group of `L/F` acts trivially on
   `A`) and every proof `hP` that this restriction is surjective, the Artin and Swan expressions
   `P.artinConductor hP`, `P.swanConductor hP` of the descended representation of `I(L/F)` are
   natural numbers.
2. If `A` is continuous, it has such a presentation with natural Artin and Swan expressions.

The representation is not assumed irreducible, and clause 1 does not assume continuity. The
existing `Langlands.Henniart.WeilArtinConductorExistenceStatement` (irreducible continuous
classes, existence of one presentation, Artin only) follows from clause 2.

## Declarations

- `WeilConductorIntegralityStatement` (definition, `Prop`).

## Literature

Pierre Deligne, *Les constantes des équations fonctionnelles des fonctions L*, Lecture Notes in
Mathematics 349 (1973), 501–597, §4.5, printed pp. 537–538: for a representation `V` of the Weil
group trivial on an open normal subgroup `J` of inertia `I`, formula (4.5.4) defines `a(V)` and
`sw(V)` on the finite quotient `I/J`, and (4.5.2) shows that they do not depend on `J`. A finite
inertia presentation is such a quotient, with `J` the inertia of `L`. Integrality is Serre,
*Local Fields*, Chapter VI, §2, Theorem 1′ (printed p. 99), for the finite Galois extension
presenting the representation; Deligne quotes it in the same paragraph ("D'après Artin").
