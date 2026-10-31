# Associated cuspidal inductions admit a nonzero intertwiner

Authors: Worker 240 and Worker 285. This module proves the published
proposition `Langlands.CuspidalSupport.AssociatedCuspidalInductionHomTheorem`
from `Langlands.Representation.CuspidalSupport.AssociationForwardStatement`.
The closing theorem is `associatedCuspidalInductionHomTheorem`. Its type is
exactly `AssociatedCuspidalInductionHomTheorem.{uF, uV, uW}`, and it has no
hypotheses.

## Statement proved

Fix a prime `p`, a p-adic field `F` of universe `uF`, a compatible topological
realization `T`, and a positive rank `n`. Fix block shapes `B` and `C` of `n`.
Let `σ` be a smooth complex representation of the Levi `B.Levi F.Carrier`
with carrier in universe `uV`, and let `τ` be one of `C.Levi F.Carrier` with
carrier in universe `uW`. Assume `σ` and `τ` are irreducible, both satisfy
`IsLeviCuspidal`, and they are associated (`RepresentationsAssociated`): some
permutation conjugating the Levi of `B` onto the Levi of `C` transports `σ` to
a representation equivalent to `τ`. Then there is a nonzero actual intertwiner
from `T.normalizedParabolicInduced B σ` to `T.normalizedParabolicInduced C τ`.
The proof does not use the irreducibility of `σ`; it uses only that `σ` is
admissible and quasicuspidal, the two components of `IsLeviCuspidal`.

## Imported results

- `minimalConjugatingCosets`, the published field-general form of
  `MinimalConjugatingCosetsTheorem` (module
  `MinimalConjugatingCosetsProof`): every conjugating permutation is a
  minimal conjugating permutation times an element of the source block-Weyl
  group. It enters through `exists_minimal_transport_equiv_of_associated`.
- `associatedJacquetFiltration` (module `AssociatedProof`), the published
  proof of `AssociatedJacquetFiltrationTheorem`, used at the given `F`, `T`
  and `n` with carrier universe `uV`. For quasicuspidal `σ` and associated
  Levis, it gives a finite object filtration of `A = r_C(i_B σ)` and a bijection `e` from its index set onto
  `MinimalConjugatingPermutations B C`. The graded piece of index `i` is
  equivalent to the Weyl transport of `σ` along `e i`.
- `leviCuspidalConstituentTheorem` (module `ConstituentProof`), the published
  proof of `LeviCuspidalConstituentTheorem`, used for the target block shape
  `C` at carrier universe `max uF uV`. This is the carrier universe of `A`.

## Implemented proof

1. Minimal representative. `exists_minimal_transport_equiv_of_associated`
   (module `BlockWeylTransport`), which uses the imported coset theorem,
   turns the association into a minimal conjugating permutation `v` together
   with an equivalence `ev` from the transport of `σ` along `v` to `τ`. In
   particular the Levis of `B` and `C` are associated (`LevisAssociated`).
2. Filtration. `associatedJacquetFiltration` at `σ`, applied with the
   quasicuspidality component of the hypothesis on `σ`, gives `r`, the
   bijection `e`, the filtration `s` of `A`, and the graded equivalences.
   (Its first conclusion, that `A` is quasicuspidal, is not used.)
3. Admissibility of `A`. `isAdmissible_of_transportFiltration` (module
   `BlockWeylTransport`) combines the smoothness of `A`, the admissibility
   component of the hypothesis on `σ`, and the graded equivalences along the
   conjugating permutations underlying `e i`. Each graded piece is admissible
   because Weyl transport preserves admissibility (the published
   `isAdmissible_transport`, module `AssociationReduction`). Admissibility
   then passes along the finite filtration
   (`isAdmissible_of_objectRepFiltration`, module `Extension`).
4. The piece equivalent to `τ`. Take the index `i = e⁻¹ v`. Its graded
   piece is equivalent to the transport along `e i`. That is the transport
   along `v` by `e (e⁻¹ v) = v`; the proof transports along this equality
   with the local lemma `htr`. Composing with `ev` gives an equivalence from
   the graded piece to `τ`.
5. Conclusion. `exists_ne_zero_of_gradedRepresentation_equiv` (module
   `AssociationForwardHomSupport`) receives the constituent theorem, the
   irreducibility and cuspidality of `τ`, the admissibility of `A`, and this
   graded equivalence. It returns the required nonzero intertwiner. Inside
   that lemma, the constituent theorem makes the graded subquotient an actual
   quotient of `A`. This gives a nonzero map `A → τ`, and the easy direction
   of Frobenius reciprocity turns it into a nonzero map between the
   inductions.

## Provenance

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups
I* (1977), Theorem 2.9(a), printed page 448 / PDF page 9, implication
(i) ⇒ (ii), with its proof in section 2.15(2), printed page 449 / PDF page 10
(registered source `bernstein-zelevinsky-1977-induced-i`). There the
filtration of `r_C(i_B σ)` from Corollary 2.13(c) has `τ` among its factors.
The cuspidal factor is a quotient by section 2.4(b), and Frobenius
reciprocity gives the nonzero intertwiner. The Lean proof follows this route.
The admissibility of `r_C(i_B σ)`, which the constituent theorem requires,
is derived here from the filtration and the admissibility of `σ`, as above.
