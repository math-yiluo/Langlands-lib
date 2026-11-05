# Conditional fundamental-weight proof for the actual cocenter

Authors: Worker 1282 and Worker 1642.

This is a derived conditional assembly for the exact proposition
`SplitTorusCentralizerCocenterInducedStatement.{u}`. It implements the
fundamental-weight argument from the target's provenance using the actual
character lattices, pullback and ordinary Galois actions. It does not prove
its five structural inputs.

`isInducedTorus_of_cocenterRootDescent` is the lattice step. Its inputs are a
finite Galois extension `E/k`, a homomorphism `g : T → Q`, a root datum `P` on
the actual character and cocharacter lattices of `T_E`, a base `B`, a selected
set `s` of simple indices, integral coroot generation, splitness of `Q_E`, and
the predicate `CocenterRootDescentData` for the actual map `g`.

Integral coroot generation makes the simple coroots an integral basis.
`fundamentalWeightBasis` is its dual basis under the root-datum perfect
pairing. The coordinate formula identifies the image of actual pullback with
the span of fundamental weights outside `s`. Twisted Galois action preserves
the pairing and permutes the simple coroots; hence it permutes these dual
fundamental weights with the same permutation. Preservation of `s` preserves
the complementary indices.

Actual pullback commutes with ordinary Galois action. The character correction
fixes its whole image, so its twisted action agrees there with ordinary Galois
action. `isInducedTorus_of_twisted_complement` pulls back the complementary
basis to `X*(Q_E)` and supplies exactly the basis required by `IsInducedTorus Q`.

`SplitTorusCentralizerCocenterInducedInputsStatement` is the conjunction of
the following five propositions, all at the arbitrary universe `u`:

- `DynamicCentralizerReductiveStatement`;
- `CocenterQuotientExistenceStatement`;
- `IsSimplyConnectedFieldExtensionStatement`;
- `SplitSimplyConnectedCorootSpanStatement`;
- `SplitTorusCentralizerCocenterRootModelStatement`.

`splitTorusCentralizerCocenterInduced_of_inputs` proves that this conjunction
implies the exact public `SplitTorusCentralizerCocenterInducedStatement`.
For its supplied field, simply connected group, split subtorus, centralizer
representative, derived subgroup and commutative fppf quotient, the first
input gives connected reductivity of that representative through
`splitTorusCentralizerReductive_of_dynamic`. The second, through
`suppliedCocenterTorus_of_existence`, gives the torus property of the supplied
quotient, rather than merely of some constructed quotient.

The fifth input then provides a maximal ground-field torus, a finite Galois
common splitting field, and actual reduced root data with the character
comparison and twisted descent laws. The third input supplies simple
connectedness over that field. The fourth, applied to the supplied actual
split maximal torus and root datum, gives integral coroot generation. The
lattice step above concludes inducedness of the original supplied quotient.

No quasi-splitness, perfectness or characteristic condition is introduced.
All extension and basis index types stay in `Type u`. The structural
propositions are explicit premises, so this module does not establish the
unconditional target, prove root-model existence, or close the host proof task.

The implementation composes the paired modules
`LeviCocenterRootModelStatement`, `SplitTorusCentralizerReduction`,
`SuppliedCocenterTorusReduction`, `FundamentalWeightPermutation` and
`InducedPermutationBasis`. Its provenance is that composition, not an
additional external theorem.
