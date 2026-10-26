# Actual Haar correction cancellation for p-adic GL parabolic orbits

Author: Worker 400.

`Langlands.Geometric.padicHaarCorrectionCancellation` proves exactly
`Langlands.Geometric.PadicHaarCorrectionCancellation.{uF}` from
`Langlands.Representation.Geometric.PadicCorrectionCancellationStatement`.
It retains every prime, actual finite p-adic extension in universe `uF`,
supplied compatible `TopologicalData`, positive rank, pair of ordered block
shapes, minimal representative, and element of the actual intersection Levi.
The conclusion is the product identity in complex units for the two published
positive-half Haar correction characters, with the second pulled back through
`General.intersectionEquiv`.

The correction subgroups are the full `U ∩ g⁻¹ Q g` and `V ∩ g P g⁻¹`.
All closedness and normalizer facts are the internally constructed ones in the
unchanged statement. The final theorem has no additional Haar, root-product,
character-determination, compatibility, or cancellation hypothesis.

## Finite root products and positive halves

The internal lemma `correction_root_products` uses two maps from a finite index
set to linearly ordered types. It splits each strictly increasing root set into the roots
allowed by the other partition and the roots omitted by it. Swapping the two
indices bijects the two omitted sets and inverts each weight `a_i / a_j`.
Consequently the omitted products cancel, leaving equality between the product
of the two full root products and the product of the allowed-pattern products.
No minimality condition or topology is needed for this finite identity.
`correction_root_products_reindex` states the same identity with the second
pattern in its own index set, transporting the weights through the inverse
index equivalence. It proves the transport by finite-product reindexing.

The internal lemma `positive_half_corrections_cancel` works with four positive
characters on a common group. It combines the published square-root homomorphism
on nonnegative real units with their embedding in complex units. Applying that
homomorphism to the balanced quotient of the four modulus values yields exact
cancellation of the two positive-half corrections. This uses the canonical
positive square root throughout.
`General.haar_corrections_cancel_of_modulus_products` instantiates this
algebraic construction with the four actual Haar modulus characters, composing
the two modulus characters on the target intersection with the published
`intersectionEquiv`. The assembly proves its balanced-modulus hypothesis on
actual diagonal matrices.

## Actual Haar moduli on diagonals

`General.intersectionEquiv_diagonal` computes the actual matrix of the transported
intersection element. The published permutation-conjugation entry formula sends
the diagonal units `t` to `t ∘ w.symm`; this holds for arbitrary commutative rings
and permutations and assumes no modulus formula.
`General.intersectionSource_radical_self` proves that the full correction
subgroup at `C = B` and the identity permutation equals the whole standard
radical. It uses its inclusion in its own parabolic.

The imported `correctionSubgroupDiagonalHaar` theorem constructs Haar on the
actual full correction subgroup by transporting product additive Haar through
its allowed-entry homeomorphism. Its proof uses finite triangular translation
for left invariance, actual diagonal matrix conjugation for coordinate scaling,
and p-adic scalar Haar scaling. Haar uniqueness identifies its pushforward
scale `c⁻¹` with the actual positive normalizer modulus `c`. This proof reuses
that published analytic theorem by Lean name; it makes no extra Haar comparison
assumption. The proof and its construction are documented in
`Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof`.

`radical_diagonal_modulus` specializes the proved full-correction
Haar formula to `C = B` and the identity permutation. The proved subgroup
equality identifies its actual subgroup with the whole radical; the strict
source-block inequality implies the remaining weak inequality. Its result is
an unconditional computation of the actual whole-radical modulus for a supplied
diagonal normalizer. Thus both the whole-radical and full-correction modulus
formulas used here follow from a proved Haar-measure calculation.

## Assembly on the actual intersection Levi

`padicHaarCorrectionCancellation_of_diagonal_character` isolates the algebraic
assembly from character determination. It takes
`IntersectionLeviDiagonalCharacterStatement.{uF}` and forms the product of the
two actual correction characters on
the source intersection Levi, pulling the second character back through
`intersectionEquiv`. The character-determination hypothesis reduces its
triviality to actual diagonal matrices. Characteristic zero of the supplied
field is obtained from its specified algebra over `Padic p` using
`Algebra.charZero_of_charZero`. On diagonal matrices, the whole-radical
specialization and the published full correction-subgroup theorem compute the four
actual positive moduli. The transported diagonal is `t ∘ w.symm`, and the
second correction uses the inverse permutation. The reindexed finite-root
identity balances those four products; the positive-half helper then proves
that the two complex corrections multiply to one on every diagonal.

The final theorem `padicHaarCorrectionCancellation` supplies the imported,
proved `intersectionLeviDiagonalCharacterTheorem` to that assembly. This
character theorem applies to every characteristic-zero field in the same
universe. Its proof realizes the actual intersection as a finite product of
general linear groups through proved refinement and embedding equivalences,
checks that simultaneous diagonal units give literal ambient diagonal matrices,
and uses diagonal/transvection induction. Scaling a transvection by two
conjugates it to its square, so every complex-unit character kills it.
Consequently triviality on actual diagonals implies triviality on the whole
actual intersection. The proof and all transport identities are documented in
`Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterProof`.
No regularity or character-generation assumption is added here.

## Provenance and scope

These finite-product and assembly arguments are internal derivations. Their
source motivation is Bernstein–Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), section 6.4, printed pp.468–469, registered as
`bernstein-zelevinsky-1977-induced-i`. That section computes the residual squared
correction by opposite root products and then uses positivity. The implemented
argument applies the published positive square-root homomorphism directly to
the balanced actual positive moduli. The actual Haar formulas and algebraic
character determination are imported proved results, with the specializations,
root balance, and assembly proved in this module.

Original file:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The entire section 6.4, printed pp.468–469 (PDF pp.29–30), was read in preparing
this proof.

All imported Lean/Markdown pairs and the target statement are preserved.
This proves scalar cancellation only. The orbit/Jacquet natural isomorphism
and the refined explicit-block/Haar bridge remain separate results.
