# Local fibrewise flatness for essentially finite type algebras

`Langlands.Algebra.localFiberwiseFlatness` proves exactly the published
`Langlands.Algebra.LocalFiberwiseFlatnessStatement`, Stacks Project,
Commutative Algebra, Lemma 10.128.9, tag
[05UV](https://stacks.math.columbia.edu/tag/05UV). The rings R, S, S' and the
module M have independent universes. Under the hypotheses of that statement,
the theorem proves essential finite presentation of S over R, flatness of S
over R, and flatness of M over S.

The proof follows the finite-ideal approximation argument of 05UV, using the
published criteria `Langlands.Algebra.essFinitePresentationFiberwiseFlatness`
(00R7) and `Langlands.Algebra.localFiberInjectivity` (046Y). The auxiliary
lemmas in the namespace `LocalFiberwiseFlatnessProof` are private steps of
this proof. They use those criteria as theorems, with no additional criterion
premises.

## Quotient comparison and finite generation

For ideals I contained in K of a ring B, `quotient_finitePresentation` makes
B/K a finitely presented module over B/I when K is finitely generated.
The module action is the one induced by the canonical factor homomorphism.
Mathlib's `Ideal.Quotient.factor_ker` identifies its kernel with the image of
K in B/I. That image is finitely generated, so
`Module.finitePresentation_of_surjective` applies to the quotient map from
the free rank-one module B/I.

The helper `quotient_factor_injective` assumes that B/I is local and
essentially finitely presented over the local ring R, B/K is flat over R,
and I and K have the same image in B tensor_R k(R).
`Langlands.Algebra.quotientBaseChangeComparison` makes the residue base change
of the actual factor map injective. The preceding finite-presentation result
and finite presentation of B/I over itself allow 046Y to be applied with
S = S' = B/I and with source module B/I and target module B/K.
Its injectivity conclusion gives injectivity of B/I to B/K.

The helper `quotient_kernel_fg` considers a proper ideal J of a local
essentially finite type R-algebra B. The ring B tensor_R k(R) is Noetherian:
Mathlib gives this for k(R) tensor_R B, and tensor commutativity transports
it. Thus the extended ideal of J is finitely generated.
Suppose every quotient B/I by a finite ideal contained in J is essentially
finitely presented, and every such quotient whose extended ideal agrees
with J's is flat over R. For finite I contained in K contained in J, equality
of I's extended ideal with J's implies the same equality for K, by
monotonicity. Properness of J makes B/I nontrivial; the quotient is local,
and its structure map from R is local. The preceding helper proves
injectivity of B/I to B/K.
`Langlands.Algebra.idealFiniteGenerationFromQuotientStability` now gives
finite generation of J. This uses Noetherianity only for the residue fibre,
derived from essential finite type, without a Noetherian hypothesis on R or B.

## Flatness of the finite quotients

The helper `intermediate_flat` starts with a surjective R-algebra map
f : A to S whose residue base change is bijective, where A is local and
essentially finitely presented over R. It retains the given S, S', M and
their original actions. It installs the A-algebra structures on S and S'
through f and its composite, and restricts the A-action on M through S'.
The two explicit scalar compatibility checks show that this action agrees
with both the given S-action and the given R-action. Surjectivity makes
f local, so A to S' is local.

`Langlands.Algebra.surjectiveBaseChangeFlatnessTransport` transfers the given
flatness of the S-residue-fibre module to the A-residue-fibre module.
The published 00R7 theorem then applies to R to A to S' with M and proves
flatness of A over R.

For a surjection f : B to S, `presentation_efp` takes its actual kernel J
and the quotient-kernel R-algebra equivalence e : B/J to S.
For each finite I contained in J with the same residue ideal as J, it uses
the composite fI : B/I to B/J to S. The quotient is local and its map
from R is local. Its residue base change is bijective: the quotient
comparison proves this for the first map, and tensoring the algebra
equivalence proves it for the second. The identity expressing tensor base
change of a composite as a composite of tensor maps is checked explicitly.
The preceding helper therefore makes B/I flat over R.
The kernel finite-generation helper gives J finitely generated.
An essential finite presentation of B/J, composed with e, supplies one of S.
This argument allows the universes of B and S to differ.

## Closing the stated criterion

`Langlands.Algebra.localPolynomialPresentation` supplies a surjection from
B = R[x_1, ..., x_n] localized at a prime q to S, together with a local
map from R to B. The prime proof is installed as an instance.
`Langlands.Algebra.essFinitePresentation_of_isLocalization` gives essential
finite presentation of B over R.
`Langlands.Algebra.essFinitePresentationFiniteQuotient` gives the same property
for every quotient B/I by a finitely generated ideal I.
The preceding argument therefore proves essential finite presentation of S.
A final application of 00R7 to the original R, S, S', M gives both flatness
conclusions.

The intermediate B and its quotients live in R's universe. The use of 00R7
there has universe instance `{u, u, w, z}`, and the final application has
`{u, v, w, z}`. The quotient use of 046Y has `{u, u, u, u}`.
No equality between the four universes of the target is imposed. All fibre
modules are the actual tensor products with the canonical residue field
`IsLocalRing.ResidueField R`, as in the unchanged statement.

## Provenance

The registered original is `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
retained in
`literature/Stacks Project - Algebra flatness criteria and essentially finite presentation (HTML snapshot 2026-10-22)/`.
The precise locator is `05UV.html`, Lemma 10.128.9, statement and proof.
Its proof uses 00R7 and 046Y, imported here by their published Lean names.
The source's first proof sentence says essential finite presentation where
its hypothesis is essential finite type; the implemented argument starts
from the displayed finite-type hypothesis. The later repeated J' in the
source's nested-ideal phrase is interpreted as J' contained in J'' contained
in J, as required by its following quotient map.

The quotient-module, scalar-action and tensor-composition lemmas above are
internal formalization steps for this source argument. Their justification
is the specified Mathlib APIs and the imported quotient comparison,
flatness transport and ideal-stability theorems. The statement and all its
imports are preserved.
