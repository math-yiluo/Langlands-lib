# Pullbacks of actual augmented Artinian tests

This is an internal algebra prerequisite for constructing an actual Picard
versal family. It constructs the ordinary fibre product of augmented local
Artinian tests when one specified leg is surjective. It does not assert
existence of a hull, a formal family, an algebraization or a smooth atlas.

## Parameters and ordinary algebra

Work in an arbitrary universe `u`. Let `k` be a commutative ring and `K` a field
with its specified `k`-algebra structure. Let `A`, `B`, `C` be the actual objects
of `ArtinianTest k K` and let `q : A ⟶ C`, `r : B ⟶ C` be actual arrows. Thus
all three algebras are local Artinian `k`-algebras with specified surjective
augmentations to `K`, and both arrows preserve the augmentations. No
`K`-algebra structure on these algebras, or section of an augmentation, is
assumed.

In `ArtinianTest.Pullback`, `algebra q r` is literally Mathlib's subalgebra
`AlgHom.pullback (toAlgHom q) (toAlgHom r)`. Its elements are pairs `(a,b)`
with `q(a) = r(b)`, and its operations and original `k`-structure come from
the product. Its specified `augmentation` is the augmentation of `B`
composed with the second projection. `augmentation_fst` identifies it with
the augmentation of `A` composed with the first projection. Mathlib's
local-ring pullback theorem supplies locality: test arrows are local.

If `q` is surjective, the second projection is surjective, so the common
augmentation is surjective. `augmentation_surjective` records this argument.
Only the construction of the actual test and its actual test arrows needs
this surjectivity hypothesis; the ordinary compatible-pair algebra and its
ring universal property do not.

## Artinianness by restriction of scalars

The helper `isFiniteLength_of_common_augmentation` is stated for arbitrary
commutative local rings `R`, `S`, with an `R`-algebra structure on `S`, local
structure homomorphism, and `S` Artinian. It takes surjective ring maps
`εR : R → K`, `εS : S → K` satisfying
`εS.comp (algebraMap R S) = εR`, and proves `IsFiniteLength R S`.

Here is the implemented proof. For a class of `s` in the residue field of `S`,
choose `r` with `εR(r) = εS(s)`. The induced residue classes agree after
applying the map from the residue field of `S` to `K`. That map is injective,
since it is a homomorphism of fields. Hence the induced algebra map of
residue fields from `R` to `S` is surjective. Its module length is one.
Mathlib's `IsLocalRing.length_restrictScalars` therefore identifies the
length of `S` over `R` with its length over itself. A commutative Artinian
ring is Noetherian, so the latter length is finite. The equivalence between
finite length and a length different from infinity gives the conclusion.
This argument uses quotient residue fields and never chooses a coefficient
field in `R` or `S`.

For `P = algebra q r`, install the scalar actions on `A` and `B` through the
ordinary two projections. They are local maps and have the common
surjective augmentation to `K`. The helper makes both `A` and `B` Artinian
as `P`-modules. Their product is then Artinian as a `P`-module. The inclusion
of compatible pairs `P → A × B` is an injective `P`-linear map, so `P` is
Artinian over itself. This proves `isArtinianRing` and completes the
construction `test q r hq` as an actual `ArtinianTest k K` on that same
ordinary algebra. Subrings of Artinian rings are not assumed to be Artinian;
the common residue field is used in the restriction-of-scalars proof.

## Actual universal properties

`fst` and `snd` are the actual test arrows given by the ordinary projections.
`condition` proves that their composites with `q` and `r` agree.
`snd_surjective` proves surjectivity of the second projection from the given
surjectivity of `q`.

`liftAlgHom` sends `x` to the compatible pair `(a(x), b(x))` for any pair
of compatible `k`-algebra maps. Its projection identities are
`fst_liftAlgHom` and `snd_liftAlgHom`. For actual test arrows,
`lift` bundles this map with its augmentation triangle. `lift_fst` and
`lift_snd` give the exact equalities of actual arrows. `hom_ext` proves
that the two projections determine such an arrow, using equality of both
coordinates. `isLimit` and `isPullback` package this into the categorical
pullback universal property in the full actual test category, for every
actual test as source.

`liftRingHom` gives the same compatible-pair construction for arbitrary
commutative ring sources, without any supplied `k`-algebra structure.
`ring_isPullback` proves that the ordinary projection square is Cartesian
in `CommRingCat`. It quantifies over all commutative ring sources in the
universe, and needs no surjectivity hypothesis on `q` or `r`.

## Elementary surjections

`snd_isElementary` proves that if `q` is an `IsElementarySurjection`, then
`snd q r hq.1` is one as well. Surjectivity is already known. For a product
of an element of the pullback maximal ideal with an element of the second
projection's kernel, the second coordinate vanishes. The first coordinate
of the former element belongs to the maximal ideal of `A`, since the first
projection is local. The first coordinate of the kernel element is in
`ker q`, by its compatible-pair relation. Their product is therefore zero
by the elementary hypothesis on `q`. Equality of both coordinates proves
that the pullback maximal ideal annihilates this kernel.

This uses the Library's elementary convention of a surjection with
maximal-ideal-annihilated kernel, including zero kernels; no dimension-one
condition is asserted.

## Provenance and retained obligations

All constructions and proofs are internal consequences of the published
actual test category and Mathlib's ordinary pullback, local-ring and module
length APIs. In particular the restriction-of-scalars length formula, the
commutative Artinian-to-Noetherian theorem, and the injective linear-map
Artinian criterion account for the new closure argument. No external
representability theorem is invoked. Pullback kernel equivalences,
nilpotence transfer, flat tensor base change and geometric bundle patching
are separate results and are not reimplemented here.

The actual Picard infinitesimal gluing equivalence, hull and formal-family
existence, effectivity, algebraization, openness and the actual smooth
scheme atlas remain separate obligations. This unit proves closure and
universal properties of the test algebras only.
