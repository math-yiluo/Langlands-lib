# Local unramified birational algebras

`Langlands.AlgebraicGeometry.localUnramifiedBirationalAlgebra` proves exactly
`LocalUnramifiedBirationalAlgebraStatement` in arbitrary universe `u`, with
no outer hypotheses. Thus a finite type formally unramified `R`-subalgebra
`A` of `FractionRing R` is the bottom subalgebra if `R` is a geometrically
unibranch local domain and `A` has a prime over the maximal ideal of `R`.

The proof has three steps. First, the private lemma
`isLocalRing_of_integral_embedding_fractionRing` proves that an integral
`R`-algebra embedding in `FractionRing R` is local. It embeds the algebra
in the canonical normalization `B` of `R`. The integral injective inclusion
into the local ring `B` reflects units, so locality descends.

Second, algebraic Zariski's Main Theorem, in Mathlib's
`Algebra.ZariskisMainProperty.of_finiteType` and
`Algebra.zariskisMainProperty_iff`, gives an element `r` integral over `R`,
outside the chosen prime of `A`, such that multiplying any element of `A`
by some power of `r` makes it integral. The integral closure `C` of `R`
in `A` is local by the first step. The chosen prime contracts to its
unique maximal ideal, so `r` is a unit in `C`. Its inverse is integral;
multiplication by powers of that inverse shows all of `A` is integral.
Since `A` is also finite type, it is finite as an `R`-module.

Third, `finiteUnramifiedSubalgebra_eq_bot` handles this finite case. It
places `A` in the canonical normalization `B` and again proves `A` local.
The residue-field tower shows that the residue field of `A` is purely
inseparable over that of `R`. Formal unramifiedness gives separability,
so this residue extension is trivial. The private lemma
`surjective_of_finite_unramified_of_surjective_residue` applies Nakayama's
lemma to the cokernel of `R → A`, using the unramified equality of
extended maximal ideals. It obtains surjectivity of `R → A`, which is
exactly the asserted bottom-subalgebra equality.

The additional transport lemma
`algebraMap_surjective_of_unramified_fractionRing_embedding` applies this
result to an arbitrary finite type formally unramified `R`-algebra `B`
with an injective `R`-algebra map to any fraction ring `K` of `R` and a
prime over the maximal ideal of `R`. It concludes surjectivity of the
actual map `algebraMap R B`. The types of `R`, `B`, and `K` may have
independent universes. The proof composes the embedding with the
canonical fraction-ring equivalence and identifies `B` with the range
subalgebra. Finite type, formal unramifiedness, and the prime over the
maximal ideal transport along this algebra equivalence. The main
theorem makes the range the bottom subalgebra, and injectivity gives
the asserted surjectivity. This is a derived corollary of the main
theorem, intended for applying it to actual scheme stalks.

The further derived corollary
`algebraMap_surjective_of_essFiniteType_unramified_fractionRing_embedding`
allows `B` to be an essentially finite type formally unramified local
`R`-algebra, provided its structure map is local. It retains the injective
map to an arbitrary fraction ring and the three independent universes.
The proof chooses Mathlib's finite type subalgebra `A` whose localization
is `B`. The elements inverted are exactly the complement of the prime
obtained by contracting the maximal ideal of `B`. After transporting
unramifiedness to this prime localization, it shrinks to an unramified
finite type localization `A_f`. Its map into `B`, and hence the fraction
ring, is injective. The finite type corollary makes `R → A_f` surjective.
Consequently every element of `A` comes from `R`. Expressing an element
of `B` as a fraction then reduces surjectivity of `R → B` to reflecting
units along its local structure map.

The statement's source provenance is the affine local consequence of
EGA IV, fourth part, 18.10.2(iii) and 18.10.18 explained in its paired
Markdown. This proof follows the algebraic normalization route above,
using existing Mathlib theorems; it does not use a strict henselization
or assume the scheme-level open-immersion conclusion. The passage to
arbitrary schemes and the generic-section extension theorem are separate
obligations. No noetherianity, normality or finite presentation hypothesis
is added.
