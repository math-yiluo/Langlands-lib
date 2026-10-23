# Restricted products of actual rational Tate modules

Let `G : Grp (Over S)` be a commutative group scheme and let
`T : Over S` be a test scheme. This module constructs the algebraic
restricted products of the actual rational prime-adic Tate modules,
relative to the images of their integral modules. It also constructs
integral comparison maps, restriction to retained primes, and maps
induced by actual homomorphisms. No rational comparison is assumed.

## The integral image

For a prime `p`, in `Langlands.GroupScheme.Tate.PrimeAdic`,
`integralImage G T p` is the `ℤ_[p]`-submodule given by the range of

\[
\operatorname{toRational}:T_p(G,T)\longrightarrow
 V_p(G,T)=\mathbb Q_p\otimes_{\mathbb Z_p}T_p(G,T),
 \qquad x\longmapsto1\otimes x.
\]

The prime hypothesis is `[Fact p.Prime]`. `mem_integralImage` states
that membership means precisely existence of such a preimage.
Using the image avoids making injectivity an assumption of this
carrier definition.

`rationalMap_mem_integralImage` proves that the local rational map
induced by `f : G ⟶ H` preserves these integral images. For a
witness `x`, its image under the integral map witnesses the claim;
the tensor formulas identify the two resulting rational elements.

## Full and away restricted products

The remaining group-scheme declarations are in
`Langlands.GroupScheme.Tate.PrimeComparison`.
`RationalRestrictedProduct G T` is Mathlib's `RestrictedProduct`
over `Nat.Primes`, with local factors `PrimeAdic.Rational G T p`,
integral subsets the underlying additive subgroups of `integralImage`,
and filter `Filter.cofinite`. Thus its elements are families

\[
(v_p)_p\in\prod_p V_p(G,T),\qquad
 v_p\in\operatorname{im}(T_p(G,T)\to V_p(G,T))
 \text{ for all but finitely many }p.
\]

The inherited additive commutative group operations are coordinatewise.
There is no bound on the ranks of the local modules in this definition.

`RationalAwayRestrictedProduct G T m` uses the same construction
over `AwayPrime m`, the subtype of primes coprime to `m` from the
published twist indexing API. For positive `m` this omits precisely
its prime divisors; `m = 1` retains all primes and `m = 0` retains
none. In particular, the last carrier is the additive group of the
unique empty family.

## Integral maps and restriction

`integralToRestrictedProduct` maps the actual full integral Tate
limit to the restricted product by

\[
x\longmapsto
 \bigl(1\otimes\operatorname{fullToPrime}_p(x)\bigr)_p.
\]

Each component belongs to the integral image, so the cofinite
condition follows from a statement true at every prime.
`integralToAwayRestrictedProduct G T m` does the same using
`awayToPrime` at each retained prime. Both are additive homomorphisms;
their `_apply` lemmas give the displayed coordinate formulas.
The additive laws follow from those of the integral coordinate and
local rationalization maps.

`restrictedProductRestrict G T m` forgets the excluded coordinates.
The injective inclusion of retained primes into all primes tends
to the cofinite filter, so a cofinite integrality condition remains
cofinite after restriction. Its `_apply` lemma is the coordinate
formula. `integralToRestrictedProduct_restrictAway` states that this
restriction commutes with the integral comparison maps and the
published restriction of actual integral Tate limits; the equality
is definitional.

## Homomorphisms and compatibility

`restrictedProductMap T f` and `awayRestrictedProductMap T m f`
apply the published local `PrimeAdic.rationalMap` coordinatewise.
Preservation of the integral image proves that these maps preserve
the cofinite restriction condition. They are additive homomorphisms,
and their `_apply` lemmas are definitional coordinate formulas.

The two `_integral` theorems say that these induced maps commute
with the integral comparison maps. Their proofs use extensionality
at each prime and the tensor formula, after which integral naturality
is definitional. The `_id` and `_comp` laws are obtained by applying
the corresponding local rational-map laws at each coordinate.
The `_mul` laws send the product of commutative group-scheme
homomorphisms to the sum of induced additive maps; this is the
multiplicative notation for addition of homomorphisms in `Grp`.
`restrictedProductRestrict_map` is the definitional compatibility of
coordinate restriction and these induced maps.

The namespace `Langlands.AbelianScheme.Tate.PrimeComparison` supplies
abbreviations for both carriers, both integral comparison maps,
restriction and both induced maps, all using `A.toGrp` for a bundled
abelian scheme. Its two `_add` theorems give the homomorphism-addition
laws in the actual abelian-scheme category. The other group-scheme
laws apply directly through the abbreviations. At a geometric point
`s`, specialize the test scheme to `Over.mk s`.

## Provenance and limits

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), Chapter I, printed p.18 (PDF p.26), defines the
full, away and at-prime Tate modules and the rationalizations of the
full and away limits. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The actual torsion-section and rational carriers here are those
already used in the published Tate modules. Their generality in
commutative group schemes and test schemes is retained explicitly.

This restricted-product construction and its elementary maps are
internal infrastructure toward comparing those rationalizations
with local rational Tate modules; the comparison itself is not
claimed by the cited passage or proved here. The implementation
uses Mathlib's algebraic restricted product with the actual integral
images, rather than identifying the global rationalization with a
product by definition. The imported `RationalPrime` construction
was developed by Worker 142 using Worker 92's tensor-lift pattern.

This module supplies additive groups and additive maps. It introduces
no rational or finite-adele scalar action on the restricted product,
no rational topology, no continuity statement, and no injectivity,
surjectivity or equivalence claim for the integral or rational
comparison. Those are separate mathematical obligations. No
finiteness, rank, characteristic, monodromy or pairing hypothesis is
needed for the constructions and elementary laws established here.
