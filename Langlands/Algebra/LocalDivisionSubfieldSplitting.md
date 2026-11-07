# Splitting and Galois structure of an original full-residue subfield

This is an internal construction in `Langlands.CentralDivision`. Let `K : Type u`
be a nonarchimedean local field with its supplied valuative relation and topology,
and let `D : Type u` be a finite-dimensional central division `K`-algebra. Write
`v = localReducedNormValuation K D`, `R = DivisionValuation.Residue v`, and
`k = 𝓀[K]`. The field operations on `R` are `localDivisionResidueField K D`,
and the `k`-algebra structure is `localDivisionResidueAlgebra K D`, obtained by
reducing the original integral scalars. Neither universe nor characteristic is
restricted.

For an original finite field embedding `ι : L →ₐ[K] D`, with `L : Type uL`, write
`w = localDivisionSubfieldValuation K D ι` and
`τ = localDivisionSubfieldResidueMap K D ι`. Thus `w` is the restriction of `v`,
and `τ` is the actual inclusion of strict-ideal residue quotients. The finite
extension `L/K` may have its own universe.

## Chosen original root lifts

`localDivisionSubfieldRootLift` takes a proof that `τ` is surjective, a monic
polynomial `f` over `𝒪[K]`, and a simple root `z : R` of its reduction. It chooses
an element of the original integer ring `w.integer` by
`localDivisionSubfield_lift_base_polynomial`. Simplicity is the explicit condition
that the reduced derivative at `z` is nonzero.

`localDivisionSubfieldRootLift_spec` proves both properties of this chosen element:
`f` evaluates to zero using `localDivisionSubfieldBaseIntegerMap K D ι` as the
coefficient map, and applying `τ` to its actual reduction gives `z`. The choice
and the claims concern the original field and its restricted valuation.

## Splitting by lifting all residue roots

`localDivisionSubfield_splits_base_polynomial` assumes that `τ` is surjective,
`f` is monic, `p = f.map (IsLocalRing.residue 𝒪[K])` is separable over `k`, and
`p.map (algebraMap k R)` splits. It proves that the original scalar polynomial
`(f.map (algebraMap 𝒪[K] K)).map (algebraMap K L)` splits over `L`.

For every element of `p.rootSet R`, separability gives nonvanishing of the
reduced derivative. The preceding construction lifts it to an original integral
root in `L`. Reduction recovers the chosen residue root, so these lifts define an
injection from `p.rootSet R` to the root set of the original polynomial over `L`.
Separable splitting makes the first root set have cardinality `p.natDegree`.
Monicity preserves degree through both coefficient maps. The injection, the
comparison between distinct-root count and root-multiset count, and the general
upper bound on the latter show that the original polynomial has as many roots
with multiplicity as its degree. The polynomial splitting criterion completes
the proof.

## The original singleton adjoin as a splitting field

`residueGenerator_isSplittingField` requires only a field `K`, a finite-dimensional
division `K`-algebra `D`, and an element `a : D`; local-field, valuation, topology
and centrality assumptions are absent from this helper. Give the actual singleton
adjoin `E = residueGeneratorSubalgebra K D a` the field structure
`residueGeneratorField K D a`. If the image of `minpoly K a` splits in `E`, then
`E` is a splitting field of that polynomial over `K`.

The internal original element `c = ⟨a, residueGenerator_mem K D a⟩` generates `E`
by `residueGenerator_adjoin_eq_top`. Injectivity of the original inclusion
identifies `minpoly K c` with `minpoly K a`, so `c` is among the polynomial's roots
in `E`. Consequently those roots generate all of `E`, proving the splitting-field
property together with the supplied splitting hypothesis.

## Existence of a Galois full-residue subfield

`exists_localDivision_fullResidue_galois_subfield` proves that there exists
`b : v.integer` such that, for the original field
`E = residueGeneratorSubalgebra K D (b : D)` with its specified field structure:

- the original element `(b : D)` is separable over `K`;
- the actual residue inclusion from `E` into `R` is surjective;
- `Module.finrank K E = Module.finrank k R`;
- `IsGalois K E` holds.

All choices are internal to the proof. Start with the polynomial and subfield
witnesses from `exists_localDivision_fullResidue_polynomial_subfield`. The residue
image of that polynomial is the minimal polynomial of the reduction of `b`.
The finite base residue field `k` is perfect, so that polynomial is separable.
The finite residue extension `R/k` is Galois, so the same polynomial splits over
`R`. The lifting and root-count argument proves splitting over the original
`E`. Its scalar image is exactly `minpoly K (b : D)`. The singleton-adjoin helper
makes `E` its splitting field, and separability of the original generator makes
this splitting field Galois. The proof retains the previous actual residue
surjectivity and exact dimension equality.

## Provenance and scope

The construction is derived internally from the actual full-residue subfield,
Hensel lift and exact polynomial witnesses in the imported `LocalDivision`
modules, together with Mathlib's separable-root counting, finite-field Galois
and separable-splitting-field results. No external structural assertion is used
as an extra premise. Perfectness is used for `k`, the finite residue field.

This pair does not prove cyclicity of the original Galois group, compare this
subfield degree with the reduced degree of `D`, compute ramification, or prove
local SK1 or local Kneser–Tits.
