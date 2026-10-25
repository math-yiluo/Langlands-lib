# Degree-prime intermediate-field test for full local degree

The theorem
`Langlands.Global.cyclicPrimePowerLocalDegreeReductionStatement.{u,v}` proves
exactly the published proposition
`Langlands.Global.CyclicPrimePowerLocalDegreeReductionStatement.{u,v}`.
For a cyclic Galois extension `E/F` of number fields of degree `ℓ^r`, with `ℓ`
prime and `r > 0`, it constructs an intermediate field `K` that is Galois and
cyclic over `F`, has degree `ℓ`, and satisfies the proposition's universal local
test. For every finite prime `v` of `F`, every prime `q` of `K` above it, and the
specified `LiesOver` witness, a completed degree `[K_q : F_v] ≠ 1` gives a prime
`w` of `E` above both `q` and `v` with `[E_w : F_v] = [E : F]`.

The fields `F : Type u` and `E : Type v` have independent universes. The primes
are actual `HeightOneSpectrum` elements of the rings of integers; the local
fields are their `adicCompletion` fields with the canonical algebra instances
from `AdelicFunctoriality.FiniteExtension`. The intermediate field inherits its
number-field instance. There are no additional hypotheses.

## Implemented proof

Choose a generator `g` of `G = Gal(E/F)` and put `H = ⟨g^ℓ⟩`. The order of `g`
is `[E:F] = ℓ^r`. Mathlib's `Subgroup.index_zpowers_zpow` therefore gives
`[G:H] = gcd(ℓ,ℓ^r) = ℓ`. For a proper subgroup `D`, its index divides `ℓ^r`,
so `Nat.dvd_prime_pow` writes it as `ℓ^k`. The exponent is nonzero because
index one would imply `D = G`. Thus `ℓ` divides `[G:D]`, and
`IsCyclic.subgroup_le_iff_index_dvd` gives `D ≤ H`.

Set `K = IntermediateField.fixedField H`. The subgroup is normal because `G`
is cyclic. Galois correspondence gives `IsGalois F K` and identifies `[K:F]`
with `[G:H] = ℓ`. Surjectivity of restriction `Gal(E/F) → Gal(K/F)` makes the
latter group cyclic.

For arbitrary `v`, `q`, and its `LiesOver` witness, the published
`AdelicFunctoriality.exists_place_above` gives `w` above `q`. Transitivity of
`LiesOver` gives its relation to `v`. Define a homomorphism

`d : Gal(E_w/F_v) → Gal(E/F)`

by restricting scalars to `F` and then restricting to the normal subfield `E`.
Mathlib's restriction compatibility says that the image of `d σ x` in `E_w`
is `σ` applied to the image of `x`. To show `d` injective, form the equalizer
subalgebra of two local automorphisms with the same image under `d`. It contains
the image of every element of `E`. The published
`AdelicFunctoriality.subalgebra_eq_top_of_algebraMap_mem` says this subalgebra is
all of `E_w`, so the automorphisms agree.

Both `E_w/F_v` and `K_q/F_v` are Galois by
`AdelicFunctoriality.isGalois_adicCompletion`. Suppose the image of `d` is
proper. The group argument gives `range(d) ≤ H`. Every automorphism `τ` of
`K_q/F_v` lifts to an automorphism `σ` of `E_w/F_v`, by Mathlib's
`AlgEquiv.restrictNormalHom_surjective`. The image `d σ` lies in `H`, so it
fixes `K`. Restriction compatibility and the canonical completion scalar tower
show that `τ` fixes the image of `K` in `K_q`. The same equalizer argument,
now using the spanning theorem for `K_q/F_v`, gives `τ = 1`. Thus the local
Galois group is trivial. Its cardinality is `[K_q:F_v]`, contradicting the
assumed inequality.

Consequently `d` is surjective as well as injective. Equality of the two group
cardinalities, followed by `IsGalois.card_aut_eq_finrank` for the local and
global extensions, proves `[E_w:F_v] = [E:F]`.

The completion scalar tower is the published
`Langlands.ClassField.Global.CompletionTower.isScalarTower_completion`.
The restriction composition and equalizer arguments are written inside this
proof to retain independent universes; the older Library `decompositionHom`
interface puts both number fields in the same universe. No assertion identifying
the image with an ideal stabilizer is needed by this implementation.

## Source and scope

This is the pointwise arithmetic step in the proof of Artin and Tate,
*Class Field Theory* (AMS Chelsea, 2009), Chapter V §4, Theorem 3, printed
page 17 (PDF page 26). Registered source:
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The original passage and appended errata dated January 23, 2009 (PDF page 202)
were checked; those errata do not modify this argument. The source's base `k`,
upper field `K`, and degree-prime field `F` correspond to `F`, `E`, and `K`
here. The source argues using the intersection with the completed base field;
the implemented proof uses restriction of local automorphisms and the published
completion spanning theorem.

All auxiliary results are imported from the published Library and pinned
Mathlib, and the target statement and its imports are unchanged. The result
does not assert existence or infinitude of primes satisfying the local premise,
and does not prove `CyclicPrimePowerLocalDegreeStatement`. Local degrees include
ramification; no unramifiedness assumption is used.
