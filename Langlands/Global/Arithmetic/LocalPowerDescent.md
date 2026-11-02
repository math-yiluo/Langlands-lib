# Global powers from local powers at almost all finite places

Author: Worker 1244.

This module proves the prime-power cases of Artin and Tate, *Class Field
Theory* (2009), Chapter IX, Section 1, Theorem 1, proof parts 3–6, printed
pp.65–66 (PDF pp.74–75). The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The appended errata at PDF p.202 do not change this passage. The lemmas are
derived infrastructure for the proof of
`Langlands.Global.AlmostEverywherePowerHalfStatement`; their routes differ from
the source in places, as described below. The namespace is
`Langlands.Global.Arithmetic.LocalPowerDescent`.

Throughout, "`a` is a local `m`-th power at almost all finite places of `F`"
means

`∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ c : v.adicCompletion F, c ^ m = algebraMap F (v.adicCompletion F) a`,

that is, the set of finite places where `a` has no `m`-th root in the actual
adic completion is finite. Infinite places play no role.

## Change of field and finite exception sets

`eventually_pow_extension`: if `a ∈ F` is a local `m`-th power at almost all
finite places of a number field `F`, then its image in a finite extension `E`
is a local `m`-th power at almost all finite places of `E`. The map
`w ↦ w.under (𝓞 F)` sends the cofinite filter to the cofinite filter, because
each fibre injects into the finite type `AdelicFunctoriality.FinitePlacesAbove E v`.
A local root `c` at `v = w.under (𝓞 F)` is carried to the root
`AdelicFunctoriality.FiniteExtension.completionMap v w c` at `w`; the Library
lemma `completionMap_coe` says this map is compatible with `algebraMap F E`.
The two fields may have different universes.

`exists_finset_of_eventually` turns an eventually true property of finite places
into a finite set `S` outside which it holds.

## Roots of unity in the base field (proof part 3)

`exists_pow_eq_of_eventually_prime`: let `B` be a number field containing a
primitive `ℓ`-th root of unity, `ℓ` prime. If `a ∈ B` is a local `ℓ`-th power at
almost all finite places, then `a = b ^ ℓ` for some `b ∈ B`. Suppose not. Then
`X ^ ℓ - a` is irreducible (`KummerRadical.irreducible_of_forall_pow_ne`), and
`E = KummerRadical.radicalExtension B ℓ a` is a Galois number field of degree
`ℓ` over `B`, hence cyclic. The proved `Langlands.Global.cyclicNonsplitPrimeStatement`
gives a finite place `v` outside the finite exception set and a place `w`
above it with local degree different from one. But `a` has an `ℓ`-th root in
`B_v`, so `KummerRadical.finrank_adicCompletion_eq_one` gives local degree one,
a contradiction. The source applies its Chapter V, Theorem 2 to the whole
Kummer extension `k(α^(1/m))`; here that theorem is used only in this prime
case, through its Library form for cyclic extensions.

`exists_pow_eq_of_pow_eq_pow`: in any field containing a primitive
`ℓ ^ (r + 1)`-th root of unity `ζ`, with `0 < ℓ`, if `c ^ ℓ ^ (r + 1) = y ^ ℓ`
then `y` is an `ℓ ^ r`-th power. With `e = c ^ ℓ ^ r` one has `y ^ ℓ = e ^ ℓ`.
If `e = 0` then `y = 0`, and `c` is a root. Otherwise `y / e` is an `ℓ`-th root of unity, so it
equals `(ζ ^ ℓ ^ r) ^ i` for some `i`, and `y = (ζ ^ i * c) ^ ℓ ^ r`.

`exists_pow_eq_of_eventually_primePow`: let `B` contain a primitive `ℓ ^ r`-th
root of unity `ζ`, `ℓ` prime. If `a` is a local `ℓ ^ r`-th power at almost all
finite places, then `a = b ^ ℓ ^ r` with `b ∈ B`. This is induction on `r`.
For `r + 1`, the prime case with the root `ζ ^ ℓ ^ r` writes `a = b ^ ℓ`. At each
good place, the local equation `c ^ ℓ ^ (r + 1) = b ^ ℓ` and the image of `ζ` in
the completion give a local `ℓ ^ r`-th root of `b`, by the previous lemma. The
induction hypothesis for `b`, with the root `ζ ^ ℓ`, finishes the proof.

## Descent through a cyclic extension (proof part 4)

`exists_pow_eq_of_isCyclic`: let `E / B` be a cyclic Galois extension of number
fields of degree `ℓ ^ e`, `ℓ` prime, and let `E` contain a primitive `m`-th
root of unity `ζ`, `0 < m`. Let `a ∈ B` be nonzero, with an `m`-th root `β ∈ E`,
and let `a` be a local `m`-th power at almost all finite places of `B`. Then
`a = b ^ m` with `b ∈ B`. For `e = 0` the extension is trivial and `β ∈ B`.
For `e > 0`, the proved `Langlands.Global.cyclicPrimePowerLocalDegreeStatement`
gives a finite place `v` outside the exception set and a place `w` above it
with `[E_w : B_v] = [E : B]`. Let `c ∈ B_v` be a local root of `a`. In `E_w`
the images of `β` and `c` have the same `m`-th power, and `β ≠ 0`, so their
ratio is a power `ζ ^ j`. Hence `ρ = ζ ^ j * β ∈ E` satisfies `ρ ^ m = a`, and
the image of `ρ` in `E_w` lies in the image of `B_v`. Every element of the field
`B(ρ)` then maps into the image of `B_v`. Therefore `E_w` is spanned over `B_v`
by the images of a basis of `E` over `B(ρ)`: this span is a subalgebra
containing the image of `E`, so it is all of `E_w`
(`AdelicFunctoriality.subalgebra_eq_top_of_algebraMap_mem`). Thus
`[E : B] = [E_w : B_v] ≤ [E : B(ρ)]`, so `[B(ρ) : B] = 1` and `ρ ∈ B`.
The source proves this step by factoring `x ^ m - α` over `k` and using the
linear order of the subfields of a cyclic prime-power extension. The Lean proof
instead uses one place of full local degree, which yields the same conclusion.

`exists_pow_eq_of_cyclotomic` combines the two previous parts. If
`E / B` is as above and `E` contains a primitive `ℓ ^ m`-th root of unity, then
a nonzero `a ∈ B` that is a local `ℓ ^ m`-th power at almost all finite places of `B`
is an `ℓ ^ m`-th power in `B`. It transports the local hypothesis to `E`,
obtains a root in `E` by the prime-power Kummer step, and descends it.

`exists_pow_eq_of_primitiveRoot`: let `B` contain a primitive `ℓ ^ k`-th root
of unity, with `ℓ` prime, `k ≠ 0`, and `k + 2 ≤ ℓ * k`. Then a nonzero `a ∈ B`
that is a local `ℓ ^ (n + k)`-th power at almost all finite places is an
`ℓ ^ (n + k)`-th power in `B`. Here `E = CyclotomicField (ℓ ^ (n + k)) B`. It is
Galois over `B`, and `CyclotomicPrimePowerGalois.isCyclic_and_finrank_eq_pow`
makes it cyclic of degree `ℓ ^ e` for some `e`. Its distinguished primitive
root is the root of unity required by the previous lemma.

## Odd primes (proof part 5)

`exists_pow_eq_of_eventually_oddPrimePow`: for an odd prime `ℓ`, every natural
`r`, and nonzero `a` in a number field `K`, if `a` is a local `ℓ ^ r`-th power at
almost all finite places, then `a = b ^ ℓ ^ r` with `b ∈ K`. The case `r = 0` is
trivial. Otherwise let `B = CyclotomicField ℓ K`. Since `ℓ ≥ 3`, the level `k = 1`
satisfies `k + 2 ≤ ℓ * k`, so the previous lemma, applied to the transported
hypothesis, gives an `ℓ ^ r`-th root of `a` in `B`. The degree `[B : K]` divides
`φ(ℓ) = ℓ - 1` (`CyclotomicPrimePowerGalois.finrank_dvd_totient`), so it is
coprime to `ℓ ^ r`. Norm descent, `PowerDescent.exists_pow_eq_of_coprime_degree`,
then gives the root in `K`.

## Powers of two (proof part 6)

`exists_pow_eq_of_eventually_twoPow`: for every natural `s` and nonzero `a` in
a number field `K`, if `a` is a local `2 ^ (s + 2)`-th power at almost all
finite places, then `a = b ^ 2 ^ (s + 1)` with `b ∈ K`. The proof splits on
whether `K` contains a square root `i` of `-1`.

If it does, `i` is a primitive fourth root of unity, and the level `k = 2`
satisfies `2 + 2 ≤ 2 * 2`. `exists_pow_eq_of_primitiveRoot` with `ℓ = 2`,
`k = 2` and `n = s` gives `a = b ^ 2 ^ (s + 2)` in `K`, and `b ^ 2` is the
required root.

Otherwise let `B = CyclotomicField 4 K`. The same lemma over `B` gives
`b ∈ B` with `b ^ 2 ^ (s + 2) = a`. The norm `c ∈ K` of `b` satisfies
`c ^ 2 ^ (s + 2) = a ^ [B : K]` (`PowerDescent.exists_pow_eq_degree_of_root`).
Since `[B : K]` divides `φ(4) = 2`, write `2 = [B : K] * t`. With
`y = (c ^ t) ^ 2 ^ (s + 1)` this gives `a ^ 2 = y ^ 2`, so `a = y` or `a = -y`.
In the first case `c ^ t` is the required root. In the second case, at each good
place a local root `z` with `z ^ 2 ^ (s + 2) = a` gives
`(z ^ 2 / c ^ t) ^ 2 ^ (s + 1) = -1`, so `-1` is a local square at almost all
finite places. The prime case with `ℓ = 2` and the primitive square root of
unity `-1` then makes `-1` a square in `K`, a contradiction. The sign
argument only needs the local exponent `2 ^ (s + 2)` to be divisible by four.
Unlike the source, the proof does not split on whether `K(ζ_{2^(s+2)}) / K`
is cyclic; it claims only the half-power `2 ^ (s + 1)` in every case.
