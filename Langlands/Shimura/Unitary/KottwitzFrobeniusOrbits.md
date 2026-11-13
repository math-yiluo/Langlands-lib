# Frobenius orbits on embeddings are the places above an unramified `p`

Module `Langlands.Shimura.Unitary.KottwitzFrobeniusOrbits`, namespace
`Langlands.Shimura.KottwitzDual`.

This module supports items 2–3 of Task 5424. Module `KottwitzFrobeniusPlaces`
introduced the Prop `FrobeniusOrbitsArePlaces K p θ` and showed that it implies
`FrobeniusInvariantsRational E K n p θ hΦ`. That rationality statement is a
hypothesis of the lift results in `KottwitzLiftIndependence`. This module
**proves** `FrobeniusOrbitsArePlaces K p θ` for every number field `K` that is
unramified at `p`, so the rationality hypothesis now follows from
unramifiedness alone.

Notation (as in `KottwitzFrobeniusPlaces`):

- `K` is a number field, `p` a prime, `θ : ℂ →+* Q̄_p` a ring homomorphism, and
  `Q̄_p = PadicAlgCl p`.
- `Frob = geometricFrobenius p ∈ Gal(Q̄_p/ℚ_p)` is the Library's chosen geometric
  Frobenius (module `KottwitzDualGroup`). It is the image in the absolute Galois
  group of `localGeometricFrobenius` of `ℚ_p`.
- `frobeniusPerm K p θ` is the permutation `i ↦ θ⁻¹ ∘ Frob ∘ θ ∘ i` of the
  complex embeddings `i : K →+* ℂ`.
- `harrisPlace p θ i` is the place `w ∣ p` of `K` made of the algebraic integers
  `x` with `|θ(i(x))|_p < 1`. `harrisPrime p θ i` is the underlying prime.
- `harrisPlaceFibre p θ w` is the set of embeddings whose place is `w`.
- `inertiaDegree w = f_w = [k_w : 𝔽_p]` is the residue degree over `ℚ`.
- "Unramified at `p`" is the Library's
  `KottwitzUnramified.IsUnramifiedAt (rationalPrimePlace p) K` (module
  `KottwitzChart`): every place `w ∣ p` of `K` has ramification index `e_w = 1`
  over `ℚ`.

## Definitions

- `frobeniusOrbit K p θ i : Finset (K →+* ℂ)` is the Frobenius orbit of the
  embedding `i`. It is the image of `r ↦ (frobeniusPerm K p θ ^ r) i` over
  `0 ≤ r < Function.minimalPeriod (frobeniusPerm K p θ) i`. Basic facts:
  - `mem_frobeniusOrbit`: `j` lies in the orbit iff `j = (frobeniusPerm K p θ ^ r) i`
    for some `r : ℕ`. Reduce `r` modulo the minimal period
    (`Function.iterate_mod_minimalPeriod_eq`).
  - `card_frobeniusOrbit`: the orbit has exactly as many elements as the minimal
    period, because the iterates below the minimal period are pairwise distinct
    (`Function.iterate_injOn_Iio_minimalPeriod`).
  - `frobeniusOrbit_subset_harrisPlaceFibre`: the orbit of `i` lies in the fibre
    over `harrisPlace p θ i` (`harrisPlace_frobeniusPerm_pow`).

## Main results

- `frobeniusOrbitsArePlaces_of_isUnramifiedAt (h : IsUnramifiedAt (rationalPrimePlace p) K) :
  FrobeniusOrbitsArePlaces K p θ`. The conclusion has two parts. For every
  embedding `i`, the minimal period of `i` under `frobeniusPerm K p θ` is
  `inertiaDegree (harrisPlace p θ i)`. Also, `harrisPlace p θ j = harrisPlace p θ i`
  holds iff `j = (frobeniusPerm K p θ ^ r) i` for some `r : ℕ`.
- `frobeniusInvariantsRational_of_isUnramifiedAt hΦ n h`: let `K` be a CM field
  with totally real subfield `E` and CM section `Φ`, and let `K` be unramified
  at `p`. Then `FrobeniusInvariantsRational E K n p θ hΦ` holds. This is the
  previous theorem combined with
  `frobeniusInvariantsRational_of_frobeniusOrbitsArePlaces` from
  `KottwitzFrobeniusPlaces`.

## Proof

The proof avoids completions. It reduces modulo the place, works in the residue
fields, and finishes by counting.

### Step 1: inverse Frobenius is the `p`-power map on residues (section `Residue`)

The section works over an arbitrary `p`-adic field `F : PadicField p`. It
equips `F.Carrier` with the topology, valuation and normed-field instances of its
canonical topological data, as local instances. Write
`σ = localProjection F (localGeometricFrobenius F) ∈ Gal(F̄/F)` and
`q = F.canonicalTopologicalData.residueCardinality`.

- `residueHom_inv_localGeometricFrobenius`: `σ⁻¹` acts on the residue field of
  `LocalGalois.closureIntegers F` (the integral closure in `F̄`) by `y ↦ y ^ q`.
  The proof transports along `LocalGalois.localResidueClosureEquiv` to the
  algebraic closure of the residue field `k_F`. There `localResidueMap F σ` is
  the geometric Frobenius of `k_F` (Library `localGeometricFrobenius_residue`).
  Its inverse is the arithmetic Frobenius `x ↦ x ^ #k_F`, and `#k_F = q`
  (`localResidueCardinality_eq`).
- `residueHom_inv_pow_localGeometricFrobenius`, `residue_integerAut_inv_pow`:
  by induction, `(σ⁻¹)^r` acts on residues by `y ↦ y ^ (q ^ r)`. In the second
  form, the residue of `(σ⁻¹)^r (y)` equals `(residue y) ^ (q ^ r)` for integral
  `y`.

Specialise to `F = PadicField.rational p`, i.e. `ℚ_p` with its canonical data:

- `rational_mem_integer_iff`: an element of `ℚ_p` lies in the valuation ring of
  the canonical valuation iff its norm is `≤ 1`. The proof uses
  `PadicField.canonicalTopologicalData_vle` and `canonicalNorm_algebraMap`.
- `mem_closureIntegers_of_norm_le_one`: every `y ∈ Q̄_p` with `‖y‖ ≤ 1` lies in
  `LocalGalois.closureIntegers`. The algebraic closure of
  `(PadicField.rational p).Carrier` is `PadicAlgCl p` by definition. By
  `LocalGalois.integral_iff_mem_spectralIntegers`, `‖y‖ ≤ 1` means that `y` is
  integral over `ℤ_p`. Integrality transfers along the inclusion of `ℤ_p` into
  the canonical valuation ring (`IsIntegral.map_of_comp_eq`). Then
  `LocalGalois.closureIntegers_integral` gives membership.
- `rational_residueCardinality`: `q = p` for `ℚ_p`
  (`PadicField.TopologicalData.residueCardinality_eq_prime_of_degree_one`).
- `norm_geometricFrobenius_inv_pow_sub_lt` (key congruence): for
  `y ∈ Q̄_p` with `‖y‖ ≤ 1` and every `r : ℕ`,
  `‖Frob⁻ʳ (y) − y ^ (p ^ r)‖ < 1`. Proof: `z = Frob⁻ʳ(y) − y^(p^r)` is integral
  and, by the previous facts, has residue `0`, so it is not a unit of the
  integral closure. If `‖z‖ ≥ 1`, then `z ≠ 0` and `‖z⁻¹‖ ≤ 1`, so `z⁻¹` is also
  integral and `z` would be a unit. This is a contradiction.

### Step 2: `f_w` divides every Frobenius period (section `Places`)

- `theta_frobeniusPerm_pow_apply`:
  `θ((frobeniusPerm K p θ ^ r) i x) = Frob^r (θ (i x))`.
- `norm_theta_algebraMap_le_one`: `‖θ(i(x))‖ ≤ 1` for every algebraic integer
  `x ∈ 𝓞 K` (Library `valuation_embedding_le_one`).
- `pow_sub_mem_harrisPrime_of_frobeniusPerm_pow`: suppose
  `(frobeniusPerm K p θ ^ r) i = i`. Then `x ^ (p ^ r) − x ∈ harrisPrime p θ i`
  for all `x ∈ 𝓞 K`. Indeed, `y = θ(i(x))` is fixed by `Frob^r`, hence by
  `Frob⁻ʳ`. The key congruence then gives `‖y ^ (p ^ r) − y‖ < 1`, which is the
  membership condition of `harrisPrime`.
- `card_quot_rationalPrimePlace`: `𝓞 ℚ ⧸ (p)` has `p` elements, through
  `𝓞 ℚ ≅ ℤ` and `ℤ ⧸ (p) ≅ ZMod p`.
- `card_quot_harrisPrime`: the residue ring `𝓞 K ⧸ P_w` has `p ^ f_w` elements
  (Mathlib `Ideal.cardQuot_pow_inertiaDeg`).
- `inertiaDegree_dvd_of_frobeniusPerm_pow_apply_eq`: suppose
  `(frobeniusPerm K p θ ^ r) i = i`, and let `w = harrisPlace p θ i`. Then
  `f_w ∣ r`. Proof: in the finite field `k_w = 𝓞 K ⧸ P_w`, every element
  satisfies `u ^ (p ^ r) = u` by the previous lemma. So every unit satisfies
  `u ^ (p ^ r − 1) = 1`, and `FiniteField.forall_pow_eq_one_iff` gives
  `p ^ f_w − 1 ∣ p ^ r − 1`. Since
  `gcd(p ^ a − 1, p ^ b − 1) = p ^ gcd(a, b) − 1`
  (`Nat.pow_sub_one_gcd_pow_sub_one`), we get `p ^ gcd(f_w, r) = p ^ f_w`.
  Hence `gcd(f_w, r) = f_w`, i.e. `f_w ∣ r`.
- `minimalPeriod_frobeniusPerm_pos`, `inertiaDegree_dvd_minimalPeriod`: every
  embedding is periodic, since `frobeniusPerm` has finite order. Its minimal
  period is positive and divisible by `f_w`.

### Step 3: counting

- `inertiaDegree_le_card_harrisPlaceFibre`: `f_w ≤ #harrisPlaceFibre p θ w` for
  every `w ∣ p`. Choose `i` over `w` (`harrisPlace_surjective`). Then
  `f_w ≤ period(i) = #orbit(i) ≤ #fibre(w)`.
- Proof of `frobeniusOrbitsArePlaces_of_isUnramifiedAt`. First,
  `∑_w #fibre(w) = [K : ℚ]` (`sum_card_harrisPlaceFibre`). Second,
  `[K : ℚ] = ∑_w e_w f_w`, the fundamental identity over the actual places above
  `p` (Library `finitePlacesAbove_sum_ramification_inertia`). Since `e_w = 1`,
  `∑_w f_w = ∑_w #fibre(w)`. Each term satisfies `f_w ≤ #fibre(w)`, so
  `f_w = #fibre(w)` for every `w` (`Finset.sum_eq_sum_iff_of_le`). Now fix `i`
  over `w`. Then `#fibre(w) = f_w ≤ period(i) = #orbit(i)` and
  `orbit(i) ⊆ fibre(w)`, so `orbit(i) = fibre(w)` and `period(i) = f_w`. The
  second conjunct follows: `harrisPlace p θ j = w` iff `j ∈ fibre(w) = orbit(i)`,
  iff `j = (frobeniusPerm K p θ ^ r) i` for some `r` (`mem_frobeniusOrbit`).

## Provenance

The Lean statements are internal. They prove the Prop
`FrobeniusOrbitsArePlaces` introduced in `KottwitzFrobeniusPlaces`, about the
Library objects `harrisPlace`, `frobeniusPerm` and `inertiaDegree`. The
mathematical content is the standard description of the `p`-adic embeddings of a
number field unramified at `p`: they are grouped by place, and Frobenius permutes
the embeddings over `w` cyclically with period `f_w`. For context see Neukirch,
*Algebraic Number Theory*, Ch. I §8 (the identity `∑ e_w f_w = [K : ℚ]`) and
Ch. II (extensions of valuations and unramified extensions). In Task 5424 this
description lets the embedding-indexed and the place-indexed coordinates of the
unramified parameters agree. The proof implemented here is our own. It uses
only the residue action of the Library's chosen Frobenius, two finite-field
facts (if every unit of `k_w` satisfies `u ^ m = 1` then `#k_w − 1 ∣ m`, and
`gcd(p ^ a − 1, p ^ b − 1) = p ^ gcd(a, b) − 1`), and the global fundamental
identity. It uses neither completions nor decomposition groups.
