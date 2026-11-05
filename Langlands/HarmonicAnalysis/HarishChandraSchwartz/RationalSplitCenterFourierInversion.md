# Fourier inversion over the split center (Proposition VII.2.1, case `M = G`)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCenterFourierInversion`.
The first section is in namespace `Langlands.HarmonicAnalysis.TorusFourier` (generic torus
results), the second in `Langlands.HarishChandraSchwartz` (actual rational points). It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalValuationCoordinates` (with
  `TorusLatticeDuality`; Worker 249, accepted candidate 2863d106): the lattice coordinates `n = rationalValuationCoordinates G hG`,
  `rationalUnitaryUnramifiedCharacter_apply`, `rationalSplitLattice hG s` (written `Λ_s`),
  `mem_rationalSplitLattice`, `finiteIndex_rationalSplitLattice`,
  `coordinates_symm_mem_restrict_ker_iff`, `latticeAnnihilator`, `finite_latticeAnnihilator`,
  `isTrivialOn_latticeAnnihilator_iff`; through them the published `TorusFourierInversion`
  (`torusFourierCoeff`, `hasSum_torusFourierCoeff_mul_conj`, `IsTrivialOn`,
  `integral_mul_right_mul_torusCharacter`, `sum_torusCharacter_subgroup`);
- the published `HarishChandraSchwartz.CentralFourierInversion`: `cosetValues` and
  `hasSum_integral_quotient` (the integral over a group with an open subgroup `Z₀` is the sum
  over `Z/Z₀` of `mes(Z₀)` times the coset values of a right `Z₀`-invariant integrable function);
- the published `Representation.Plancherel.RationalCharacterHaar`: the I.1 measure
  `rationalUnitaryUnramifiedCharacterHaar s hs hindex` on `Im X(G)` and its total mass
  `rationalUnitaryUnramifiedCharacterHaar_univ` (the cardinality of the kernel of the restriction
  `Im X(G) → Im X(T)`); through its imports `exists_circle_character_extension`
  (`RationalRestrictionSurjectivity`), `rationalCommonNormKernel` (`G¹`),
  `isOpen_rationalCommonNormKernel` and `compactSpace_rationalUnitaryUnramifiedCharacters`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.

- Proof of Proposition VII.2.1, case `M = G`, printed pp. 317–318 (PDF pp. 83–84). With
  `ϕ(g) = ∫_{A_G} f_ψ(ag) χ_{ω'}(a⁻¹) da`, Waldspurger writes
  `ϕ(g) = ∫_{A_G} χ_{ω'}(a⁻¹) ∫_O (E^G_G ψ_ω)(g) χ_ω(a) dω da`, where `χ_π` is the restriction
  to `A_G` of the central character of `π`. "La restriction à `A_G ∩ K` de `χ_ω` ne dépend pas
  du point `ω ∈ O`. Si cette restriction est différente de celle de `χ_{ω'}`, on a `ϕ(g) = 0`.
  Supposons ces restrictions égales. Comme la fonction `ω ↦ (E^G_G ψ_ω)(g)` est continue, on
  peut appliquer la formule d'inversion de Fourier. Compte tenu des définitions de nos mesures,
  on obtient `ϕ(g) = ∑_{ω ∈ O ; χ_ω = χ_{ω'}} (E^G_G ψ_ω)(g)`."
- I.1, printed p. 239 (PDF p. 5): the measure on `Im X(G)` (restriction to `Im X(A_G)`, which
  carries total mass 1, preserves measures locally); printed p. 240 (PDF p. 6): every closed
  subgroup `H` gets the left Haar measure with `mes(H ∩ K) = 1`.

This module proves the two cases of that step for the actual rational points, with the orbit
replaced by `Im X(G)` as described below. The generic torus lemmas of the first section are
derived for the proof. The second section states the source step; the integrand is a derived
definition that writes Waldspurger's integrand in terms of a function on `Im X(G)`.

### Correspondence with the source

- `A_G` is the image `(GroupScheme.rationalPoints.map s).range` of the rational points of a
  central morphism `s : T → G` of group schemes (`hs : GroupScheme.IsCentral s`). It carries
  the subspace topology of `G(F)` and an arbitrary Borel measurable structure.
- For a point `ω₀` of `O`, `c = χ_{ω₀}` and `η = χ_{ω'}` are arbitrary homomorphisms
  `A_G → Circle`. For `χ ∈ Im X(G)` the twist `ω₀ ⊗ χ` has `χ_{ω₀ ⊗ χ}(a) = χ(a) c(a)`. The
  function `f : Im X(G) → ℂ` stands for `χ ↦ (E^G_G ψ_{ω₀ ⊗ χ})(g)` at a fixed `g`.
- The integral over `O` is replaced by the integral over `Im X(G)` against the I.1 measure
  `rationalUnitaryUnramifiedCharacterHaar s hs hindex`, and the sum over `ω ∈ O` by a sum over
  `χ ∈ Im X(G)`. The orbit is `O = Im X(G)/S` for the finite stabilizer `S` of `ω₀` (III.7). The
  passage from `Im X(G)` to `O`, with its factor `|S|`, is made in the module
  `RationalOrbitFourierInversion` submitted with this one.
- The measure `ν` on `A_G` is an arbitrary left invariant measure. Its value
  `ν(A_G ∩ G¹)` appears in the result; Waldspurger's normalization `mes(A_G ∩ K) = 1` is not
  imposed.
- Waldspurger splits the cases by the restriction to `A_G ∩ K`. This module splits by the
  restriction to `A_G ∩ G¹`. That restriction of `χ c` equals the restriction of `c` for every
  `χ ∈ Im X(G)`, because unitary unramified characters are trivial on `G¹`
  (`unitaryUnramifiedCharacter_apply_of_mem`). The two results below cover all cases. Equality
  of `A_G ∩ K` and `A_G ∩ G¹` is neither proved nor used.

## Scope and hypotheses

### Generic section (namespace `Langlands.HarmonicAnalysis.TorusFourier`)

`J` is a finite type and `J → Circle` the compact torus.

- `exists_torusCharacter_eq ψ`: `ψ : Multiplicative (J → ℤ) →* Circle` arbitrary.
- `exists_torusCharacter_eq_of_ker_le N ρ hker`: `H` an arbitrary group,
  `N : H →* Multiplicative (J → ℤ)`, `ρ : H →* Circle`, and `hker : N.ker ≤ ρ.ker`.
- `torusFourierCoeff_sum_mul_right mu K hf n`: `mu` a finite left invariant measure on the
  torus, `K` a finite subgroup of the torus (`Fintype K`, decidable `IsTrivialOn K`), `f`
  continuous (`hf`).
- `hasSum_torusFourierCoeff_mul_conj_lattice mu Λ hf hs z`: `mu` as above, `Λ` an additive
  subgroup of `ℤ^J` of finite index, `Fintype` on `latticeAnnihilator Λ`, `f` continuous
  (`hf`), and `hs`: the norms of the Fourier coefficients of `f` are summable **over `Λ`**.

### Rational section (namespace `Langlands.HarishChandraSchwartz`)

`F` is a nonarchimedean local field (`IsNonarchimedeanLocalField`), `G` an affine group scheme
over `F` locally of finite type (except where omitted below), and `G(F)` carries the canonical
`rationalPointTopology F G.X`. Connected reductivity `hG : GroupScheme.IsConnectedReductive G` is
an explicit argument exactly where listed below. `T` is an affine commutative group scheme over `F`,
`s : T → G` a morphism, `hs : GroupScheme.IsCentral s`, and
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex` (finite index of the image of
`T(F)` in the valuation image lattice of `G`; used for the I.1 measure and for `Λ_s`).

- `rationalValuationCoordinates_eq_zero_iff hG g`: `hG` only (no affineness or finite type).
- `unitaryUnramifiedCharacter_apply_of_mem χ hg`: `G` affine (not locally of finite type, not
  `hG`), `hg : g ∈ G¹`.
- `rationalSplitCenterInversionIntegrand s hs hindex c eta f a`: no further hypotheses.
- `integral_rationalSplitCenterInversionIntegrand_eq_zero s hs hindex ν c eta f h` (no `hG`): a
  measurable space with `BorelSpace` on `A_G`, `ν` left invariant (`ν.IsMulLeftInvariant`),
  and `h`: some `b ∈ A_G ∩ G¹` has `η(b) ≠ c(b)`. No integrability or continuity is assumed
  (a non-integrable integrand has integral `0` by convention).
- `integral_rationalSplitCenterInversionIntegrand hG s hs hindex ν c eta hf h hint`: the same
  measurable structure and `ν`; `hf : Continuous f` on `Im X(G)`; `h`: `η(b) = c(b)` for every
  `b ∈ A_G ∩ G¹`; `hint`: the integrand is `ν`-integrable on `A_G`.

## Definitions

- `rationalSplitCenterInversionIntegrand s hs hindex c eta f a`
  `= η(a⁻¹) ∫_{Im X(G)} f(χ) χ(a) c(a) dχ`, Waldspurger's
  `χ_{ω'}(a⁻¹) ∫_O (E^G_G ψ_ω)(g) χ_ω(a) dω` with `O` replaced by `Im X(G)` as above.

## Results

Generic:

- `exists_torusCharacter_eq`: every character `ψ` of `ℤ^J` is `k ↦ χ_k(z)` for the point
  `z = (ψ(e_j))_j` of the torus.
- `exists_torusCharacter_eq_of_ker_le`: if `ker N ≤ ker ρ`, then `ρ(a) = χ_{N(a)}(z)` for some
  torus point `z`.
- `torusFourierCoeff_sum_mul_right`: the Fourier coefficients of `x ↦ ∑_{w ∈ K} f(x w)` are
  `|K| f̂(n)` if `χ_n` is trivial on `K` and `0` otherwise.
- `hasSum_torusFourierCoeff_mul_conj_lattice`: if `∑_{m ∈ Λ} |f̂(m)| < ∞`, then
  `∑_{m ∈ Λ} f̂(m) conj(χ_m(z)) = mu(T) |Λ^⊥|⁻¹ ∑_{w ∈ Λ^⊥} f(z w)`, with `Λ^⊥ =
  latticeAnnihilator Λ`. `hasSum_torusFourierCoeff_mul_conj_mem` (`TorusLatticeDuality`) has the
  same conclusion under summability over all of `ℤ^J`; here summability is needed only on `Λ`,
  which is what integrability over `A_G` provides.

Rational:

- `rationalValuationCoordinates_eq_zero_iff`: `n(g) = 0` if and only if `g ∈ G¹`.
- `unitaryUnramifiedCharacter_apply_of_mem`: every `χ ∈ Im X(G)` takes the value `1` on `G¹`.
- `integral_rationalSplitCenterInversionIntegrand_eq_zero` (**different restrictions**): if
  `η ≠ c` at some point of `A_G ∩ G¹`, then `∫_{A_G} η(a⁻¹) ∫ f(χ) χ(a) c(a) dχ dν(a) = 0`.
- `integral_rationalSplitCenterInversionIntegrand` (**equal restrictions**):
  `∫_{A_G} η(a⁻¹) ∫ f(χ) χ(a) c(a) dχ dν(a) = ν(A_G ∩ G¹) ∑ᶠ_{χ ∈ Im X(G) ; χ c = η on A_G} f(χ)`.
  Here `ν(A_G ∩ G¹)` is `(ν (Subtype.val ⁻¹' G¹)).toReal`, and the index set is a coset of the
  finite kernel of the restriction `Im X(G) → Im X(T)` (shown in the proof), so the sum is
  finite.

## Proof notes

Generic:

1. `exists_torusCharacter_eq`: write `k = ∑_j k_j e_j` and use multiplicativity of `ψ` and of
   `Circle → ℂ`.
2. `exists_torusCharacter_eq_of_ker_le`: `ρ` induces a character of `N(H) ≅ H / ker N`
   (`QuotientGroup.quotientKerEquivRange`, `QuotientGroup.lift`); it extends to `ℤ^J`
   (`exists_circle_character_extension`), and step 1 applies.
3. `torusFourierCoeff_sum_mul_right`: exchange the finite sum and the integral, use
   `integral_mul_right_mul_torusCharacter` (translation by `w` multiplies the coefficient by
   `conj χ_n(w)`), then `sum_torusCharacter_subgroup` (the character sum over `K` is `|K|` or `0`).
4. `hasSum_torusFourierCoeff_mul_conj_lattice`: by step 3 and the double annihilator
   `isTrivialOn_latticeAnnihilator_iff`, the coefficients of `F = ∑_{w ∈ Λ^⊥} f(· w)` are
   `|Λ^⊥| f̂` on `Λ` and `0` off `Λ`, so they are absolutely summable on `ℤ^J`. Fourier inversion
   `hasSum_torusFourierCoeff_mul_conj` for `F` at `z`, restricted to `Λ`
   (`hasSum_subtype_iff_indicator`) and divided by `|Λ^⊥|`, gives the claim.

Rational:

5. `rationalValuationCoordinates_eq_zero_iff`: the coordinate map is an isomorphism and the
   kernel of the valuation projection is `G¹` (`rationalValuationImageProjection_ker`).
   `unitaryUnramifiedCharacter_apply_of_mem`: `Im X(G)` consists of characters in
   `unramifiedCharacters`, which by definition contain `G¹ = rationalCommonNormKernel G` in
   their kernel.
6. Vanishing: for `b ∈ A_G ∩ G¹`, `χ(b) = 1` for every `χ ∈ Im X(G)`, so the integrand `I`
   satisfies `I(b a) = η(b)⁻¹ c(b) I(a)`. Left invariance of `ν`
   (`integral_mul_left_eq_self`) gives `∫ I = η(b)⁻¹ c(b) ∫ I`, and `η(b)⁻¹ c(b) ≠ 1`.
7. Equal restrictions. Let `K` be the circle coordinates of `Im X(G)`,
   `mu = K_*(rationalUnitaryUnramifiedCharacterHaar s hs hindex)` (a finite Haar measure on the
   torus) and `F_z = f ∘ K⁻¹`. The map `N(a) = n(a)` on `A_G` has kernel `A_G ∩ G¹` (step 5),
   and `η c⁻¹` is trivial there by `h`; step 2 gives `z'` with `η(a) c(a)⁻¹ = χ_{n(a)}(z')`.
   By the character formula, `∫ f(χ) χ(a) dχ = F̂_z(n(a))`, so the integrand is
   `Φ(n(a)) = F̂_z(n(a)) conj(χ_{n(a)}(z'))`. It is right invariant under the open subgroup
   `A_G ∩ G¹` (`isOpen_rationalCommonNormKernel`); `A_G / (A_G ∩ G¹)` is countable and, via `n`,
   in bijection with `Λ_s` (`mem_rationalSplitLattice`). `hasSum_integral_quotient` gives
   `∫ I dν = ∑_{m ∈ Λ_s} ν(A_G ∩ G¹) Φ(m)`. If `ν(A_G ∩ G¹) = 0` both sides vanish. Otherwise
   the same formula for `|I|` (integrable by `hint`) gives summability of `|F̂_z|` on `Λ_s`,
   and step 4 gives `∑_{m ∈ Λ_s} Φ(m) = mu(T) |Λ_s^⊥|⁻¹ ∑_{w ∈ Λ_s^⊥} F_z(z' w)`.
   `rationalUnitaryUnramifiedCharacterHaar_univ` and `coordinates_symm_mem_restrict_ker_iff`
   give `mu(T) = |ker(Im X(G) → Im X(T))| = |Λ_s^⊥|`, so the factor is `1`. Finally the index
   set `{χ ; χ c = η on A_G}` is `K⁻¹(z' Λ_s^⊥)` (the characters with `χ_{n(a)}(K χ) =
   η(a) c(a)⁻¹` for all `a`), and `finsum_mem_range` turns the sum over `Λ_s^⊥` into the finite
   sum over this set.

## Relation to the Library

`CentralFourierInversion` treats Fourier inversion over a central subgroup abstractly (coset
sums, vanishing of all central projections); this module applies its
`hasSum_integral_quotient` to `A_G` with the open subgroup `A_G ∩ G¹`. `TorusFourierInversion`
and `TorusLatticeDuality` supply the torus inversion and the lattice annihilators.
`RationalCharacterHaar` supplies the I.1 measure on `Im X(G)`. No other Library declaration
states Fourier inversion over `A_G` for functions on `Im X(G)`. `RationalOrbitFourierInversion`
(submitted with this module) transfers the results to a discrete-series orbit.

## Open obligations

For Proposition VII.2.1, case `M = G` (beyond the orbit version in
`RationalOrbitFourierInversion`): the normalization `mes(A_G ∩ K) = 1` and
its relation to `ν(A_G ∩ G¹)`, the integrability and continuity of `χ ↦ (E^G_G ψ_{ω₀ ⊗ χ})(g)`
for `ψ ∈ C^∞(O)`, and the remaining steps (formulas analogous to III.1 (2), (3) and Lemma
VII.1.1 (ii)).
