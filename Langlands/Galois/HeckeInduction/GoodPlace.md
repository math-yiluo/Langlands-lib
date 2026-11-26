# The induced representation at a base place where everything is unramified

Module `Langlands.Galois.HeckeInduction.GoodPlace`, name space
`Langlands.GaloisRepresentation.HeckeInduction`. Let `E/K` be an extension of number fields,
`e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E` a closure embedding, `C` a topological field
(a topological ring) and `ψ : Gal(Ē/E) →ₜ* Cˣ` a continuous character. The notation is that of
`LocalCosets`.

## Objects

- `imageSubgroup e` is the image of `restrictionAlongClosure e`, with its finite-index instance;
  `descended e ψ` is `descendedCharacter e ψ` on it (`descended_apply`).
- `inducedObject e ψ : Objects K C` is `InducedCharacter.induced (imageSubgroup e) (descended e ψ)`
  with its continuity, from `continuous_induced`, `isOpen_range_restrictionAlongClosure` and
  `continuous_descendedCharacter`. The carrier is the space of equivariant functions, in the
  universe `max uK uC`. `inducedObject_rank`: its rank is `[E : K]`.

## The good place

Let `v` be a finite place of `K` such that every place `w` of `E` above `v` has ramification
index `1`, and the induced place of the normal closure of `E` at `v` is unramified over `K`. Let
`γ` be a geometric Frobenius lift at `v` and `σ = r_v γ`.

- `conj_inertia`, `conj_inertia_of_mem`: for every `y` in the right coset of
  `placeConj e v w * σ ^ k` and `i` in local inertia at `v`, the conjugate `y * r_v i * y⁻¹` lies
  in the image subgroup and is killed by `descended e ψ`, provided `ψ` is unramified at `w`. The
  element `γ ^ k * i * γ⁻ᵏ` is in local inertia, hence equals `ρ a` with `a` in inertia at `w`
  (`inertia_mem_range`, `inertia_fixes_conjugates`, `map_mem_inertia_iff`), and
  `conj_placeConj_map` turns the conjugate into a conjugate of `restrictionAlongClosure e (r_w a)`,
  on which `descended e ψ` is `ψ (r_w a) = 1`.
- `descended_conj_frobenius`: if `ψ` takes the value `c` at every geometric Frobenius lift at `w`
  (through `r_w`), then `descended e ψ` takes the value `c` at
  `placeConj * σ ^ f(w|v) * placeConj⁻¹`. For a geometric Frobenius lift `a` at `w`, `ρ a` is
  `γ ^ f` times an element of local inertia (`residueAction_map_eq_pow`); `conj_placeConj_map`
  writes `restrictionAlongClosure e (r_w a)` as the product of the return element and a conjugate
  of an inertia element, killed by `conj_inertia`.
- `cycle_bijective`: `⟨w, k⟩ ↦ coset (placeConj e v w * σ ^ k)`, for the places `w` above `v`
  and `k < f(w|v)`, is a bijection onto the right cosets of the image subgroup. Injectivity: the
  coset prime of `placeConj e v w` is `w` (`cosetPrime_placeConj`) and is constant on the double
  cosets (`cosetPrime_eq_of_coset_eq`), so equal cosets have equal `w`; then
  `placeConj * σ ^ m * placeConj⁻¹ ∈ H` with `0 < m < f(w|v)` would put `γ ^ m` in the image of
  `ρ` (`conj_mem_iff_mem_range`), which `pow_not_mem_range` excludes. Surjectivity follows by
  counting: `∑_w f(w|v) = [E : K]` (`finitePlacesAbove_sum_ramification_inertia` with ramification
  indices `1`), which is the index of the image subgroup.
- `hasEulerPolynomialAt_inducedObject`: if moreover `ψ` is unramified at every `w` above `v`
  (through `r_w`) with value `c w` at every geometric Frobenius lift at `w`, then
  `HasEulerPolynomialAt (inducedObject e ψ) v (∏ w, (1 - C (c w) * X ^ f(w|v)))`.
  Unramifiedness: every element of `Gal(K̄/K)` lies in one of the cosets of `cycle_bijective`,
  so `conj_inertia_of_mem` and `InducedCharacter.induced_eq_one` show that `r_v i` acts
  trivially. Euler polynomial: `eulerPolynomial_eq_det` in the coset basis and
  `InducedCharacter.det_one_sub_X_smul_induced`, with the cycles of `cycle_bijective`, the return
  elements in the image subgroup by `pow_inertiaDeg_mem_range` and `conj_mem_iff_mem_range`, and
  their values from `descended_conj_frobenius`. The geometric Frobenius lift used is the
  chosen `γ`; `HasEulerPolynomialAt` asks for one lift.

## Provenance

This is a derived, internal module. It formalizes the classical computation of the unramified
local factor of an induced representation: geometric Frobenius at `v` permutes the coset
coordinates in one cycle of length `f(w|v)` for each place `w` above `v`, and the return map on
that cycle is geometric Frobenius at `w`, evaluated by the inducing character. The implemented
proofs are those described above.
