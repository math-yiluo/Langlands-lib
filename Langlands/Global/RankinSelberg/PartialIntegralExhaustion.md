# Exhausting `N_m(𝔸) \ GL_m(𝔸)` by the partial integration domains

Module `Langlands.Global.RankinSelberg.PartialIntegralExhaustion`, namespace
`Langlands.Global.RankinSelbergGlobal`.

## Content

Let `F` be a number field and `n` a natural number. Write `WhittakerQuotient F n` for the left
coset space `N_n(𝔸) \ GL_n(𝔸)`. For a finite place `v`, `finiteComponent F n v g` is the
component `g_v ∈ GL_n(F_v)` of an adelic point `g`. `IsUnipotentIntegral F n v x` says that
`x ∈ N_n(F_v) GL_n(𝒪_v)`. `unipotentIntegralOutside F n S` is the set of adelic points `g` with
`g_v ∈ N_n(F_v) GL_n(𝒪_v)` at every finite place `v ∉ S`. All of these are Library definitions
(module `Langlands.Global.RankinSelberg.PartialWhittakerIntegrals`).

- `unipotentIntegralClasses F n S : Set (WhittakerQuotient F n)` (entry definition) is the set
  of classes `q` whose chosen representative `q.out` lies in `unipotentIntegralOutside F n S`.
  It is the integration domain of the Library's partial integrals:
  `partialUnequalWhittakerIntegral_eq_setIntegral`,
  `partialDualWhittakerIntegral_eq_setIntegral` and
  `partialEqualWhittakerIntegral_eq_setIntegral` rewrite `partialUnequalWhittakerIntegral`,
  `partialDualWhittakerIntegral` and `partialEqualWhittakerIntegral` as set integrals over
  `unipotentIntegralClasses F m S` with `m = t + 1` (resp. `r + 1`). All three hold by `rfl`.
- Monotonicity: `unipotentIntegralOutside_mono` and `unipotentIntegralClasses_mono`. If
  `S ⊆ S'` then the set for `S` is contained in the set for `S'`.
- Independence of the representative: `mul_mem_unipotentIntegralOutside` says that
  `u ∈ N_n(𝔸)` and `g ∈ unipotentIntegralOutside F n S` imply `u g ∈ unipotentIntegralOutside F n S`.
  Hence `mk_mem_unipotentIntegralClasses_iff`: the class of `g` lies in
  `unipotentIntegralClasses F n S` iff `g ∈ unipotentIntegralOutside F n S`, for every `g`, not
  only for the chosen representative. Equivalently (`preimage_mk_unipotentIntegralClasses`), the
  preimage of the set under the quotient map is `unipotentIntegralOutside F n S`.
- Topology: `isClosed_unipotentIntegralOutside` and `isClosed_unipotentIntegralClasses` say both
  sets are closed. Consequently `measurableSet_unipotentIntegralClasses` holds for the Borel
  σ-algebra of the quotient.
- Exhaustion: by `exists_mem_unipotentIntegralOutside`, every adelic point lies in
  `unipotentIntegralOutside F n A` for some finite set `A`. By `iUnion_unipotentIntegralClasses`,
  the union of the sets `unipotentIntegralClasses F n A` over all finite `A` is the whole quotient.
- **Main theorem** `integral_eq_hasProd_mul_setIntegral`. Take any measure `ν` on
  `WhittakerQuotient F n`, a `ν`-integrable `f : WhittakerQuotient F n → ℂ`, a finite set `S` of
  finite places, a family `c : {v // v ∉ S} → ℂ` with `HasProd c p` (an unconditional product
  over the finite places outside `S`), and the step hypothesis `hstep`: for every finite
  `A ⊇ S` and every `v ∉ A` (with `v ∉ S`),

  `∫_(unipotentIntegralClasses F n (A ∪ {v})) f dν = c_v · ∫_(unipotentIntegralClasses F n A) f dν`.

  Then `∫ f dν = p · ∫_(unipotentIntegralClasses F n S) f dν`. In `hstep`, `A ∪ {v}` is written
  `Finset.cons v A hv`, so no decidable equality on places is needed.

Some local lemmas are also stated: `finiteComponent_mul` (`g ↦ g_v` is multiplicative),
`continuous_finiteComponent`, and `finiteComponent_apply` (matrix entries of `g_v`).
`isUnitriangular_finiteComponent` says the local components of a point of `N_n(𝔸)` are upper
unitriangular. `localUnitriangular F n v` is the set of upper unitriangular elements of
`GL_n(F_v)`, closed by `isClosed_localUnitriangular`. `isUnipotentIntegral_iff` identifies
`{x | IsUnipotentIntegral F n v x}` with the product set `N_n(F_v) · GL_n(𝒪_v)`, and
`isClosed_setOf_isUnipotentIntegral` says this set is closed.

## Provenance

This is internal supporting material for the proof of `UnequalEulerFactorizationStatement`
(Cogdell, "Analytic theory of L-functions for GL_n", in Bernstein–Gelbart (2004), §2.2,
p.206, with Theorem 3.3, p.215). The same material serves the dual and equal-rank
factorizations (`UnequalDualEulerFactorizationStatement`, `EqualEulerFactorizationStatement`). Cogdell computes the global integral by factoring the
integrand over the places and integrating place by place. The Library's targets state the
factorization with partial integrals over the domains `unipotentIntegralClasses F m S`. This
module supplies the measure-theoretic passage from those partial integrals to the full integral:
the domains exhaust the quotient as `S` grows. With the one-place step identity `hstep`, the full
integral is then the partial integral times the Euler product. The step identity itself is not
proved here. The definitions `unipotentIntegralClasses` and `localUnitriangular` add no new
construction: they name the integration domain already used by the Library's partial integrals,
and the set of upper unitriangular local matrices.

## Proof

- `isUnipotentIntegral_iff`. If `x k` is upper unitriangular with `k ∈ GL_n(𝒪_v)`, then
  `x = (x k) · k⁻¹`. Conversely, from `x = y k` with `y` unitriangular, the element `k⁻¹` works.
- `isClosed_setOf_isUnipotentIntegral`. The unitriangular set is closed: it is an intersection
  of entry conditions `x_ij = 0` (`j < i`) and `x_ii = 1`, each closed since the entries are
  continuous on `GL_n(F_v)`. `GL_n(𝒪_v)` is compact (`FiniteAdelicGL.isCompact_localIntegral`),
  and in a topological group, a closed set times a compact set is closed
  (`IsClosed.mul_right_of_isCompact`).
- `isClosed_unipotentIntegralOutside`. It is the intersection over `v ∉ S` of preimages of these
  closed sets under the continuous maps `g ↦ g_v`. `isClosed_unipotentIntegralClasses` follows
  from `preimage_mk_unipotentIntegralClasses` because the quotient map
  `LeftCosetSpace.mk` is a quotient map (`LeftCosetSpace.isQuotientMap_mk`).
- `mul_mem_unipotentIntegralOutside`. If `g_v k` is unitriangular, then
  `(u g)_v k = u_v (g_v k)` is a product of two unitriangular matrices. The components `u_v` of
  `u ∈ N_n(𝔸)` are unitriangular by `Unfolding.mem_unipotentAdelic_iff`.
  `mk_mem_unipotentIntegralClasses_iff` applies this to `u = g · q.out⁻¹` and its inverse, which
  lie in `N_n(𝔸)` since `q.out` and `g` have the same class.
- `exists_mem_unipotentIntegralOutside`. By `FiniteAdelicGL.eventually_localIntegral`,
  `g_v ∈ GL_n(𝒪_v)` for all but finitely many `v`. At those places take `k = g_v⁻¹`, so that
  `g_v k = 1`. Let `A` be the finite exceptional set.
- `integral_eq_hasProd_mul_setIntegral`. Index by finite sets `B` of places outside `S` and put
  `s_B = unipotentIntegralClasses F n (S ∪ B)`. Induction on `B` with `hstep` gives
  `∫_(s_B) f dν = (∏_(v ∈ B) c_v) · ∫_(s_∅) f dν`. The sets `s_B` are measurable, increase with
  `B`, and their union is the whole quotient: a class whose representative lies in
  `unipotentIntegralOutside F n A` lies in `s_B` for `B = A \ S`. Since `f` is integrable and
  `Finset`s directed by inclusion form a countably generated filter (finite places are
  countable), `tendsto_setIntegral_of_monotone` gives `∫_(s_B) f dν → ∫ f dν` along `atTop`.
  By `HasProd c p`, the finite partial products tend to `p` along the same filter, so
  `∫_(s_B) f dν → p · ∫_(s_∅) f dν`. Uniqueness of limits (`tendsto_nhds_unique`) gives the
  identity.
