# Greenberg rings attached to Witt-vector coordinate data

## Setting and provenance

Let `k` be a perfect field of characteristic `p`. Let `A` be a commutative ring with a ring
map `ψ : W(k) →+* A`, and let `D : WittDecomposition p ψ` be cyclic Witt coordinates of `A`
(`GreenbergWitt.lean`): generators `e i`, exponents `m i`, and semilinear coordinates
`coord i : A → W_{m i}(k)`. For a `k`-algebra `T` this file builds a ring `GreenbergRing D T`.
Its underlying set is naturally `∏_i W_{m i}(T)`, and its value at `T = k` is `A`. It is the
coefficient ring of Greenberg's functor (Greenberg, *Schemata over local rings*, 1961;
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, §A.4).

The construction is not copied from either source. It is an internal presentation chosen
for Lean: the Greenberg ring is a quotient of the ordinary tensor product `A ⊗[ℤ] W(T)` by
the common kernel of explicit coordinate functionals. This avoids tensor products over
`W_m(k)`, which do not behave well for non-free `A`. The file uses
`set_option maxSynthPendingDepth 2`, which instance search needs for the quotient of a
tensor product.

## Auxiliary Witt-vector facts

- `truncate_out`, `coeff_truncMap`, `coeff_out_of_le`, `map_out`, `out_zero`: the canonical
  lift `y.out ∈ W(R)` of a truncated Witt vector, and its compatibility with `truncMap`.
- `eq_teichmuller_add_verschiebung`: `x = [x_0] + V (x.shift 1)`.
- `mul_eq_natCast_mul_of_charP`, `mul_eq_natCast_mul`: let `T` be a `k`-algebra and
  `x, y ∈ W(T)` with `x_0 y_0 = 0`, `x_0 ^ p = 0` and `y_0 ^ p = 0`. Then `x * y = p * z`
  for some `z`.

  Proof: expand `([x_0] + V x')([y_0] + V y')` using `V a · b = V (a · F b)`. The
  Teichmüller product vanishes. `F [a] = [a ^ p] = 0` kills the two mixed terms. Finally
  `V x' · V y' = V (x' · F V y') = V (x' y' p) = p · V (x' y')`.

## Coordinate data (`WittDecomposition.*`)

- `eq_zero_of_coord`: an element with all coordinates zero is zero.
- `psi_pow_mul_e`: `ψ (p ^ m i) * e i = 0`.
- `e_eq_zero_of_m_eq_zero`: generators of exponent `0` vanish.
- `mulLeft_semilinear`: composing a coordinate with multiplication by `b` stays
  semilinear.

## The coordinate functionals and balanced maps

- `semiExt T μ : A ⊗[ℤ] W(T) →+ W_j(T)`, for a `ψ`-semilinear `μ : A →+ W_j(k)`, is the map
  `a ⊗ w ↦ truncMap (algebraMap k T) (μ a) * truncate j w` (`semiExt_tmul`).
- `coordMap D T := (semiExt T (coord i))_i : A ⊗[ℤ] W(T) →+ ∏_i W_{m i}(T)`.
- `Balanced D T Λ`, for an additive `Λ` on `A ⊗[ℤ] W(T)`, has two fields:
  - `smul`: `Λ ((ψ c * a) ⊗ w) = Λ (a ⊗ (map c * w))`;
  - `vanish`: `Λ (e i ⊗ w) = 0` whenever `truncate (m i) w = 0`.
- `Balanced.eq_sum`, the key principle: a balanced `Λ` satisfies
  `Λ x = Σ_i Λ (e i ⊗ (coordMap x i).out)`. Hence it factors through `coordMap`
  (`eq_of_coordMap_eq`, `map_eq_zero`).

  Proof: induction on tensors. For `a ⊗ w`, expand `a = Σ ψ (c_i) e_i` with `c_i` the lifts
  of the coordinates of `a`, move `c_i` across with `smul`, and compare truncations with
  `vanish`. Sums are handled by `vanish` again.
- `semiExt_balanced`, `coordMap_balanced`. The `vanish` field is the vanishing lemma
  `truncate_mul_map_eq_zero` applied with `c = (μ (e i)).out`.
- `coordMap_tmul_mul`: `coordMap ((b ⊗ v) * x) l = truncate v * semiExt (coord l ∘ (b * ·)) x`.

## The Greenberg ring

- `kerIdeal D T`: the ideal `{x | coordMap D T x = 0}` (`mem_kerIdeal`). It is closed under
  multiplication by `coordMap_tmul_mul` and `Balanced.map_eq_zero`.
- `GreenbergRing D T := (A ⊗[ℤ] W(T)) ⧸ kerIdeal D T`, an `abbrev`. It is a commutative
  ring and an algebra over every ring `R₀` with `[Algebra R₀ A]`.
- `mk_eq_mk_iff`: two classes agree iff their coordinates agree.
- `coordRing`, `coordRing_mk`, `coordRing_zero`, `ext_coord`: the coordinates of an
  element, which determine it.
- `ofCoords`, `coordMap_sum_out`, `coordRing_ofCoords`: the element `Σ e i ⊗ (y i).out`
  with prescribed coordinates `y`.
- `coordEquiv D T : GreenbergRing D T ≃ ((ij : Σ i, Fin (m i)) → T)`: the natural
  coordinates, Witt components of the `coordRing` (`coordEquiv_apply`).
- `incL : A →+* GreenbergRing D T`, `incR : W(T) →+* GreenbergRing D T` (`incL_apply`,
  `incR_apply`), with `ofCoords_eq` and `eq_sum_incL_mul_incR`:
  `x = Σ_i incL (e i) * incR (coordRing x i).out`.

## Functoriality

- `preMap A R₀ f := id ⊗ map f : A ⊗[ℤ] W(T) →ₐ[R₀] A ⊗[ℤ] W(T')`, for `f : T →ₐ[k] T'`
  (`preMap_tmul`).
- `coordMap_preMap`: coordinates transform by `truncMap f`.
- `kerIdeal_le_comap`; `gmap D R₀ f : GreenbergRing D T →ₐ[R₀] GreenbergRing D T'`, the
  induced quotient map (`gmap_mk`).
- `coordRing_gmap`, `coordEquiv_gmap`: `gmap f` acts on the natural coordinates by
  applying `f` to each coordinate.
- `gmap_id`, `gmap_comp`: the functor laws, checked on coordinates.

## The Greenberg ring of `k`

- `theta ψ R₀ : A ⊗[ℤ] W(k) →ₐ[R₀] A`, `a ⊗ w ↦ a * ψ w` (`theta_tmul`).
- `coord_theta`: `coord l (theta s) = coordMap s l`.
- `ker_theta`: `ker theta = kerIdeal D k`. `theta_surjective`.
- `levelEquiv D R₀ : GreenbergRing D k ≃ₐ[R₀] A`.

## Reduction

Fix `r : A →+* k` with `hψr : ∀ c, r (ψ c) = c.coeff 0`.

- `preRed T r : A ⊗[ℤ] W(T) →+* T`, `a ⊗ w ↦ r(a) · w_0` (`preRed_tmul`). It is balanced
  (`preRed_balanced`).
- `red D T r hψr : GreenbergRing D T →+* T` (`red_mk`), with `red_incL`, `red_incR` and
  `red_algebraMap` (`algebraMap R₀ c ↦ algebraMap k T (r (algebraMap R₀ A c))`).
- `red_eq_sum`: `red x = Σ_{ij} algebraMap k T (if ij.2 = 0 then r (e ij.1) else 0) *
  coordEquiv x ij`. This is a fixed `k`-linear form in the coordinates, obtained from
  `Balanced.eq_sum`.
- `auxIdeal D T r := Ideal.map incL (ker r)`, with `auxIdeal_pow` (if `(ker r)^(N+1) = ⊥`
  then `auxIdeal^(N+1) = ⊥`), `natCast_mem_auxIdeal` (`p ∈ auxIdeal`) and
  `auxIdeal_le_ker_red`.
- `exists_sub_mem_auxIdeal`: every `x` is `incR W` modulo `auxIdeal`. For `a ⊗ w`, take
  `W = map [r a] · w`.
- `mul_mem_auxIdeal_of_red`: if `red x = red y = 0`, then `x * y ∈ auxIdeal`. Write
  `x ≡ incR W` and `y ≡ incR W'`. Then `W_0 = W'_0 = 0`, so `W W' = p z` by
  `mul_eq_natCast_mul`, and `p ∈ auxIdeal`.
- `isNilpotent_of_sq_le`: an ideal `K` with all products in `auxIdeal` satisfies
  `K ^ (2 (N + 1)) = ⊥`.
- `ker_red_pow`: if `(ker r)^(N+1) = ⊥` then `(ker red)^(2 (N + 1)) = ⊥`.

## Square-zero thickenings

- `mul_mem_auxIdeal_of_gmap`: let `f : T →ₐ[k] T'` have square-zero kernel (any two kernel
  elements multiply to `0`). If `gmap f x = gmap f y = 0`, then `x * y ∈ auxIdeal`. Expand
  `x` and `y` with `eq_sum_incL_mul_incR`. The constant coefficients of the lifts
  `(coordRing x i).out` lie in `ker f`, so `mul_eq_natCast_mul` applies to each product of
  lifts.
- `ker_gmap_pow`: under the same hypothesis and `(ker r)^(N+1) = ⊥`,
  `(ker (gmap f))^(2 (N + 1)) = ⊥`.
