# The abstract core of the Bernstein–Gelfand chase

Module: `Langlands.Representation.Archimedean.BGChaseCore`, namespace
`Langlands.Archimedean.BGChase`. It formalizes the central step of Bernstein–Gelfand 1980, proof
of Theorem 5.9 in 5.10 (J. Bernstein, S. Gelfand, *Tensor products of finite and infinite
dimensional representations of semisimple Lie algebras*, Compositio Math. 41 (1980)), for
`𝔤𝔩_n(ℂ)` and lower Verma modules `M = M⁻(λ)` (Library module `LowerVerma`). Everything here is
proved. The six Bernstein–Gelfand inputs enter only through the hypotheses of `exists_h`.

The setting uses abstract types: `κ = kE` is a representation on `E`, `σ_F` a representation on
`F`, and `ι_F : F → E ⊗ U` a linear map intertwining `σ_F` with `κ ⊗ ad`. The hypothesis is
`hiF : ι_F(σ_F(Y)x) = (κ ⊗ ad)(Y)(ι_F x)`.

## The lower Verma module

- `smul_gen`: `u · gen` is the class of `u`;
- `unitU_smul_gen_of_lt`, `unitU_smul_gen_diag`: `E_pq · gen = 0` for `q < p`, and
  `E_pp · gen = λ_p gen`;
- `action_apply`, `evalBil`: the action and the bilinear pairing `(m, u) ↦ u · m`.

## Pairing `E ⊗ U` with `M`

- `cM m : E ⊗ U → E ⊗ M`, `e ⊗ u ↦ e ⊗ u·m` (written `c_m`), linear in `m`;
- `rmulE u`: right multiplication by `u` on the `U` factor, with `cM_rmulE`:
  `c_m(x · u) = c_{u·m}(x)`;
- `Tlie`: the representation `κ ⊗ M` on `E ⊗ M`; `cM_adP`:
  `c_m((κ ⊗ ad)(Y)x) + c_{Y·m}(x) = (κ ⊗ M)(Y)(c_m x)`;
- `theta m : E → E ⊗ M`, `e ↦ e ⊗ m`; `homLie_theta`: `Y · θ_m = θ_{Y·m}` in `Hom(E, E ⊗ M)`.

## The map `f : Hom(E, F) ⊗ M → Hom(E, E ⊗ M)`

- `fmap`: `f(ψ ⊗ m)(e) = c_m(ι_F(ψ e))`; `fmap_equivariant`: `f` is equivariant (from `hiF` and
  `cM_adP`);
- `Ispan`: the span of all `c_m(ι_F x)`. `Tlie_mem_Ispan`: it is `κ ⊗ M`-stable.
  `Ispan_eq_top`: if every `e ⊗ gen` is some `c_gen(ι_F x)`, it is everything (induction over
  `U`, since `M = U · gen`);
- `fmap_surjective`: then `f` is surjective (for `E` finite-dimensional, a map
  `E → E ⊗ M` is a sum of maps `e ↦ b_j^*(e) z_j`).

## The map `Θ`

For a representation `σ_A` on `A` and `t ∈ A ⊗ M`:

- `phiT`: `u ↦ Λ(u) t`, `Λ` the enveloping action of `σ_A ⊗ M`; `phiT_ker`: if `t` is killed by
  the strictly lower triangular matrix units and has weight `λ`, it vanishes on the ideal defining
  `M`;
- `Theta`: the induced map `Θ : M → A ⊗ M`, `u · gen ↦ Λ(u) t`, with `Theta_mk`, `Theta_smul` and
  `Theta_action` (equivariance);
- `gmap`: `α ↦ (α ⊗ 1) ∘ Θ`, a linear map `A* → End M`; `gmap_equivariant`: it is equivariant
  for the dual representation `homLie σ_A 0` on `A*` and the commutator action on `End M`.

## The element `h`

- `fmap_Theta`: if `f(t) = θ_gen`, then `f(Θ(m)) = θ_m` for all `m` (both sides are equivariant
  in `m` and agree on `gen`).
- `exists_h`: assume `LowerVermaWeightStatement`, `LowerVermaDufloStatement`,
  `KostantMultiplicityStatement`, `LowerVermaHomBoundStatement` and
  `LowerVermaProjectiveStatement`. Let `λ` be `Z`-extremal with central character `χ`, let `E` and
  `F` be finite-dimensional with integral weights, and suppose every `e ⊗ gen` is some
  `c_gen(ι_F x)`. Then for every `e ∈ E` there is `h` in the span of the `ι_F(x) · u` with
  `c_m(h) = e ⊗ m` for all `m ∈ M`.

  Proof of `exists_h`. Let `A = Hom(E, F)`; it has integral weights by `intSpan_homLie`. The
  vector `θ_gen ∈ Hom(E, E ⊗ M)` is killed by the strictly lower triangular units and has weight
  `λ`. Projectivity applied to the surjection `f` gives such a `t` with `f(t) = θ_gen`.
  `exists_lift` (module `BGChaseKS`) applied to `gmap` gives `g' : A* → U` with
  `g'(α) · m = (α ⊗ 1)(Θ m)`. For a basis `a_k` of `A`,
  `e ⊗ m = f(Θ m)(e) = Σ_k c_{g'(a_k^*)·m}(ι_F(a_k e))`, so
  `h = Σ_k ι_F(a_k e) · g'(a_k^*)` works.
