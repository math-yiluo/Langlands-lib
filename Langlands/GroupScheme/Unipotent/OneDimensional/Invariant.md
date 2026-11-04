# A primitive coordinate outside the polynomials in a given primitive coordinate

Worker 716. Internal step of the proof of
`Langlands.GroupScheme.PerfectFieldOneDimensionalUnipotentStatement`. No
registered source was used. The argument is the one implemented in Lean and
combines the Library's unipotence machinery (`Unipotent.HopfFixed`) with the
cocycle lemma of `Cocycle`.

## Main result

`exists_primitive_not_mem_polys` works in the Library bialgebra structure
`bialgebra e` on the coordinate algebra `B` of a corepresented group. Assume:

- `k` is perfect;
- `B` and `B ⊗[k] B` are domains;
- `OneMemStable k B` holds (the Library's Hopf-algebraic form of unipotence);
- `y` is a nonzero primitive element with `B/(y)` finite-dimensional.

If some `b ∈ B` is not a polynomial in `y` (`b ∉ polys y`, where `polys y` is
the range of `aeval y`), then some primitive `t` is not a polynomial in `y`.

## Implemented argument

1. **An invariant vector modulo `k[y]`** (`exists_invariant_mod_polys`). Let
   `S = k[y]` and `Q = B/S`. The right translations `rightAct g`, for linear
   functionals `g`, preserve `S`: by `comul_aeval`, the comultiplication of a
   polynomial `f(y)` is `f(y ⊗ 1 + 1 ⊗ y)` with left factor in `S`. They
   therefore induce operators `T g` on `Q`. For each functional `θ` vanishing
   on `S`, the left translation `leftAct θ` vanishes on `S`
   (`leftAct_aeval_eq_zero`). It therefore induces `π θ : Q → B`, which
   intertwines `T g` with `rightAct g`, because left and right translations
   commute.

   These maps jointly separate points of `Q`. If `m = [b]` satisfies
   `π θ m = 0` for all `θ`, take any functional `ψ` on `Q` and set
   `θ = ψ ∘ mkQ`. Then `ε(leftAct θ b) = θ(b) = ψ(m)` (`counit_leftAct`), so
   `ψ(m) = 0` and hence `m = 0`.

   The image `W` in `Q` of the finite-dimensional `regularSpan {b}` is a
   nonzero `T`-stable subspace. The Library's `Unipotent.exists_invariant`
   (fixed vectors for `OneMemStable` bialgebras) gives a nonzero `w ∈ W` with
   `T g w = g(1) w` for all `g`. Lift `w` to `b'` and normalize to
   `a = b' - ε(b')·1`. Then `a ∉ S`, `ε(a) = 0`, and
   `rightAct g a - g(1) a ∈ S` for all `g`.
2. **A polynomial cocycle** (`exists_comul_eq_of_invariant`). Let `y` be
   transcendental, the comultiplication cocommutative, and `a` invariant
   modulo `S`. Choose a linear left inverse `ρ` of `aeval y` and put
   `P = aeval y ∘ ρ`, a projection onto `S`. Let
   `D = Δa - a ⊗ 1 - 1 ⊗ a`. Contracting the right factor with `g` gives
   `rightAct g a - g(1) a - g(a)·1 ∈ S`, so `(P ⊗ id) D = D` by the Library
   `tensor_ext`. Cocommutativity makes `D` symmetric, so also
   `(id ⊗ P) D = D`. Hence `D` lies in the image of `S ⊗ S`. Transport through
   `polyEquivTensor` gives `c : k[X][X]` with
   `Δa = a ⊗ 1 + 1 ⊗ a + c(y ⊗ 1, 1 ⊗ y)`. The last term is
   `tensorEval (aeval y) y c`.
3. **Properties of `c`**, from the point formula
   `a(u v) = a(u) + a(v) + c(y(u), y(v))` (`val_mul_apply_of_comul`):
   - *normalized* (`coeff_zero_eq_zero_of_comul`): take `u` universal, `v = 1`;
   - *symmetric* (`swap_eq_of_comul`): points commute when the
     comultiplication is cocommutative (`mul_comm_of_comm`). Compare the two
     tensor inclusions in `F(B ⊗ B)` and use injectivity of `tensorEval`;
   - *a two-cocycle* (`isCocycle_of_comul`): evaluate associativity of three
     points of `F((B ⊗ B) ⊗ B)` given by the three inclusions. The defect maps
     to zero under the injective map `E3 : k[X][Y][Z] → (B ⊗ B) ⊗ B`
     (`map_defect`, `tensorEval_injective` twice);
   - *vanishing obstruction in characteristic `p`*
     (`powerSum_eq_zero_of_comul`): the universal point satisfies
     `a(uⁿ) = n a + ∑_{i<n} c(i y, y)` (`val_univ_pow_apply_of_comul`). Its
     `p`-th power is trivial (`univ_pow_char` from `Hopf`), so
     `∑_{i<p} c(i y, y) = 0`, and injectivity of `aeval y` gives
     `powerSum p c = 0`.
4. **Conclusion.** Cocommutativity comes from `comm_comp_comul`, and
   transcendence of `y` from the Library `transcendental_of_augmentation_eq_zero`.
   In characteristic zero, `exists_eq_coboundary_of_charZero` applies. In
   characteristic `p`, `exists_eq_coboundary_of_charP` applies, using
   perfectness of `k`. Either way `c = coboundary f`. Then `t = a - f(y)` is
   primitive: its comultiplication is computed with `comul_aeval_eq` and
   `ev2_coboundary`. Moreover `t ∉ S`, since `a ∉ S` and `f(y) ∈ S`.
