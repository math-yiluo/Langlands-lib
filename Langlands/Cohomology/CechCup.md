# Products of ordered Čech cochains of a presheaf of rings

Author: Worker 274.

This module defines the Alexander–Whitney products of ordered Čech cochains that are needed
to multiply degree-one Čech classes of a presheaf of commutative rings, and proves their
Leibniz rules. It is a helper for the proof of
`Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement`. It contains no `sorry`
and no new axioms.

## Provenance

The cochains are the ordered Čech cochains `Langlands.Cohomology.Cech.C` of the Library module
`Langlands.Cohomology.CechCochains`. The product is the cup product of Čech cochains in The
Stacks Project, Cohomology of Sheaves, section "Čech cohomology of complexes" (tag 01FP), `cohomology.tex` lines
5240–5300 of the registered source `stacks-flasque-affine-vanishing-kunneth-a04446e5` (Stacks
commit `a04446e5`): `(α ∪ β)_{i₀…i_p} = α_{i₀…i_r} ⊗ β_{i_r…i_p}` with `r = deg α`. For sheaves
placed in degree `0` this formula has no signs. Here the coefficients are a presheaf of
commutative rings and `⊗` is multiplication of sections. Only products with a factor of degree
`0` or `1` are formalized, which is all the proof needs. Their exact form and names are a
project choice.

## Definitions

All declarations are in namespace `Langlands.Cohomology.Cech`. Throughout, `T : TopCat.{u}`,
`ι : Type w` and `U : ι → Opens T`.

- `face x τ θ`, for a family `x : ∀ σ : Fin m → ι, P.obj (op (inter U σ))`, a tuple
  `τ : Fin n → ι` and `θ : Fin m → Fin n`, is the restriction of `x (τ ∘ θ)` to `inter U τ`.
- `ab R`, for `R : TopCat.Presheaf CommRingCat T`, is the underlying presheaf of abelian groups.
  Each `(ab R).obj (op V)` gets the commutative ring structure of `R.obj (op V)`.
- `edge k : Fin 2 → Fin (n + 1)` is the edge `(k, k + 1)` of the standard `n`-simplex.
- `one R U : C (ab R) U 0` is the unit cochain `fun _ => 1`.
- `cup₀ R U h b` multiplies a `0`-cochain `h` with a `q`-cochain `b`:
  `(cup₀ h b) τ = h (τ 0) * b τ`, restricted to `inter U τ`.
- `cup₁ R U z b` multiplies a `1`-cochain `z` with a `q`-cochain `b`:
  `(cup₁ z b) τ = z (τ 0, τ 1) * b (τ 1, …, τ (q + 1))`.
- `prod R U n z` multiplies `n` one-cochains `z : Fin n → C (ab R) U 1`:
  `(prod n z) τ = ∏ₖ z k (τ k, τ (k + 1))`.

## Results

- Face calculus: `res_face`, `face_congr`, `face_id`, `face_add`, `face_sub`, `face_neg`,
  `face_zero`, `face_zsmul`, `face_sum`, `face_mul`, `face_prod`, `face_one`, `face_one'`;
  `d_apply_face` and `face_d` write the differential as an alternating sum of faces.
- `cocycle_apply_const`: a `1`-cocycle vanishes on constant pairs `(i, i)`.
- `inter_two`: `inter U ![a, b] = U a ⊓ U b`.
- `cocycle_add`: the cocycle identity `z (x, y) + z (y, w) = z (x, w)` of a `1`-cocycle on any
  open contained in the three pairwise intersections.
- `res_mul`, `res_one`, `res_prod`: restriction is a ring map.
- `prod_zero`, `prod_one`, `prod_succ`: `prod 0 z = one`, `prod 1 z = z 0` and `prod (n + 1) z = cup₁ (z 0) (prod n (Fin.tail z))`.
- Biadditivity: `cup₁_add_left`, `cup₁_sub_left`, `cup₁_add_right`, `cup₁_sub_right`,
  `cup₁_neg_right`, `cup₁_zero_right`, `cup₀_zero_right`, `cup₀_sub_left`.
- `d_one`: `d (one R U) = 0`.
- `d_cup₀`: `d (cup₀ h b) = cup₁ (d h) b + cup₀ h (d b)`.
- `d_cup₁_of_cocycle`: for a `1`-cocycle `z`, `d (cup₁ z b) = -cup₁ z (d b)`.
- `prod_cocycle`: a product of `1`-cocycles is a cocycle.
- `prod_sub_eq_d`: if `z' k - z k = d (h k)` for `1`-cocycles `z k`, `z' k`, then
  `prod (n + 1) z' - prod (n + 1) z` is a coboundary.
