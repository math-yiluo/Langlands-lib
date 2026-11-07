# Weyl normalization over a reduced local ring from the field case

Module `Langlands.GroupScheme.Reductive.LocalWeylNormalizationProof`.

Main result: `Langlands.GroupScheme.localWeylNormalization_of_field`,

```
theorem localWeylNormalization_of_field (hF : FieldWeylNormalizationStatement.{u}) :
    LocalWeylNormalizationStatement.{u}
```

Both statements are defined in `Langlands.GroupScheme.Reductive.LocalWeylNormalizationStatement`.
`LocalWeylNormalizationStatement` works over a reduced local ring `R`. Take a reductive `G`
with a closed coordinate split torus `i`, maximal on every residue fibre, a fibrewise root
datum `P`, a base `b`, a simple root `a ∈ b.support`, and a root parametrization `u` of the
root `a`. It asks for a root parametrization `v` of `-a = P.reflectionPerm a a` such that the
Weyl point `v(-1) u(1) v(-1)` (`weylPoint u v`) acts on the torus through the simple
reflection `s_a` (`IsWeylPoint`). `FieldWeylNormalizationStatement` gives, for given `u` and
`v` and every field `k` over `R`, a nonzero `d ∈ k` with two properties. First, the base
changes `u_k` and `v'_k := v_k(d ·)` satisfy the rank-one relation
`u(X) v'(Y) = v'(Y/w) a^∨(w) u(X/w)`, `w = 1 + XY` (`RootCell.RelationOver`). Second,
`v'_k(-1) u_k(1) v'_k(-1)` acts on the torus through `s_a`.

This is the ring-level half of the Weyl normalization step used for the Isomorphism Theorem
over a reduced local ring (Conrad, *Reductive group schemes*, Thm. 6.1.17, specialized to
reduced local bases). Its counterpart in the literature is Conrad, Cor. 5.1.9(1)
(pp. 140-141): `w_a(X) = exp_a(X) exp_{-a}(-X⁻¹) exp_a(X)` normalizes `T` and induces the
reflection `s_a`. Conrad gets the dual section `X⁻¹` from the Lie algebra pairing. The route
here, through dual numbers and field points, is internal to this project and not taken from
the literature. It uses that `R` is reduced, which the target
`LocalSplitReducedIsomorphismTheoremStatement` assumes.

## The proof of `localWeylNormalization_of_field`

1. **Choices.** `a` is positive for `b` (`RootPairing.Base.isPos_of_mem_support`), and `-a`
   is not, because its height is `-height a`. Hence `-a ≠ a`. Choose root parametrizations
   of all roots with `LocalRootGroup.exists_rootParametrization` and replace the one at `a`
   by `u`. The family `fam` then has `fam a = u` and `fam (-a) = v`, where `v` is the chosen
   parametrization of `-a`. Enumerate the negative and the positive roots. By
   `localSplitBigCell` the big-cell map `cellMap i fam neg pos` is an open immersion.
2. **The point `u(1) v(ε)` over `R[ε]`.** `exists_dualCellLift` writes it as `y ≫ cellMap`
   for a point `y` of the cell source over `Spec R[ε]`. Let `X ∈ R[ε]` be the `u`-coordinate
   of `y`, read through `Γ(Spec R[ε]) ≅ R[ε]`, and put `c := -snd X`, minus its
   `ε`-coefficient.
3. **Fields.** Let `k` be a field over `R` and let `d` be as in the field statement.
   `algebraMap_snd_posCoord` shows that the image of `snd X` in `k` is `-d⁻¹`. So the image
   of `c` is `d⁻¹`.
4. **`c` is a unit.** Apply step 3 with `k` the residue field. The image of `c` is nonzero,
   so `c` is a unit of the local ring `R`.
5. **The answer** is `v' := scaleHom c⁻¹ ≫ v`, which is `v(c⁻¹ ·)`. It is a root
   parametrization of `-a` by `IsRootParametrization.scale`. Its base change to `k` is
   `scaleHom d ≫ v_k` (`baseChangeRoot_scaleHom`, and the image of `c⁻¹` is `d`). So the
   field statement gives the Weyl-point property over every field `k`.
   `isWeylPoint_of_baseChange` then gives it over `R`.

## Auxiliary results

### Big-cell points (`section Cell`, any commutative ring)

- `list_prod_ofFn_eq`: a product `∏ₖ f k` over `Fin r`, in a monoid, whose factors are `1`
  except at `k₀` equals `f k₀`.
- `orderedProduct_single`: an ordered product of root values whose coordinates vanish except
  at one index is that root value.
- `cellPoint_single`: the big-cell formula with one nonzero negative and one nonzero positive
  coordinate is `u_{neg kn}(y) · i(t) · u_{pos kp}(x)`.
- `posCoord_eq_of_cellPoint_eq`: if the big-cell map is a monomorphism, equal cell points
  have equal positive coordinates. The proof uses `coordTriple_bijective` and cancels the
  monomorphism.

### Weyl points from field points (`section WeylFields`)

- `isWeylPoint_apply_of_baseChange`: let `K` be a field over `R`. If the Weyl point of the
  base-changed root maps `baseChangeRoot K u`, `baseChangeRoot K v` acts through `f` on the
  base-changed torus, then the Weyl point of `u, v` satisfies `n t n⁻¹ = f(t)` on every test
  scheme over `Spec K`, regarded over `Spec R`. This reverses the computation of the
  Library's `IsWeylPoint.baseChange`, using `baseChangePointsEquiv`.
- `isWeylPoint_of_baseChange`: over a reduced ring, if this holds after base change to every
  field, then `IsWeylPoint i (weylPoint u v) f` holds. The identity is an equality of two
  morphisms `T ⟶ G` from the split torus. `T` is smooth over the reduced ring `R`, hence
  reduced, and `G` is affine, hence separated. So it suffices to check field-valued points
  (`LocalRootGroup.ext_of_fieldPoints`), and these come from the previous lemma.

### Spectra and open immersions

- `specMap_appTop_inv` and `ΓSpecIso_hom_specMap_appTop`: naturality of `Γ(Spec A) ≅ A`,
  evaluated at elements.
- `exists_lift_of_surjective`: a point `g` of `Y` over `S` factors through an open immersion
  `j : X ⟶ Y` if `s ≫ g` factors through `j` for some morphism `s` that is surjective on
  points. The topological image of `g` lies in that of `j`, and `IsOpenImmersion.lift`
  applies.

### Dual numbers (`section Dual`)

- `dualOver R` is `Spec R[ε]` over `Spec R`, and `epsSec R` is the global function `ε`.
- `dualZero R : Spec R ⟶ Spec R[ε]` is given by `ε ↦ 0`. `surjective_dualZero`: it is
  surjective on points, by `PrimeSpectrum.isHomeomorph_comap`, since the kernel `εR` is
  nilpotent. `dualZero_appTop_epsSec`: it pulls `ε` back to `0`.
- `exists_dualCellLift`: if the big-cell map is an open immersion, then the point
  `u_{pos kp}(1) · u_{neg kn}(ε)` over `R[ε]` factors through it. Its pullback along `dualZero`
  is `u_{pos kp}(1)`, the cell point with coordinates `(0, 1, e_{kp})`, and
  `exists_lift_of_surjective` applies.

### The field computation (`section FieldCoord`)

- `dualMap k : R[ε] →ₐ[R] k[ε]` sends `r + sε` to `r + sε`. `dualMap_eps` and
  `snd_dualMap` compute it.
- `dualUnit k c` is the unit `1 + cε` of `k[ε]`, with inverse `1 - cε`.
- `testOverHom_appTop`, `testOverHom_rootPoint`, `testOverHom_torus`: a point of the base
  change `G_k` over `Spec D` (for a `k`-algebra `D`) gives a point of `G` over `Spec D`
  regarded over `Spec R`. These lemmas say that this transport sends root values of
  `baseChangeRoot k w` to root values of `w` with the same coordinate, and torus values to
  torus values. They use `testOverHom` from `Dynamic.RingPointCoordinates`.
- `baseScalar_testOver`, `dualMap_appTop_epsSec`: structure scalars of `Spec D` over `k`,
  and the pullback of `ε` along `Spec k[ε] ⟶ Spec R[ε]`.
- `algebraMap_snd_posCoord`: assume `u(1) v(ε) = y ≫ cellMap` over `R[ε]`, with
  `u = fam (pos kp)` and `v = fam (neg kn)`, and the cell map a monomorphism. Assume also that
  over `k`, `u_k` and `v_k(d ·)` satisfy the rank-one relation on `Spec k[ε]`. Then the image
  in `k` of the `ε`-coefficient of the `u`-coordinate of `y` is `-d⁻¹`. To see this, apply the
  relation with `X = 1` and `Y = ε/d`, so `w = 1 + ε/d`. It gives
  `u(1) v(ε) = v(ε/w) · a^∨(w) · u(1/w)` over `k[ε]`. Transported to `R`-points over
  `Spec k[ε]`, this is a second cell decomposition of the pullback of `u(1) v(ε)`, with
  `u`-coordinate `1/w = 1 - d⁻¹ε`. Uniqueness of cell coordinates
  (`posCoord_eq_of_cellPoint_eq`) compares it with the pullback of `y`.
