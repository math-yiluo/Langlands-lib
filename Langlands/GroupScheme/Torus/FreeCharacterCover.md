# A free cover of a finitely generated abelian group, functorial in isomorphisms

For an additive commutative group `Λ` in universe `u`, this module defines a
free abelian group `F(Λ)` with a surjection `F(Λ) → Λ`. Every isomorphism
`Λ ≃+ Λ'` induces an isomorphism `F(Λ) ≃+ F(Λ')`, and this assignment
respects identities, composition and the projections. This functoriality is
what the torus embedding needs: the descent datum on the glued torus is
induced by the isomorphisms between character groups on overlaps.

Definitions (namespace `Langlands.GroupScheme.FreeCharacterCover`):

- `torsionOrder Λ` is the cardinality of the torsion subgroup
  `Submodule.torsion ℤ Λ` (`Nat.card`, hence `0` if it is infinite). Write
  `e` for it. `torsionOrder_smul_eq_zero`: `e • x = 0` for every torsion `x`.
  For finitely generated `Λ`, the torsion subgroup is finite (`finite_torsion`)
  and `e > 0` (`torsionOrder_pos`).
- `multiples Λ = eΛ`, and `Quot Λ = Λ / eΛ`. For finitely generated `Λ` this
  quotient is torsion and finite (`quot_isTorsion`, `quot_finite`).
- `sumMap Λ : ℤ[Λ/eΛ] → Λ/eΛ` is the ℤ-linear map sending the basis element
  of `q` to `q`, where `ℤ[Λ/eΛ]` is `Quot Λ →₀ ℤ`.
- `cover Λ` is the kernel of `(l, c) ↦ [l] − sumMap c` on
  `Λ × ℤ[Λ/eΛ]`, that is, the fibre product `Λ ×_{Λ/eΛ} ℤ[Λ/eΛ]`.
  `Cover Λ` is this subgroup as a type (`mem_cover` restates membership).
- `proj Λ : Cover Λ →+ Λ` is the first projection.

Properties:

- `proj_surjective`: `l` is the image of `(l, [l]·1)`.
- For finitely generated `Λ`, `Cover Λ` is a finite ℤ-module
  (`cover_finite`: it is a submodule of the finitely generated
  `Λ × ℤ[Λ/eΛ]`). It is torsion-free (`cover_isTorsionFree`). Indeed, if
  `r ≠ 0` and `r • (l, c) = 0`, then `c = 0` because `ℤ[Λ/eΛ]` is free. Then
  `[l] = 0`, so `l = e • y`, and `y` is torsion because `(r e) • y = 0`. Hence
  `l = e • y = 0`. So `Cover Λ` is free (`cover_free`, Mathlib's
  `Module.free_of_finite_type_torsion_free'`).

Functoriality in an isomorphism `g : Λ ≃+ Λ'`:

- `g` preserves torsion (`mem_torsion_congr`), so `torsionOrder_congr` gives
  `e(Λ) = e(Λ')` and `map_multiples` gives `g(eΛ) = eΛ'`. It therefore induces
  `quotEquiv g : Λ/eΛ ≃+ Λ'/eΛ'`, with `quotEquiv_refl` and `quotEquiv_trans`.
- `sumMap_mapDomain`: `sumMap` commutes with `Finsupp.mapDomain (quotEquiv g)`.
- `coverHom g` maps `(l, c)` to `(g l, mapDomain (quotEquiv g) c)`, and
  `coverEquiv g : Cover Λ ≃+ Cover Λ'` is the resulting isomorphism. The laws
  `coverEquiv_refl` and `coverEquiv_trans` hold, and `proj_coverEquiv` and
  `proj_comp_coverEquiv` say `proj ∘ coverEquiv g = g ∘ proj`.

Provenance: this is an internal construction. Conrad, *Reductive group
schemes* (2014), Proposition B.3.8, embeds a group of multiplicative type
into a torus by covering its character groups locally by free groups. The
specific fibre product `Λ ×_{Λ/eΛ} ℤ[Λ/eΛ]` was chosen here so that the cover
is functorial in isomorphisms of `Λ`. It is not taken from the source.
