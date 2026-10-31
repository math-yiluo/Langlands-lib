# Exact additive adjunctions and cohomology

Let `C` and `D` be abelian categories, with independent object and morphism
universes, and let `adj : F ⊣ G` be an adjunction of additive functors
`F : C ⥤ D` and `G : D ⥤ C`. All complexes below are cochain complexes indexed
by `ℕ`, and all assertions hold for every degree `n : ℕ`.

Write

```text
γ(P,K,n) : Hⁿ(P(K)) ≅ P(Hⁿ(K))
```

for the published `DerivedComparison.mapHomologyIso`. Here `P(K)` denotes
termwise application of the functor. This is the actual homology comparison,
constructed from the short complex around degree `n`.

The definition
`Langlands.Cohomology.ExactAdjunction.homologyAdjunct` assumes that `G`
preserves homology. For an actual cochain map `t : K ⟶ G(L)`, it is the
adjunct under `adj` of the composite

```text
Hⁿ(K) --Hⁿ(t)--> Hⁿ(G(L)) --γ(G,L,n).hom--> G(Hⁿ(L)).
```

Its source is `F(Hⁿ(K))` and its target is `Hⁿ(L)`. The definition requires
no exactness or homology preservation of `F`.

The two compatibility lemmas assume that both `F` and `G` preserve finite
limits and finite colimits. In particular, both preserve homology.
`unit_homology` identifies the unit of the original adjunction with the
cohomology of the degreewise unit of the published `complexAdjunction`:

```text
Hⁿ(unit_K) ≫ γ(G,F(K),n).hom ≫ G.map(γ(F,K,n).hom)
  = adj.unit.app (Hⁿ(K)).
```

Let `s : F(K) ⟶ L` be the cochain adjunct of `t` under `complexAdjunction adj`.
Then `homologyAdjunct_eq` proves the equality of specified morphisms

```text
homologyAdjunct adj t n = γ(F,K,n).inv ≫ Hⁿ(s).
```

Thus the cohomological adjunct agrees with cohomology of the cochain adjunct
through the canonical comparison for the left adjoint. No choice of an
unrelated isomorphism between their sources occurs.

The auxiliary `mapHomologyIso_id_hom` proves that the homology comparison
for the identity functor on any short complex in `C` has identity forward
map. Its proof first uses the monomorphism from cycles into the middle term
to identify the cycles comparison, then uses the epimorphism from cycles
onto homology and the published
`DerivedPlus.homologyπ_mapHomologyIso_hom` to identify the homology comparison.

For `unit_homology`, the implementation applies Mathlib's
`NatTrans.app_homology` to `adj.unit` and to the short complex around degree
`n`. The identity comparison just proved removes the identity-functor
factor. The published `DerivedPlus.mapHomologyIso_comp_hom` splits the
comparison for `F ⋙ G` into those for `F` and `G`. Extensionality identifies
the short-complex map of the degreewise unit with `mapNatTrans adj.unit`.

For `homologyAdjunct_eq`, the implementation applies the original adjunction's
hom-set equivalence to both sides. The cochain adjunction gives
`t = unit_K ≫ G(s)`. Naturality of the homology comparison for `G` moves
`Hⁿ(G(s))` past that comparison; `unit_homology` then supplies the original
unit. Functoriality and inverse cancellation finish the equality.

This is an internal consequence of the published additive cochain adjunction,
the published homology comparisons and their composition formula, and
Mathlib's natural-transformation and homology-comparison naturality identities.
It introduces no literature-dependent geometric assertion. In particular, it
does not establish exactness of scalar extension in any particular case,
cohomology base change for schemes, a Čech-resolution comparison, or the
relative cube theorem.
