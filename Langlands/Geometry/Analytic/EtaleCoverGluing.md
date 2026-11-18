# Gluing analytic morphisms along jointly surjective étale families

Internal helper lemmas (derived provenance) for the conditional existence argument of
`SpaceAnalytificationExistenceStatement`. Each assumes the sheaf property of
`etaleHomPresheaf S T`, i.e. of `V ↦ (V.left ⟶ T)` on Berkovich's small étale site
`EtaleSite S` with `etaleTopology S`. That property is the form of étale descent of morphisms
used by Conrad–Temkin (2009), Theorem 4.1.2 and the discussion around it, and Berkovich
(1993), §4.1.

- `etaleHomPresheaf S T`: the presheaf `(V : EtaleSite S) ↦ (V.left ⟶ T)`. It is the
  presheaf in Worker 790's proposed `EtaleHomSheafStatement`.
- `etaleSiteTop S`: the terminal object `𝟙 S` of the étale site.
- `hom_ext_of_etale_cover`: two maps `S ⟶ T` that agree after composition with every member
  of a family of étale maps `e j : U j ⟶ S` are equal, provided the family is jointly
  surjective on underlying points. Proof: the maps `V ⟶ S` along which the two agree form a
  sieve. It contains the family, so it covers by `mem_etaleTopology_of_jointlySurjective`.
  Separatedness of the sheaf then gives equality.
- `exists_glue_of_etale_cover`: suppose maps `h j : U j ⟶ T` agree on every pair of
  factorizations, i.e. `a ≫ e j = b ≫ e k` implies `a ≫ h j = b ≫ h k` for all
  `a : V ⟶ U j` and `b : V ⟶ U k`. Then they glue to a map `g : S ⟶ T` with
  `e j ≫ g = h j`. Proof: on the covering sieve of maps factoring through the family, pick a
  factorization of each member and compose with `h`. The compatibility hypothesis makes this
  family of elements compatible, and amalgamation gives `g`. Its restriction to `e j` is
  computed through the factorization `𝟙`.

No unconditional descent statement is claimed. The sheaf property is a hypothesis.
