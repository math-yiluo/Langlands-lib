# Descent of group-scheme homomorphisms along fppf maps

All schemes lie in an arbitrary universe `u`. Let `p : U ⟶ S` be surjective,
flat and locally of finite presentation, and let `C, D` be actual group
schemes over `S`. Let `f : p*C ⟶ p*D` be a homomorphism of the base-changed
group schemes. Assume `f` is compatible with the canonical descent data
(`Compatible (canonicalDatum p C) (canonicalDatum p D) f`). This module
descends `f` to a homomorphism `C ⟶ D`. The published module `FpqcHomDescent`
does the same along fpqc maps; this module reuses its lemma
`comp_eq_of_projection_eq` but needs no quasi-compactness of `p`.

- `underlying`: the projection `pullback.fst C.X.hom p` is a base change of
  `p`, hence an fppf surjection. By Mathlib it is an effective epimorphism.
  `FpqcHomDescent.comp_eq_of_projection_eq` shows that `f` followed by the
  projection of `D` is invariant under the kernel pair. `EffectiveEpi.desc`
  descends it. `underlying_fac` is the factorization identity.
- `underlying_over` proves that the descended map lies over `S`, by cancelling
  the epimorphism. `overHom` is the resulting map in `Over S`, and
  `pullback_overHom` says that slice pullback along `p` recovers `f`.
- `overHom_isMonHom`: slice pullback along `p` is faithful (Mathlib instance
  for fppf surjections) and monoidal. The published lemma
  `GaloisCocharacterDescent.isMonHom_of_faithfulMap` therefore lets the
  homomorphism laws of `f` descend. `hom` is the descended group-scheme
  homomorphism. `baseChange_hom` gives `(baseChange p).map (hom p f hf) = f`,
  and `unique` says that this equation determines it.
- `Solution.descendHomOfFppf s t f hf` handles supplied solutions
  `s : Solution D'` and `t : Solution E` of data over `p` and a compatible
  homomorphism `f` between the groups over `U`. It applies `hom` to
  `s.iso.hom ≫ f ≫ t.iso.inv`. `baseChange_descendHomOfFppf` is the recovery
  square `(baseChange p).map (descendHomOfFppf …) ≫ t.iso.hom = s.iso.hom ≫ f`,
  and `descendHomOfFppf_unique` says that this square determines the map.

Provenance is internal: this is the published étale and fpqc descent argument
with Mathlib's fppf effective-epimorphism and faithfulness instances. There is
no literature assertion.
