# Geometric points, the regular cocharacter, and factorizations

Module `Langlands.GroupScheme.SplitExistence.GeometricPoints`, namespace
`Langlands.GroupScheme.SplitExistence` (with sub-namespace `ChevalleyData`). Internal helper of
the proof of the split reductive Existence Theorem (task 2132924b). Derived content.

## Factorization through closed subgroups

- `exists_hom_factor j hj f hf`: let `j : M ⟶ G` be a closed subgroup over any base scheme, and
  `f : H ⟶ G` a homomorphism whose underlying morphism factors through `j`. Then `f = g ≫ j`
  for a homomorphism `g : H ⟶ M`. The closed immersion represents its own range, and
  the Library's `IsRepresentedBy.factorHom` provides `g`.
- `glMapEquiv e`: a ring isomorphism `e : A ≃+* B` induces `GL_n(A) ≃* GL_n(B)`.

## Transport of the abstract subgroups

For a ring homomorphism `f : A →+* B`, applying `f` entrywise maps the subgroups of `GL_n`
from the module `Subgroups` into the corresponding ones over `B`. This holds for the torus
`T(A)`, the root groups `U_j(A)`, `rootsSub`, the Chevalley group `Γ(A)` and the Borel
subgroup `B(A)` (`map_torusSub_le`, `map_rootSub_le`, `map_rootsSub_le`, `map_chevSub_le`,
`map_borelSub_le`). The reason is that `f` sends `diag(χ(wt c))` and `x_j(s)` to the same
formulas over `B` (`torusHom_map`, `x_map`). For an isomorphism, membership is equivalent on
both sides (`mem_chevSub_iff_of_equiv`, `mem_borelSub_iff_of_equiv`).

## The regular cocharacter

- `ellWeights`: the integers `c ↦ ℓ(wt c)`.
- `ellChar R : Rˣ →* (Multiplicative X →* Rˣ)`, `t ↦ (x ↦ t ^ ℓ(x))`. Its image under
  `torusHom` is `diag(t ^ ℓ(wt c))`, the Library's `diagonalUnits` with weights `ellWeights`
  (`torusHom_ellChar`). It commutes with ring homomorphisms (`ellChar_map`).
- `cocharPoints k T`, `cocharPoints_naturality`, `cochar k`: the cocharacter
  `λ : 𝔾ₘ → D(X)` given on points by `ellChar`, built with the Library's `homOfPoints`.
- `cochar_comp_torusToGL`: `λ` followed by `torusToGL` is the Library's diagonal cocharacter
  `GeneralLinear.diagonalCocharacter (Fin n) k ellWeights`, that is `t ↦ diag(t ^ ℓ(wt c))`.
  It is proved by comparing points on every test scheme (`hom_ext_points`).

## Geometric points of `GL_n`

For a field `K` with a `k`-algebra structure:

- `specRingEquiv k K : Γ(Spec K, ⊤) ≃+* K` is Mathlib's `Scheme.ΓSpecIso`.
- `glExt k K`: the `K`-valued points `extPoint K ⟶ GL_n` are identified with `GL_n(K)`. It
  composes the Library's `GeneralLinear.pointsEquiv` with `glMapEquiv (specRingEquiv k K)`.
- `mem_chevPoints_iff_glExt`: a `K`-valued point lies in `chevPoints` exactly when its matrix
  lies in the abstract Chevalley group `Γ(K)`.
