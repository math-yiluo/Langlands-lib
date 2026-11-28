# Simple lisse sheaves and change of monodromy group

Module `Langlands.Sheaf.LisseMonodromyTransport` works with a monodromy `M` of lisse `ℓ`-adic
sheaves on a scheme `Y` (weil-conjectures's `AlgebraicGeometry.ProEtale.LisseMonodromy`).
An equivalence at a geometric point `t : Spec Ω̄ ⟶ Y`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt`) supplies continuity of the matrix
coefficients of `M.rep t G` on `π₁(Y, t) = Aut (fiber t)`. It also gives faithfulness, fullness
onto equivariant maps and essential surjectivity onto continuous finite-dimensional
representations. All results are in the namespace
`AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt`.

## Simple objects

- `isZero_of_isZero_obj` gives a zero object in the full subcategory of lisse sheaves when the
  underlying `ℓ`-adic sheaf is zero. The zero morphism has zero stalk map by
  `lisseStalkMap_eq_zero`.
- `simple_iff_isIrreducible` shows that on a locally Noetherian `Y`, a lisse sheaf `G` is simple
  in the category of lisse sheaves (Mathlib's `CategoryTheory.Simple`) exactly when `M.rep t G`
  is irreducible. The proof follows weil-conjectures's
  `AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt.isIrreducibleAdicLocalSystem_iff`.
  An invariant subspace is the image of the stalk of a lisse sheaf mapping to `G` with injective
  stalk map (`exists_hom_range_eq`). Such a morphism is a monomorphism (`mono_of_injective`, using
  that kernels of morphisms of lisse sheaves on a locally Noetherian scheme are lisse). A
  monomorphism has injective stalk map (`injective_of_mono`). A lisse sheaf with zero stalk is zero
  (`isZero_of_subsingleton`), and a morphism with bijective stalk map is an isomorphism
  (`isIso_of_bijective`). Irreducibility requires a nontrivial stalk, and simplicity requires a
  nonzero sheaf.

## Change of group

Let `f : H →* Aut (fiber t)` be a homomorphism from a topological group `H`.

- `continuous_rep_comp` gives continuity of the matrix coefficients of `(M.rep t G).comp f`
  for continuous `f`.
- For surjective `f`, `full_comp` realizes every linear map intertwining the restrictions along
  `f` as the stalk map of a morphism of lisse sheaves.
- When `f` is a homeomorphism (`IsHomeomorph f`), `essSurj_comp` realizes every
  finite-dimensional representation `σ` of `H` on a carrier in universe `u + 1` with continuous
  matrix coefficients up to equivalence as `(M.rep t G).comp f` for some lisse `G`. It applies
  `essSurj` to `σ ∘ f⁻¹`, whose coefficients are continuous because `f⁻¹` is.
- For surjective `f`, `isIrreducible_comp_iff` gives irreducibility of `(M.rep t G).comp f`
  exactly when `M.rep t G` is irreducible. It uses weil-conjectures's
  `Representation.isIrreducible_comp_iff`.

All declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.
