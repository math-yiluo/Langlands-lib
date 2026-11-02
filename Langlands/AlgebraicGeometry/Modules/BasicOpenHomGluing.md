# Gluing morphisms of module sheaves from compatible maps on basic opens

This module specializes the basis gluing of `BasisHomGluing.lean` to the setting that
arises for affine charts. There, compatibility of local maps is easy to check along
basic opens but hard along arbitrary inclusions. All declarations are in the namespace
`Langlands.Scheme.Modules.BasisHomGluing`.

Fix a scheme `Y : Scheme.{u}` and modules `N M : Y.Modules`. `Γ(N, V)` denotes
Mathlib's sections over `V`, a `Γ(Y, V)`-module, and `Y.basicOpen g ≤ V` is the basic
open of `g : Γ(Y, V)` (Mathlib's `Scheme.basicOpen_le`).

## Hypotheses

The predicate `P : Y.Opens → Prop` satisfies

- `hPaff : ∀ V, P V → IsAffineOpen V`: every `P`-open is affine;
- `hPbasic : ∀ V (g : Γ(Y, V)), P V → P (Y.basicOpen g)`: `P` is closed under
  passing to basic opens;
- `hPcover : ∀ y : Y, ∃ V, P V ∧ y ∈ V`: the `P`-opens cover `Y`.

The local data are `Γ(Y, V)`-linear maps `θ V hV : Γ(N, V) →ₗ[Γ(Y, V)] Γ(M, V)`, one
for each `P`-open `V`, compatible with restriction to basic opens:

`hθ : ∀ V hV g n, θ (Y.basicOpen g) _ (n|_{D(g)}) = (θ V hV n)|_{D(g)}`.

## Results

- `eq_of_forall_mem s t h`: two sections over `O` that agree on some open
  neighbourhood `W ≤ O` of every point of `O` are equal. This is Mathlib's
  `TopCat.Sheaf.eq_of_locally_eq'`, applied to the cover by all such neighbourhoods.
- `isBasis_of_basicOpen hPaff hPbasic hPcover`: the `P`-opens form a basis in the sense
  of `BasisHomGluing` (`∀ y U, y ∈ U → ∃ V, P V ∧ y ∈ V ∧ V ≤ U`). Given `y ∈ U`, pick
  a `P`-open `V ∋ y`. Mathlib's `IsAffineOpen.exists_basicOpen_le` gives a basic open
  `D(g) ⊆ U` of the affine `V` that contains `y`, and `D(g)` is a `P`-open by
  `hPbasic`.
- `hom_ext_of_basicOpen hPaff hPbasic hPcover f g h`: two morphisms `N ⟶ M` that agree
  on every `P`-open are equal. This is `hom_ext_of_basis` for that basis.
- `compat_of_basicOpen hPaff hPbasic θ hθ`: for `P`-opens `V' ≤ V` and
  `s : Γ(N, V)`, `(θ V s)|_{V'} = θ V' (s|_{V'})`. The proof applies
  `eq_of_forall_mem` on `V'`. Mathlib's `exists_basicOpen_le_affine_inter`, applied to
  the affine opens `V'` and `V`, gives near each point `y ∈ V'` an open
  `W = D_{V'}(f) = D_V(g)` containing `y` that is basic in both. Restricted to `W`, both
  sides equal `θ W (s|_W)`: apply `hθ` once in `V'` (for `f`) and once in `V` (for
  `g`). The identification of the two descriptions of `W` is handled by substituting
  the equation `W = D_V(g)`.
- `homOfBasicOpen hPaff hPbasic hPcover θ hθ : N ⟶ M`: the glued morphism. It is
  `BasisHomGluing.hom` applied to the basis above and to the compatibility from
  `compat_of_basicOpen`.
- `homOfBasicOpen_app`: for every `P`-open `V` and `n : Γ(N, V)`,
  `(homOfBasicOpen …).app V n = θ V hV n`.
- `exists_hom_of_basicOpen`: there is `φ : N ⟶ M` with `φ.app V n = θ V hV n` for all
  `P`-opens `V` and sections `n`.

## Provenance and scope

This is an internal helper for the trace construction of proof task
`f2728a31-103a-4d50-ae2d-6cb3f9ce05a9`. There, `P V` will be "`V` is affine and the
pushforward of the structure sheaf is free over `V`". Mathematically it is the standard
reduction of compatibility on an affine basis to compatibility along basic opens:
basic opens of two affine opens refine their intersection. The basis gluing it
specializes is that of Stacks Project Lemma 6.30.13 (Tag 009U), as cited in
`BasisHomGluing.md`. It uses the module `BasisHomGluing`, the published
`OpenCoverHomGluing` helpers `sheafAb` and `map_map_eq`, and pinned Mathlib
(`Mathlib/AlgebraicGeometry/AffineScheme.lean`: `IsAffineOpen.exists_basicOpen_le`,
`exists_basicOpen_le_affine_inter`; `Mathlib/AlgebraicGeometry/Scheme.lean`:
`Scheme.basicOpen_le`; commit `5ed2965256430c3649e86755f9576b54eca72435`). It asserts
nothing about any particular trace map.
