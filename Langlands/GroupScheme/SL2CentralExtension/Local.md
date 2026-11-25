# Fppf-local properties of test morphisms

Internal supporting development for the proof of
`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement` (Conrad, *Reductive group
schemes*, Proposition 4.3.1). It has no separate literature source; it packages standard facts
about the fppf topology on `Over S` from Mathlib.

## Definition

For a scheme `S`, a test object `T : Over S` and a property `P` of morphisms `g : V ⟶ T` in
`Over S`, `Loc P` means: there is a sieve on `T` that covers `T` for `Scheme.fppfTopology.over S`,
and `P g` holds for every `g` in that sieve. In words, `P` holds fppf-locally on `T`.

## Results

- `Loc.of_forall`, `Loc.mono`, `Loc.and`, `Loc.pull`, `Loc.bind`: a property that holds
  everywhere holds locally; local properties are monotone, closed under conjunction, stable under
  pullback along any `T' ⟶ T`, and local-on-local is local (transitivity of coverings).
- `Loc.ext`: two morphisms `x y : T ⟶ X` whose restrictions agree fppf-locally are equal. The
  proof uses that representable presheaves are fppf sheaves (the topology is subcanonical).
- `Loc.glue`: let `P g x` be a property of a test morphism `g : V ⟶ T` and a point
  `x : V ⟶ X`. Assume it is stable under further restriction, has at most one solution `x` for
  each `g`, and has a solution fppf-locally. Then there is one `e : T ⟶ X` whose restriction
  along every `g` is the solution there. The proof amalgamates a compatible family in the
  sheaf `yoneda.obj X`.
- `Loc.of_presieve`, `Loc.of_cover`, `Loc.of_single`: an fppf covering presieve of `T.left`,
  a cover in `Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)` (the form used in the
  target statement), or a single flat, surjective morphism locally of finite presentation,
  yields an fppf-local property: every local test map factors through a member.
- `Loc.of_affine`: to prove `Loc P`, it suffices to prove for every test map `g : V ⟶ T` with
  affine `V.left` that the pulled-back property holds fppf-locally on `V`, using the affine
  open cover of `T.left`.
