# Tensor powers of actual equivariant line bundles

Module `Langlands.AlgebraicGeometry.Picard.EquivariantLineBundleTensorPow`. Worker 5217,
Task 7409. Internal, derived construction used by
`Langlands.AlgebraicGeometry.Picard.EquivariantSectionDescent` and the proof
`polarizedEtaleRelationEffectivity`.

It transports the coherent identifications of a published
`Langlands.AlgebraicGeometry.Picard.EquivariantLineBundle E` to the right-associated tensor
powers `tensorPow B.bundle.obj n` of its actual module sheaf. These are the powers used by the
Library's `LineBundle.powSections`, `LineBundle.sectionOpen` and `LineBundle.IsAmple`.

## Tensor-power functoriality (namespace `Langlands.Scheme.Modules`)

- `tensorPowMap_id`, `tensorPowMap_comp`: the published `tensorPowMap` preserves identities
  and composition (induction on `n` with `tensorMap_comp`).
- `tensorPowIso_refl`, `tensorPowIso_trans`, `tensorPowIso_symm`: the corresponding facts for
  the published `tensorPowIso`, proved from `tensorPowIso_hom`.

## Pullback of tensor powers

`pullbackTensorPowIso f M n : (pullback f).obj (tensorPow M n) ≅ tensorPow ((pullback f).obj M) n`
is defined by recursion on `n`. In degree zero it is the published `pullbackUnitIso f`. In degree `n + 1` it is
the published canonical comparison `pullbackTensorIso f M (tensorPow M n)` followed by the
identity tensored with the degree-`n` comparison. `pullbackTensorPowIso_succ_hom` records the
successor formula.

- `pullbackTensorPowIso_naturality` (and `_naturality_iso`): for a module morphism
  `g : M ⟶ M'`, `(pullback f).map (tensorPowMap g n) ≫ P f M' n = P f M n ≫ tensorPowMap
  ((pullback f).map g) n`. Induction with the published `pullbackTensorComparisonApp_naturality`.
- `pullbackTensorPowIso_comp` (and `_comp_iso`): for `k : W ⟶ X`, `a : X ⟶ Y`,

  ```text
  (pullbackComp k a).hom.app (tensorPow M n) ≫ (P (k ≫ a) M n).hom =
    (pullback k).map (P a M n).hom ≫ (P k (a^*M) n).hom ≫
      tensorPowMap ((pullbackComp k a).hom.app M) n.
  ```

  Degree zero is the published `pullbackUnitComposition`; the successor step uses the
  published `pullbackTensorComposition` and the naturality of the comparison for `k`.

## The transported identifications (namespace `EquivariantLineBundle`)

- `transportModule B a b h` is the underlying module isomorphism of `B.transport a b h`.
  `transportModule_self`, `_trans`, `_precompose` restate the three published laws of
  `EquivariantLineBundle` at the module level.
- `tensorPowTransport B n a b h : (pullback a).obj (tensorPow B.bundle.obj n) ≅
  (pullback b).obj (tensorPow B.bundle.obj n)` is
  `pullbackTensorPowIso a _ n ≪≫ tensorPowIso (transportModule B a b h) n ≪≫
  (pullbackTensorPowIso b _ n).symm`.
- `tensorPowTransport_self`: it is the identity when `B.transport` is.
- `tensorPowTransport_trans`: identifications compose along related triples.
- `tensorPowTransport_precompose`: for `k : W ⟶ T`, the identification along
  `(k ≫ a, k ≫ b)` is the pullback along `k` of the one along `(a, b)`, conjugated by the
  composition comparisons `pullbackComp k a`, `pullbackComp k b`. The proof combines
  `pullbackTensorPowIso_comp_iso`, `pullbackTensorPowIso_naturality_iso` and
  `transportModule_precompose`.

These are the same three laws as the fields of `EquivariantLineBundle`, now for
the `n`-th tensor power. No ampleness, flatness or cartesian hypothesis is used.

## Provenance

Derived internal construction: monoidal coherence of actual sheaf pullback, built only from
the Library's published tensor comparison isomorphism and its identity/composition proofs.
It introduces no literature claim.
