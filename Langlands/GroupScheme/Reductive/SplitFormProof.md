# The split form of a reductive group: proof

Worker 164.

This module proves the Library statement `Langlands.GroupScheme.SplitFormStatement`
(module `Langlands.GroupScheme.Reductive.SplitFormStatement`) at its universe parameter:

```lean
theorem splitForm : SplitFormStatement.{u}
```

It also contains one helper, `Langlands.GroupScheme.SplitForm.nonempty_iso_of_rootDatumEquiv`.
The proof uses no additional hypotheses. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`. The module sets no options. It imports the statement module and published
Library modules only.

The statement is Milne, *Algebraic Groups* (2017), Corollary 23.57. The statement's Markdown
gives the source quotations and the correspondence. Milne's one-line proof takes the split
group with the root datum of `(G, T)_{k_s}`. This proof follows the same idea. The proof
outline follows the route that Worker 3483 recorded in the task context. No code from Worker
3483's draft was reused, because that draft was not available in this instance. The Lean
code was written from that outline.

Notation: `k_s = SeparableClosure k`, `b = algebraBaseMap k k_s : Spec k_s ⟶ Spec k`, and
`X_{k_s}` is `(GroupScheme.baseChange b).obj X`. For a commutative group scheme `T` the
base change is `(CommGroupScheme.baseChange b).obj T`.

## Helper: equivalent root data give isomorphic groups

`SplitForm.nonempty_iso_of_rootDatumEquiv` (lines 18–48). Suppose `G` and `H` are connected
reductive over a field `k`. Let `i : T ⟶ G` and `j : T' ⟶ H` be maximal tori with split `T`
and `T'`. Let `P` and `Q` be root data of `i` and `j` (`IsRootDatumOf`), and let
`e : RootPairing.Equiv P Q`. Then `Nonempty (G ≅ H)`.

Proof:

1. `t : T ≅ T'` is `IsSplitTorus.isoOfCharacterEquiv hT hT' e.weightEquiv.toAddEquiv`.
   This is the torus isomorphism whose character map is the weight map of `e`. By
   `IsSplitTorus.character_congr_isoOfCharacterEquiv`,
   `characterLattice.congr t = e.weightEquiv`.
2. `IsRootDatumOf.precomp_torusIso` then says that `P` is a root datum of the composite
   `groupHom t.hom ≫ j : T ⟶ H`. Its inputs are `hQ`, the pairing equation `hP.1` of `P`,
   `e`, and the pointwise form of step 1.
3. `IsMaximalTorus.precomp_torusIso` says this composite is a maximal torus of `H`.
4. Now `i : T ⟶ G` and `groupHom t.hom ≫ j : T ⟶ H` are maximal tori with the same
   split torus `T`, and `P` is a root datum of both. `splitCommonTorusIsomorphism` is
   applied with the identity reindexing `Equiv.refl J`. The root and coroot conditions hold
   by `rfl`. It gives `ψ : G ≅ H`, and the helper keeps only `ψ`.

## Existence (part 1)

Lines 59–77. Let `G` be connected reductive over `k`.

1. `G_{k_s}` is connected reductive by `connectedReductiveFieldExtensionStatement`. In
   particular it is smooth and affine.
2. `k_s` is separably closed (Mathlib instance `SeparableClosure.isSepClosed`).
   `exists_isMaximalTorus_isSplitTorus_of_isSepClosed` gives a maximal torus
   `is : Ts ⟶ G_{k_s}` with `Ts` split.
3. `rootDatumExistence` gives a finite index type `J`, a root datum
   `P : RootDatum J (characterLattice Ts) (cocharacterLattice Ts)` of `is`, and the
   fact that `P` is reduced.
4. `characterLattice Ts` is a finitely generated `ℤ`-module by
   `IsSplitTorus.finite_characterLattice`. So `splitReductiveExistence` applies to `P`
   over `k`. It gives a connected reductive `G₀` over `k` and a maximal torus
   `i₀ : T₀ ⟶ G₀` with `T₀` split. It also gives a root datum `Q` of `i₀` and
   `eQ : RootPairing.Equiv P Q`. The triple `(G₀, T₀, i₀)` is the witness. It remains to
   show `G₀_{k_s} ≅ G_{k_s}`.
5. Over `k_s`:
   - `G₀_{k_s}` is connected reductive (`connectedReductiveFieldExtensionStatement`).
   - `i₀_{k_s}` is a maximal torus (forward direction of `maximalTorusBaseChange`).
   - `T₀_{k_s}` is split (`IsSplitTorus.baseChange`).
   - `SplitRootDatum.baseChange b T₀ hT₀ Q` is a root datum of `i₀_{k_s}`
     (`splitRootDatumFieldExtension`).
6. `SplitRootDatum.baseChangeEquiv b T₀ hT₀ Q` is an equivalence from `Q` to its base
   change. Composing it with `eQ` gives an equivalence from `P` to the base-changed `Q`.
   Its inverse runs from the root datum of `i₀_{k_s}` to the root datum `P` of `is`.
   The helper over `k_s` then gives `G₀_{k_s} ≅ G_{k_s}`.

## Uniqueness (part 2)

Lines 78–96. Let `G₁` and `G₂` be connected reductive over `k`. Let `i₁ : T₁ ⟶ G₁` and
`i₂ : T₂ ⟶ G₂` be maximal tori with split `T₁` and `T₂`. Let `f₁ : G₁_{k_s} ≅ G_{k_s}` and
`f₂ : G₂_{k_s} ≅ G_{k_s}`.

1. `rootDatumExistence` gives root data `P₁` of `i₁` and `P₂` of `i₂`, indexed by
   `J₁` and `J₂`.
2. Over `k_s`, each `G_ℓ` is handled as in existence step 5:
   - `G_ℓ_{k_s}` is connected reductive.
   - `i_ℓ_{k_s}` is a maximal torus.
   - `T_ℓ_{k_s}` is split.
   - `SplitRootDatum.baseChange b T_ℓ hT_ℓ P_ℓ` is a root datum of `i_ℓ_{k_s}`.
3. `nonempty_rootDatumEquiv_of_iso` is applied to `f₁ ≪≫ f₂.symm : G₁_{k_s} ≅ G₂_{k_s}`.
   It gives an equivalence `es` between the base-changed root data.
4. The equivalence `P₁ ≃ P₂` over `k` is
   `(baseChangeEquiv b T₂ hT₂ P₂).symm.comp (es.comp (baseChangeEquiv b T₁ hT₁ P₁))`.
   The helper over `k` then gives `G₁ ≅ G₂`.

## Published theorems and definitions used

| Lean name | Module |
| --- | --- |
| `Langlands.GroupScheme.IsSplitTorus.isoOfCharacterEquiv` (definition) | `Langlands.GroupScheme.Reductive.PinningLattice` |
| `Langlands.GroupScheme.IsSplitTorus.character_congr_isoOfCharacterEquiv` | `Langlands.GroupScheme.Reductive.PinningLattice` |
| `Langlands.GroupScheme.IsRootDatumOf.precomp_torusIso` | `Langlands.GroupScheme.Reductive.PinnedIsomorphismReduction` |
| `Langlands.GroupScheme.IsMaximalTorus.precomp_torusIso` | `Langlands.GroupScheme.Reductive.PinnedIsomorphismReduction` |
| `Langlands.GroupScheme.splitCommonTorusIsomorphism` | `Langlands.GroupScheme.Reductive.SplitIsomorphismProof` |
| `Langlands.GroupScheme.connectedReductiveFieldExtensionStatement` | `Langlands.GroupScheme.Reductive.FieldExtensionProof` |
| `Langlands.GroupScheme.exists_isMaximalTorus_isSplitTorus_of_isSepClosed` | `Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction` |
| `Langlands.GroupScheme.rootDatumExistence` | `Langlands.GroupScheme.Reductive.RootDatumExistence` |
| `Langlands.GroupScheme.IsSplitTorus.finite_characterLattice` | `Langlands.GroupScheme.Rational.StandardCocharacterFiniteness` |
| `Langlands.GroupScheme.splitReductiveExistence` | `Langlands.GroupScheme.Reductive.SplitExistence` |
| `Langlands.GroupScheme.maximalTorusBaseChange` | `Langlands.GroupScheme.Torus.MaximalBaseChangeProof` |
| `Langlands.GroupScheme.splitRootDatumFieldExtension` | `Langlands.GroupScheme.Reductive.RootDatumBaseChangeProof` |
| `Langlands.GroupScheme.SplitRootDatum.baseChange` (definition) | `Langlands.GroupScheme.Reductive.RootDatumBaseChangeStatement` |
| `Langlands.GroupScheme.SplitRootDatum.baseChangeEquiv` (definition) | `Langlands.GroupScheme.Reductive.RootDatumFieldComparison` |
| `Langlands.GroupScheme.nonempty_rootDatumEquiv_of_iso` | `Langlands.GroupScheme.Reductive.RootDatumFieldComparison` |
| `Langlands.GroupScheme.IsSplitTorus.baseChange` | `Langlands.GroupScheme.Torus.Split` |
| `SeparableClosure.isSepClosed` (Mathlib instance) | `Mathlib.FieldTheory.IsSepClosed` |
| `RootPairing.Equiv.comp`, `RootPairing.Equiv.symm`, `RootPairing.Equiv.weightEquiv` (Mathlib) | `Mathlib.LinearAlgebra.RootSystem.Hom` |
