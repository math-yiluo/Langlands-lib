# The root datum of a split maximal torus from reflection data and the finite Weyl image

Author: Worker 1223. The structure follows the published
`Reductive.RootDatumAssembly` by Worker 835, whose root permutation, conjugate
reflection and coroot injectivity lemmas this module imports and reuses.

This module is a derived, conditional assembly step toward the published
`RootDatumExistenceStatement`
(`Langlands.GroupScheme.Reductive.RootDatumStatement`). It proves:

```
rootDatumExistence_of_reflectionExistence_of_reducedness
    (hrefl : RelativeRootReflectionExistenceStatement.{u})
    (hred : RootReducednessStatement.{u}) : RootDatumExistenceStatement.{u}
```

So the published root-datum existence proposition follows from two published
propositions: integral reflection existence and reducedness of the roots. The
module does **not** prove either of them; both enter as hypotheses. The target
statement and every file it imports are unchanged.

The published `Reductive.RootDatumAssembly` already builds the root datum from
reflection data. Its coroot uniqueness needs an extra spanning premise: the
roots together with the restrictions of the characters of `G` span the
rational character space. This module replaces that premise with the
finiteness of the Weyl image. That finiteness is proved unconditionally in the
Library (`splitTorusWeylImageFinite`), so the spanning premise is not needed.

## Mathematical model

Milne, *Algebraic Groups* (2017), Theorem 21.11 and Corollary 21.12 (printed
pp. 428–430, PDF pp. 444–446). For a split reductive group `(G, T)` and a root
`α`, the reflection `s_α` is represented by a point `n_α ∈ N_G(T)(k)`
(21.11(d)). There is a unique `α^∨` with `s_α(x) = x - ⟨x, α^∨⟩ α`, and
`⟨α, α^∨⟩ = 2` (21.11(e)). In the proof of Corollary 21.12, the reflections
lie in `W(G,T)`, which "is finite by definition". Hence
`(X(T), Φ(G,T), α ↦ α^∨)` is a root datum, and 21.11(b) shows that it is
reduced.

This module formalizes the lattice-theoretic half of Corollary 21.12. Here
the finiteness of `W(G,T)` is used a second time: it shows that the coroot
attached to a root does not depend on the normalizing point chosen to
represent its reflection. This is the uniqueness needed for the coroot axiom
of Mathlib's `RootDatum`.

## Setting

The universe is an arbitrary `u`. The setting is a field `k : Type u`, a
commutative group scheme `T` and a group scheme `G` over `Spec k`, and a
homomorphism `i : T.toGrp ⟶ G`. Apart from the final theorem, every
declaration uses the published instance hypotheses `[IsAffineHom G.X.hom]`
and `[Mono i.hom.hom.left]` of `RelativeRootReflectionData i`. The first
theorem omits `[IsAffineHom G.X.hom]`, which it does not need. The finiteness
of the Weyl image enters as the instance argument `[Finite (weylImage i)]`,
where `weylImage i` is the published subgroup of character automorphisms
given by the actual normalizing points.

## Uniqueness of the coroot

`coroot_eq_of_weylAction_of_finite_weylImage` assumes that `T` is split and
that `weylImage i` is finite. Let `n₁`, `n₂` be normalizing points and `γ` a
character such that, for cocharacters `c₁`, `c₂` with
`⟨γ, c₁⟩ = ⟨γ, c₂⟩ = 2`,

```
weylAction i n₁ χ = χ - ⟨χ, c₁⟩ • γ,   weylAction i n₂ χ = χ - ⟨χ, c₂⟩ • γ
```

for every character `χ`. The theorem concludes `c₁ = c₂`. The proof:

1. The elements `weylAction i n₁` and `weylAction i n₂` lie in the finite
   group `weylImage i`, so their product has finite order there
   (`isOfFinOrder_of_finite`). The subgroup inclusion
   (`Subgroup.subtype`, `MonoidHom.isOfFinOrder`) transports this to the
   product `weylAction i n₁ * weylAction i n₂` of character automorphisms.
2. The published `Langlands.LinearAlgebra.eq_functional_of_finiteOrder_reflections`
   (`Reductive.RootDatumCorootComparison`) applies to the functionals
   `(latticePairing T).flip c₁` and `(latticePairing T).flip c₂`. It states
   that two integral reflections along the same vector, whose product has
   finite order, have the same functional. (Their product is
   `χ ↦ χ + (⟨χ, c₂⟩ - ⟨χ, c₁⟩) • γ`, and a finite power being the identity
   forces the two functionals to agree.)
3. Right injectivity of the perfect pairing `latticePairing T`
   (`IsSplitTorus.isPerfPair_latticePairing`) gives `c₁ = c₂`.

The spanning premise of the published `coroot_eq_of_weylAction` and the
finiteness of `relativeRoots i` are not used.

## Coroot stability

For `D : RelativeRootReflectionData i`, the published assembly defines
`reflectedCoroot α β := D.coroot β - ⟨α, D.coroot β⟩ • D.coroot α`, the
cocharacter `s_α^∨(β^∨)`. It proves `weylAction_conj` (the conjugate
`n_α n_β n_α⁻¹` acts by the reflection formula along `s_α(β)` with
cocharacter `reflectedCoroot α β`) and `pairing_reflectedCoroot`
(`⟨s_α(β), s_α^∨(β^∨)⟩ = 2`).

`RelativeRootReflectionData.coroot_weylRootPerm_of_finite_weylImage`, for
split `T` and finite `weylImage i`, proves

```
D.coroot (weylRootPerm i (D.representative α) β) = D.reflectedCoroot α β.
```

It applies the uniqueness theorem above to `D.representative (s_α β)`, which
acts by the reflection formula along `s_α(β)` with cocharacter
`D.coroot (s_α β)` (`D.action`, `D.pair_self`), and to the conjugate
`n_α n_β n_α⁻¹`. This is the coroot axiom `reflectionPerm_coroot` of a root
pairing.

## The root datum

`RelativeRootReflectionData.rootDatumOfFiniteWeylImage D hT hfinite` is a
`RootDatum (relativeRoots i) (characterLattice T) (cocharacterLattice T)`.
Here `hT : IsSplitTorus T.toGrp` and `hfinite : (relativeRoots i).Finite`,
and `weylImage i` is finite. Its data are:

* pairing `latticePairing T`, perfect by `IsSplitTorus.isPerfPair_latticePairing`;
* roots the inclusion `Function.Embedding.subtype` of the actual roots;
* coroots `D.coroot`, an embedding by the published `coroot_injective`, which
  uses `hT` and `hfinite`;
* `root_coroot_two` from `D.pair_self`;
* reflection permutations `weylRootPerm i (D.representative α)`, with the root
  axiom from `D.action` and the coroot axiom from
  `coroot_weylRootPerm_of_finite_weylImage`.

Only the coroot axiom differs from the published `RelativeRootReflectionData.rootDatum`.
The simp lemmas `rootDatumOfFiniteWeylImage_toLinearMap`,
`rootDatumOfFiniteWeylImage_root` and `rootDatumOfFiniteWeylImage_coroot`
record the data. `rootDatumOfFiniteWeylImage_reflection` identifies
`P.reflection α` with `weylAction i (D.representative α)`, via `D.action` and
`RootPairing.reflection_apply`.

`isRootDatumOf_rootDatumOfFiniteWeylImage` proves the full published
`IsRootDatumOf i` for this root datum:

* the pairing is `latticePairing T` (`rfl`);
* `Set.range P.root = roots i`, by `Subtype.range_coe` and the definitional
  equality `relativeRoots i = roots i`;
* each reflection `P.reflection α` is `characterAut σ` for the normalizing
  point `D.representative α` and `σ := normalizingAut i (D.representative α)`,
  with `IsNormalizingPoint` from the published
  `isNormalizingPoint_normalizingAut`. The equality comes from
  `rootDatumOfFiniteWeylImage_reflection`, because the published `weylAction`
  is definitionally `characterAut (normalizingAut i n)`.

`isReduced_rootDatumOfFiniteWeylImage` assumes that any two actual roots `α`,
`β` that are not linearly independent over `ℤ` satisfy `α = β ∨ α = -β`. It
concludes that the root datum is reduced; this hypothesis is the field of
`RootPairing.IsReduced` verbatim.

## Conditional existence

`exists_rootDatum_of_reflectionData_of_finite_weylImage` takes
`hG : IsConnectedReductive G`, a split `T`, `D : RelativeRootReflectionData i`,
finite `weylImage i` and the reducedness hypothesis
`∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β] → α = β ∨ α = -β`.
It concludes the body of `RootDatumExistenceStatement`:

```
∃ (J : Type u) (_ : Finite J)
  (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
  IsRootDatumOf i P ∧ P.IsReduced
```

with `J := relativeRoots i`. Finiteness of the roots comes from the published
`IsSplitTorus.finite_relativeRoots`; its local-finite-type instance comes from
the smoothness field of `IsConnectedReductive`.

## The reduction of root-datum existence

`rootDatumExistence_of_reflectionExistence_of_reducedness` proves
`RootDatumExistenceStatement.{u}` from `RelativeRootReflectionExistenceStatement.{u}`
and `RootReducednessStatement.{u}`. Take `k`, `G`, `hG`, a split `T` and
`i` with `hi : IsMaximalTorus i`. Then:

1. `hG.isAffineHom` supplies `[IsAffineHom G.X.hom]`.
2. The published `IsMaximalTorus.isMaximalSplitTorus hi hT` makes `i` a
   maximal split torus; its `isSplitSubtorus.mono` supplies
   `[Mono i.hom.hom.left]`.
3. `hrefl` at this maximal split torus gives reflection data `D`. Its extra
   kernel-centralizer clause is not used.
4. `hi.2.1 : IsClosedSubgroup i` makes `i.hom.hom.left` a closed immersion.
   The published `splitTorusWeylImageFinite`, with the local-finite-type
   instance from `hG.smooth`, gives `Finite (weylImage i)`.
5. `hred` at the same data gives the reducedness hypothesis, and
   `exists_rootDatum_of_reflectionData_of_finite_weylImage` concludes.

The final proof of `RootDatumExistenceStatement` is then this theorem applied
to a proof of `RelativeRootReflectionExistenceStatement` and to the published
`rootReducedness : RootReducednessStatement.{u}`
(`Reductive.RootReducednessProof`).

## Provenance

The mathematics follows Milne 21.11(e) and 21.12. Milne's proof of 21.12
deduces the root-datum axioms from the finiteness of `W(G,T)`. Here the same
finiteness also gives the coroot uniqueness needed for Mathlib's
`reflectionPerm_coroot`. Milne does not state this step separately: his
uniqueness in 21.11(e) is for a fixed reflection `s_α`. The comparison of two
representing points through the finite order of their product is an internal
argument of the published architecture
(`eq_functional_of_finiteOrder_reflections`). The reflection data, the
reducedness statement and the split-maximal adapter are also internal
interfaces of the published architecture. Milne's axiom (rd3), finiteness of
the group generated by the reflections, is not a field of Mathlib's
`RootDatum`; the finite index type `relativeRoots i` takes its place. Axioms:
`propext`, `Classical.choice`, `Quot.sound`.
