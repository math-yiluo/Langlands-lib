# Assembling the root datum of a split maximal torus from integral reflection data

This module is a derived, conditional assembly step toward the published
`RootDatumExistenceStatement`
(`Langlands.GroupScheme.Reductive.RootDatumStatement`). It builds a finite
Mathlib `RootDatum` on the actual character and cocharacter lattices of a
split torus. It proves that this root datum satisfies the full published
`IsRootDatumOf i`, and that it is reduced under an explicit hypothesis. It
does **not** prove the existence of reflection data, the spanning premise, or
reducedness of the roots of a reductive group. Those enter as explicit
hypotheses and are separate obligations. The target statement and every file
it imports are unchanged.

The mathematical model is Milne, *Algebraic Groups* (2017), Theorem 21.11 and
Corollary 21.12 (printed pp. 428–430, PDF pp. 444–446). There, for a split
reductive group `(G, T)`, the coroot `α^∨` is the unique cocharacter with
`s_α(x) = x - ⟨x, α^∨⟩ α`, where `s_α` is represented by a point
`n_α ∈ N_G(T)(k)` (21.11(d),(e)). The triple `(X(T), Φ(G,T), α ↦ α^∨)` is a
reduced root datum because the reflections lie in the finite Weyl group and
21.11(b) excludes rational multiples other than `±α` (21.12). This module
formalizes the lattice-theoretic half of Corollary 21.12 in the published
architecture: the reflection axioms, the stability of the coroots, finiteness,
and the passage from the "no other multiples" condition to Mathlib's
`RootPairing.IsReduced`. The group-theoretic inputs of Theorem 21.11 are
hypotheses.

## Setting

The universe is an arbitrary `u`. The setting is a field `k : Type u`, a
commutative group scheme `T` and a group scheme `G` over `Spec k`, and a
homomorphism `i : T.toGrp ⟶ G`. After `IsMaximalTorus.isMaximalSplitTorus`,
which needs neither, every declaration uses the published instance hypotheses
`[IsAffineHom G.X.hom]` and `[Mono i.hom.hom.left]`. `relativeRoots i` is the
published set of actual relative roots. It equals `roots i` by definition, and
the proofs use this `rfl`.

## Reducedness criterion for finite root pairings over ℤ

`RootPairing.isReduced_of_two_smul_notMem` holds for a root pairing `P` over
`ℤ` with finite index type. If no root `2 • P.root j` lies in the range of
`P.root`, then `P.IsReduced`. The proof starts from two linearly dependent
roots `i`, `j`. Mathlib's `coxeterWeight_eq_four_iff_not_linearIndependent`
gives `P.pairing i j * P.pairing j i = 4`, which bounds `a = P.pairing i j` to
`[-4, 4]`. In each integral factorization, Mathlib's pairing lemmas give one
of three outcomes:

* `(2, 2)`: `pairing_two_two_iff`, so `root i = root j`;
* `(-2, -2)`: `pairing_neg_two_neg_two_iff`, so `root i = -root j`;
* `(1, 4)`, `(4, 1)`, `(-1, -4)`, `(-4, -1)`: a root equal to `±2` times a
  root, via `pairing_one_four_iff` and `pairing_neg_one_neg_four_iff`. This is
  excluded by the hypothesis. The `-2` case is reduced to the `2` case through
  the reflection `s_j`, which sends `root j` to `-root j`.

## Split maximal tori

`IsMaximalTorus.isMaximalSplitTorus` states: if `i` is a maximal torus
(`IsMaximalTorus i`) and `T` is split, then `i` is a maximal split torus
(`IsMaximalSplitTorus i`). A split torus is a torus (`IsSplitTorus.isTorus`),
so the maximality of `i` among tori implies its maximality among split tori.
This adapter matches the hypothesis of the published
`RelativeRootReflectionExistenceStatement` and of
`RelativeCharacterRootComplementStatement`.

## Uniqueness of the coroot

`preReflection_rootVector_of_weylAction` rationalizes a reflection law. Let
`n` be a normalizing point with
`weylAction i n χ = χ - latticePairing T χ c • γ` for an actual root `γ` and a
cocharacter `c`. Then the rational pre-reflection with vector `1 ⊗ γ` and
functional `corootFunctional i c` sends each root vector `1 ⊗ δ` to the root
vector of `weylAction i n δ`.

`coroot_eq_of_weylAction` is the uniqueness half of Milne 21.11(e), proved in
the lattice setting. Its hypotheses are that `T` is split, that
`relativeRoots i` is finite, and the spanning premise

```
Submodule.span ℚ (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤
```

(the actual roots together with the restrictions of the characters of `G`
span the rational character space). Let `n₁`, `n₂` be normalizing points
acting by the reflection formula along the same root `γ`, with cocharacters
`c₁`, `c₂` such that `⟨γ, c₁⟩ = ⟨γ, c₂⟩ = 2`. The theorem concludes
`c₁ = c₂`. The proof has four steps.

1. Both pre-reflections preserve the finite set of root vectors, which spans
   `relativeRootSpan i` (`span_range_rootVector`). Mathlib's
   `Module.Dual.eq_of_preReflection_mapsTo` therefore makes the two rational
   functionals equal, so `⟨δ, c₁⟩ = ⟨δ, c₂⟩` for every actual root `δ`.
2. The product `n₁ n₂` acts by `χ ↦ χ + (⟨χ, c₂⟩ - ⟨χ, c₁⟩) • γ`, so it fixes
   every actual root. The published
   `IsSplitTorus.weylAction_eq_one_of_fixed_roots`, which uses the spanning
   premise, then gives `weylAction i (n₁ n₂) = 1`.
3. Hence `(⟨χ, c₂⟩ - ⟨χ, c₁⟩) • γ = 0` for every character `χ`. Pairing with
   `c₁` gives `2 (⟨χ, c₂⟩ - ⟨χ, c₁⟩) = 0` in `ℤ`, so `⟨χ, c₁⟩ = ⟨χ, c₂⟩`. No
   torsion-freeness argument is needed.
4. Right injectivity of the perfect pairing `latticePairing T`
   (`IsSplitTorus.isPerfPair_latticePairing`) gives `c₁ = c₂`.

## The root permutation and the coroot stability

`weylRootPerm i n` is the permutation of `relativeRoots i` given by
`weylAction i n`. Its inverse is given by `n⁻¹`, and roots go to roots by the
published `weylAction_mapsTo_relativeRoots`. `coe_weylRootPerm` is its value.

The published structure `RelativeRootReflectionData i` gives, for each actual
root `α`, a cocharacter `D.coroot α` with `⟨α, D.coroot α⟩ = 2` and a
normalizing point `D.representative α` acting by the reflection formula. For
such data `D`, this module proves:

* `weylAction_representative_involutive` and `weylAction_inv_representative`:
  the action of `D.representative α` is an involution, so its inverse acts in
  the same way.
* `reflectedCoroot α β := D.coroot β - ⟨α, D.coroot β⟩ • D.coroot α`, the
  cocharacter `s_α^∨(β^∨)`.
* `weylAction_conj`: the conjugate `n_α n_β n_α⁻¹` acts by the reflection
  formula along `s_α(β)` with cocharacter `reflectedCoroot α β`.
  `pairing_reflectedCoroot` gives `⟨s_α(β), s_α^∨(β^∨)⟩ = 2`.
* `coroot_weylRootPerm`: for split `T`, finite roots and the spanning
  premise, `D.coroot (s_α β) = reflectedCoroot α β`. This follows from
  `coroot_eq_of_weylAction` applied to `D.representative (s_α β)` and the
  conjugate. It is the coroot axiom `reflectionPerm_coroot` of a root pairing.
* `coroot_injective`: for split `T` and finite roots, `D.coroot` is injective.
  This follows from the published `corootFunctional_injective`.

## The root datum

`RelativeRootReflectionData.rootDatum D hT hfinite hspan` is a
`RootDatum (relativeRoots i) (characterLattice T) (cocharacterLattice T)` with
the following data:

* pairing `latticePairing T`, perfect by `IsSplitTorus.isPerfPair_latticePairing`;
* roots the inclusion `Function.Embedding.subtype` of the actual roots;
* coroots `D.coroot`, an embedding by `coroot_injective`;
* `root_coroot_two` from `D.pair_self`;
* reflection permutations `weylRootPerm i (D.representative α)`, with the root
  axiom from `D.action` and the coroot axiom from `coroot_weylRootPerm`.

The index type `relativeRoots i` is finite under `hfinite`. The simp lemmas
`rootDatum_toLinearMap`, `rootDatum_root` and `rootDatum_coroot` record the
data. `rootDatum_reflection` identifies `P.reflection α` with
`weylAction i (D.representative α)`.

`isRootDatumOf_rootDatum` proves the full published `IsRootDatumOf i` for
this root datum:

* the pairing is `latticePairing T` (`rfl`);
* `Set.range P.root = roots i`, by `Subtype.range_coe` and the definitional
  equality `relativeRoots i = roots i`;
* each reflection `P.reflection α` is `characterAut σ` for the normalizing
  point `D.representative α` and `σ := normalizingAut i (D.representative α)`,
  with `IsNormalizingPoint` from the published
  `isNormalizingPoint_normalizingAut`. The equality comes from
  `rootDatum_reflection`, because the published `weylAction` is
  definitionally `characterAut (normalizingAut i n)`.

Reducedness is proved under either of two explicit hypotheses:

* `isReduced_rootDatum`: if `2 • α ∉ relativeRoots i` for every actual root
  `α`, then the root datum is reduced, by
  `RootPairing.isReduced_of_two_smul_notMem`.
* `isReduced_rootDatum_of_eq_or_eq_neg`: if any two actual roots `α`, `β` that
  are not linearly independent over `ℤ` satisfy `α = β ∨ α = -β`, then the
  root datum is reduced. This is the field of `RootPairing.IsReduced`
  verbatim.

## Conditional existence

`exists_rootDatum_of_reflectionData` and
`exists_rootDatum_of_reflectionData_of_eq_or_eq_neg` share most of their
hypotheses: `hG : IsConnectedReductive G`, a split `T`,
`D : RelativeRootReflectionData i` and the spanning premise. The first also
takes `∀ α ∈ roots i, (2 : ℤ) • α ∉ roots i`. The second also takes
`∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β] → α = β ∨ α = -β`.
Each concludes the body of `RootDatumExistenceStatement`:

```
∃ (J : Type u) (_ : Finite J)
  (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
  IsRootDatumOf i P ∧ P.IsReduced
```

Here `J := relativeRoots i`. Finiteness comes from the published
`IsSplitTorus.finite_relativeRoots`. Its local-finite-type instance comes
from the smoothness field of `IsConnectedReductive`. Neither theorem uses
maximality of `i` itself. In the intended final proof, `D` comes from
`RelativeRootReflectionExistenceStatement` applied with
`IsMaximalTorus.isMaximalSplitTorus`, the spanning premise from
`RelativeCharacterRootComplementStatement`, and reducedness from a separate
reducedness statement for the roots of a split maximal torus (Milne
21.11(b)).

## Provenance

The mathematics follows Milne 21.11(e) (uniqueness of the coroot) and 21.12
(the root datum axioms and reducedness). Milne's argument that the reflections
preserve `Φ` and the coroots is replaced by `D.action`, the published root
stability under the Weyl action, and the uniqueness argument above. Mathlib's
`RootDatum` also asks for the coroot axiom `reflectionPerm_coroot` and for
injective coroots, and both are proved here. Milne's axiom (rd3), finiteness
of the Weyl group, is not a field of Mathlib's `RootDatum`. Its role is taken
by the finite index type `relativeRoots i`. The spanning premise, the reflection
data, the Coxeter-weight reducedness criterion and the split-maximal adapter
are internal interfaces of the published architecture. Axioms: `propext`,
`Classical.choice`, `Quot.sound`.
