# Renard A.IX: a support partition splits every subquotient of a split object

Author: Worker 1074.

This module proves the unchanged public
`Langlands.Renard.SimpleSupportPartitionSubquotientStatement` from
`Langlands.CategoryTheory.Renard.SimpleSupportSplittingSubquotientsStatements`.
All declarations are in namespace `Langlands.Renard`. The closing theorem is

```lean
theorem simpleSupportPartitionSubquotient
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportPartitionSubquotientStatement.{r,w,v,u} C
```

with independent level parameters `r w v u`: the source family universe,
the partition index universe, the Hom universe and the object universe.
Two reusable helper lemmas accompany it. The proof shows that the actual
canonical map `simpleSupportPartitionDesc S Y` is both monic and epic, and
concludes with `isIso_of_mono_of_epi`.

## Source and relation to the source proof

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, A.IX, the
unnumbered lemma after the boxed splitting definition, printed268/PDF274.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1074 read PDF274 in full. The lemma says that if
`Irr(M) = ⨆_α S_α` splits `E`, then every subquotient of `E` is split
by the same decomposition.

Renard writes `E = ⨁_α E_α`, says it is clear that it suffices to treat a
subobject `L` of `E`, and shows `L = ⨁_α (E_α ∩ L)`. He puts
`C = L / ⨁_α (E_α ∩ L)` and proves, for every `α`,

```
JH(C) ⊂ JH(L / (E_α ∩ L)) ⊂ JH(E / E_α) ⊂ ⋃_{β≠α} JH(E_β) ⊂ Irr(M) \ S_α,
```

so `JH(C)` is empty and `C = 0`. The passage from subobjects to
quotients is left to the reader.

The Lean proof works directly at the subquotient `Y`, presented by an
actual monomorphism `j : N ⟶ X` and an actual epimorphism `p : N ⟶ Y`,
and treats subobjects and quotients at once. It never forms the
intersections `E_α ∩ L` as summands. Instead it proves separately that
the canonical map `φ : ∐ i, Y_(S i) ⟶ Y` has zero kernel and zero
cokernel, where `Y_(S i)` is the public `simpleSupportSum (S i) Y`.

- The epimorphism part is the source chain, transported to `Y`. Its
  cokernel `Q = Y / ∑_i Y_(S i)` plays the role of Renard's `C`, and
  the chain of simple-class inclusions below runs through
  `N / (N ∩ X_α)` and `X / X_α` exactly as Renard's runs through
  `L / (E_α ∩ L)` and `E / E_α`.
- The monomorphism part is internal to the formalization: Renard writes
  the direct sum `⨁_α (E_α ∩ L)` inside `L`, which presupposes that the
  canonical map from the coproduct is monic. Here monicity is proved by
  the same "no simple subquotient" device and does not use the
  splitting of `X`.

Both parts use the cokernel of one coproduct injection in place of
Renard's `E / E_α`. Its simple classes come from the other summands,
which is the step `JH(E / E_α) ⊂ ⋃_{β≠α} JH(E_β)`.

## Helper lemmas

`simpleSubquotientClasses_sigma_subset_of_small` is an internal size
adapter. For `hG : IsSourceGrothendieck.{r} C`, `SourceAB6 C`, an index
type `J : Type w` with `[Small.{r} J]`, and `F : J → C` with
`[HasCoproduct F]`, it proves

```lean
simpleSubquotientClasses (∐ F) ⊆ ⋃ j, simpleSubquotientClasses (F j)
```

The published `simpleSubquotientClasses_sigma_subset` (in
`SimpleSupportColimit`) only covers index types in `Type r`. The proof
takes `e := equivShrink.{r} J` and the Mathlib isomorphism
`Sigma.reindex e.symm F : ∐ (F ∘ e.symm) ≅ ∐ F`. Its inverse is monic,
so `simpleSubquotientClasses_subset_of_mono` moves a class of `∐ F` to
`∐ (F ∘ e.symm)`. The published lemma then places it in some
`F (e.symm k)`.

`simpleSubquotientClasses_cokernel_sigmaι_subset` has the same
hypotheses and an index `a : J`. It proves

```lean
simpleSubquotientClasses (cokernel (Sigma.ι F a)) ⊆
  ⋃ (j : J) (_ : j ≠ a), simpleSubquotientClasses (F j)
```

Let `G : {j // j ≠ a} → C` be the restriction of `F`. Its coproduct
exists by `hasCoproductsOfShape_of_small.{r}` from `hG.1`, since the
subtype of a `Small.{r}` type is `Small.{r}`. The map
`g := Sigma.desc fun j => Sigma.ι F j.1 ≫ cokernel.π (Sigma.ι F a)` from
`∐ G` to the cokernel is epic. Indeed, if `g ≫ h = 0` then
`cokernel.π (Sigma.ι F a) ≫ h` vanishes on every injection of `∐ F`: on
`a` by the cokernel condition, and on `i ≠ a` because it equals the
`⟨i, _⟩` component of `g ≫ h`. Hence `h = 0`, by `Sigma.hom_ext` and
cancelling the cokernel projection. The cokernel is therefore a quotient
of `∐ G`. `simpleSubquotientClasses_subset_of_epi` and the size adapter
give the result. No decomposition of `∐ F` as `F a ⊕ ∐ G` is constructed.

## The main proof

After introducing all binders of the target, the proof installs
`HasCoproducts.{r} C := hG.1` and destructs the splitting of `X` into
the partition condition `hpart`, the inner coproducts at `X`, the outer
coproduct at `X`, and invertibility of `simpleSupportPartitionDesc S X`.
At `Y` the inner coproducts and the outer coproduct over `I` come from
`hasCoproductsOfShape_of_small.{r}` and the `Small.{r}` hypotheses at `Y`
and on `I`. The conclusion is then filled with `hpart`, these two
coproduct proofs, and invertibility of `φ := simpleSupportPartitionDesc S Y`.
Since `HasCoproduct` is a proposition, the coproduct proofs used here and
in the published lemmas agree definitionally.

Three facts are used throughout.

- Support of the blocks: for `Z = X` and `Z = Y`, each
  `simpleSupportSum (S i) Z` is supported on `S i`. This is the published
  `simpleSupportSumSupport` at universe `r`, using the `Small.{r}`
  hypothesis at `Z` and `S i ⊆ simpleClasses C` from
  `IsSimpleSupportPartition.subset`.
- Zero detection: the published `simpleSubquotientEmpty` at universe `r`
  says that an object has no simple subquotient class exactly when it is
  zero.
- Covering: every simple subquotient class of any object is in
  `simpleClasses C`, which by the partition condition is `⋃ i, S i`.

To show that an object `Z` is zero it therefore suffices to show that a
class `q ∈ JH(Z)` with `q ∈ S a` cannot exist: one finds `b ≠ a` with
`q ∈ JH(Y_(S b))` or `q ∈ JH(X_(S b))`, so `q ∈ S b`, contradicting
disjointness of `S b` and `S a`.

### Monicity

By `Preadditive.mono_of_isZero_kernel` it suffices that `K := kernel φ`
is zero. Take `q ∈ JH(K)` with `q ∈ S a`. The injection `ι_a` of the
summand `Y_(S a)` satisfies `ι_a ≫ φ = (Y_(S a)).arrow`
(`ι_simpleSupportPartitionDesc`), so it is monic. The composite
`kernel.ι φ ≫ cokernel.π ι_a : K ⟶ cokernel ι_a` is monic: if
`h ≫ kernel.ι φ ≫ cokernel.π ι_a = 0`, then `Abelian.monoLift` writes
`h ≫ kernel.ι φ` as `h' ≫ ι_a`. Then
`h' ≫ (Y_(S a)).arrow = h ≫ kernel.ι φ ≫ φ = 0`, so `h' = 0` because
the subobject arrow is monic, and hence `h = 0` because `kernel.ι φ` is
monic. Transport along this monomorphism and the cokernel helper put `q`
in `JH(Y_(S b))` for some `b ≠ a`, which gives the contradiction. This
part uses neither the splitting of `X` nor the maps `j` and `p`.

### Epicity

By `Preadditive.epi_of_isZero_cokernel` it suffices that
`Q := cokernel φ` is zero. Take `q ∈ JH(Q)` with `q ∈ S a`, and write
`X_a := simpleSupportSum (S a) X` and `Y_a := simpleSupportSum (S a) Y`.
Let `P := pullback j X_a.arrow`, with `fst : P ⟶ N` and
`snd : P ⟶ X_a`; it represents `N ∩ X_a`.

1. `snd` is monic because `j` is monic, so `P` is supported on `S a`
   (`HasSimpleSupport.of_mono` and support of `X_a`). Its quotient
   `imageSubobject (fst ≫ p)` is supported on `S a`
   (`HasSimpleSupport.of_epi` with `factorThruImageSubobject`). By
   `le_simpleSupportSum` it lies below `Y_a`. Hence `fst ≫ p` factors
   through `Y_a.arrow`, and `fst ≫ p ≫ cokernel.π φ = 0`, because
   `Y_a.arrow ≫ cokernel.π φ = ι_a ≫ φ ≫ cokernel.π φ = 0`.
2. So `d := cokernel.desc fst (p ≫ cokernel.π φ) _ : cokernel fst ⟶ Q`
   exists. It is epic, since `cokernel.π fst ≫ d = p ≫ cokernel.π φ` is
   a composite of epimorphisms. This is the source step
   `JH(C) ⊂ JH(L / (E_α ∩ L))`, at the level of `Y`.
3. Mathlib's `Abelian.mono_cokernel_map_of_isPullback`, applied to the
   pullback square `IsPullback.of_hasPullback j X_a.arrow`, gives a
   monomorphism `cokernel fst ⟶ cokernel X_a.arrow`. This is the source
   step `JH(L / (E_α ∩ L)) ⊂ JH(E / E_α)`.
4. With `ι^X_a` the injection of `X_a` into `∐ i, X_(S i)`, the map
   `cokernel.desc ι^X_a (simpleSupportPartitionDesc S X ≫ cokernel.π X_a.arrow) _`
   is epic, because `simpleSupportPartitionDesc S X` is invertible by the
   splitting of `X`. So `JH(cokernel X_a.arrow) ⊆ JH(cokernel ι^X_a)`.
5. The cokernel helper gives `b ≠ a` with `q ∈ JH(X_(S b)) ⊆ S b`, the
   source step `JH(E / E_α) ⊂ ⋃_{β≠α} JH(E_β)`. This contradicts
   disjointness.

Monicity and epicity give `IsIso φ` in the abelian category, which
completes the splitting of `Y`.

## Scope and reused work

The theorem proves the complete published proposition for an arbitrary
abelian `C`, with the four universes independent. It covers empty `I`,
empty blocks, identity maps and isomorphic representatives. It uses no
smallness or coproduct at `N`, no global coproducts at size `max u v`,
no generator, finite length or concreteness. The source hypotheses are
used only through the published support, coproduct-support and
zero-detection theorems. The intersection decomposition
`L = ⨁_α (E_α ∩ L)` of the source proof is not stated or proved; the
proof establishes the target splitting of `Y` directly.

Reused by Lean name: the target statement (Workers 6 and 713), the
splitting definitions, the supported sums and their laws, and the
published proofs `simpleSupportSumSupport`,
`simpleSubquotientClasses_sigma_subset`, `simpleSubquotientEmpty`,
`simpleSubquotientClasses_subset_of_mono`/`_of_epi` and
`HasSimpleSupport.of_mono`/`.of_epi`, each by its recorded authors.
Worker 1074 authored the two helper lemmas and the main proof.

## Verification

The approved Lean service (environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`) compiled the module with zero
errors and warnings. Inspection of
`Langlands.Renard.simpleSupportPartitionSubquotient` reported a theorem
with level parameters `r, w, v, u` whose only axioms are `propext`,
`Classical.choice` and `Quot.sound`. These development checks are
separate from exact-target validation, independent semantic review and
publication.
