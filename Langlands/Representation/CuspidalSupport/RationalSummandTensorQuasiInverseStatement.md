# The tensor quasi-inverse of the VI.4.1 Hom equivalence: statement

Module `Langlands.Representation.CuspidalSupport.RationalSummandTensorQuasiInverseStatement`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `uF, uV`.
The module contains one **statement**, the `Prop`-valued definition
`RationalSummandTensorQuasiInverseStatement`; it proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read the passage from (VI.4.1.3) to the end of the proof of the
Theorem, printed pp.150–151 / PDF pp.156–157. The functors and the Theorem
are on printed p.150 / PDF p.156:

> Posons `R = End_G(Π) = Hom_G(Π, Π)`. Pour toute représentation lisse `(τ, E)`
> de `G`, `Hom_G(Π, τ)` est un `R`-module à droite. […]
> (VI.4.1.3) `F_Π : M(G)_[π] → M(R)_d, (τ, E) ↦ Hom_G(Π, τ)`.
> Comme `V_Π` est naturellement un `R`-module à gauche, pour tout `R`-module à
> droite unitaire `M`, on peut former `M ⊗_R V_Π`. Le groupe `G` agit sur
> `M ⊗_R V_Π` par `g · (m ⊗ f) = m ⊗ Π(g) · f` […]
> (VI.4.1.4) `G_Π : M(R)_d → M(G)_[π], M ↦ M ⊗_R V_Π`.
>
> **Théorème.** Le foncteur `F_Π` établit une équivalence de catégories entre
> `M(G)_[π]` et `M(R)_d`, un quasi-inverse étant donné par `G_Π`.

The proof (printed pp.150–151) shows that the evaluation
`ev_E : Hom_G(Π, τ) ⊗_R V_Π → E, α ⊗ w ↦ α(w)` is an isomorphism for every `τ`
in the block, and that `θ_M : M → Hom_G(V_Π, M ⊗_R V_Π)` is an isomorphism for
every unital right `R`-module `M`.

The published `RationalSummandHomEquivalenceStatement` states the first half of
the Theorem: `Π` lies in the block and `Hom(Π, ·)` is an equivalence onto unital
right `End Π`-modules. The present unit states the second half, the quasi-inverse
`G_Π`, in the same setting.

## The statement

The binders are copied from `RationalSummandHomEquivalenceStatement`: a
nonarchimedean local field `F`, a connected reductive `G` with a maximal split
torus `i`, the canonical topology on `G(F)` with the instances
`LocallyCompactSpace`, `NonarchimedeanGroup` and `T2Space`, a generic
cocharacter `ν`, the structural inputs `hStandard`, `hRoots` and `hU`, an
irreducible cuspidal `π`, an irreducible smooth `ρ` of the common norm kernel
`⁰G` and an injective `⁰G`-map `j : ρ → π|_{⁰G}`. The statement then asserts:

- the compact induction `Π = ind_{⁰G}^G ρ` lies in the inertia block
  `RationalInertiaBlock G (rationalInertiaBaseLift G π)`; call `P` the block
  object;
- for every object `τ` of the block there is a `ℤ`-linear map
  `ev : (P ⟶ τ) ⊗[ℤ] P.obj → τ.obj` with `ev (α ⊗ₜ w) = α(w)`, which is
  surjective and whose kernel is the `ℤ`-span of the elements
  `(r ≫ α) ⊗ₜ w − α ⊗ₜ r(w)` for `r ∈ End P`, `α : P ⟶ τ` and `w ∈ V_Π`.

## Formalization choices

- **The balanced tensor.** `Hom_G(Π, τ)` is a right `R`-module by
  precomposition, `α · r = r ≫ α`, and `V_Π` a left `R`-module by evaluation.
  `M ⊗_R V_Π` is the quotient of `M ⊗_ℤ V_Π` by the span of the balancing
  differences `(α · r) ⊗ w − α ⊗ r w`. (The same quotient is the Library's
  `Langlands.Algebra.NonUnitalModuleTensor.Tensor`.) Since `ℂ ⊂ R` through
  scalar endomorphisms, balancing over `R` includes `ℂ`-balancing, so this is
  Renard's `M ⊗_R V_Π`. The statement asserts that the evaluation map from
  `M ⊗_ℤ V_Π` is onto with exactly this kernel. Equivalently, the induced map
  `Hom_G(Π, τ) ⊗_R V_Π → E` is bijective. The map `ev` exists and is unique
  (pure tensors generate); it is stated existentially to avoid constructing it
  inside the statement.
- **What is stated of `G_Π`.** The `G`-action on `M ⊗_R V_Π` is through the
  second factor, so `ev` is automatically `G`-equivariant. Bijectivity of `ev` is
  therefore Renard's isomorphism `ev_E : G_Π F_Π(τ) ≅ τ`. With the published
  equivalence `F_Π`, the rest of the quasi-inverse assertion follows by formal
  category theory. Every `M` is isomorphic to some `F_Π(τ)`, so
  `G_Π(M) ≅ τ` lies in the block. The triangle identity of the tensor–Hom
  adjunction makes `θ_{F_Π(τ)}` inverse to `F_Π(ev_τ)`, and by naturality every
  `θ_M` is an isomorphism. The functor `G_Π` itself, the smoothness of
  `M ⊗_R V_Π` and the statement that it lies in the block for arbitrary `M` are
  not formalized as separate constructions.
- **Block membership.** The statement repeats the existential
  `∃ hmem : rationalInertiaBlockProperty …` of the published Theorem, so that
  `P` is the block object `⟨Π, hmem⟩`. `End P` and `P ⟶ τ` are taken in the
  block, a full subcategory of smooth representations.
- **Carriers.** `P.obj` and `τ.obj` are the underlying smooth representations;
  their carriers are coerced to types. `SmoothRep.hom α.hom w` is `α(w)`.

## Why the statement is true

This follows Renard's proof. `𝓕 = G_Π ∘ F_Π` is right exact and commutes with
direct sums, because `Π` is projective and small (published VI.4.1
Proposition `RationalSummandSmallProgeneratorStatement`) and the tensor product
is right exact. `ev_{V_Π}` is the canonical isomorphism `R ⊗_R V_Π ≅ V_Π`.
Every `τ` in the block is a cokernel of a map between direct sums of copies of
`Π`, by the progenerator property and Lemma A.VIII.2. The five lemma on
(VI.4.1.5) then shows that `ev_τ` is an isomorphism.

## Remaining obligations

The proof is a separate obligation. It needs the published
`RationalSummandSmallProgeneratorStatement` (projectivity, smallness and
generation of `Π` in the block) and the right exactness of balanced tensor
products.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceStatement` | the binders and objects of VI.4.1: `RationalInertiaBlock`, `rationalInertiaBlockProperty`, `rationalInertiaBaseLift`, `IsCuspidal`, `Induction.compactInductionFunctor`, `rationalCommonNormKernel`, `StandardCocharacterStatement`, `HasRelativeRootSystem`, `isSemidirectDecomposition_of_standardCocharacterStatement` |
| `Mathlib.LinearAlgebra.TensorProduct.Basic` | the integer tensor product `⊗[ℤ]` |
