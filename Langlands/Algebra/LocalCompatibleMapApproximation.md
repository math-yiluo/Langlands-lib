# Simultaneous local approximation of a module map from Stacks 00QV

This module reduces the published proposition
`LocalCompatibleMapApproximationExistenceStatement` (first paragraph of the
proof of Stacks 046Y) to the published ring-system existence proposition
`LocalAlgebraApproximationExistenceStatement` (Stacks 00QV). The reduction is
the theorem
`localCompatibleMapApproximationExistence_of_localAlgebraApproximationExistence`.
It takes the 00QV proposition as a hypothesis and does not prove 00QV. The
module also collects the helper results the reduction uses. All of them use the
published structures `LocalAlgebraSystem`, `LocalModuleSystem`,
`LocalModuleSystem.CompatibleMap`, `CompatibleMap.cokernelSystem` and the
published constructions of `Langlands.Algebra.LocalModuleApproximation`
(`tail`, `mapAlgEquiv`, `mapLinearEquiv`, `freeSystem`, `matrixMap`,
`cokernelSystem_isApproximation`, `exists_matrix_presentation`) unchanged.

## Source and provenance

The motivating source is the registered original
`stacks-algebra-flatness-criteria-2026-10-22` (content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`).

- `046Y.html` (also `00R3.html`), proof of Lemma 10.128.4 (tag 046Y), first
  sentence. "By Lemma 10.127.13 and its proof" it finds one system
  `R_λ → S_λ` of local ring maps with maps of `S_λ`-modules
  `u_λ : M_λ → N_λ`. Conditions (1)–(6) of that lemma hold for both `M` and
  `N`, and the colimit of the `u_λ` is `u`. The source gives no further detail.
- `00QL.html`, proof of Lemma 10.127.13 (tag 00QX). It starts from a ring
  system as in Lemma 10.127.11 (00QV). It lifts a presentation matrix `A` of `M`
  to some `S_{λ₂}` and takes `M_λ = Coker(A_λ)` for `λ ≥ λ₂`. It ends with
  "We leave it to the reader to see that this works."

The declarations here are an internal construction that carries out the
argument "by the proof of 00QX" for two modules and a map at once. They form no
separately numbered source result. The route is as follows. Choose matrix
presentations `A` of `M` and `A'` of `N`. Lift `f` to matrices `B` and `C` with
`A' B = C A`. Descend all four matrices to one ring component, and make the
relation `A' B = C A` hold there. Pass to the tail above that index. Then the
component maps `u_λ` are the maps of cokernels induced by the images of `C`.

`cokernelSystem_moduleColimitMap_bijective` is Worker 293's proof from their
unpublished draft for task d4f3a655 (revision 3, file
`LocalModuleApproximationExistence.lean`). It is reproduced here unchanged,
with Worker 293 as coauthor. The published helper module leaves this colimit
comparison as an explicit hypothesis `hC`. It is an ordinary theorem here, not a
separate Prop-valued statement.

## Matrices over a ring system

In `Langlands.Algebra.LocalAlgebraSystem`, for a local algebra system `D`:

- `matrix_map_algMap_map_algι`: pushing a component matrix along a transition
  `D.algMap i j h` and then mapping to `S` gives the same matrix as mapping it
  to `S` directly. The proof applies `D.algι_compat` entrywise.
- `exists_matrix_map_algι`: if `D.algebraColimitMap` is surjective, then every
  matrix over `S` with finite row and column types is the entrywise image of a
  matrix over some component `D.alg j` with `j ≥ i₀`, for any prescribed
  `i₀`. The proof lifts the finite family of entries with the published
  `exists_algι_eq_fun` and pushes it above `i₀`.
- `exists_matrix_map_algMap_eq`: if `D.algebraColimitMap` is injective and two
  finite component matrices over `D.alg i` have the same image over `S`, then
  they agree after some transition. The proof applies the published
  `exists_algMap_eq_zero_fun` to the entrywise differences.
- `tailMatrix i₀ X`: a matrix `X` over `D.alg i₀`, pushed to every index
  `j` of the tail `D.tail i₀` (indexed by `{j // i₀ ≤ j}`). Its lemmas:
  - `tailMatrix_map`: the pushed matrices are compatible with the tail's
    transitions;
  - `tailMatrix_map_algι`: each pushed matrix has the same image over `S` as
    `X`;
  - `tailMatrix_mul`: pushing commutes with matrix products.

## Compatible maps

In `Langlands.Algebra.LocalModuleSystem.CompatibleMap`:

- `cokernelSystem_moduleColimitMap_bijective`: for `φ : CompatibleMap E F f`,
  suppose `E.moduleColimitMap` is surjective and `F.moduleColimitMap` is
  bijective. Then the additive colimit comparison of the published
  `φ.cokernelSystem` is bijective. The proof uses the published criterion
  `moduleColimitMap_bijective_of`.
  - Surjectivity: lift a representative in `N` to some `F.obj i`.
  - Injectivity: suppose a class `[n]` maps to `0` in `N ⧸ range f`. Then
    `F.ιM i n = f m`. Lift `m` to some `E.obj k` and go to a common index `l`.
    The difference `F.map n - φ.component (E.map y)` maps to `0` in `N`, so it
    dies at some `l'` by injectivity for `F`. The transported `n` is then in
    the range of `φ.component l'`.
- `cokernelSystem_isApproximation_of_isApproximation`: if
  `φ.IsApproximation` (both systems are approximation systems), then
  `φ.cokernelSystem.IsApproximation`. This is the published
  `cokernelSystem_isApproximation` with the hypothesis `hC` discharged by the
  previous result.
- `mapLinearEquiv φ eM eN f hf`: for `φ : CompatibleMap E F g` and `S`-linear
  equivalences `eM : M ≃ M'` and `eN : N ≃ N'`, take a map `f : M' → N'` with
  `f (eM x) = eN (g x)`. The same component maps then form a compatible map
  between the transported systems `E.mapLinearEquiv eM` and
  `F.mapLinearEquiv eN` over `f`. `mapLinearEquiv_isApproximation` says that
  this transport preserves `IsApproximation`, by the published lemma for
  module systems.
- `cokernelSystemMap φ₁ φ₂ γ hγ hg`: for compatible maps
  `φ₁ : CompatibleMap E₁ F₁ f₁`, `φ₂ : CompatibleMap E₂ F₂ f₂` and
  `γ : CompatibleMap F₁ F₂ g`, assume the following:
  - `hγ`: each `γ.component i` carries `range (φ₁.component i)` into
    `range (φ₂.component i)`;
  - `hg`: `g` carries `range f₁` into `range f₂`.

  Then the induced component maps of quotients (`Submodule.mapQ`) form a
  compatible map from `φ₁.cokernelSystem` to `φ₂.cokernelSystem`. It lies over
  the induced map `(range f₁).mapQ (range f₂) g hg` of target cokernels. Both
  compatibility laws are checked on quotient representatives from those of
  `γ`. `cokernelSystemMap_component_mk` says that a class `[n]` goes to
  `[γ.component i n]`.

## Lifting a map of cokernels to matrices

`Langlands.Algebra.exists_matrix_lift`: let `A` be an `n × m` matrix and `A'` an
`n' × m'` matrix over a commutative ring `S`. Every `S`-linear map
`g : (Fin n → S) ⧸ range A.mulVecLin → (Fin n' → S) ⧸ range A'.mulVecLin`
lifts as follows. There are matrices `B` (`m' × m`) and `C` (`n' × n`) with
`A' * B = C * A` and `g [v] = [C *ᵥ v]` for every `v`. The proof uses
projectivity of the free modules twice (`Module.projective_lifting_property`):

- first it lifts `g` composed with the quotient map to a linear map `c`;
- `c` then sends the image of `A` into the image of `A'`, which gives a second
  lift `b` with `A' ∘ b = c ∘ A`.

`B` and `C` are the matrices of `b` and `c` (`LinearMap.toMatrix'`).

## The reduction

`localCompatibleMapApproximationExistence_of_localAlgebraApproximationExistence`
proves
`LocalAlgebraApproximationExistenceStatement.{uR, max uS uM uN} →
LocalCompatibleMapApproximationExistenceStatement.{uR, uS, uM, uN}`. The
implemented proof has these steps:

1. **Universe transport.** Locality, the local algebra map and
   `EssFinitePresentation` pass from `S` to `ULift.{max uM uN} S`. The last uses
   the composition of the given algebra equivalence with
   `ULift.algEquiv.symm`. The hypothesis then gives an approximation system
   `D₀` for `R → ULift S` whose index and components lie in
   `Type (max uR uS uM uN)`. `D₁ := D₀.mapAlgEquiv ULift.algEquiv` is an
   approximation system for `R → S` with the same index and components, by
   `mapAlgEquiv_isApproximation`.
2. **Presentations and a matrix lift of `f`.** `exists_matrix_presentation`
   gives `eA : (Fin n → S) ⧸ range A ≃ M` and
   `eA' : (Fin n' → S) ⧸ range A' ≃ N`. `exists_matrix_lift`, applied to
   `eA'⁻¹ ∘ f ∘ eA`, gives `B` and `C` with `A' * B = C * A`.
3. **Descent to one component.** Four chained applications of
   `exists_matrix_map_algι` give, at one index `i₄`, component matrices `a₄`,
   `a'₄`, `b₄` and `c₄` mapping to `A`, `A'`, `B` and `C`. The images of
   `a'₄ * b₄` and `c₄ * a₄` over `S` agree, so `exists_matrix_map_algMap_eq`
   gives `i₅ ≥ i₄` where the pushed matrices `a`, `a'`, `b` and `c` satisfy
   `a' * b = c * a`.
4. **Tail and matrix maps.** Let `D := D₁.tail i₅`, an approximation system
   by `tail_isApproximation`. The published `matrixMap` gives three compatible
   maps between finite free systems, from the pushed matrices via
   `tailMatrix`:
   - `φA` over `A.mulVecLin`;
   - `φA'` over `A'.mulVecLin`;
   - `γ` over `C.mulVecLin`.

   The relation `a' * b = c * a`, pushed to each tail index, shows that the
   components of `γ` carry the image of `φA` into the image of `φA'`.
   Similarly `A' * B = C * A` shows that `C.mulVecLin` carries `range A` into
   `range A'`.
5. **Cokernels.** Let `ψ := cokernelSystemMap φA φA' γ`, a compatible map
   from `φA.cokernelSystem` to `φA'.cokernelSystem`. Both systems are
   approximation systems by `cokernelSystem_isApproximation_of_isApproximation`,
   since the free systems are approximation systems
   (`freeSystem_isApproximation`).
6. **Transport to `f`.** On representatives, the identity
   `g [v] = [C *ᵥ v]` from step 2 gives `f (eA x) = eA' (mapQ C x)`. So
   `ψ.mapLinearEquiv eA eA' f` is a compatible map of approximation systems
   over `f` between systems for `M` and `N` over `D`. It supplies the required
   witnesses. The index `{j // i₅ ≤ j}` and all component carriers (components
   of `D₀` and quotients of finite free modules over them) lie in
   `Type (max uR uS uM uN)`.

The theorem therefore proves the target proposition once the 00QV proposition
is available at universes `uR` and `max uS uM uN`. The 00QV proposition
`LocalAlgebraApproximationExistenceStatement.{uR, uS}` quantifies over
arbitrary ambient universes, so a universe-polymorphic proof of it covers this
instance.
