# Renard A.VIII.2: proof of the small-progenerator equivalence

Authors: Worker 923 (Lean proof and proof documentation). The target
statement and its documentation are by Worker 6 and Worker 923; they are
imported unchanged.

This proof module imports the published
`Langlands.CategoryTheory.Renard.SmallProgeneratorEquivalenceStatements` and
proves its exact target `Langlands.Renard.SmallProgeneratorEquivalenceStatement`.
The aggregate theorem is `Langlands.Renard.smallProgeneratorEquivalence`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques` (SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). The
unnumbered Théorème of A.VIII.2, printed page 267 / PDF page 273, states that
a cocomplete abelian category with a small progenerator `P` is equivalent to
unital right modules over `End_A(P)` via `Hom_A(P, •)`. Renard refers to
Pareigis [37], §4.11, Theorem 1 and gives no proof on the page. Pareigis was
not read for this proof. The Lean route below is a standard argument chosen
for this formalization. It is not taken from either text.

The published statement Markdown explains how the hypotheses are encoded.
`Abelian C` and `HasCoproducts.{v} C` give cocompleteness at the Hom size.
`HomSmallProgenerator.{v} P` is Renard's small progenerator, defined through
the actual integer-module Hom functor.

## Declarations and universes

All declarations are in namespace `Langlands.Renard`. The section context is

```lean
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{v} C] {P : C}
```

The two helpers `preadditiveCoyonedaObj_comp_eq_smul` and
`preadditiveCoyonedaObj_hom_comp` omit `HasCoproducts.{v} C`. The exported
results are:

```lean
theorem projective_of_homSmallProgenerator (hP : HomSmallProgenerator.{v} P) :
    Projective P
theorem preadditiveCoyonedaObj_faithful_of_homSmallProgenerator
    (hP : HomSmallProgenerator.{v} P) : (preadditiveCoyonedaObj P).Faithful
theorem preadditiveCoyonedaObj_preservesCoproducts_of_homSmallProgenerator
    (hP : HomSmallProgenerator.{v} P) (I : Type v) :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyonedaObj P)
theorem preadditiveCoyonedaObj_comp_eq_smul {X : C} (f : P ⟶ P)
    (x : (preadditiveCoyonedaObj P).obj X) :
    (f ≫ x : (preadditiveCoyonedaObj P).obj X) = (MulOpposite.op f : (End P)ᵐᵒᵖ) • x
theorem preadditiveCoyonedaObj_hom_comp {X : C} {M : ModuleCat.{v} (End P)ᵐᵒᵖ}
    (φ : (preadditiveCoyonedaObj P).obj X ⟶ M) (f : P ⟶ P)
    (x : (preadditiveCoyonedaObj P).obj X) :
    φ (f ≫ x) = (MulOpposite.op f : (End P)ᵐᵒᵖ) • φ x
theorem preadditiveCoyonedaObj_sigma_hom_ext (hP : HomSmallProgenerator.{v} P)
    {I : Type v} {M : ModuleCat.{v} (End P)ᵐᵒᵖ}
    {φ ψ : (preadditiveCoyonedaObj P).obj (∐ fun _ : I => P) ⟶ M}
    (h : ∀ i, φ (Sigma.ι (fun _ : I => P) i) = ψ (Sigma.ι (fun _ : I => P) i)) :
    φ = ψ
theorem preadditiveCoyonedaObj_sigma_map_surjective (hP : HomSmallProgenerator.{v} P)
    {I : Type v} {Y : C}
    (ψ : (preadditiveCoyonedaObj P).obj (∐ fun _ : I => P) ⟶
      (preadditiveCoyonedaObj P).obj Y) :
    ∃ g : (∐ fun _ : I => P) ⟶ Y, (preadditiveCoyonedaObj P).map g = ψ
theorem preadditiveCoyonedaObj_full_of_homSmallProgenerator
    (hP : HomSmallProgenerator.{v} P) : (preadditiveCoyonedaObj P).Full
noncomputable def preadditiveCoyonedaObjEvalHom (M : ModuleCat.{v} (End P)ᵐᵒᵖ) (m : M) :
    (preadditiveCoyonedaObj P).obj P ⟶ M
theorem preadditiveCoyonedaObj_exists_epi_sigma (hP : HomSmallProgenerator.{v} P)
    (M : ModuleCat.{v} (End P)ᵐᵒᵖ) :
    ∃ (I : Type v) (ε : (preadditiveCoyonedaObj P).obj (∐ fun _ : I => P) ⟶ M), Epi ε
theorem preadditiveCoyonedaObj_essSurj_of_homSmallProgenerator
    (hP : HomSmallProgenerator.{v} P) : (preadditiveCoyonedaObj P).EssSurj
theorem preadditiveCoyonedaObj_isEquivalence_of_homSmallProgenerator
    (hP : HomSmallProgenerator.{v} P) : (preadditiveCoyonedaObj P).IsEquivalence
```

The aggregate theorem lies outside the section:

```lean
theorem smallProgeneratorEquivalence (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{v} C] : SmallProgeneratorEquivalenceStatement.{v,u} C
```

Its complete type is exactly the target, with no further parameters. The
universes `u` and `v` are independent. Every coproduct index type used below
(`I`, `P ⟶ X` and the carrier of a module) lies in `Type v`. No hypothesis
beyond the target's is added. In particular `End P` may be noncommutative or
zero, and no Grothendieck or AB5 condition is used. The aggregate unfolds the
target and applies `preadditiveCoyonedaObj_isEquivalence_of_homSmallProgenerator`.
That theorem fills the three fields of Mathlib's `Functor.IsEquivalence`
(`faithful`, `full`, `essSurj`) with the three named results below.

## Implemented proof

Write `F := preadditiveCoyonedaObj P`. Its object `F.obj X` has carrier
`P ⟶ X`, `F.map g` is postcomposition with `g`, and `op r • f = r ≫ f`.

**Projectivity and faithfulness.** `hP.1.1 : HomProjective P` becomes
Mathlib's `Projective P` by the published `homProjectiveComparison`.
`hP.2 : HomGenerator P` becomes `IsSeparator P` by the published
`homGenerator_isSeparator`. Mathlib's
`isSeparator_iff_faithful_preadditiveCoyonedaObj` then makes `F` faithful.
Projectivity provides Mathlib's instance
`preservesFiniteColimits_preadditiveCoyonedaObj_of_projective`, so `F`
preserves cokernels. By
`Projective.projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj`,
`F` also preserves epimorphisms.

**Coproducts.** `hP.1.2 I` says that
`F ⋙ ModuleCat.restrictScalars (Int.castRingHom (End P)ᵐᵒᵖ)` preserves
colimits of shape `Discrete I` for `I : Type v`. Restriction of scalars
reflects isomorphisms (Mathlib, `ChangeOfRings.lean`) and preserves these
colimits, and `ModuleCat.{v} (End P)ᵐᵒᵖ` has them. So
`reflectsColimitsOfShape_of_reflectsIsomorphisms` shows that restriction
reflects them, and `preservesColimitsOfShape_of_reflects_of_preserves` shows
that `F` itself preserves them.

**Linearity in the source variable.** For `f : P ⟶ P` and `x : P ⟶ X`,
`f ≫ x = op f • x` holds by definition (`preadditiveCoyonedaObj_comp_eq_smul`).
Hence every module map `φ` out of `F.obj X` satisfies
`φ (f ≫ x) = op f • φ x` (`preadditiveCoyonedaObj_hom_comp`, by `map_smul`).

**Maps out of `F(∐_I P)`.** By coproduct preservation, `F.mapCocone` of the
chosen coproduct cofan is a colimit. Two module maps `φ ψ` out of
`F(∐_I P)` therefore agree once they agree after each `F(Sigma.ι _ i)`. On an
element `f : P ⟶ P` of `F.obj P`, that composite sends `f` to
`f ≫ Sigma.ι _ i`. By the previous paragraph its images under `φ` and `ψ`
are `op f • φ (Sigma.ι _ i)` and `op f • ψ (Sigma.ι _ i)`, which agree by the
hypothesis `h i` (`preadditiveCoyonedaObj_sigma_hom_ext`). Given a module map
`ψ : F(∐_I P) ⟶ F Y`, the morphism
`g := Sigma.desc fun i => ψ (Sigma.ι _ i)` satisfies `F.map g = ψ`. This
equality reduces by the extension lemma to `Sigma.ι _ i ≫ g = ψ (Sigma.ι _ i)`,
which is `Sigma.ι_comp_desc` (`preadditiveCoyonedaObj_sigma_map_surjective`).

**Fullness.** Let `φ : F X ⟶ F Y`. The published
`homGenerator_epi_evaluation` makes `π := Sigma.desc fun a : P ⟶ X => a`,
from `∐_{a : P ⟶ X} P`, an epimorphism. The previous step gives
`g₀ : ∐ P ⟶ Y` with `F.map g₀ = F.map π ≫ φ`. Then
`F.map (kernel.ι π ≫ g₀) = F.map (kernel.ι π ≫ π) ≫ φ = 0`, so faithfulness
gives `kernel.ι π ≫ g₀ = 0`. Mathlib's `Abelian.epiDesc` gives
`g : X ⟶ Y` with `π ≫ g = g₀`. Thus `F.map π ≫ F.map g = F.map π ≫ φ`.
`F.map π` is epi because `F` preserves epimorphisms, so `F.map g = φ`.

**Free covers of modules.** For a module `M` and `m : M`,
`preadditiveCoyonedaObjEvalHom M m : F.obj P ⟶ M` sends `f` to `op f • m`.
Additivity is `add_smul`. Linearity is `mul_smul`, since
`op (r.unop ≫ f) = r * op f` in `(End P)ᵐᵒᵖ`. Index the coproduct by the
carrier of `M`, which lies in `Type v`. The colimit property of
`F.mapCocone` gives a module map `ε : F(∐_{m : M} P) ⟶ M` whose composite
with `F(Sigma.ι _ m)` is `preadditiveCoyonedaObjEvalHom M m`. Evaluating at
`𝟙 P` gives `ε (Sigma.ι _ m) = op (𝟙 P) • m = m`. Thus `ε` is surjective, and
hence epi by `ModuleCat.epi_iff_surjective`
(`preadditiveCoyonedaObj_exists_epi_sigma`).

**Essential surjectivity.** Let `M` be a module. Take an epimorphism
`ε : F(∐_I P) ⟶ M` as above. Take a second one,
`ε' : F(∐_J P) ⟶ kernel ε`, onto the actual kernel in `ModuleCat`. The
composite `ε' ≫ kernel.ι ε` equals `F.map d` for some `d : ∐_J P ⟶ ∐_I P`,
by `preadditiveCoyonedaObj_sigma_map_surjective`. Put `X := cokernel d` in
`C`. The isomorphism `F.obj X ≅ M` is the composite of

- `PreservesCokernel.iso F d : F(cokernel d) ≅ cokernel (F.map d)`;
- `cokernelIsoOfEq hd : cokernel (F.map d) ≅ cokernel (ε' ≫ kernel.ι ε)`;
- `cokernelEpiComp ε' (kernel.ι ε)`, which removes the epimorphism `ε'`;
- the comparison `cokernel (kernel.ι ε) ≅ M` given by
  `IsColimit.coconePointUniqueUpToIso`. One side is `cokernelIsCokernel`. The
  other is `Abelian.epiIsCokernelOfKernel`, which says the epimorphism `ε`
  is a cokernel of its kernel, and is applied to `kernelIsKernel ε`.

So `M` lies in the essential image of `F`.

The Mathlib inputs are used by name at the pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`. They include
`isSeparator_iff_faithful_preadditiveCoyonedaObj`
(`CategoryTheory/Generator/Preadditive.lean`),
`preservesFiniteColimits_preadditiveCoyonedaObj_of_projective`
(`CategoryTheory/Abelian/Projective/Basic.lean`),
`Projective.projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj`
(`CategoryTheory/Preadditive/Yoneda/Projective.lean`), the colimit
reflection lemmas (`CategoryTheory/Limits/Preserves/Basic.lean`),
`Abelian.epiDesc` and `Abelian.epiIsCokernelOfKernel`
(`CategoryTheory/Abelian/Basic.lean`), and the cokernel isomorphisms
(`CategoryTheory/Limits/Shapes/Kernels.lean` and
`CategoryTheory/Limits/Preserves/Shapes/Kernels.lean`). All kernels,
cokernels and coproducts are Mathlib's actual categorical constructions.

## Scope

This unit proves only the forward equivalence. The converse (the regular
module is a small progenerator), the finite-support and finite-type
characterizations of small projectives, the presentation lemma and
comparisons with nonunital modules remain with their own Library modules and
tasks. No explicit inverse functor or `Equivalence` structure is
constructed. Mathlib's `Functor.asEquivalence` produces one from the
`IsEquivalence` instance.
