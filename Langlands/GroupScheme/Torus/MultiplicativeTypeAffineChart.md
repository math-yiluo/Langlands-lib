# An affine fppf chart of a group of multiplicative type

Author: Worker 743 (Task 6941, `cb433511-4d2d-4361-b34b-2a0eff7b495e`).

This helper module serves the proof of
`Langlands.GroupScheme.MultiplicativeTypeQuasiIsotrivialStatement` (Conrad, *Reductive group
schemes* (2014), Proposition B.3.4, pp.290–292). It begins that proof by working locally on
the base. Let `H` be a group of multiplicative type over `S`. Every point of `S` then has an
affine open neighbourhood `Spec R` over which `H` is affine and locally of finite
presentation. Moreover, a single faithfully flat ring map `R ⟶ R'` of finite presentation
splits `H` there. Conrad uses this reduction implicitly ("the problem is local on `S`").
The statements below are internal to this proof.

`IsDiagonalizable` and `IsMultiplicativeType` are the Library predicates of
`Langlands.GroupScheme.Torus.RelativeMultiplicativeType`. `IsMultiplicativeType H` asks for
an fppf cover of `S`, meaning one whose members are flat and locally of finite presentation,
over each member of which `H` is diagonalizable.

## Declarations

All names are in `Langlands.GroupScheme.RelativeMultiplicativeType`.

- `exists_affine_fppf_chart`: let `f : U ⟶ S` be flat and locally of finite presentation and
  let `u ∈ U`. Then there are an open immersion `ι : Spec R ⟶ S` with `f u` in its image, a
  faithfully flat ring map `φ : R ⟶ R'` of finite presentation, and `g : Spec R' ⟶ U` with
  `Spec.map φ ≫ ι = g ≫ f`.
- `finitePresentation_addMonoidAlgebra`: for a commutative ring `R` and a finitely generated
  abelian group `Λ`, the group algebra `AddMonoidAlgebra R Λ` is a finitely presented
  `R`-algebra.
- `diagonalizable_isAffineHom_and_lfp`: for a finitely generated abelian group `Λ`, the
  structure morphism of `diagonalizable S Λ` is affine and locally of finite presentation.
- `isAffine_and_lfp_of_faithfullyFlat`: let `G` be a group scheme over `Spec R` and
  `φ : R ⟶ R'` faithfully flat. If `G` becomes diagonalizable after base change along
  `Spec.map φ`, then the total space of `G` is affine and its structure morphism is locally
  of finite presentation.
- `IsMultiplicativeType.exists_affine_chart`: let `H` be of multiplicative type over `S` and
  `s ∈ S`. Then there is an open immersion `ι : Spec R ⟶ S` with `s` in its image such that:
  the total space of `H` base changed along `ι` is affine; its structure morphism is locally
  of finite presentation; and there is a faithfully flat ring map `φ : R ⟶ R'` of finite
  presentation such that `H` becomes diagonalizable after base change along
  `Spec.map φ ≫ ι`.

## Proofs

**Affine chart of an fppf morphism.** Choose an affine open `V ∋ f u` of `S` and an affine
open `W ∋ u` contained in `f ⁻¹ V`. Flat morphisms locally of finite presentation are open
(`Scheme.Hom.isOpenMap`), so `f(W)` is an open neighbourhood of `f u`. Choose a basic open
`D = D(r) ⊆ V` with `f u ∈ D ⊆ f(W)` (`IsAffineOpen.exists_basicOpen_le`). Then
`W' := basicOpen (f.appLE V W r)` equals `W ∩ f ⁻¹ D` (`Scheme.basicOpen_appLE`) and is
affine. Take `ι` to be the inclusion of `D`, `g` the inclusion of `W'`, and
`φ := f.appLE D W'`. The square commutes by `IsAffineOpen.SpecMap_appLE_fromSpec`. `φ` is
flat and of finite presentation by `HasRingHomProperty.appLE`. The map `Spec.map φ` is
surjective: a point `y` of `D` is `f w` for some `w ∈ W`, and that `w` then lies in `W'`.
Flat and surjective on spectra means faithfully flat (`flat_and_surjective_SpecMap_iff`).

**Group algebras.** `ℤ[Λ]` is of finite type over `ℤ` because `Λ` is finitely generated.
`ℤ` is noetherian, so `ℤ[Λ]` is finitely presented
(`Algebra.FinitePresentation.of_finiteType`). Finite presentation transfers to
`R[Λ] ≅ R ⊗ ℤ[Λ]` along `AddMonoidAlgebra.scalarTensorEquiv`.

**Diagonalizable groups.** The Library defines `diagonalizable S Λ` as the base change of
`Diagonalizable.groupScheme (ULift ℤ) Λ`, whose structure morphism is
`Spec ℤ[Λ] ⟶ Spec ℤ`. That morphism is affine (`Diagonalizable.isAffineHom`). It is locally
of finite presentation by `HasRingHomProperty.Spec_iff` and the previous lemma. Both
properties are stable under base change (`MorphismProperty.pullback_snd`).

**Descent.** Write the isomorphism over `Spec R'` as `e`. The structure morphism of the base
change of `G` factors as `e` followed by the structure morphism of `diagonalizable (Spec R') Λ`.
It is therefore affine and locally of finite presentation. `Spec.map φ` is surjective, flat
and quasi-compact. Both properties descend along such morphisms by
`MorphismProperty.of_pullback_snd_of_descendsAlong`. For `IsAffineHom` this uses the Library
module `Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent`. For
`LocallyOfFinitePresentation` it uses Mathlib's `Morphisms/LocalFlatDescent`. An affine
morphism to an affine scheme has affine source (`isAffine_of_isAffineHom`).

**The chart.** Choose a member `𝒰.f i` of the fppf cover of `S` with `s` in its image, say
`s = 𝒰.f i u`, and apply the first lemma to it. `H` is diagonalizable over the member, hence
over `Spec R'` along `g` (`IsDiagonalizable.baseChange`). The Library comparison
`Descent.pullbackComparison` with `Spec.map φ ≫ ι = g ≫ 𝒰.f i` transports this to base
change along `Spec.map φ ≫ ι`. A second application rewrites it as base change along
`Spec.map φ` of the base change along `ι`. The descent lemma then gives affineness and local
finite presentation over `Spec R`.
