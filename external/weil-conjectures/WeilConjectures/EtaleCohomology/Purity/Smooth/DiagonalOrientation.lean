/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.QuasiCompact
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionThomFrames
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence

/-!
# The canonical identification of the dualizing complex of a smooth morphism

For `f : X ⟶ Y` smooth separated of pure relative dimension `d`, `Y` separated and locally of
finite type over a field, and a finite coefficient ring `Λ` with invertible exponent and a
normalized Kummer class, this file constructs an explicit isomorphism

`ω_f = Rf^! Λ_Y ≅ Λ_X(d)[2d]`

(blueprint `proposition-relative-dualizing-complex--1`). The existence of such an isomorphism is
`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`; here every step of its proof
is replaced by a concrete map, and nothing is chosen from a `Nonempty`:

1. `ω_{p₁} ≅ Lp₂^* ω_f` for the projections of `X ×_Y X` is the inverse of the canonical base
   change map of the dualizing complexes (`AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`),
   an isomorphism by smooth base change (blueprint
   `proposition-exceptional-inverse-image-smooth-morphism--7`). Pulling back along the diagonal
   gives `𝒞(p₁, Δ) ≅ ω_f`.
2. For a closed section `s` of a smooth `g : V ⟶ B` of relative dimension `c`, the purity of the
   section `Rs^!(Λ_V(c)[2c]) ≅ Λ_B` is the inverse of the adjoint of the fundamental class
   glued from the coordinate frames (`AlgebraicGeometry.Etale.thomFundamentalClassMap`), and
   `Rs^! ω_g ≅ Λ_B` is the composition isomorphism of `R^!` conjugate to that of `R_!`
   (`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIsoOfEq`).
3. These determine `𝒞(g, s) = Ls^* ω_g ≅ Λ_B(c)[2c]` through the canonical tensor maps
   `Rs^! M ⊗ Ls^* N ⟶ Rs^!(M ⊗ N)` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap`),
   which are isomorphisms at invertible `N`, and the symmetry of `⊗ᴸ`.

The Kummer class is an instance argument (`HasKummerClass Λ`, which induces the Tate twist),
rather than one chosen from a normalized Tate twist datum. The fundamental class of the
diagonal is the unique class restricting to the frame classes; in particular the isomorphism
does not depend on the structure morphism to the field
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_eq`).

## Main definitions

- `AlgebraicGeometry.Etale.dualizingComplexPullbackFstIso`: `ω_{p₁} ≅ Lp₂^* ω_f`.
- `AlgebraicGeometry.Etale.sectionInvariantDiagonalIso`: `𝒞(p₁, Δ) ≅ ω_f`.
- `AlgebraicGeometry.Etale.sectionInvariantTwistShiftIsoOfSection`: `𝒞(g, s) ≅ Λ_B(c)[2c]`.
- `AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`: `ω_f ≅ Λ_X(d)[2d]`.

## Main statements

- `AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_eq`: the isomorphism does not depend on
  the structure morphism of `Y` to a field.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product and of the tensor maps of `R^!`.
attribute [local instance high] SymmetricCategory.toBraidedCategory

/-! ### Purity of a section -/

/-- For a section `s` of `g`, `Rs^! ω_g ≅ Λ_B`: the composition isomorphism
`Rs^! Rg^! ≅ R(s ≫ g)^! = R(𝟙 B)^!` conjugate to the composition isomorphism
`R(𝟙 B)_! ≅ Rs_! ⋙ Rg_!` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIsoOfEq`),
followed by `R(𝟙 B)^! ≅ 𝟭`. -/
noncomputable def rightDerivedUpperShriekDualizingComplexIsoOfCompEqId {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (s : B ⟶ V) [HasCompactification s]
    (hs : s ≫ g = 𝟙 B) :
    (R(s)^![Λ]).obj (dualizingComplex Λ g) ≅ constantComplex Λ B :=
  (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ s).comp
      (rightDerivedUpperShriekAdjunction Λ g)) (rightDerivedUpperShriekAdjunction Λ (𝟙 B))
      (rightDerivedLowerShriekCompIsoOfEq Λ s g (𝟙 B) hs)).app (𝟙_ _) ≪≫
    (rightDerivedUpperShriekIdIso Λ B).app _

/-- Blueprint `lemma-section-normal-bundle--1`: Section invariant

For `s : B ⟶ V` admitting a compactification and invertible objects `ω`, `T` of `D(V_ét, Λ)`
with `Rs^! T ≅ Λ_B` and `Rs^! ω ≅ Λ_B`, the isomorphism

`Ls^* ω ≅ Rs^! T ⊗ Ls^* ω ≅ Rs^!(T ⊗ ω) ≅ Rs^!(ω ⊗ T) ≅ Rs^! ω ⊗ Ls^* T ≅ Ls^* T`,

through the canonical tensor maps `Rs^! M ⊗ Ls^* N ⟶ Rs^!(M ⊗ N)`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap`, the co-projection of
`lem-pur-coprojection`), which are isomorphisms for `N` invertible, and the symmetry of `⊗ᴸ`.
Unlike `AlgebraicGeometry.Etale.derivedTensorRightCompRightDerivedUpperShriekIso`, it does not
depend on a choice of tensor inverses of `ω` and `T`. -/
noncomputable def leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso {V B : Scheme.{u}}
    (s : B ⟶ V) [HasCompactification s]
    {ω T : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hω : DerivedCategory.isInvertible Λ V ω) (hT : DerivedCategory.isInvertible Λ V T)
    (θ : (R(s)^![Λ]).obj T ≅ constantComplex Λ B)
    (ε : (R(s)^![Λ]).obj ω ≅ constantComplex Λ B) :
    (L((s)^*[ModuleCat.{u + 1} Λ])).obj ω ≅ (L((s)^*[ModuleCat.{u + 1} Λ])).obj T :=
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible
    (rightDerivedUpperShriekAdjunction Λ s) T ((isInvertible_iff_exists_derivedTensor _).2 hω)
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible
    (rightDerivedUpperShriekAdjunction Λ s) ω ((isInvertible_iff_exists_derivedTensor _).2 hT)
  (derivedTensorLeftUnitor _ B _).symm ≪≫ ((derivedTensor _ B).mapIso θ.symm).app _ ≪≫
    asIso (rightDerivedUpperShriekTensorMap s T ω) ≪≫
    (R(s)^![Λ]).mapIso (derivedTensorBraidingIso _ V T ω) ≪≫
    (asIso (rightDerivedUpperShriekTensorMap s ω T)).symm ≪≫
    ((derivedTensor _ B).mapIso ε).app _ ≪≫ derivedTensorLeftUnitor _ B _

/-- **Purity for a section of a smooth morphism.** For `g : V ⟶ B` smooth of relative dimension
`c` with a closed section `s`, `B` separated and locally of finite type over a field,
`Rs^! (Λ_V(c)[2c]) ≅ Λ_B`: the inverse of the adjoint
`cl_s : Λ_B ⟶ Rs^! (Λ_V(c)[2c])` (`AlgebraicGeometry.Etale.thomFundamentalClassMap`) of the
fundamental class of `s`, glued from the classes of the coordinate frames
(`AlgebraicGeometry.Etale.hasThomFrames_of_section`). This is the isomorphism of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_tateObject_of_section`. -/
noncomputable def rightDerivedUpperShriekTateObjectIsoOfSection [HasKummerClass Λ]
    [HasKummerClass.IsNormalized Λ] {V B : Scheme.{u}} (c : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension c g] (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ V] :
    (R(s)^![Λ]).obj ((tateObject Λ V c)⟦2 * (c : ℤ)⟧) ≅ constantComplex Λ B :=
  have := SmoothOfRelativeDimension.smooth c g
  have := isIso_thomFundamentalClassMap Λ (hasThomFrames_of_section Λ c g s hs aB)
    (hasRegularZariskiFrames_of_section c g s hs) (g ≫ aB)
  (asIso (thomFundamentalClassMap Λ (hasThomFrames_of_section Λ c g s hs aB)
    (hasRegularZariskiFrames_of_section c g s hs) (g ≫ aB))).symm

/-- Blueprint `lemma-section-normal-bundle--1`: Section invariant

**The section invariant of a section of a smooth morphism.** For `g : V ⟶ B` smooth of relative
dimension `c` with a closed section `s`, `B` separated and locally of finite type over a field,
and a normalized Kummer class,

`𝒞(g, s) = Ls^* ω_g ≅ Ls^* (Λ_V(c)[2c]) ≅ Λ_B(c)[2c]`,

where the first isomorphism is
`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso` for the purity of
the section (`AlgebraicGeometry.Etale.rightDerivedUpperShriekTateObjectIsoOfSection`) and
`Rs^! ω_g ≅ Λ_B` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIsoOfCompEqId`).
This is the isomorphism of
`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_twistShift_of_section`. -/
noncomputable def sectionInvariantTwistShiftIsoOfSection [HasKummerClass Λ]
    [HasKummerClass.IsNormalized Λ] {V B : Scheme.{u}} (c : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension c g] [HasCompactification g] (s : B ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [HasInvertibleExponent Λ V] :
    sectionInvariant Λ g s ≅ (twistShift Λ B c).obj (constantComplex Λ B) :=
  have : HasInvertibleExponent Λ B := .of_hom s
  leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso Λ s
      (isInvertible_dualizingComplex Λ (d := c) g)
      ((isInvertible_tateObject Λ V c).shift (2 * (c : ℤ)))
      (rightDerivedUpperShriekTateObjectIsoOfSection Λ c g s hs aB)
      (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ g s hs) ≪≫
    leftDerivedUpperStarTateShiftIso Λ s c ≪≫ (twistShiftConstantComplexIso Λ B c).symm

/-! ### The diagonal -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f]
  [HasCompactification f] [HasInvertibleExponent Λ X]

/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism--7`: Base change for the
dualizing object of a projection

Let `W = X ×_Y X` with projections `p₁, p₂`. The square `p₂ ≫ f = p₁ ≫ f` is cartesian and `p₁`
is the base change of the smooth `f`, so the canonical base change map
`Lp₂^* ω_f ⟶ ω_{p₁}` (`AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`) is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`);
this is its inverse

`ω_{p₁} = Rp₁^! Λ_X ≅ Lp₂^* Rf^! Λ_Y = Lp₂^* ω_f`.

Smooth base change is available over a quasi-separated base `Y` for the quasi-compact base
change `p₁` of `f`. -/
noncomputable def dualizingComplexPullbackFstIso [QuasiSeparatedSpace Y] [QuasiCompact f] :
    dualizingComplex Λ (pullback.fst f f) ≅
      (L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ f) :=
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d
    (IsPullback.of_hasPullback f f).flip
  have := (isIso_dualizingComplexBaseChangeMap_iff Λ (IsPullback.of_hasPullback f f).flip).2
    inferInstance
  (asIso (dualizingComplexBaseChangeMap Λ (IsPullback.of_hasPullback f f).flip)).symm

/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism--7`: Base change for the
dualizing object of a projection

The section invariant of the diagonal `Δ : X ⟶ X ×_Y X`, a closed section of `p₁`, is the
dualizing complex of `f`: since `Δ ≫ p₂ = 𝟙 X`,

`𝒞(p₁, Δ) = LΔ^* ω_{p₁} ≅ LΔ^* Lp₂^* ω_f ≅ ω_f`,

through `AlgebraicGeometry.Etale.dualizingComplexPullbackFstIso` and
`AlgebraicGeometry.Etale.leftDerivedUpperStarCompSectionIso`. This is the isomorphism of
`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_diagonal`. -/
noncomputable def sectionInvariantDiagonalIso [QuasiSeparatedSpace Y] [QuasiCompact f] :
    sectionInvariant Λ (pullback.fst f f) (pullback.diagonal f) ≅ dualizingComplex Λ f :=
  (L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ])).mapIso
      (dualizingComplexPullbackFstIso Λ f d) ≪≫
    (leftDerivedUpperStarCompSectionIso _ _ _ (pullback.diagonal_snd f)).app _

/-- Blueprint `proposition-relative-dualizing-complex--1`: The dualizing object of a smooth morphism

For `f : X ⟶ Y` smooth separated of pure relative dimension `d`, `Y` separated and locally of
finite type over a field, and a finite coefficient ring `Λ` with invertible exponent and a
normalized Kummer class, the isomorphism

`θ : ω_f = Rf^! Λ_Y ≅ 𝒞(p₁, Δ) ≅ Λ_X(d)[2d]`

of the diagonal argument: the inverse of
`AlgebraicGeometry.Etale.sectionInvariantDiagonalIso` (smooth base change, blueprint
`proposition-exceptional-inverse-image-smooth-morphism--7`) followed by
`AlgebraicGeometry.Etale.sectionInvariantTwistShiftIsoOfSection` for the diagonal, a closed
section of the smooth projection `p₁ : X ×_Y X ⟶ X`. Every step is a concrete isomorphism, so
this is a canonical form of `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`;
it does not depend on the structure morphism `aY`
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_eq`). -/
noncomputable def dualizingComplexTwistShiftIso [HasKummerClass Λ]
    [HasKummerClass.IsNormalized Λ] [IsSeparated f] {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] :
    dualizingComplex Λ f ≅ (twistShift Λ X d).obj (constantComplex Λ X) :=
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated aY
  have : QuasiCompact f := HasCompactification.quasiCompact_of_locallyOfFiniteType f aY
  have := SmoothOfRelativeDimension.smooth d f
  have : HasInvertibleExponent Λ (pullback f f) := .of_hom (pullback.fst f f)
  (sectionInvariantDiagonalIso Λ f d).symm ≪≫
    sectionInvariantTwistShiftIsoOfSection Λ d (pullback.fst f f) (pullback.diagonal f)
      (pullback.diagonal_fst f) (f ≫ aY)

/-- The fundamental class of a closed immersion with Thom frames does not depend on the
structure morphism to a field used to construct it: it is the unique class restricting to the
frame classes (`AlgebraicGeometry.Etale.HasThomFrames.existsUnique_fundamentalClass`). -/
theorem thomFundamentalClass_eq [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]
    {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] {c : ℕ} {i : Z ⟶ X} [IsClosedImmersion i]
    (hT : HasThomFrames Λ c i) (hR : HasRegularZariskiFrames c i) {k k' : Type u} [Field k]
    [Field k'] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] (aX' : X ⟶ Spec (.of k'))
    [LocallyOfFiniteType aX'] :
    thomFundamentalClass Λ hT hR aX = thomFundamentalClass Λ hT hR aX' :=
  (hT.existsUnique_fundamentalClass hR aX).unique
    (frameRestriction_thomFundamentalClass Λ hT hR aX)
    (frameRestriction_thomFundamentalClass Λ hT hR aX')

/-- The isomorphism `ω_f ≅ Λ_X(d)[2d]` (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`)
does not depend on the structure morphism of `Y` to a field: it is determined by `f`, `d`, `Λ`
and the Kummer class. -/
theorem dualizingComplexTwistShiftIso_eq [HasKummerClass Λ]
    [HasKummerClass.IsNormalized Λ] [IsSeparated f] {k k' : Type u} [Field k] [Field k']
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    (aY' : Y ⟶ Spec (.of k')) [IsSeparated aY'] [LocallyOfFiniteType aY'] :
    dualizingComplexTwistShiftIso Λ f d aY = dualizingComplexTwistShiftIso Λ f d aY' := by
  simp only [dualizingComplexTwistShiftIso, sectionInvariantTwistShiftIsoOfSection,
    rightDerivedUpperShriekTateObjectIsoOfSection, thomFundamentalClassMap]
  have : HasInvertibleExponent Λ (pullback f f) := .of_hom (pullback.fst f f)
  simp only [thomFundamentalClass_eq Λ _ _ (pullback.fst f f ≫ f ≫ aY)
    (pullback.fst f f ≫ f ≫ aY')]

end Etale

end AlgebraicGeometry
