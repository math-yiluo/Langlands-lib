/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Functor.MapCancelMono

/-!
# The section invariant under a monoidal change of coefficients

A change of coefficients `Ψ : D(X_ét, Λ) ⥤ D(X_ét, Λ')` with comparisons with `Le^*`, `Ri_!`
and `Ri^!` (`AlgebraicGeometry.Etale.SupportedCoefficientChange`) is *monoidal*
(`AlgebraicGeometry.Etale.MonoidalSupportedCoefficientChange`) if it comes with natural
isomorphisms `Ψ(M ⊗ᴸ N) ≅ Ψ M ⊗ᴸ Ψ N` compatible with the left unitors, the symmetries and the
tensor maps `Ri^! M ⊗ᴸ Li^* N ⟶ Ri^!(M ⊗ᴸ N)` of closed immersions (the expected behaviour of
the derived extension of scalars). We show that a monoidal change of coefficients preserves the
section invariant construction `Ls^* ω ≅ Ls^* T`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso`), which is the
hypothesis `hL` of
`AlgebraicGeometry.Etale.SupportedCoefficientChange.map_dualizingComplexTwistShiftIso`
(blueprint `proposition-relative-dualizing-complex--1`,
`proposition-compatibility-purity-change-coefficients`).

## Main definitions

- `AlgebraicGeometry.Etale.MonoidalSupportedCoefficientChange`: a monoidal change of
  coefficients.

## Main statements

In the namespace `AlgebraicGeometry.Etale.MonoidalSupportedCoefficientChange`:

- `map_leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso`, `preservesSectionInvariantIso`: a
  monoidal change of coefficients preserves the section invariant construction.
- `map_dualizingComplexTwistShiftIso`: the canonical orientation `ω_f ≅ Λ_X(d)[2d]` is
  compatible with a monoidal change of coefficients carrying frame classes to frame classes,
  provided the smooth base change `𝒞(p₁, Δ) ≅ ω_f` and the composition isomorphism
  `RΔ^! ω_{p₁} ≅ Λ_X` are.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the definitions of
-- the derived tensor product, of the tensor maps of `R^!` and of the section invariant.
attribute [local instance high] SymmetricCategory.toBraidedCategory

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

section TensorMap

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasCompactification f]

/-- The tensor map `Rf^! M ⊗ᴸ Lf^* N ⟶ Rf^!(M ⊗ᴸ N)` is natural in `M`. -/
@[reassoc]
lemma rightDerivedUpperShriekTensorMap_naturality_left {M M' : 𝐃(Y, Λ)} (φ : M ⟶ M')
    (N : 𝐃(Y, Λ)) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map ((R(f)^![Λ]).map φ)).app _ ≫
        rightDerivedUpperShriekTensorMap f M' N =
      rightDerivedUpperShriekTensorMap f M N ≫
        (R(f)^![Λ]).map (((derivedTensor (ModuleCat.{u + 1} Λ) Y).map φ).app N) :=
  Adjunction.projectionTensorMap_naturality_left _ _
    (projectionMap_app_app_naturality_left f) φ N

/-- The tensor map `Rf^! M ⊗ᴸ Lf^* N ⟶ Rf^!(M ⊗ᴸ N)` is natural in `N`. -/
@[reassoc]
lemma rightDerivedUpperShriekTensorMap_naturality_right (M : 𝐃(Y, Λ)) {N N' : 𝐃(Y, Λ)}
    (ψ : N ⟶ N') :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map ψ) ≫
        rightDerivedUpperShriekTensorMap f M N' =
      rightDerivedUpperShriekTensorMap f M N ≫
        (R(f)^![Λ]).map (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj M).map ψ) :=
  Adjunction.projectionTensorMap_naturality_right _ _
    (projectionMap_app_app_naturality_right f) M ψ

variable (Λ) in
/-- The section invariant construction
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso`)
`Ls^* ω ≅ Ls^* T`, followed by `Ls^* T ≅ Λ_B ⊗ Ls^* T ≅ Rs^! ω ⊗ Ls^* T ⟶ Rs^!(ω ⊗ T)`, is
`Ls^* ω ≅ Λ_B ⊗ Ls^* ω ≅ Rs^! T ⊗ Ls^* ω ⟶ Rs^!(T ⊗ ω) ≅ Rs^!(ω ⊗ T)`. -/
lemma leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso_hom_comp {V B : Scheme.{u}}
    (s : B ⟶ V) [HasCompactification s] {ω T : 𝐃(V, Λ)}
    (hω : DerivedCategory.isInvertible Λ V ω) (hT : DerivedCategory.isInvertible Λ V T)
    (θ : (R(s)^![Λ]).obj T ≅ constantComplex Λ B)
    (ε : (R(s)^![Λ]).obj ω ≅ constantComplex Λ B) :
    (leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso Λ s hω hT θ ε).hom ≫
        (derivedTensorLeftUnitor _ B _).inv ≫ ((derivedTensor _ B).map ε.inv).app _ ≫
          rightDerivedUpperShriekTensorMap s ω T =
      (derivedTensorLeftUnitor _ B _).inv ≫ ((derivedTensor _ B).map θ.inv).app _ ≫
        rightDerivedUpperShriekTensorMap s T ω ≫
          (R(s)^![Λ]).map (derivedTensorBraidingIso _ V T ω).hom := by
  simp only [leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, asIso_hom, asIso_inv, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, IsIso.inv_hom_id,
    Category.comp_id]

end TensorMap

variable (Λ Λ' : Type (u + 1)) [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']
  [HasTateTwist Λ] [HasTateTwist Λ']

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

A *monoidal* change of coefficients: a change of coefficients with comparisons with `Le^*`,
`Ri_!` and `Ri^!` (`AlgebraicGeometry.Etale.SupportedCoefficientChange`) together with natural
isomorphisms `Ψ(M ⊗ᴸ N) ≅ Ψ M ⊗ᴸ Ψ N` compatible with the left unitors (through
`Ψ Λ_X ≅ Λ'_X`), with the symmetries of `⊗ᴸ` and with the tensor maps
`Ri^! M ⊗ᴸ Li^* N ⟶ Ri^!(M ⊗ᴸ N)` of closed immersions (through the comparisons with `Ri^!` and
`Li^*`). -/
structure MonoidalSupportedCoefficientChange extends SupportedCoefficientChange Λ Λ' where
  /-- The change of coefficients of a derived tensor product. -/
  tensorIso (X : Scheme.{u}) (M N : 𝐃(X, Λ)) :
    (functor X).obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj N) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj ((functor X).obj M)).obj ((functor X).obj N)
  /-- Naturality of `tensorIso` in the first variable. -/
  tensorIso_hom_naturality_left (X : Scheme.{u}) {M M' : 𝐃(X, Λ)} (φ : M ⟶ M') (N : 𝐃(X, Λ)) :
    (functor X).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).map φ).app N) ≫
        (tensorIso X M' N).hom =
      (tensorIso X M N).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).map ((functor X).map φ)).app _
  /-- Naturality of `tensorIso` in the second variable. -/
  tensorIso_hom_naturality_right (X : Scheme.{u}) (M : 𝐃(X, Λ)) {N N' : 𝐃(X, Λ)} (ψ : N ⟶ N') :
    (functor X).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).map ψ) ≫
        (tensorIso X M N').hom =
      (tensorIso X M N).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj _).map ((functor X).map ψ)
  /-- Compatibility with the left unitors. -/
  map_derivedTensorLeftUnitor (X : Scheme.{u}) (M : 𝐃(X, Λ)) :
    (functor X).map (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X M).hom =
      (tensorIso X (constantComplex Λ X) M).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).map (constantComplexIso X).hom).app _ ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ') X _).hom
  /-- Compatibility with the symmetries. -/
  map_derivedTensorBraidingIso (X : Scheme.{u}) (M N : 𝐃(X, Λ)) :
    (functor X).map (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) X M N).hom ≫
        (tensorIso X N M).hom =
      (tensorIso X M N).hom ≫ (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ') X _ _).hom
  /-- Compatibility with the tensor maps `Ri^! M ⊗ᴸ Li^* N ⟶ Ri^!(M ⊗ᴸ N)`. -/
  map_rightDerivedUpperShriekTensorMap {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M N : 𝐃(X, Λ)) :
    (functor Z).map (rightDerivedUpperShriekTensorMap i M N) ≫
        (upperShriekMap i).app (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj N) ≫
          (R(i)^![Λ']).map (tensorIso X M N).hom =
      (tensorIso Z ((R(i)^![Λ]).obj M) ((L((i)^*[ModuleCat.{u + 1} Λ])).obj N)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') Z).map ((upperShriekMap i).app M)).app _ ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ') Z).obj _).map ((pullbackIso i).hom.app N) ≫
            rightDerivedUpperShriekTensorMap i _ _

namespace MonoidalSupportedCoefficientChange

variable {Λ Λ'} (Φ : MonoidalSupportedCoefficientChange Λ Λ')

/-- The comparison `Ψ(P ⊗ᴸ A) ⟶ P' ⊗ᴸ A'` induced by `Ψ P ⟶ P'` and `Ψ A ⟶ A'`. -/
noncomputable def tensorMap {X : Scheme.{u}} {P A : 𝐃(X, Λ)} {P' A' : 𝐃(X, Λ')}
    (vP : (Φ.functor X).obj P ⟶ P') (vA : (Φ.functor X).obj A ⟶ A') :
    (Φ.functor X).obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj P).obj A) ⟶
      ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj P').obj A' :=
  (Φ.tensorIso X P A).hom ≫ ((derivedTensor (ModuleCat.{u + 1} Λ') X).map vP).app _ ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj P').map vA

/-- The left unitor `Λ_X ⊗ᴸ A ≅ A` is compatible with the change of coefficients. -/
@[reassoc]
lemma map_derivedTensorLeftUnitor_hom_comp {X : Scheme.{u}} {A : 𝐃(X, Λ)} {A' : 𝐃(X, Λ')}
    (vA : (Φ.functor X).obj A ⟶ A') :
    (Φ.functor X).map (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X A).hom ≫ vA =
      Φ.tensorMap (Φ.constantComplexIso X).hom vA ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ') X A').hom := by
  rw [Φ.map_derivedTensorLeftUnitor, tensorMap, Category.assoc, Category.assoc, Category.assoc,
    Category.assoc]
  exact congrArg (_ ≫ _ ≫ ·) (leftUnitor_naturality vA).symm

/-- The inverse of the left unitor `Λ_X ⊗ᴸ A ≅ A` is compatible with the change of
coefficients. -/
@[reassoc]
lemma map_derivedTensorLeftUnitor_inv_comp {X : Scheme.{u}} {A : 𝐃(X, Λ)} {A' : 𝐃(X, Λ')}
    (vA : (Φ.functor X).obj A ⟶ A') :
    (Φ.functor X).map (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X A).inv ≫
        Φ.tensorMap (Φ.constantComplexIso X).hom vA =
      vA ≫ (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ') X A').inv := by
  rw [← cancel_mono (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ') X A').hom, Category.assoc,
    ← map_derivedTensorLeftUnitor_hom_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Tensoring on the right with a fixed object is compatible with the change of
coefficients. -/
@[reassoc]
lemma map_derivedTensor_map_app_comp_tensorMap {X : Scheme.{u}} {P Q A : 𝐃(X, Λ)}
    {P' Q' A' : 𝐃(X, Λ')} (f : P ⟶ Q) (f' : P' ⟶ Q') (vP : (Φ.functor X).obj P ⟶ P')
    (vQ : (Φ.functor X).obj Q ⟶ Q') (vA : (Φ.functor X).obj A ⟶ A')
    (hf : (Φ.functor X).map f ≫ vQ = vP ≫ f') :
    (Φ.functor X).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).map f).app A) ≫
        Φ.tensorMap vQ vA =
      Φ.tensorMap vP vA ≫ ((derivedTensor (ModuleCat.{u + 1} Λ') X).map f').app A' := by
  rw [tensorMap, tensorMap, reassoc_of% (Φ.tensorIso_hom_naturality_left X f A), Category.assoc,
    Category.assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp, hf, Functor.map_comp,
    NatTrans.comp_app_assoc, NatTrans.naturality]

/-- The symmetry of `⊗ᴸ` is compatible with the change of coefficients. -/
@[reassoc]
lemma map_derivedTensorBraidingIso_comp_tensorMap {X : Scheme.{u}} {M N : 𝐃(X, Λ)}
    {M' N' : 𝐃(X, Λ')} (vM : (Φ.functor X).obj M ⟶ M') (vN : (Φ.functor X).obj N ⟶ N') :
    (Φ.functor X).map (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) X M N).hom ≫
        Φ.tensorMap vN vM =
      Φ.tensorMap vM vN ≫ (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ') X M' N').hom := by
  rw [tensorMap, tensorMap, reassoc_of% (Φ.map_derivedTensorBraidingIso X M N), Category.assoc,
    Category.assoc, derivedTensorBraidingIso_hom_naturality_right,
    derivedTensorBraidingIso_hom_naturality_left_assoc, NatTrans.naturality]

variable {V B : Scheme.{u}} (s : B ⟶ V) [IsClosedImmersion s]

/-- The composite `Ψ(Rs^! M) ⟶ Rs^! Ψ M ⟶ Rs^! M'` of the comparison with `Rs^!` and of
`Rs^! (Ψ M ⟶ M')`. -/
noncomputable abbrev upperShriekComp {M : 𝐃(V, Λ)} {M' : 𝐃(V, Λ')}
    (vM : (Φ.functor V).obj M ⟶ M') :
    (Φ.functor B).obj ((R(s)^![Λ]).obj M) ⟶ (R(s)^![Λ']).obj M' :=
  (Φ.upperShriekMap s).app M ≫ (R(s)^![Λ']).map vM

/-- The composite `Ψ(Ls^* M) ≅ Ls^* Ψ M ⟶ Ls^* M'` of the comparison with `Ls^*` and of
`Ls^* (Ψ M ⟶ M')`. -/
noncomputable abbrev pullbackComp {M : 𝐃(V, Λ)} {M' : 𝐃(V, Λ')}
    (vM : (Φ.functor V).obj M ⟶ M') :
    (Φ.functor B).obj ((L((s)^*[ModuleCat.{u + 1} Λ])).obj M) ⟶
      (L((s)^*[ModuleCat.{u + 1} Λ'])).obj M' :=
  (Φ.pullbackIso s).hom.app M ≫ (L((s)^*[ModuleCat.{u + 1} Λ'])).map vM

/-- The tensor maps `Rs^! M ⊗ᴸ Ls^* N ⟶ Rs^!(M ⊗ᴸ N)` are compatible with the change of
coefficients. -/
@[reassoc]
lemma map_rightDerivedUpperShriekTensorMap_comp {M N : 𝐃(V, Λ)} {M' N' : 𝐃(V, Λ')}
    (vM : (Φ.functor V).obj M ⟶ M') (vN : (Φ.functor V).obj N ⟶ N') :
    (Φ.functor B).map (rightDerivedUpperShriekTensorMap s M N) ≫
        (Φ.upperShriekMap s).app (((derivedTensor (ModuleCat.{u + 1} Λ) V).obj M).obj N) ≫
          (R(s)^![Λ']).map (Φ.tensorMap vM vN) =
      Φ.tensorMap (Φ.upperShriekComp s vM) (Φ.pullbackComp s vN) ≫
        rightDerivedUpperShriekTensorMap s M' N' := by
  simp only [upperShriekComp, pullbackComp, tensorMap, Functor.map_comp, NatTrans.comp_app,
    Category.assoc]
  rw [reassoc_of% (Φ.map_rightDerivedUpperShriekTensorMap s M N),
    ← rightDerivedUpperShriekTensorMap_naturality_left_assoc,
    ← rightDerivedUpperShriekTensorMap_naturality_right, NatTrans.naturality_assoc]

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

**A monoidal change of coefficients preserves the section invariant construction.** For a
closed immersion `s : B ⟶ V`, identifications `vω : Ψ ω ≅ ω'`, `vT : Ψ T ≅ T'` of invertible
objects and corresponding isomorphisms `θ : Rs^! T ≅ Λ_B`, `θ' : Rs^! T' ≅ Λ'_B` and
`ε : Rs^! ω ≅ Λ_B`, `ε' : Rs^! ω' ≅ Λ'_B`, the isomorphisms `Ls^* ω ≅ Ls^* T`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso`) over `Λ` and
`Λ'` correspond. After composing with the isomorphism
`Ls^* T ≅ Λ_B ⊗ Ls^* T ≅ Rs^! ω ⊗ Ls^* T ≅ Rs^!(ω ⊗ T)`, the construction becomes
`Ls^* ω ≅ Λ_B ⊗ Ls^* ω ≅ Rs^! T ⊗ Ls^* ω ≅ Rs^!(T ⊗ ω) ≅ Rs^!(ω ⊗ T)`; both are composites of
unitors, of the given isomorphisms, of tensor maps of `Rs^!` and of `Rs^!` of the symmetry,
each of which is compatible with the change of coefficients. -/
theorem map_leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso {ω T : 𝐃(V, Λ)}
    {ω' T' : 𝐃(V, Λ')} (vω : (Φ.functor V).obj ω ≅ ω') (vT : (Φ.functor V).obj T ≅ T')
    (hω : DerivedCategory.isInvertible Λ V ω) (hT : DerivedCategory.isInvertible Λ V T)
    (hω' : DerivedCategory.isInvertible Λ' V ω') (hT' : DerivedCategory.isInvertible Λ' V T')
    (θ : (R(s)^![Λ]).obj T ≅ constantComplex Λ B) (ε : (R(s)^![Λ]).obj ω ≅ constantComplex Λ B)
    (θ' : (R(s)^![Λ']).obj T' ≅ constantComplex Λ' B)
    (ε' : (R(s)^![Λ']).obj ω' ≅ constantComplex Λ' B)
    (hθ : (Φ.functor B).map θ.hom ≫ (Φ.constantComplexIso B).hom =
      ((Φ.upperShriekMap s).app T ≫ (R(s)^![Λ']).map vT.hom) ≫ θ'.hom)
    (hε : (Φ.functor B).map ε.hom ≫ (Φ.constantComplexIso B).hom =
      ((Φ.upperShriekMap s).app ω ≫ (R(s)^![Λ']).map vω.hom) ≫ ε'.hom) :
    (Φ.functor B).map (leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso Λ s hω hT θ ε).hom ≫
        (Φ.pullbackIso s).hom.app T ≫ (L((s)^*[ModuleCat.{u + 1} Λ'])).map vT.hom =
      (Φ.pullbackIso s).hom.app ω ≫ (L((s)^*[ModuleCat.{u + 1} Λ'])).map vω.hom ≫
        (leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso Λ' s hω' hT' θ' ε').hom := by
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible
    (rightDerivedUpperShriekAdjunction Λ' s) ω' ((isInvertible_iff_exists_derivedTensor _).2 hT')
  -- the squares of `Ls^* ω ≅ Λ_B ⊗ Ls^* ω ≅ Rs^! T ⊗ Ls^* ω ⟶ Rs^!(T ⊗ ω) ≅ Rs^!(ω ⊗ T)`
  have h₁ : (Φ.functor B).map θ.inv ≫ Φ.upperShriekComp s vT.hom =
      (Φ.constantComplexIso B).hom ≫ θ'.inv := by
    rw [← cancel_epi ((Φ.functor B).map θ.hom), ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hθ, Iso.hom_inv_id,
      Category.comp_id]
  have sq₀ : CommSq ((Φ.functor B).map (derivedTensorLeftUnitor _ B _).inv)
      (Φ.pullbackComp s vω.hom)
      (Φ.tensorMap (Φ.constantComplexIso B).hom (Φ.pullbackComp s vω.hom))
      (derivedTensorLeftUnitor _ B _).inv :=
    ⟨Φ.map_derivedTensorLeftUnitor_inv_comp _⟩
  have sq₁ : CommSq ((Φ.functor B).map (((derivedTensor _ B).map θ.inv).app _))
      (Φ.tensorMap (Φ.constantComplexIso B).hom (Φ.pullbackComp s vω.hom))
      (Φ.tensorMap (Φ.upperShriekComp s vT.hom) (Φ.pullbackComp s vω.hom))
      (((derivedTensor _ B).map θ'.inv).app _) :=
    ⟨Φ.map_derivedTensor_map_app_comp_tensorMap θ.inv θ'.inv _ _ _ h₁⟩
  have sq₂ : CommSq ((Φ.functor B).map (rightDerivedUpperShriekTensorMap s T ω))
      (Φ.tensorMap (Φ.upperShriekComp s vT.hom) (Φ.pullbackComp s vω.hom))
      ((Φ.upperShriekMap s).app (((derivedTensor (ModuleCat.{u + 1} Λ) V).obj T).obj ω) ≫
        (R(s)^![Λ']).map (Φ.tensorMap vT.hom vω.hom))
      (rightDerivedUpperShriekTensorMap s T' ω') :=
    ⟨Φ.map_rightDerivedUpperShriekTensorMap_comp s vT.hom vω.hom⟩
  have sq₃ : CommSq ((Φ.functor B).map ((R(s)^![Λ]).map (derivedTensorBraidingIso _ V T ω).hom))
      ((Φ.upperShriekMap s).app (((derivedTensor (ModuleCat.{u + 1} Λ) V).obj T).obj ω) ≫
        (R(s)^![Λ']).map (Φ.tensorMap vT.hom vω.hom))
      ((Φ.upperShriekMap s).app (((derivedTensor (ModuleCat.{u + 1} Λ) V).obj ω).obj T) ≫
        (R(s)^![Λ']).map (Φ.tensorMap vω.hom vT.hom))
      ((R(s)^![Λ']).map (derivedTensorBraidingIso _ V T' ω').hom) := by
    have hn := (Φ.upperShriekMap s).naturality (derivedTensorBraidingIso _ V T ω).hom
    simp only [Functor.comp_obj, Functor.comp_map] at hn
    refine ⟨?_⟩
    rw [reassoc_of% hn, ← Functor.map_comp, Φ.map_derivedTensorBraidingIso_comp_tensorMap,
      Functor.map_comp, Category.assoc]
  -- the squares of `Ls^* T ≅ Λ_B ⊗ Ls^* T ≅ Rs^! ω ⊗ Ls^* T ⟶ Rs^!(ω ⊗ T)`
  have h₅ : (Φ.functor B).map ε.inv ≫ Φ.upperShriekComp s vω.hom =
      (Φ.constantComplexIso B).hom ≫ ε'.inv := by
    rw [← cancel_epi ((Φ.functor B).map ε.hom), ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hε, Iso.hom_inv_id,
      Category.comp_id]
  have sq₆ : CommSq ((Φ.functor B).map (derivedTensorLeftUnitor _ B _).inv)
      (Φ.pullbackComp s vT.hom)
      (Φ.tensorMap (Φ.constantComplexIso B).hom (Φ.pullbackComp s vT.hom))
      (derivedTensorLeftUnitor _ B _).inv :=
    ⟨Φ.map_derivedTensorLeftUnitor_inv_comp _⟩
  have sq₅ : CommSq ((Φ.functor B).map (((derivedTensor _ B).map ε.inv).app _))
      (Φ.tensorMap (Φ.constantComplexIso B).hom (Φ.pullbackComp s vT.hom))
      (Φ.tensorMap (Φ.upperShriekComp s vω.hom) (Φ.pullbackComp s vT.hom))
      (((derivedTensor _ B).map ε'.inv).app _) :=
    ⟨Φ.map_derivedTensor_map_app_comp_tensorMap ε.inv ε'.inv _ _ _ h₅⟩
  have sq₄ : CommSq ((Φ.functor B).map (rightDerivedUpperShriekTensorMap s ω T))
      (Φ.tensorMap (Φ.upperShriekComp s vω.hom) (Φ.pullbackComp s vT.hom))
      ((Φ.upperShriekMap s).app (((derivedTensor (ModuleCat.{u + 1} Λ) V).obj ω).obj T) ≫
        (R(s)^![Λ']).map (Φ.tensorMap vω.hom vT.hom))
      (rightDerivedUpperShriekTensorMap s ω' T') :=
    ⟨Φ.map_rightDerivedUpperShriekTensorMap_comp s vω.hom vT.hom⟩
  have hM := (sq₀.horiz_comp (sq₁.horiz_comp (sq₂.horiz_comp sq₃))).w
  have hK := (sq₆.horiz_comp (sq₅.horiz_comp sq₄)).w
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp] at hM
  rw [← Functor.map_comp, ← Functor.map_comp] at hK
  -- `Ls^* T' ≅ Λ_B ⊗ Ls^* T' ≅ Rs^! ω' ⊗ Ls^* T' ≅ Rs^!(ω' ⊗ T')` is a monomorphism
  have : Mono ((derivedTensorLeftUnitor _ B _).inv ≫ ((derivedTensor _ B).map ε'.inv).app _ ≫
      rightDerivedUpperShriekTensorMap s ω' T') := inferInstance
  simpa only [pullbackComp, Category.assoc] using (Φ.functor B).map_comp_eq_comp_of_mono
    (leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso_hom_comp Λ s hω hT θ ε)
    (leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso_hom_comp Λ' s hω' hT' θ' ε') hK hM

/-- A monoidal change of coefficients preserves the section invariant construction at every
closed immersion
(`AlgebraicGeometry.Etale.SupportedCoefficientChange.PreservesSectionInvariantIso`). -/
theorem preservesSectionInvariantIso :
    Φ.toSupportedCoefficientChange.PreservesSectionInvariantIso s :=
  fun vω vT hω hT hω' hT' θ ε θ' ε' hθ hε ↦
    Φ.map_leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso s vω vT hω hT hω' hT' θ ε θ' ε' hθ hε

end MonoidalSupportedCoefficientChange

namespace MonoidalSupportedCoefficientChange

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']
  [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasKummerClass Λ']
  [HasKummerClass.IsNormalized Λ'] (Φ : MonoidalSupportedCoefficientChange Λ Λ')

/-- Blueprint `proposition-relative-dualizing-complex--1`,
`proposition-compatibility-purity-change-coefficients`

**The canonical orientation `ω_f ≅ Λ_X(d)[2d]` is compatible with a monoidal change of
coefficients** (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`), as soon as the change
of coefficients carries the frame classes of the diagonal over `Λ` to those over `Λ'`
(`hframe`), and the smooth base change identifications `𝒞(p₁, Δ) ≅ ω_f` (`hC`) and the
composition isomorphisms `RΔ^! ω_{p₁} ≅ Λ_X` (`hε`) correspond: this is
`AlgebraicGeometry.Etale.SupportedCoefficientChange.map_dualizingComplexTwistShiftIso`, whose
remaining hypothesis is
`AlgebraicGeometry.Etale.MonoidalSupportedCoefficientChange.preservesSectionInvariantIso`. -/
theorem map_dualizingComplexTwistShiftIso {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f] [HasCompactification f] [IsSeparated f]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiSeparatedSpace Y]
    [QuasiCompact f] [HasInvertibleExponent Λ (pullback f f)]
    [HasInvertibleExponent Λ' (pullback f f)]
    (vω : (Φ.functor X).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ' f)
    (vω₁ : (Φ.functor (pullback f f)).obj (dualizingComplex Λ (pullback.fst f f)) ≅
      dualizingComplex Λ' (pullback.fst f f))
    (hframe : ∀ F : (pullback.diagonal f).EtaleFrame d, IsOpenImmersion F.e →
      Φ.mapSupportedClass _ (Φ.tateShiftIso F.U d) (frameClass Λ F) = frameClass Λ' F)
    (hC : (Φ.functor X).map (sectionInvariantDiagonalIso Λ f d).hom ≫ vω.hom =
      ((Φ.pullbackIso (pullback.diagonal f)).hom.app _ ≫
          (L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ'])).map vω₁.hom) ≫
        (sectionInvariantDiagonalIso Λ' f d).hom)
    (hε : (Φ.functor X).map (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ
          (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)).hom ≫
        (Φ.constantComplexIso X).hom =
      ((Φ.upperShriekMap (pullback.diagonal f)).app (dualizingComplex Λ (pullback.fst f f)) ≫
          (R(pullback.diagonal f)^![Λ']).map vω₁.hom) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ' (pullback.fst f f)
          (pullback.diagonal f) (pullback.diagonal_fst f)).hom) :
    (Φ.functor X).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        (Φ.twistShiftConstantComplexIso X d).hom =
      vω.hom ≫ (dualizingComplexTwistShiftIso Λ' f d aY).hom :=
  Φ.toSupportedCoefficientChange.map_dualizingComplexTwistShiftIso f d aY vω vω₁ hframe hC hε
    (Φ.preservesSectionInvariantIso _)

end MonoidalSupportedCoefficientChange

end Etale

end AlgebraicGeometry
