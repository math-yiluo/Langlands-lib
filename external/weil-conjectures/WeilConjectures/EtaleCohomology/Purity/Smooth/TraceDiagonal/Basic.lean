/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Isomorphisms for the trace–diagonal criterion

Isomorphisms of functors on the unbounded derived categories `D(X_ét, Λ)` of étale sheaves of
`Λ`-modules, `Λ` a finite ring, which build the unit and counit of a trace–diagonal datum
(`WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal`): the projection formula
`Rf_! L ⊗ᴸ K ≅ Rf_!(L ⊗ᴸ Lf^* K)` as an isomorphism of functors, the composition isomorphism
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` as data, `R(𝟙)_! ≅ 𝟭`, and, for a separated `f : X ⟶ Y` with
`W = X ×_Y X`, the isomorphisms `RΔ_! ≅ RΔ_! Λ_X ⊗ᴸ Lp₁^*(-)`, `𝟭 ≅ RΔ_! ⋙ Rp₂_!` and proper
base change `Rf_! ⋙ Lf^* ≅ Lp₁^* ⋙ Rp₂_!`.

## Implementation notes

The unit `Λ_X` is written `AlgebraicGeometry.Etale.derivedTensorUnit`, defined over a general
coefficient category: for `A = ModuleCat Λ`, the monoidal instance on `D(X_ét)` found by
instance search is a different term from the one inside `derivedTensor` and its unitors, and
the kernel does not compare the two in reasonable time (see
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).

Similarly, the diagonal is used in the form `AlgebraicGeometry.Etale.TraceDiagonalDatum.diagonal`,
with codomain `pullback f f` rather than the reducible synonym `pullback.diagonalObj f`: the
kernel does not compare functors on the derived categories over the two in reasonable time.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G G' : D ⥤ C}

/-- A variant of `CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit` for an isomorphism
`e` which is equal to `rightAdjointUniq adj₁ adj₂`. Applied with `he := rfl`, it avoids unifying
`e` with `rightAdjointUniq adj₁ adj₂` under the projections `Iso.hom` and `NatTrans.app`, which
can be very expensive for functors between derived categories. -/
lemma map_hom_app_counit_of_eq_rightAdjointUniq (adj₁ : F ⊣ G) (adj₂ : F ⊣ G') (e : G ≅ G')
    (he : e = adj₁.rightAdjointUniq adj₂) (x : D) :
    F.map (e.hom.app x) ≫ adj₂.counit.app x = adj₁.counit.app x := by
  subst he
  exact rightAdjointUniq_hom_app_counit adj₁ adj₂ x

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- The unit `Λ_X = 𝟙_` of the derived tensor product on `D(X_ét)`. It is stated over a general
coefficient category `A`, so that its specialisation to `A = ModuleCat Λ` is the unit appearing
in `AlgebraicGeometry.Etale.derivedTensorLeftUnitorNatIso` and
`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`. -/
noncomputable def derivedTensorUnit : DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  𝟙_ _

/-- The left unitor `Λ_X ⊗ᴸ - ≅ 𝟭`, with the unit written `derivedTensorUnit`. -/
noncomputable def derivedTensorUnitLeftUnitor :
    (derivedTensor A X).obj (derivedTensorUnit A X) ≅
      𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  derivedTensorLeftUnitorNatIso A X

/-- A chosen symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of the derived tensor product on `D(X_ét)`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`). -/
noncomputable def derivedTensorFlipIso :
    derivedTensor A X ≅ (derivedTensor A X).flip :=
  (nonempty_iso_derivedTensor_flip A X).some

/-- The derived lower shriek along the identity is the identity, `R(𝟙_X)_! ≅ R(𝟙_X)_* ≅ 𝟭`: the
identity is proper (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`)
and `(𝟙_X)_* ≅ 𝟭`. This is the isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerShriekIdIso`
of `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality`, rebuilt here to avoid the large
import closure of that file. -/
noncomputable def rightDerivedLowerShriekIdIsoOfLowerStar :
    R(𝟙 X)_![A] ≅ 𝟭 _ :=
  rightDerivedLowerShriekIsoRightDerivedLowerStar A (𝟙 X) ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarId A X) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

variable {A X} in
/-- The derived pullback preserves the unit, `Lg^* Λ_Y ≅ Λ_Z`, with the unit written
`derivedTensorUnit`. -/
noncomputable def leftDerivedUpperStarDerivedTensorUnitIso {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [(g)^*[A].PreservesFlat] :
    (L((g)^*[A])).obj (derivedTensorUnit A Y) ≅ derivedTensorUnit A Z :=
  leftDerivedUpperStarUnitIso A g

end General

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The derived lower shriek along equal morphisms: `R(f)_! ≅ R(f')_!` for `f = f'`. -/
noncomputable def rightDerivedLowerShriekCongrIso {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    R(f)_![ModuleCat.{u + 1} Λ] ≅ R(f')_![ModuleCat.{u + 1} Λ] := by
  subst h
  exact Iso.refl _

variable [Finite Λ]

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on the unbounded derived categories,
for torsion coefficients: the isomorphism of `proposition-composition-base-change-rf-shriek--1`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`) as data. -/
noncomputable def rightDerivedLowerShriekCompIso {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] :=
  haveI : QuasiCompact f := .of_comp f g
  (rightDerivedLowerShriekIso Λ ((HasCompactification.compactification g).comp
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)))).symm ≪≫
    (rightDerivedLowerShriekOfCompactificationCompIso Λ (HasCompactification.compactification g)
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g))).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerShriekIso Λ
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)).restrict) _

/-- The projection formula `Rf_! L ⊗ᴸ K ≅ Rf_!(L ⊗ᴸ Lf^* K)`, as an isomorphism of functors of
`K`, for torsion coefficients. -/
noncomputable def projectionIso {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule Λ X) :
    (derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj L) ≅
      (L((f)^*[ModuleCat.{u + 1} Λ])) ⋙ (derivedTensor (ModuleCat.{u + 1} Λ) X).obj L ⋙
        (R(f)_![ModuleCat.{u + 1} Λ]) :=
  haveI := isIso_projectionMap_of_finite Λ f
  asIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app L)

/-- The projection formula `Rf_! K ⊗ᴸ M ≅ Rf_!(K ⊗ᴸ Lf^* M)`, as an isomorphism of functors of
`K`, for torsion coefficients. -/
noncomputable def projectionRightIso {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule Λ Y) :
    (R(f)_![ModuleCat.{u + 1} Λ]) ⋙ derivedTensorRight (ModuleCat.{u + 1} Λ) Y M ≅
      derivedTensorRight (ModuleCat.{u + 1} Λ) X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M) ⋙
        (R(f)_![ModuleCat.{u + 1} Λ]) :=
  haveI := isIso_projectionMap_of_finite Λ f
  asIso (((flipFunctor _ _ _).map (projectionMap (ModuleCat.{u + 1} Λ) f)).app M)

/-- The projection formula for the unit: `Lf^* ⋙ Rf_! ≅ Rf_! Λ_X ⊗ᴸ -`, the left unitor
followed by the inverse of the projection formula
`AlgebraicGeometry.Etale.projectionIso`. -/
noncomputable def projectionUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (L((f)^*[ModuleCat.{u + 1} Λ])) ⋙ (R(f)_![ModuleCat.{u + 1} Λ]) ≅
      (derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj (derivedTensorUnit _ X)) :=
  Functor.isoWhiskerLeft (L((f)^*[ModuleCat.{u + 1} Λ]))
      (Functor.isoWhiskerRight (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} Λ) X).symm
        (R(f)_![ModuleCat.{u + 1} Λ])) ≪≫
    (projectionIso Λ f (derivedTensorUnit _ X)).symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
  [IsSeparated f]

namespace TraceDiagonalDatum

omit [HasCompactification f] [QuasiCompact f] [IsSeparated f] in
/-- The diagonal `Δ : X ⟶ X ×_Y X`, with codomain written `pullback f f`.

This is `CategoryTheory.Limits.pullback.diagonal f`, whose codomain is the reducible synonym
`pullback.diagonalObj f`; the kernel compares functors between derived categories over
`pullback.diagonalObj f` and over `pullback f f` only very slowly, so all constructions below use
this version of the diagonal. -/
noncomputable def diagonal : X ⟶ pullback f f :=
  pullback.diagonal f

omit [HasCompactification f] [QuasiCompact f] [IsSeparated f] in
@[reassoc (attr := simp)]
lemma diagonal_fst : diagonal f ≫ pullback.fst f f = 𝟙 X :=
  pullback.diagonal_fst f

omit [HasCompactification f] [QuasiCompact f] [IsSeparated f] in
@[reassoc (attr := simp)]
lemma diagonal_snd : diagonal f ≫ pullback.snd f f = 𝟙 X :=
  pullback.diagonal_snd f

/-- The diagonal of a separated morphism admits a compactification. -/
instance hasCompactification_diagonal : HasCompactification (diagonal f) := by
  unfold diagonal
  infer_instance

/-- `Δ ≫ p₂ = 𝟙` admits a compactification. -/
instance hasCompactification_diagonal_snd :
    HasCompactification (diagonal f ≫ pullback.snd f f) := by
  rw [diagonal_snd]
  infer_instance

/-- `Δ ≫ p₂ = 𝟙` is quasi-compact. -/
instance quasiCompact_diagonal_snd : QuasiCompact (diagonal f ≫ pullback.snd f f) := by
  rw [diagonal_snd]
  infer_instance

variable {Λ}

/-- The isomorphism `𝟭 ≅ Lp₁^* ⋙ LΔ^*`, from `Δ ≫ p₁ = 𝟙`. -/
noncomputable def diagonalSectionIso :
    𝟭 (DerivedCategoryModule Λ X) ≅
      (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])) ⋙ (L((diagonal f)^*[ModuleCat.{u + 1} Λ])) :=
  (leftDerivedUpperStarCompSectionIso _ (diagonal f) (pullback.fst f f) (diagonal_fst f)).symm

/-- The isomorphism `RΔ_! ≅ Lp₁^* ⋙ LΔ^* ⋙ RΔ_!`, from `Δ ≫ p₁ = 𝟙`. -/
noncomputable def diagonalLowerShriekSectionIso :
    R(diagonal f)_![ModuleCat.{u + 1} Λ] ≅
      (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])) ⋙
        (L((diagonal f)^*[ModuleCat.{u + 1} Λ])) ⋙ (R(diagonal f)_![ModuleCat.{u + 1} Λ]) :=
  (Functor.leftUnitor (R(diagonal f)_![ModuleCat.{u + 1} Λ])).symm ≪≫
    Functor.isoWhiskerRight (diagonalSectionIso f) (R(diagonal f)_![ModuleCat.{u + 1} Λ]) ≪≫
    Functor.associator (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ]))
      (L((diagonal f)^*[ModuleCat.{u + 1} Λ])) (R(diagonal f)_![ModuleCat.{u + 1} Λ])

/-- The isomorphism `RΔ_! A ≅ RΔ_! Λ_X ⊗ᴸ Lp₁^* A`: `L(Δ ≫ p₁)^* = L(𝟙)^* ≅ 𝟭` and the
projection formula for `Δ` (`AlgebraicGeometry.Etale.projectionUnitIso`). -/
noncomputable def diagonalIso :
    R(diagonal f)_![ModuleCat.{u + 1} Λ] ≅
      (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])) ⋙
        (derivedTensor (ModuleCat.{u + 1} Λ) (pullback f f)).obj
          ((R(diagonal f)_![ModuleCat.{u + 1} Λ]).obj (derivedTensorUnit _ X)) :=
  diagonalLowerShriekSectionIso f ≪≫
    Functor.isoWhiskerLeft (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ]))
      (projectionUnitIso Λ (diagonal f))

/-- The isomorphism `𝟭 ≅ R(𝟙)_! = R(Δ ≫ p₂)_! ≅ RΔ_! ⋙ Rp₂_!`. -/
noncomputable def idIsoDiagonalSnd :
    𝟭 (DerivedCategoryModule Λ X) ≅
      (R(diagonal f)_![ModuleCat.{u + 1} Λ]) ⋙ (R(pullback.snd f f)_![ModuleCat.{u + 1} Λ]) :=
  (rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} Λ) X).symm ≪≫
    rightDerivedLowerShriekCongrIso Λ (diagonal_snd f).symm ≪≫
    rightDerivedLowerShriekCompIso Λ (diagonal f) (pullback.snd f f)

/-- Proper base change `Rf_! ⋙ Lf^* ≅ Lp₁^* ⋙ Rp₂_!` for the cartesian square of
`W = X ×_Y X`. -/
noncomputable def baseChangeIso :
    (R(f)_![ModuleCat.{u + 1} Λ]) ⋙ (L((f)^*[ModuleCat.{u + 1} Λ])) ≅
      (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])) ⋙
        (R(pullback.snd f f)_![ModuleCat.{u + 1} Λ]) :=
  haveI := isIso_rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f f)
  asIso (rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f f))

/-- The isomorphism `Rp₂_!(Lp₁^* A ⊗ᴸ Lp₂^* L) ≅ Rp₂_!(Lp₁^* A) ⊗ᴸ L ≅ Lf^* Rf_! A ⊗ᴸ L`: the
projection formula for `p₂` and proper base change. -/
noncomputable def sndProjectionIso (L : DerivedCategoryModule Λ X) :
    ((L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])) ⋙
        derivedTensorRight _ (pullback f f) ((L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ])).obj L))
          ⋙ (R(pullback.snd f f)_![ModuleCat.{u + 1} Λ]) ≅
      (R(f)_![ModuleCat.{u + 1} Λ]) ⋙ ((L((f)^*[ModuleCat.{u + 1} Λ])) ⋙
        derivedTensorRight (ModuleCat.{u + 1} Λ) X L) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ]))
      (projectionRightIso Λ (pullback.snd f f) L).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (baseChangeIso f).symm
      (derivedTensorRight (ModuleCat.{u + 1} Λ) X L) ≪≫
    Functor.associator _ _ _

end TraceDiagonalDatum

end Etale

end AlgebraicGeometry
