/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteLevelProEtaleBaseChange
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement

/-!
# The four finite-level arrows

Source: blueprint, proper base change, four finite-level arrows, order 1343;
Stacks Project Tags 07A7, 09C9, 0B56 and 0944 (blueprint: def-weil-pbc-four-arrows).

The horizontal arrows and the finite exchange are isomorphisms. The reduced ambient
exchange is a morphism; neither its invertibility nor commutativity of this square is
part of this definition. All scalar extensions and pullbacks are uncompleted.

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourArrows`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u v w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open CategoryTheory CategoryTheory.Limits

private theorem invertSquare {C : Type u₁} [Category.{v₁} C]
    {U V W X Y Z : C} (u : U ⟶ V) (b : V ≅ W) (e : W ≅ X)
    (t : U ≅ Y) (a : Y ≅ Z) (v : Z ⟶ X)
    (h : u ≫ b.hom ≫ e.hom = t.hom ≫ a.hom ≫ v) :
    v ≫ e.inv ≫ b.inv = a.inv ≫ t.inv ≫ u := by
  have hh := congrArg (fun k ↦ a.inv ≫ t.inv ≫ k ≫ e.inv ≫ b.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, Category.comp_id, Category.id_comp] using hh.symm

private theorem invertMappedSquare {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] (P : C ⥤ E) (Q : D ⥤ E)
    {B₁ B₂ : C} {T₁ T₂ : D} {U V : E}
    (b : B₁ ≅ B₂) (t : T₁ ≅ T₂) (e : P.obj B₁ ≅ V)
    (a : U ≅ Q.obj T₁) (u : Q.obj T₂ ⟶ P.obj B₂) (v : U ⟶ V)
    (h : u ≫ P.map b.inv ≫ e.hom = Q.map t.inv ≫ a.inv ≫ v) :
    v ≫ e.inv ≫ P.map b.hom = a.hom ≫ Q.map t.hom ≫ u := by
  exact invertSquare u (P.mapIso b.symm) e (Q.mapIso t.symm) a.symm v h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem swap
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {S : A ⥤ C} {U : C ⥤ A} {S' : B ⥤ D} {U' : D ⥤ B}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (sc : S ⊣ U) (sc' : S' ⊣ U')
    (b : L' ⋙ U' ≅ U ⋙ L)
    (a : L ⋙ S' ≅ S ⋙ L')
    (ha : a.hom = (mateEquiv sc sc').symm b.inv)
    (d : R' ⋙ U ≅ U' ⋙ R)
    (hd : ∀ (M : C) (N : D) (t : L'.obj M ⟶ N),
      adj.homEquiv _ _ (b.inv.app M ≫ U'.map t) =
        U.map (adj'.homEquiv M N t) ≫ d.hom.app N)
    (H : B) :
    adj'.homEquiv _ _ (a.inv.app (R.obj H) ≫ S'.map (adj.counit.app H)) =
      (sc.homEquiv _ _).symm
        (R.map (sc'.unit.app H) ≫ d.inv.app (S'.obj H)) := by
  apply (sc.homEquiv _ _).injective
  dsimp only [Functor.id_obj] at *
  rw [Equiv.apply_symm_apply]
  apply (cancel_mono (d.hom.app (S'.obj H))).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj]
  rw [Category.comp_id]
  rw [Adjunction.homEquiv_unit, Category.assoc, ← hd]
  erw [← adj.homEquiv_naturality_left]
  have hu := unit_mateEquiv_symm sc sc' (TwoSquare.mk _ _ _ _ b.inv) (R.obj H)
  rw [← ha] at hu
  change L.map (sc.unit.app (R.obj H)) ≫ b.inv.app (S.obj (R.obj H)) =
    sc'.unit.app (L.obj (R.obj H)) ≫ U'.map (a.hom.app (R.obj H)) at hu
  rw [← Category.assoc, hu]
  simp only [Category.assoc, ← U'.map_comp, Iso.hom_inv_id_app_assoc]
  have hn := sc'.unit.naturality (adj.counit.app H)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← hn]
  rw [adj.homEquiv_naturality_right]
  simp only [Adjunction.homEquiv_unit, adj.right_triangle_components, Category.id_comp]

namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {X Y : Scheme.{u}} (f : X ⟶ Y)
private theorem ordinaryComparison (n : ℕ) :
    completedRestrictionDirectImageIso f d n =
      (proEtaleRingRestrictionDirectImage f
        (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
        (d.projection Y n) (d.projection X n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n)).symm := by
  apply (completedRestrictionDirectImageIso_exists f d n).unique
  · exact (completedRestrictionDirectImageIso_exists f d n).exists.choose_spec
  · intro M U x
    let e := proEtaleRingRestrictionDirectImage f
      (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
      (d.projection Y n) (d.projection X n) (d.integralRingIso f)
      (d.finiteRingIso f n) (d.projection_comm f n)
    have h := congrArg (fun a ↦ a.val.app U x) (e.inv_hom_id_app M)
    change (e.hom.app M).val.app U ((e.inv.app M).val.app U x) = x at h
    have he := (proEtaleRingRestrictionDirectImage_existsUnique f
      (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
      (d.projection Y n) (d.projection X n) (d.integralRingIso f)
      (d.finiteRingIso f n) (d.projection_comm f n)).choose_spec.1
    exact (he M U _).symm.trans h

private theorem completedUnit_eq
    (C : CochainComplex (proEtaleRingModules X (d.completedRing X)) ℤ) :
    completedDirectImageComplexUnit f d C =
      proEtaleRingDirectImageDerivedUnit f (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso f) C := by
  have h : (((completedModuleDirectImage f d).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) =
      𝟙 _ := rfl
  simp only [completedDirectImageComplexUnit, proEtaleRingDirectImageDerivedUnit,
    h]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem finiteUnit_eq (n : ℕ)
    (C : CochainComplex (proEtaleRingModules X (d.finiteRing X n)) ℤ) :
    completedFiniteDirectImageComplexUnit f d n C =
      proEtaleRingDirectImageDerivedUnit f (d.finiteRing Y n) (d.finiteRing X n)
        (d.finiteRingIso f n) C := by
  have h : (((completedFiniteModuleDirectImage f d n).mapHomotopyCategoryFactors
      (.up ℤ)).inv.app C) = 𝟙 _ := rfl
  simp only [completedFiniteDirectImageComplexUnit, proEtaleRingDirectImageDerivedUnit,
    h]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Comparing the two normalized derived presentations requires unfolding their factor isos.
private theorem derivedComparison (n : ℕ) :
    completedDerivedRestrictionDirectImageIso f d n =
      (proEtaleRingRestrictionDerivedDirectImage f
        (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
        (d.projection Y n) (d.projection X n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n)).symm := by
  let D := proEtaleRingRestrictionDerivedDirectImage f
    (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
    (d.projection Y n) (d.projection X n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)
  let E := completedDerivedRestrictionDirectImageIso f d n
  have he := (completedDerivedRestrictionDirectImageIso_exists f d n).exists.choose_spec
  have hD : D = E.symm := by
    apply (proEtaleRingRestrictionDerivedDirectImage_existsUnique f
      (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
      (d.projection Y n) (d.projection X n) (d.integralRingIso f)
      (d.finiteRingIso f n) (d.projection_comm f n)).unique
    · exact (proEtaleRingRestrictionDerivedDirectImage_existsUnique f
        (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
        (d.projection Y n) (d.projection X n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n)).choose_spec.1
    · intro C
      have hC := he C
      change completedDirectImageComplexUnit f d _ ≫ _ ≫ E.hom.app _ = _ at hC
      rw [ordinaryComparison d f n, completedUnit_eq d f, finiteUnit_eq d f n] at hC
      let b := (pbcRestrict (pbcAdicProjection X d n)).mapDerivedCategoryFactors.app C
      let a := (pbcRestrict (pbcAdicProjection Y d n)).mapDerivedCategoryFactors.app
        (((completedFiniteModuleDirectImage f d n).mapHomologicalComplex (.up ℤ)).obj C)
      let o := proEtaleRingRestrictionDirectImage f
        (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
        (d.projection Y n) (d.projection X n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n)
      let t := NatIso.mapHomologicalComplex o (.up ℤ)
      let P := d.push f
      let u := proEtaleRingDirectImageDerivedUnit f (d.completedRing Y)
        (d.completedRing X) (d.integralRingIso f)
        (((pbcRestrict (pbcAdicProjection X d n)).mapHomologicalComplex (.up ℤ)).obj C)
      let v := (pbcDerivedRestrict (pbcAdicProjection Y d n)).map
        (proEtaleRingDirectImageDerivedUnit f (d.finiteRing Y n) (d.finiteRing X n)
          (d.finiteRingIso f n) C)
      have hsquare := invertMappedSquare P DerivedCategory.Q b (t.app C)
        (E.app (DerivedCategory.Q.obj C)) a u v hC
      exact hsquare
  exact (congrArg Iso.symm hD).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable {U V : Scheme.{u}} (f : U ⟶ V)
  (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
  (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
  (aV : RV ⟶ SV) (aU : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarProjection_eq (H : DerivedCategory (proEtaleRingModules U RU)) :
    (proEtaleRingDerivedAdjunction f SV SU cS).homEquiv _ _
      ((proEtaleReductionPullbackIso f RV SV RU SU aV aU cR cS comm).hom.app
        ((proEtaleRingDerivedDirectImage f RV RU cR).obj H) ≫
        (proEtaleRingDerivedExtension aU).map
          ((proEtaleRingDerivedAdjunction f RV RU cR).counit.app H)) =
      ((proEtaleRingDerivedExtensionAdjunction aV).homEquiv _ _).symm
        ((proEtaleRingDerivedDirectImage f RV RU cR).map
          ((proEtaleRingDerivedExtensionAdjunction aU).unit.app H) ≫
          (proEtaleRingRestrictionDerivedDirectImage f RV SV RU SU aV aU cR cS comm).inv.app
            ((proEtaleRingDerivedExtension aU).obj H)) := by
  exact swap (proEtaleRingDerivedAdjunction f RV RU cR)
    (proEtaleRingDerivedAdjunction f SV SU cS)
    (proEtaleRingDerivedExtensionAdjunction aV)
    (proEtaleRingDerivedExtensionAdjunction aU)
    (proEtaleRingRestrictionDerivedPullback f RV SV RU SU aV aU cR cS comm)
    (proEtaleReductionPullbackIso f RV SV RU SU aV aU cR cS comm).symm rfl
    (proEtaleRingRestrictionDerivedDirectImage f RV SV RU SU aV aU cR cS comm)
    (proEtaleRingSheafChangeAdjunction f RV SV RU SU aV aU cR cS comm).2.2 H
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The finite-coefficient projection is the adjunct of chi followed by scalar extension
of the ambient counit. Its target retains the quotient-coefficient action.
Source: blueprint four arrows; Stacks Tags 0B56 and 0944
(blueprint: def-weil-pbc-four-arrows). -/
noncomputable def AdicCoefficientDatum.finiteProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : d.derived X) (n : ℕ) :
    (d.reduction Y n).obj ((d.push f).obj H) ⟶
      (d.finitePush f n).obj ((d.reduction X n).obj H) :=
  (proEtaleRingDerivedAdjunction f (d.finiteRing Y n) (d.finiteRing X n)
    (d.finiteRingIso f n)).homEquiv _ _
      ((d.chi f n).hom.app ((d.push f).obj H) ≫
        (d.reduction X n).map
          ((proEtaleRingDerivedAdjunction f (d.completedRing Y) (d.completedRing X)
            (d.integralRingIso f)).counit.app H))

/-- The specified finite projection is invertible, also without properness or a bound on H.
Source: blueprint four arrows; Stacks Tags 0944, 0D6D and 0D6E
(blueprint: def-weil-pbc-four-arrows).
Proof: the coefficient-change adjunction comparison identifies the restriction of this
adjunct with the canonical uncompleted projection-formula mate for (P_n)_Y. The perfect
coefficient theorem lemma-weil-pbc-perfect-projection-formula gives the signed finite-total
inverse. Exact restriction reflects derived isomorphisms by
lem-weil-pbc-ring-sheaf-change-adjunction, hence the original quotient-linear map is an
isomorphism. The same argument applies to f' and H = Lg'*K. -/
theorem AdicCoefficientDatum.finiteProjection_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : d.derived X) (n : ℕ) : IsIso (d.finiteProjection f H n) := by
  have he : d.finiteProjection f H n = completedDirectImageProjectionFormula f d n H := by
    rw [AdicCoefficientDatum.finiteProjection, completedDirectImageProjectionFormula,
      derivedComparison d f n]
    exact scalarProjection_eq f (d.completedRing Y) (d.finiteRing Y n)
      (d.completedRing X) (d.finiteRing X n) (d.projection Y n) (d.projection X n)
      (d.integralRingIso f) (d.finiteRingIso f n) (d.projection_comm f n) H
  rw [he]
  exact (completedDirectImageProjectionFormula_properties f d).1 n H

attribute [instance] AdicCoefficientDatum.finiteProjection_isIso

/-- A square of four arrows with exactly the asserted three isomorphisms. No equation
between its two paths is imposed. Source: blueprint four arrows
(blueprint: def-weil-pbc-four-arrows). -/
structure FourFiniteLevelArrows {C : Type v} [Category.{w} C] (corners : Fin 4 → C) where
  h : corners 0 ≅ corners 1
  h' : corners 2 ≅ corners 3
  v : corners 0 ⟶ corners 2
  v' : corners 1 ≅ corners 3

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

-- Keep coefficient transport outside the expanded exchange term. In particular, generalize
-- the ring sheaves before specializing from the function presentation to the quotient tower.
private structure ExchangeInvertible (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing X Λ)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing Y' Λ)
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing X Λ) ≅ finiteOriginFunctionRing X' Λ)
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y' Λ) ≅ finiteOriginFunctionRing X' Λ)
    (M : DerivedCategory (proEtaleRingModules X (finiteOriginFunctionRing X Λ))) : Prop where
  isIso : ∀ hc : HEq
    (proEtaleRingCompositeCoefficients g' f (finiteOriginFunctionRing Y Λ)
      (finiteOriginFunctionRing X Λ)
      (finiteOriginFunctionRing X' Λ) c_f c_g')
    (proEtaleRingCompositeCoefficients f' g (finiteOriginFunctionRing Y Λ)
      (finiteOriginFunctionRing Y' Λ)
      (finiteOriginFunctionRing X' Λ) c_g c_f'),
    IsIso ((proEtaleAmbientRingedExchange sq (finiteOriginFunctionRing X Λ)
      (finiteOriginFunctionRing Y Λ)
      (finiteOriginFunctionRing X' Λ) (finiteOriginFunctionRing Y' Λ) c_f c_g c_g' c_f' hc).app M)

private theorem levelConstantComparison_eq (T : Scheme.{u}) (n : ℕ) :
    pbcLevelConstantComparison T d n =
      finiteOriginConstantIso T (A ⧸ d.ideal ^ (n + 1)) := by
  apply (pbcLevelConstantComparison_exists T d n).unique
  · exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec
  · intro U b
    have h := toSheafify_naturality (ProEt.topology T)
      (AdicCoefficients.constants T (A ⧸ d.ideal ^ (n + 1)))
    have hU := congrArg (fun t ↦ t.app U) h
    exact (congrArg (fun t ↦ t b) hU).symm

private theorem finiteRingIso_eq {U V : Scheme.{u}} (h : U ⟶ V) (n : ℕ) :
    d.finiteRingIso h n = finiteCoefficientRingIso (A ⧸ d.ideal ^ (n + 1)) h := by
  apply Iso.ext
  simp only [AdicCoefficientDatum.finiteRingIso, finiteCoefficientRingIso,
    levelConstantComparison_eq]
  rfl

private theorem finiteExchangeInvertible (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [IsProper f]
    (M : DerivedCategory (proEtaleRingModules X (finiteOriginFunctionRing X Λ)))
    (W : FiniteEtaleOriginWitness X Λ M) : ExchangeInvertible sq Λ
      (finiteCoefficientRingIso Λ f) (finiteCoefficientRingIso Λ g)
      (finiteCoefficientRingIso Λ g') (finiteCoefficientRingIso Λ f') M := by
  constructor
  intro hc
  let P := fun h : HEq
      (proEtaleRingCompositeCoefficients g' f (finiteOriginFunctionRing Y Λ)
        (finiteOriginFunctionRing X Λ) (finiteOriginFunctionRing X' Λ)
        (finiteCoefficientRingIso Λ f) (finiteCoefficientRingIso Λ g'))
      (proEtaleRingCompositeCoefficients f' g (finiteOriginFunctionRing Y Λ)
        (finiteOriginFunctionRing Y' Λ) (finiteOriginFunctionRing X' Λ)
        (finiteCoefficientRingIso Λ g) (finiteCoefficientRingIso Λ f')) ↦
    IsIso ((proEtaleAmbientRingedExchange sq (finiteOriginFunctionRing X Λ)
      (finiteOriginFunctionRing Y Λ) (finiteOriginFunctionRing X' Λ)
      (finiteOriginFunctionRing Y' Λ) (finiteCoefficientRingIso Λ f)
      (finiteCoefficientRingIso Λ g) (finiteCoefficientRingIso Λ g')
      (finiteCoefficientRingIso Λ f') h).app M)
  exact Eq.mp (congrArg P (Subsingleton.elim
    (finiteCoefficientRingIso_coherent Λ sq) hc))
    (finiteLevelProEtaleBaseChange Λ sq M W)

private theorem exchangeTransportRings (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [IsProper f]
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (RY' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RY ≅ RY')
    (cg' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj RX ≅ RX')
    (cf' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj RY' ≅ RX')
    (eX : RX = finiteOriginFunctionRing X Λ)
    (eY : RY = finiteOriginFunctionRing Y Λ)
    (eX' : RX' = finiteOriginFunctionRing X' Λ)
    (eY' : RY' = finiteOriginFunctionRing Y' Λ)
    (ef : HEq cf (finiteCoefficientRingIso Λ f))
    (eg : HEq cg (finiteCoefficientRingIso Λ g))
    (eg' : HEq cg' (finiteCoefficientRingIso Λ g'))
    (ef' : HEq cf' (finiteCoefficientRingIso Λ f'))
    (M : DerivedCategory (proEtaleRingModules X RX))
    (N : DerivedCategory (proEtaleRingModules X (finiteOriginFunctionRing X Λ)))
    (eM : HEq M N) (W : FiniteEtaleOriginWitness X Λ N)
    (hc : HEq (proEtaleRingCompositeCoefficients g' f RY RX RX' cf cg')
      (proEtaleRingCompositeCoefficients f' g RY RY' RX' cg cf')) :
    IsIso ((proEtaleAmbientRingedExchange sq RX RY RX' RY' cf cg cg' cf' hc).app M) := by
  subst RX RY RX' RY'
  have ef := eq_of_heq ef
  have eg := eq_of_heq eg
  have eg' := eq_of_heq eg'
  have ef' := eq_of_heq ef'
  have eM := eq_of_heq eM
  subst cf cg cg' cf' M
  exact (finiteExchangeInvertible sq Λ N W).isIso hc

/-- The finite proper-base-change theorem in the normalized corner notation.
Source: blueprint four arrows, Stacks 09C9
(blueprint: def-weil-pbc-four-arrows).
Proof: apply finiteLevelProEtaleBaseChange to the finite quotient and its retained
etale witness. The finiteExchange abbreviation is exactly that canonical ringed
adjunction mate, so the conclusion is unchanged. -/
theorem AdicCoefficientDatum.finiteExchange_isIso [IsProper f]
    (K : d.derived X) (n : ℕ)
    (W : FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    IsIso ((d.finiteExchange sq n).app ((d.reduction X n).obj K)) := by
  exact exchangeTransportRings sq (A ⧸ d.ideal ^ (n + 1))
    (d.finiteRing X n) (d.finiteRing Y n) (d.finiteRing X' n) (d.finiteRing Y' n)
    (d.finiteRingIso f n) (d.finiteRingIso g n)
    (d.finiteRingIso g' n) (d.finiteRingIso f' n)
    rfl rfl rfl rfl
    (heq_of_eq (finiteRingIso_eq d f n)) (heq_of_eq (finiteRingIso_eq d g n))
    (heq_of_eq (finiteRingIso_eq d g' n)) (heq_of_eq (finiteRingIso_eq d f' n))
    ((d.reduction X n).obj K) ((d.reduction X n).obj K) HEq.rfl W
    (d.finite_coherent sq n)

/-- The finite exchange is the canonical ambient exchange with its isomorphism certified
by finite-level proper base change and the specified witness. The underlying morphism
contains no witness choices. Source: blueprint four arrows; Stacks Tags 07A7 and 09C9
(blueprint: def-weil-pbc-four-arrows). -/
noncomputable def AdicCoefficientDatum.finiteExchangeIso [IsProper f]
    (K : d.derived X) (n : ℕ)
    (W : FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    (d.finitePull g n).obj ((d.finitePush f n).obj ((d.reduction X n).obj K)) ≅
      (d.finitePush f' n).obj ((d.finitePull g' n).obj ((d.reduction X n).obj K)) :=
  @asIso _ _ _ _ ((d.finiteExchange sq n).app ((d.reduction X n).obj K))
    (d.finiteExchange_isIso sq K n W)

/-- The four specified arrows at positive level n+1: pullback of the finite projection;
projection followed by pushforward of delta; chi followed by reduction of the ambient
exchange; and the canonical finite-coefficient exchange. The family W retains separate
bounded-below etale witnesses, with no uniform bound or compatibility requirement.
Source: blueprint four arrows, order 1343; Stacks Tags 07A7, 09C9, 0B56 and 0944
(blueprint: def-weil-pbc-four-arrows). -/
noncomputable def AdicCoefficientDatum.fourArrows [IsProper f] (K : d.derived X)
    (_hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) :
    FourFiniteLevelArrows (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n) where
  h := asIso ((d.finitePull g n).map (d.finiteProjection f K n))
  h' := asIso (d.finiteProjection f' ((d.pull g').obj K) n ≫
    (d.finitePush f' n).map ((d.delta (g' := g') K n).hom))
  v := (d.chi g n).hom.app ((d.push f).obj K) ≫
    (d.reduction Y' n).map ((d.integralExchange sq).app K)
  v' := d.finiteExchangeIso sq K n (W n)

end AlgebraicGeometry.Scheme
