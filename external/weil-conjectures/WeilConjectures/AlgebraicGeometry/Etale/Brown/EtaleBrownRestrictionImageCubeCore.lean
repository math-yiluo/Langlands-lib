/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison
import all WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleInverseTensorCoherence
import all WeilConjectures.CategoryTheory.IndependentDerivedCube.IndependentDerivedCube
import WeilConjectures.CategoryTheory.Derived.DerivedSquareIndependentUniverses
import WeilConjectures.CategoryTheory.Derived.DerivedAdjunctionCochainUnit
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Exact restriction and normalized Brown direct image

Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 07A4 and 0D6J.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

section MateCalculus
universe a av b bv c cv d dv
variable {A : Type a} [Category.{av} A] {B₀ : Type b} [Category.{bv} B₀]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]

-- Hom transposition identifies the recorded scalar comparison and its double mate.
private theorem brown_conjugate_transpose
    {L L' : A ⥤ B₀} {R R' : B₀ ⥤ A} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L' ≅ L) (P : A) (Q : B₀) (f : L.obj P ⟶ Q) :
    b.homEquiv P Q (e.hom.app P ≫ f) =
      a.homEquiv P Q f ≫ (conjugateIsoEquiv a b e).hom.app Q := by
  rw [a.homEquiv_unit, b.homEquiv_unit, Category.assoc]
  rw [show R.map f ≫ (conjugateIsoEquiv a b e).hom.app Q =
    (conjugateIsoEquiv a b e).hom.app (L.obj P) ≫ R'.map f from
      (conjugateIsoEquiv a b e).hom.naturality f]
  rw [← Category.assoc]
  erw [unit_conjugateEquiv]
  simp only [Functor.map_comp, Category.assoc]

private theorem brown_conjugate_of_transpose
    {L L' : A ⥤ B₀} {R R' : B₀ ⥤ A} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L' ≅ L) (δ : R ≅ R')
    (h : ∀ P Q (f : L'.obj P ⟶ Q),
      b.homEquiv P Q f = a.homEquiv P Q (e.inv.app P ≫ f) ≫ δ.hom.app Q) :
    conjugateIsoEquiv a b e = δ := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  have hh := h (R.obj Q) Q (e.hom.app _ ≫ a.counit.app Q)
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hh
  have hc := brown_conjugate_transpose a b e (R.obj Q) Q (a.counit.app Q)
  have hi : a.homEquiv (R.obj Q) Q (a.counit.app Q) = 𝟙 _ := by
    rw [← a.homEquiv_symm_id Q]
    exact Equiv.apply_symm_apply _ _
  rw [hi, Category.id_comp] at hh hc
  exact hc.symm.trans hh

private theorem brown_scalar_conjugate
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RB ⋙ Gm ≅ Gn ⋙ RA)
    (h : ∀ P Q (f : Fn.obj (TA.obj P) ⟶ Q),
      a.homEquiv P _ (an.homEquiv _ Q f) =
        am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q) :
    conjugateIsoEquiv (am.comp b) (a.comp an) γ = δ := by
  apply brown_conjugate_of_transpose
  intro P Q f
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change a.homEquiv P _ (an.homEquiv _ Q f) =
    am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q
  exact h P Q f

private theorem right_mate_transpose
    {L : A ⥤ B₀} {R : B₀ ⥤ A} (a : L ⊣ R)
    {K : C ⥤ D} {S : D ⥤ C} (b : K ⊣ S)
    {X : A ⥤ C} {Y : B₀ ⥤ D} (χ : TwoSquare X L K Y)
    (P : A) (N : B₀) (f : L.obj P ⟶ N) :
    b.homEquiv _ _ (χ.app P ≫ Y.map f) =
      X.map (a.homEquiv P N f) ≫ (mateEquiv a b χ).app N := by
  have hh := adjunctionMate_transpose a b (mateEquiv a b χ) P N f
  rw [Equiv.symm_apply_apply] at hh
  exact hh

private theorem right_mate_transport
    {L L' : A ⥤ B₀} {R : B₀ ⥤ A} (a : L ⊣ R) (e : L ≅ L')
    {K K' : C ⥤ D} {S : D ⥤ C} (b : K ⊣ S) (f : K ≅ K')
    (X : A ⥤ C) (Y : B₀ ⥤ D) (χ : X ⋙ K' ⟶ L' ⋙ Y) :
    (mateEquiv (a.ofNatIsoLeft e) (b.ofNatIsoLeft f) (.mk _ _ _ _ χ)) =
      (mateEquiv a b (.mk _ _ _ _
        (Functor.whiskerLeft X f.hom ≫ χ ≫ Functor.whiskerRight e.inv Y))) := by
  ext N
  simp only [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Functor.map_comp, Functor.comp_map, Category.id_comp, Category.assoc]

private theorem rotate_iso_square {X Y Z T : A} (j : X ≅ Y) (i : Z ≅ T)
    (a : X ⟶ Z) (b : Y ⟶ T) (h : b ≫ i.inv = j.inv ≫ a) :
    a ≫ i.hom = j.hom ≫ b := by
  calc
    a ≫ i.hom = j.hom ≫ (j.inv ≫ a) ≫ i.hom := by simp
    _ = j.hom ≫ (b ≫ i.inv) ≫ i.hom := by rw [h]
    _ = j.hom ≫ b := by simp [Category.assoc]

end MateCalculus

section NormalizedMate
universe a av b bv c cv d dv da db dc dd
variable {C : Type a} [Category.{av} C] [Abelian C] [HasDerivedCategory.{da} C]
  {D : Type b} [Category.{bv} D] [Abelian D] [HasDerivedCategory.{db} D]
  {E : Type c} [Category.{cv} E] [Abelian E] [HasDerivedCategory.{dc} E]
  {F : Type d} [Category.{dv} F] [Abelian F] [HasDerivedCategory.{dd} F]

private theorem exact_transpose
    (l : E ⥤ F) (r : F ⥤ E) [l.Additive] [r.Additive]
    [PreservesFiniteLimits l] [PreservesFiniteColimits l]
    [Abelian.HasKInjectiveResolutions F]
    (a : l ⊣ r) (P : CochainComplex E ℤ) (I : CochainComplex F ℤ)
    (f : (l.mapHomologicalComplex (.up ℤ)).obj P ⟶ I) :
    a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
      (l.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map f) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P I f) ≫
      r.rightDerivedFunctorUnitQ I := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    derived_unit_cochain]
  rw [Category.assoc, ← r.rightDerivedFunctorUnitQ_naturality, ← Category.assoc,
    ← DerivedCategory.Q.map_comp]
  rfl

private theorem mate_right_normalized
    (f : C ⥤ D) (g : D ⥤ C) (l : E ⥤ F) (r : F ⥤ E)
    [f.Additive] [g.Additive] [l.Additive] [r.Additive]
    (a : f ⊣ g) (ag : l ⊣ r)
    (e : C ⥤ E) (j : D ⥤ F) [e.Additive] [j.Additive]
    (fd : DerivedCategory C ⥤ DerivedCategory D)
    (gd : DerivedCategory D ⥤ DerivedCategory C) (ad : fd ⊣ gd)
    (ld : DerivedCategory E ⥤ DerivedCategory F)
    (rd : DerivedCategory F ⥤ DerivedCategory E) (adg : ld ⊣ rd)
    (ed : DerivedCategory C ⥤ DerivedCategory E)
    (jd : DerivedCategory D ⥤ DerivedCategory F)
    (ff : DerivedCategory.Q ⋙ fd ≅ f.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ef : DerivedCategory.Q ⋙ ed ≅ e.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (jf : DerivedCategory.Q ⋙ jd ≅ j.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (lf : DerivedCategory.Q ⋙ ld ≅ l.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (u : g.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ gd)
    (v : r.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ rd)
    (hu : ∀ P I (k : (f.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
      ad.homEquiv _ _ (ff.hom.app P ≫ DerivedCategory.Q.map k) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P I k) ≫ u.app I)
    (hv : ∀ P I (k : (l.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
      adg.homEquiv _ _ (lf.hom.app P ≫ DerivedCategory.Q.map k) =
        DerivedCategory.Q.map ((ag.mapHomologicalComplex (.up ℤ)).homEquiv P I k) ≫ v.app I)
    (β : e ⋙ l ≅ f ⋙ j) (α : g ⋙ e ⟶ j ⋙ r)
    (hβ : (mateEquiv a ag (.mk _ _ _ _ β.hom)) = α)
    (χ : ed ⋙ ld ≅ fd ⋙ jd)
    (hχ : ∀ P, χ.hom.app (DerivedCategory.Q.obj P) ≫
        jd.map (ff.hom.app P) ≫ jf.hom.app ((f.mapHomologicalComplex (.up ℤ)).obj P) =
      ld.map (ef.hom.app P) ≫ lf.hom.app ((e.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex β (.up ℤ)).hom.app P))
    (I : CochainComplex D ℤ) :
    ed.map (u.app I) ≫
        (mateEquiv ad adg (.mk _ _ _ _ χ.hom)).app (DerivedCategory.Q.obj I) ≫
        rd.map (jf.hom.app I) =
      ef.hom.app ((g.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I) ≫
        v.app ((j.mapHomologicalComplex (.up ℤ)).obj I) := by
  let G := g.mapHomologicalComplex (.up ℤ)
  let ac := a.mapHomologicalComplex (.up ℤ)
  let ε : (f.mapHomologicalComplex (.up ℤ)).obj (G.obj I) ⟶ I := ac.counit.app I
  have hε : ad.homEquiv _ _
      (ff.hom.app (G.obj I) ≫ DerivedCategory.Q.map ε) = u.app I := by
    rw [hu]
    have hi : ac.homEquiv _ _ ε = 𝟙 _ := by
      change ac.homEquiv _ _ (ac.counit.app I) = 𝟙 _
      rw [← ac.homEquiv_symm_id]
      exact Equiv.apply_symm_apply _ _
    rw [hi, CategoryTheory.Functor.map_id, Category.id_comp]
  have hm := right_mate_transpose ad adg (.mk _ _ _ _ χ.hom)
    (DerivedCategory.Q.obj (G.obj I)) (DerivedCategory.Q.obj I)
    (ff.hom.app (G.obj I) ≫ DerivedCategory.Q.map ε)
  rw [← hε, ← Category.assoc, ← hm]
  erw [← adg.homEquiv_naturality_right _ (jf.hom.app I)]
  simp only [Functor.map_comp, Category.assoc]
  erw [jf.hom.naturality ε]
  rw [reassoc_of% hχ (G.obj I)]
  simp only [Functor.comp_map]
  rw [← DerivedCategory.Q.map_comp, adg.homEquiv_naturality_left]
  erw [hv]
  have ho : (ag.mapHomologicalComplex (.up ℤ)).homEquiv
      ((e.mapHomologicalComplex (.up ℤ)).obj (G.obj I))
      ((j.mapHomologicalComplex (.up ℤ)).obj I)
      ((NatIso.mapHomologicalComplex β (.up ℤ)).hom.app (G.obj I) ≫
        (j.mapHomologicalComplex (.up ℤ)).map ε) =
      (NatTrans.mapHomologicalComplex α (.up ℤ)).app I := by
    ext i
    change ag.homEquiv _ _
      (β.hom.app (g.obj (I.X i)) ≫ j.map (a.counit.app (I.X i))) = α.app (I.X i)
    have hh := right_mate_transpose a ag (.mk _ _ _ _ β.hom)
      (g.obj (I.X i)) (I.X i) (a.counit.app (I.X i))
    rw [hβ] at hh
    have hi : a.homEquiv _ _ (a.counit.app (I.X i)) = 𝟙 _ := by
      rw [← a.homEquiv_symm_id]
      exact Equiv.apply_symm_apply _ _
    erw [hi] at hh
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Functor.id_obj,
      TwoSquare.mk] using hh
  rw [ho]

end NormalizedMate

section UnitSquares
universe a av b bv c cv d dv e ev f fv da db dc dd de df
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{dc} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{dd} D]
  {E : Type e} [Category.{ev} E] [Abelian E] [HasDerivedCategory.{de} E]
  {F : Type f} [Category.{fv} F] [Abelian F] [HasDerivedCategory.{df} F]

/-- A square agrees with ordinary cochain maps after the supplied derived units.
Source: Stacks 07A4; Zheng Lemma 5.16.
(blueprint: lem-pur-brown-unit-normalized-naturality). -/
def EtaleBrownUnitNorm
    (F₀ : A ⥤ B) (G₀ : C ⥤ D) [F₀.Additive] [G₀.Additive]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (GD : DerivedCategory C ⥤ DerivedCategory D)
    (u : F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FD)
    (v : G₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ GD)
    (x : A ⥤ C) (y : B ⥤ D) [x.Additive] [y.Additive]
    (X : DerivedCategory A ⥤ DerivedCategory C)
    (Y : DerivedCategory B ⥤ DerivedCategory D)
    (xf : DerivedCategory.Q ⋙ X ≅ x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf : DerivedCategory.Q ⋙ Y ≅ y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : F₀ ⋙ y ⟶ x ⋙ G₀) (b : FD ⋙ Y ⟶ X ⋙ GD) : Prop :=
  ∀ I : CochainComplex A ℤ,
    Y.map (u.app I) ≫ b.app (DerivedCategory.Q.obj I) ≫ GD.map (xf.hom.app I) =
      yf.hom.app ((F₀.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c (.up ℤ)).app I) ≫
        v.app ((x.mapHomologicalComplex (.up ℤ)).obj I)

private theorem normalized_composition
    (F₀ : A ⥤ B) (G₀ : C ⥤ D) (H₀ : E ⥤ F)
    [F₀.Additive] [G₀.Additive] [H₀.Additive]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (GD : DerivedCategory C ⥤ DerivedCategory D)
    (HD : DerivedCategory E ⥤ DerivedCategory F)
    (u : F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FD)
    (v : G₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ GD)
    (w : H₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ HD)
    (x : A ⥤ C) (y : B ⥤ D) (z : C ⥤ E) (t : D ⥤ F)
    [x.Additive] [y.Additive] [z.Additive] [t.Additive]
    (X : DerivedCategory A ⥤ DerivedCategory C)
    (Y : DerivedCategory B ⥤ DerivedCategory D)
    (Z : DerivedCategory C ⥤ DerivedCategory E)
    (T : DerivedCategory D ⥤ DerivedCategory F)
    (xf : DerivedCategory.Q ⋙ X ≅ x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf : DerivedCategory.Q ⋙ Y ≅ y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (zf : DerivedCategory.Q ⋙ Z ≅ z.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (tf : DerivedCategory.Q ⋙ T ≅ t.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : F₀ ⋙ y ⟶ x ⋙ G₀) (d : G₀ ⋙ t ⟶ z ⋙ H₀)
    (b : FD ⋙ Y ⟶ X ⋙ GD) (e : GD ⋙ T ⟶ Z ⋙ HD)
    (hb : EtaleBrownUnitNorm F₀ G₀ FD GD u v x y X Y xf yf c b)
    (he : EtaleBrownUnitNorm G₀ H₀ GD HD v w z t Z T zf tf d e) :
    EtaleBrownUnitNorm F₀ H₀ FD HD u w (x ⋙ z) (y ⋙ t) (X ⋙ Z) (Y ⋙ T)
      (Functor.isoWhiskerRight xf Z ≪≫
        Functor.isoWhiskerLeft (x.mapHomologicalComplex (.up ℤ)) zf)
      (Functor.isoWhiskerRight yf T ≪≫
        Functor.isoWhiskerLeft (y.mapHomologicalComplex (.up ℤ)) tf)
      (Functor.whiskerRight c t ≫ Functor.whiskerLeft x d)
      (Functor.whiskerRight b T ≫ Functor.whiskerLeft X e) := by
  intro I
  dsimp only [Functor.comp_map, Functor.comp_obj, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  simp only [Category.assoc, Functor.map_comp]
  erw [← reassoc_of% e.naturality (xf.hom.app I)]
  erw [← T.map_comp_assoc, ← T.map_comp_assoc]
  erw [Category.assoc, hb I]
  simp only [Functor.map_comp, Category.assoc]
  erw [he ((x.mapHomologicalComplex (.up ℤ)).obj I)]
  erw [reassoc_of% (tf.hom.naturality
    ((NatTrans.mapHomologicalComplex c (.up ℤ)).app I))]
  simp only [← DerivedCategory.Q.map_comp_assoc]
  rfl

/-- Naturality of squares specified by their cochain derived-unit equations.
Source: Stacks 07A4; Zheng Lemma 5.16.
(blueprint: lem-pur-brown-unit-normalized-naturality).
Proof: precompose both routes with the source derived unit and postcompose with
the exact comparison factor. Substitute both unit normalizations, naturality of
the edge transformations, and the ordinary cube. On a K-injective complex the
source unit is invertible, so cancellation gives equality. Every derived object
has such a representative; naturality transports the equality along its
representative isomorphism. This includes zero objects and identity edges. -/
theorem etaleBrownNormalizedNaturality
    [Abelian.HasKInjectiveResolutions A]
    (F₀ : A ⥤ B) (G₀ : C ⥤ D) [F₀.Additive] [G₀.Additive]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (GD : DerivedCategory C ⥤ DerivedCategory D)
    (u : F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FD)
    (v : G₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ GD)
    (hu : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (u.app I))
    (x x' : A ⥤ C) (y y' : B ⥤ D)
    [x.Additive] [x'.Additive] [y.Additive] [y'.Additive]
    (X X' : DerivedCategory A ⥤ DerivedCategory C)
    (Y Y' : DerivedCategory B ⥤ DerivedCategory D)
    (xf : DerivedCategory.Q ⋙ X ≅ x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (xf' : DerivedCategory.Q ⋙ X' ≅ x'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf : DerivedCategory.Q ⋙ Y ≅ y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf' : DerivedCategory.Q ⋙ Y' ≅ y'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : F₀ ⋙ y ⟶ x ⋙ G₀) (c' : F₀ ⋙ y' ⟶ x' ⋙ G₀)
    (b : FD ⋙ Y ⟶ X ⋙ GD) (b' : FD ⋙ Y' ⟶ X' ⋙ GD)
    (hn : EtaleBrownUnitNorm F₀ G₀ FD GD u v x y X Y xf yf c b)
    (hn' : EtaleBrownUnitNorm F₀ G₀ FD GD u v x' y' X' Y' xf' yf' c' b')
    (a : x ⟶ x') (d : y ⟶ y') (ad : X ⟶ X') (dd : Y ⟶ Y')
    (ha : ∀ I : CochainComplex A ℤ,
      ad.app (DerivedCategory.Q.obj I) ≫ xf'.hom.app I =
        xf.hom.app I ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I))
    (hd : ∀ I : CochainComplex B ℤ,
      dd.app (DerivedCategory.Q.obj I) ≫ yf'.hom.app I =
        yf.hom.app I ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex d (.up ℤ)).app I))
    (hc : ∀ M : A, d.app (F₀.obj M) ≫ c'.app M = c.app M ≫ G₀.map (a.app M)) :
    Functor.whiskerLeft FD dd ≫ b' = b ≫ Functor.whiskerRight ad GD := by
  have hI (I : CochainComplex A ℤ) :
      Y.map (u.app I) ≫ (dd.app (FD.obj (DerivedCategory.Q.obj I)) ≫
        b'.app (DerivedCategory.Q.obj I)) =
      Y.map (u.app I) ≫ (b.app (DerivedCategory.Q.obj I) ≫
        GD.map (ad.app (DerivedCategory.Q.obj I))) := by
    apply (cancel_mono (GD.map (xf'.hom.app I))).mp
    simp only [Category.assoc]
    rw [reassoc_of% dd.naturality (u.app I)]
    rw [hn' I, reassoc_of% hd ((F₀.mapHomologicalComplex (.up ℤ)).obj I)]
    rw [← GD.map_comp, ha, Functor.map_comp, reassoc_of% hn I]
    erw [← DerivedCategory.Q.map_comp_assoc]
    have hcI :
        (NatTrans.mapHomologicalComplex d (.up ℤ)).app
            ((F₀.mapHomologicalComplex (.up ℤ)).obj I) ≫
          (NatTrans.mapHomologicalComplex c' (.up ℤ)).app I =
        (NatTrans.mapHomologicalComplex c (.up ℤ)).app I ≫
          (G₀.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I) := by
      ext n
      exact hc (I.X n)
    erw [hcI, DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    have hvn := v.naturality ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I)
    dsimp only [Functor.comp_map] at hvn
    rw [hvn]
  ext N
  obtain ⟨I, hIi, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  have hi : (Functor.whiskerLeft FD dd ≫ b').app (DerivedCategory.Q.obj I) =
      (b ≫ Functor.whiskerRight ad GD).app (DerivedCategory.Q.obj I) := by
    have := hu I hIi
    exact (cancel_epi (Y.map (u.app I))).mp (hI I)
  apply (cancel_mono ((X' ⋙ GD).map e.hom)).mp
  rw [← (Functor.whiskerLeft FD dd ≫ b').naturality,
    ← (b ≫ Functor.whiskerRight ad GD).naturality, hi]

-- Package the component calculation before specializing to large coefficient categories.
private theorem pasted_factors_naturality
    (x₁ : A ⥤ B) (x₂ : A ⥤ C) (y₁ : B ⥤ D) (y₂ : C ⥤ D)
    [x₁.Additive] [x₂.Additive] [y₁.Additive] [y₂.Additive]
    (X₁ : DerivedCategory A ⥤ DerivedCategory B)
    (X₂ : DerivedCategory A ⥤ DerivedCategory C)
    (Y₁ : DerivedCategory B ⥤ DerivedCategory D)
    (Y₂ : DerivedCategory C ⥤ DerivedCategory D)
    (xf₁ : DerivedCategory.Q ⋙ X₁ ≅ x₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (xf₂ : DerivedCategory.Q ⋙ X₂ ≅ x₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf₁ : DerivedCategory.Q ⋙ Y₁ ≅ y₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf₂ : DerivedCategory.Q ⋙ Y₂ ≅ y₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (a : x₁ ⋙ y₁ ≅ x₂ ⋙ y₂) (ad : X₁ ⋙ Y₁ ≅ X₂ ⋙ Y₂)
    (h : ∀ I : CochainComplex A ℤ,
      ad.hom.app (DerivedCategory.Q.obj I) ≫ Y₂.map (xf₂.hom.app I) ≫
          yf₂.hom.app ((x₂.mapHomologicalComplex (.up ℤ)).obj I) =
        Y₁.map (xf₁.hom.app I) ≫
          yf₁.hom.app ((x₁.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app I))
    (I : CochainComplex A ℤ) :
    ad.hom.app (DerivedCategory.Q.obj I) ≫
        (Functor.isoWhiskerRight xf₂ Y₂ ≪≫
          Functor.isoWhiskerLeft (x₂.mapHomologicalComplex (.up ℤ)) yf₂).hom.app I =
      (Functor.isoWhiskerRight xf₁ Y₁ ≪≫
          Functor.isoWhiskerLeft (x₁.mapHomologicalComplex (.up ℤ)) yf₁).hom.app I ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app I) := by
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatIso.mapHomologicalComplex, Category.assoc] using h I

end UnitSquares

section GeometricRestriction

private abbrev rightUnitNT {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app I := F.rightDerivedFunctorUnitQ I
  naturality {_ _} f := F.rightDerivedFunctorUnitQ_naturality f

private theorem quotient_hom_inv {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (I : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).hom.app I =
      (DerivedCategory.quotientCompQhIso C).inv.app I := by
  rfl

private theorem geometric_exact_adjunction
    (Λ : Type (u + 1)) [CommRing Λ] {V W : Scheme.{u}} (g : V ⟶ W) :
    (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryRightDerivedAdjunction =
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).ofNatIsoLeft
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g) := by
  let f := Etale.upperStar (ModuleCat.{u + 1} Λ) g
  let a := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g
  refine (a.mapHomotopyCategory (.up ℤ)).derived_eq_ofNatIsoLeft
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
    f.leftDerivedFunctorIsoMapDerivedCategory.symm ?_
  ext K
  simp only [Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]

private theorem geometric_restriction_normalized
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {V W : Scheme.{u}} (g : V ⟶ W) :
    EtaleBrownUnitNorm (Etale.lowerStar (ModuleCat.{u + 1} Λ') g)
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) g)
      (Etale.lowerStar (ModuleCat.{u + 1} Λ') g).rightDerivedFunctor
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor
      (rightUnitNT _) (rightUnitNT _)
      (Sheaf.restrictScalars V.smallEtaleTopology φ)
      (Sheaf.restrictScalars W.smallEtaleTopology φ)
      (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
      (Sheaf.restrictScalars V.smallEtaleTopology φ).mapDerivedCategoryFactors
      (Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryFactors
      (Etale.lowerStarRestrictScalarsIso φ g).hom
      (Etale.scalarRestrictionDirectImageMap φ g) := by
  have hm : (mateEquiv
      (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ') g).mapDerivedCategoryRightDerivedAdjunction
      (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryRightDerivedAdjunction
      (.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
        (Etale.upperStarRestrictScalarsIsoSheaf φ g)).hom)) =
        Etale.scalarRestrictionDirectImageMap φ g := by
    rw [geometric_exact_adjunction, geometric_exact_adjunction, right_mate_transport]
    rfl
  intro I
  rw [← hm]
  apply mate_right_normalized
    (Etale.upperStar (ModuleCat.{u + 1} Λ') g)
    (Etale.lowerStar (ModuleCat.{u + 1} Λ') g)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) g)
    (Etale.upperStarLowerStarAdjunction _ g) (Etale.upperStarLowerStarAdjunction _ g)
    (Sheaf.restrictScalars W.smallEtaleTopology φ)
    (Sheaf.restrictScalars V.smallEtaleTopology φ)
    _ _ _ _ _ _ _ _
    (Etale.upperStar (ModuleCat.{u + 1} Λ') g).mapDerivedCategoryFactors
    (Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryFactors
    (Sheaf.restrictScalars V.smallEtaleTopology φ).mapDerivedCategoryFactors
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryFactors
    (rightUnitNT _) (rightUnitNT _)
    (exact_transpose _ _ _) (exact_transpose _ _ _)
    (Etale.upperStarRestrictScalarsIsoSheaf φ g)
    (Etale.lowerStarRestrictScalarsIso φ g).hom (Etale.underived_mate φ g)
    (Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIsoSheaf φ g))
  intro P
  simpa only [CategoryTheory.IndependentDerivedCube.localizedSquare] using
    (CategoryTheory.IndependentDerivedCube.squareFactors
      (Sheaf.restrictScalars W.smallEtaleTopology φ)
      (Sheaf.restrictScalars V.smallEtaleTopology φ)
      (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
      (Etale.upperStar (ModuleCat.{u + 1} Λ') g)
      (Etale.upperStarRestrictScalarsIsoSheaf φ g) P)

end GeometricRestriction

section CoefficientRestriction
attribute [local irreducible] coefficientQuotientSheaf coefficientQuotientMap
  siteCoefficientTensorAdj
variable (O : Type (u + 1)) [CommRing O] (t : O)
  {V W : Scheme.{u}} (g : V ⟶ W)
  (A : StrictEtaleOrdinaryImage O t g)
  (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
  (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
    (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
  {m n : ℕ} (h : m ≤ n)

-- Compare the normalized scalar mate on flat representatives.
private theorem coefficient_restriction_normalized :
    ∃ β : (PW.scalar h).restriction ⋙ (B.level n).inverse ≅
      (B.level m).inverse ⋙ (PV.scalar h).restriction,
    (mateEquiv (B.level m).adjunction (B.level n).adjunction
      (.mk _ _ _ _ β.hom)) = (B.restrictedDirect h).inv ∧
    ∀ K : CochainComplex (strictEtaleLevel W O t m) ℤ,
      β.hom.app (DerivedCategory.Q.obj K) ≫
        (PV.scalar h).restriction.map ((B.level m).inverseFactors.hom.app K) ≫
        (PV.scalar h).restrictionFactors.hom.app
          (((A.lift m).modules.mapHomologicalComplex (.up ℤ)).obj K) =
      (B.level n).inverse.map ((PW.scalar h).restrictionFactors.hom.app K) ≫
        (B.level n).inverseFactors.hom.app
          (((coefficientRestriction.{u + 1, u, u + 1}
            (J := W.smallEtaleTopology) O t h).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (A.restrictInverse h) (.up ℤ)).hom.app K) := by
  have : PreservesFiniteLimits (A.lift n).modules := (A.inverseExact n).1
  have : PreservesFiniteColimits (A.lift n).modules := (A.inverseExact n).2
  obtain ⟨β, hβ⟩ := exists_derivedSquare_independentUniverses
    (coefficientRestriction.{u + 1, u, u + 1} (J := W.smallEtaleTopology) O t h)
    (A.lift m).modules (A.lift n).modules
    (coefficientRestriction.{u + 1, u, u + 1} (J := V.smallEtaleTopology) O t h)
    (PW.scalar h).restriction (B.level m).inverse (B.level n).inverse
    (PV.scalar h).restriction (PW.scalar h).restrictionFactors
    (B.level m).inverseFactors (B.level n).inverseFactors
    (PV.scalar h).restrictionFactors (A.restrictInverse h)
  let τ := ((mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj).symm
    (.mk _ _ _ _ β.hom))
  have hτ : τ = (B.derivedTensor h).inv := by
    apply hom_ext_flat W.smallEtaleTopology n
    intro P hk hf
    have hrep := derivedLeftSquare_rep (A.lift n).modules
      (coefficientTensor.{u + 1, u, u + 1} (J := W.smallEtaleTopology)
        (O := O) (ell := t) h)
      (coefficientRestriction.{u + 1, u, u + 1} (J := W.smallEtaleTopology) O t h)
      (coefficientTensor.{u + 1, u, u + 1} (J := V.smallEtaleTopology)
        (O := O) (ell := t) h)
      (coefficientRestriction.{u + 1, u, u + 1} (J := V.smallEtaleTopology) O t h)
      (coefficientTensorAdj.{u + 1, u, u + 1} (J := W.smallEtaleTopology)
        (O := O) (ell := t) h)
      (coefficientTensorAdj.{u + 1, u, u + 1} (J := V.smallEtaleTopology)
        (O := O) (ell := t) h)
      _ _ (PW.scalar h) (PV.scalar h) (A.lift m).modules
      (B.level n).inverse (B.level m).inverse
      (B.level n).inverseFactors (B.level m).inverseFactors
      (A.restrictInverse h) β hβ (B.tensor h).symm
      (tensorSquare_transpose (A.lift n).modules
        (coefficientTensor.{u + 1, u, u + 1} (J := W.smallEtaleTopology)
        (O := O) (ell := t) h)
        (coefficientRestriction.{u + 1, u, u + 1} (J := W.smallEtaleTopology) O t h)
        (coefficientTensor.{u + 1, u, u + 1} (J := V.smallEtaleTopology)
        (O := O) (ell := t) h)
        (coefficientRestriction.{u + 1, u, u + 1} (J := V.smallEtaleTopology) O t h)
        (A.lift m).modules
        (coefficientTensorAdj.{u + 1, u, u + 1} (J := W.smallEtaleTopology)
        (O := O) (ell := t) h)
        (coefficientTensorAdj.{u + 1, u, u + 1} (J := V.smallEtaleTopology)
        (O := O) (ell := t) h)
        (A.restrictInverse h) (B.tensor h) (B.tensor_unit h)) P
    have hcomp := (PW.scalar h).computes P hk
    apply (cancel_mono
      ((B.level m).inverse.map ((PW.scalar h).counit.app P) ≫
        (B.level m).inverseFactors.hom.app
          (((coefficientTensor.{u + 1, u, u + 1} (J := W.smallEtaleTopology)
        (O := O) (ell := t) h).mapHomologicalComplex (.up ℤ)).obj P))).mp
    change τ.app _ ≫ _ = _
    rw [show τ.app _ ≫ _ = _ from hrep]
    have hh := B.derivedTensor_rep h P hk hf
    have hh' := congrArg (fun z ↦ (B.derivedTensor h).inv.app
      (DerivedCategory.Q.obj P) ≫ z ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (B.tensor h).symm (.up ℤ)).hom.app P)) hh
    have hθ :
        (NatIso.mapHomologicalComplex (B.tensor h) (.up ℤ)).hom.app P ≫
          (NatIso.mapHomologicalComplex (B.tensor h).symm (.up ℤ)).hom.app P = 𝟙 _ := by
      exact (NatIso.mapHomologicalComplex (B.tensor h) (.up ℤ)).hom_inv_id_app P
    dsimp only [CoefficientSystemDerivedImage.derivedTensor,
      CoefficientSystemDerivedImage.tensor, CoefficientSystemDerivedImage.level] at hh' hθ ⊢
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← DerivedCategory.Q.map_comp,
      hθ] at hh'
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh'
    exact hh'
  refine ⟨β, ?_, hβ⟩
  have ht : (mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj
      (.mk _ _ _ _ (B.derivedTensor h).inv)) = β.hom := by
    rw [← hτ]
    exact (Equiv.apply_symm_apply _ _)
  have hc : conjugateEquiv
      ((PW.scalar h).derivedAdj.comp (B.level m).adjunction)
      ((B.level n).adjunction.comp (PV.scalar h).derivedAdj)
      (B.derivedTensor h).inv =
      (mateEquiv (B.level m).adjunction (B.level n).adjunction
        (.mk _ _ _ _ β.hom)) := by
    rw [← iterated_mateEquiv_conjugateEquiv
      (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj
      (B.level n).adjunction (B.level m).adjunction]
    exact congrArg (fun z ↦ (mateEquiv
      (B.level m).adjunction (B.level n).adjunction z)) ht
  rw [← hc]
  exact congrArg Iso.inv (brown_scalar_conjugate
    (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj
    (B.level n).adjunction (B.level m).adjunction
    (B.derivedTensor h) (B.restrictedDirect h) (B.restrictedDirect_mate h))

private theorem coefficient_right_normalized :
    EtaleBrownUnitNorm (A.right m) (A.right n) (B.level m).direct (B.level n).direct
      (B.level m).directUnit (B.level n).directUnit
      (coefficientRestriction.{u + 1, u, u + 1} (J := V.smallEtaleTopology) O t h)
      (coefficientRestriction.{u + 1, u, u + 1} (J := W.smallEtaleTopology) O t h)
      (PV.scalar h).restriction (PW.scalar h).restriction
      (PV.scalar h).restrictionFactors (PW.scalar h).restrictionFactors
      (mateEquiv (A.levelAdj m) (A.levelAdj n)
        (.mk _ _ _ _ (A.restrictInverse h).hom))
      (B.restrictedDirect h).inv := by
  obtain ⟨β, hm, hβ⟩ := coefficient_restriction_normalized O t g A PW PV B h
  intro I
  rw [← hm]
  exact mate_right_normalized (A.lift m).modules (A.right m)
    (A.lift n).modules (A.right n) (A.levelAdj m) (A.levelAdj n)
    (coefficientRestriction.{u + 1, u, u + 1} (J := W.smallEtaleTopology) O t h)
    (coefficientRestriction.{u + 1, u, u + 1} (J := V.smallEtaleTopology) O t h)
    (B.level m).inverse (B.level m).direct (B.level m).adjunction
    (B.level n).inverse (B.level n).direct (B.level n).adjunction
    (PW.scalar h).restriction (PV.scalar h).restriction
    (B.level m).inverseFactors (PW.scalar h).restrictionFactors
    (PV.scalar h).restrictionFactors (B.level n).inverseFactors
    (B.level m).directUnit (B.level n).directUnit
    (B.level m).transpose (B.level n).transpose
    (A.restrictInverse h) _ rfl β hβ I

end CoefficientRestriction

-- Check the Brown unit equation independently of the cube.
private theorem brown_image_normalized
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    (k : ℕ) :
    letI := RV.val.ordinaryAdditive
    letI := RW.val.ordinaryAdditive
    EtaleBrownUnitNorm (A.right k)
      (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k)) g)
      (B.level k).direct
      (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k)) g).rightDerivedFunctor
      (B.level k).directUnit (rightUnitNT (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing
      O t k)) g))
      (strictEtaleBrownConstant O t V k) (strictEtaleBrownConstant O t W k) (RV.derived k)
      (RW.derived k)
      (RV.factors k) (RW.factors k) (rg k).val.ordinaryRight.hom
      (rg k).right.hom := by
  let := RV.val.ordinaryAdditive
  let := RW.val.ordinaryAdditive
  intro I
  simpa only [EtaleBrownUnitNorm, rightUnitNT, strictEtaleBrownRightUnit,
    Functor.rightDerivedFunctorUnitQ, quotient_hom_inv] using (rg k).property.2.1 I

end AlgebraicGeometry
