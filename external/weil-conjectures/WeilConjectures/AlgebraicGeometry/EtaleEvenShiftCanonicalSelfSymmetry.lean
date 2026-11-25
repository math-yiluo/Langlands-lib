/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData

/-! # Identity derived self symmetry of an even shifted flat object

Source: blueprint latest, second triangle even-shift computation.
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
suppress_compilation
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoordinateTrace
private lemma self_braiding_of_iso {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {X Z : C} (e : X ≅ Z) (h : (β_ Z Z).hom = 𝟙 _) :
    (β_ X X).hom = 𝟙 _ := by
  have : IsIso (e.hom ⊗ₘ e.hom) := inferInstance
  apply (cancel_mono (e.hom ⊗ₘ e.hom)).1
  simpa only [BraidedCategory.braiding_naturality, h, Category.comp_id,
    Category.id_comp] using BraidedCategory.braiding_naturality e.hom e.hom |>.symm

private lemma single_even_braiding {C : Type*} [Category C] [Abelian C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] (J : C) (hJ : (β_ J J).hom = 𝟙 _)
    (n : ℤ) (hn : Even n) :
    let S := (HomologicalComplex.single C (.up ℤ) n).obj J
    (β_ S S).hom = 𝟙 _ := by
  let S := (HomologicalComplex.single C (.up ℤ) n).obj J
  ext k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  by_cases hp : p = n
  · subst p
    by_cases hq : q = n
    · subst q
      have h : (β_ (S.X n) (S.X n)).hom = 𝟙 _ :=
        self_braiding_of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) n J) hJ
      change HomologicalComplex.ιTensorObj S S n n k hpq ≫
        (CochainComplex.Monoidal.braiding S S).hom.f k =
          HomologicalComplex.ιTensorObj S S n n k hpq ≫ 𝟙 _
      rw [Category.comp_id, CochainComplex.Monoidal.ι_braiding_hom]
      simp only [Int.negOnePow_mul_self,
        Int.negOnePow_even n hn, Units.val_one, one_smul, h, Category.id_comp]
    · exact ((tensorLeft (S.X n)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) n J q hq)).eq_of_src _ _
  · exact ((tensorRight (S.X q)).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) n J p hp)).eq_of_src _ _

section DerivedBraiding

attribute [local instance] _root_.DerivedCategory.braidedCategory'

private lemma derived_single_even_braiding
    {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (J : C) (hflat : ObjectProperty.flat J) (hJ : (β_ J J).hom = 𝟙 _)
    (n : ℤ) (hn : Even n) :
    (β_ ((_root_.DerivedCategory.singleFunctor C n).obj J)
      ((_root_.DerivedCategory.singleFunctor C n).obj J)).hom = 𝟙 _ := by
  let : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C
  let S := (HomologicalComplex.single C (.up ℤ) n).obj J
  let H := HomotopyCategory.quotient C (.up ℤ)
  let P := H.obj S
  have hk : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat P :=
    (HomotopyCategory.kFlat_quotient_obj_iff S).2
      ((CochainComplex.kFlat_single_obj_iff_flat J n).2 hflat)
  let e : (_root_.DerivedCategory.singleFunctor C n).obj J ≅
      _root_.DerivedCategory.Qh.obj P :=
    (_root_.DerivedCategory.singleFunctorIsoCompQ C n).app J ≪≫
      (_root_.DerivedCategory.quotientCompQhIso C).symm.app S
  apply self_braiding_of_iso e
  have hp : (β_ P P).hom = 𝟙 _ := by
    change H.map (β_ S S).hom = _
    rw [single_even_braiding J hJ n hn, H.map_id]
    rfl
  have : IsIso (Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh P P) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left _root_.DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) P P hk
  apply (cancel_mono (Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh P P)).1
  have hb :
      (β_ (_root_.DerivedCategory.Qh.obj P) (_root_.DerivedCategory.Qh.obj P)).hom ≫
          Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh P P =
        Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh P P ≫
          _root_.DerivedCategory.Qh.map (β_ P P).hom :=
    DerivedMonoidal.braiding_hom_μ _root_.DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) P P
  rw [hp, CategoryTheory.Functor.map_id, Category.comp_id] at hb
  simpa only [Category.id_comp] using hb

@[irreducible]
private def shifted_single_iso {C : Type*} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 1} C] (J : C) (d : ℤ) :
    ((_root_.DerivedCategory.singleFunctor C 0).obj J)⟦(2 * d : ℤ)⟧ ≅
      (_root_.DerivedCategory.singleFunctor C (-2 * d)).obj J :=
  ((_root_.DerivedCategory.singleFunctors C).shiftIso (2 * d) (-2 * d) 0
    (by omega)).app J

/-- Identity derived self symmetry of an even shifted flat object.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, second triangle.
(auxiliary; not a blueprint node).

Proof: For a single complex in even degree n, use total-tensor coproduct extensionality. Every
summand except bidegree (n,n) has zero source. The explicit Koszul braiding on that summand is the
ordinary braiding multiplied by (-1)^(n*n); evenness makes this sign one. Naturality along
singleObjXSelf transports the assumed ordinary self braiding.
The single complex is K-flat since J is flat. The quotient preserves its identity braiding.
Compatibility braiding_hom_mu identifies the derived braiding followed by the Qh tensor comparison
with the comparison followed by Qh of the homotopy braiding. The comparison is invertible for this
K-flat object, so cancellation gives identity.
The canonical singleFunctors.shiftIso identifies J[2d] with the single in degree -2d. This degree
is even also for negative d. Braiding naturality along this isomorphism transports the preceding
result. -/
theorem evenShiftCanonicalSelfSymmetry
    {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (J : C) (hflat : ObjectProperty.flat J) (hJ : (β_ J J).hom = 𝟙 _) (d : ℤ) :
    let L := ((_root_.DerivedCategory.singleFunctor C 0).obj J)⟦(2 * d : ℤ)⟧
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).hom.app L).app L = 𝟙 _ :=
  self_braiding_of_iso (shifted_single_iso J d)
    (derived_single_even_braiding J hflat hJ (-2 * d) ⟨-d, by ring⟩)

end DerivedBraiding

end AlgebraicGeometry.Etale.CoordinateTrace
