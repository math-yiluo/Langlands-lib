/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageScalarModels
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageColumns
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageScalarShift
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageShift
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingCoherence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Finite-free direct-image coefficient coherence

Source: Stacks Project, Tags 0B56 and 0944
(blueprint: lem-sp-finite-free-direct-image-coherence).

All module and derived categories are the existing ones. The auxiliary records bundle
coefficient squares and normalized presentations of the existing scalar functors.
Balancing is the conjugate of the canonical restriction/direct-image comparison, and
its right mate is the specified counit-tensor map. No arbitrary comparison is bound.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

private theorem comparison_isIso_app_private {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (hfree : Nonempty ((proEtaleRingRestrictScalars a.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
            (ULift.{u + 1} (Fin d))))
    (M : DerivedCategory (proEtaleRingModules Z R.source)) :
    IsIso ((comparison sW sZ a).app M) := by
  obtain ⟨eW, eZ, hcol⟩ := finiteFreeDirectImage_columns q sW sZ R S a d hfree M
  let G := proEtaleRingDerivedDirectImage q R.target R.source R.identification
  let U := (proEtaleRingRestrictScalars a.target).mapDerivedCategory
  let δ := proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  let f := (comparison sW sZ a).app M
  have heq : eW.hom ≫ U.map f ≫ δ.hom.app ((sZ.presentation a.source).derived.obj M) =
      (Functor.mapBiproduct G (fun _ : Fin d ↦ M)).inv ≫ G.map eZ.hom := by
    apply biproduct.hom_ext'
    intro i
    simpa only [Category.assoc, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc,
      ← G.map_comp] using hcol i
  have : IsIso (eW.hom ≫ U.map f ≫
      δ.hom.app ((sZ.presentation a.source).derived.obj M)) := by
    rw [heq]
    infer_instance
  have : IsIso (U.map f ≫ δ.hom.app ((sZ.presentation a.source).derived.obj M)) :=
    IsIso.of_isIso_comp_left eW.hom _
  have : IsIso (U.map f) := IsIso.of_isIso_comp_right _
    (δ.hom.app ((sZ.presentation a.source).derived.obj M))
  have : U.ReflectsIsomorphisms :=
    (proEtaleRingSheafChangeAdjunction q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm).2.1
  exact isIso_of_reflects_iso f U

/-- The identity equation for the actual direct-image mate.
Source: Stacks Project, Tags 0B56 and 0D6D.
(blueprint: lem-sp-finite-free-direct-image-coherence).

Proof: whisker the balancing square by the scalar multiplication units. Balancing
coherence identifies this square with the identity square. Whiskering commutes
with the mates correspondence, and the mate of the identity square is the identity.
Evaluating this equality gives the displayed equation. -/
private theorem finiteFreeDirectImageUnit {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z) (R : Coefficients q)
    (M : DerivedCategory (proEtaleRingModules Z R.source)) :
    (sW.unit R.target).inv.app
        ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≫
      (comparison sW sZ (CoefficientMap.id R)).app M ≫
      (proEtaleRingDerivedDirectImage q R.target R.source R.identification).map
        ((sZ.unit R.source).hom.app M) = 𝟙 _ := by
  let adj := proEtaleRingDerivedAdjunction q R.target R.source R.identification
  let L := proEtaleRingDerivedPullback q R.target R.source R.identification
  let α := TwoSquare.mk _ _ _ _ (balancing sW sZ (CoefficientMap.id R)).hom
  have heq : (α.whiskerTop (sW.unit R.target).inv).whiskerBottom (sZ.unit R.source).hom =
      TwoSquare.mk (𝟭 _) L L (𝟭 _)
        ((Functor.leftUnitor L).hom ≫ (Functor.rightUnitor L).inv) := by
    ext K
    simpa [α, TwoSquare.whiskerTop, TwoSquare.whiskerBottom] using
      (finiteFreeDirectImageBalancingCoherence q sW sZ).1 R K
  have h := mateEquiv_whiskerTop_whiskerBottom adj adj α
    (sW.unit R.target).inv (sZ.unit R.source).hom
  rw [heq, mateEquiv_unitors] at h
  have hc := congrArg (fun t ↦ t.app M) h
  simpa [comparison, α, TwoSquare.whiskerRight, TwoSquare.whiskerLeft] using hc.symm

/-- The coefficient tower equation for the actual direct-image mate.
Source: Stacks Project, Tags 0B56 and 0D6D.
(blueprint: lem-sp-finite-free-direct-image-coherence).

Proof: horizontally paste the two balancing squares and whisker by the inverse
target associator and source associator. Balancing coherence identifies this with
the single square for the composite ring map. Mate pasting identifies its mate
with the vertical paste of the two direct-image comparisons. Compatibility of
whiskering with mates supplies the two displayed associators. -/
private theorem finiteFreeDirectImageTower {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    (R S B : Coefficients q) (a : CoefficientMap R S) (b : CoefficientMap S B)
    (M : DerivedCategory (proEtaleRingModules Z R.source)) :
    (comparison sW sZ (a.comp b)).app M =
      (sW.normalization.derived a.target b.target).inv.app
          ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≫
        (sW.presentation b.target).derived.map ((comparison sW sZ a).app M) ≫
        (comparison sW sZ b).app ((sZ.presentation a.source).derived.obj M) ≫
        (proEtaleRingDerivedDirectImage q B.target B.source B.identification).map
          ((sZ.normalization.derived a.source b.source).hom.app M) := by
  let ar := proEtaleRingDerivedAdjunction q R.target R.source R.identification
  let as' := proEtaleRingDerivedAdjunction q S.target S.source S.identification
  let ab := proEtaleRingDerivedAdjunction q B.target B.source B.identification
  let α := TwoSquare.mk _ _ _ _ (balancing sW sZ a).hom
  let β := TwoSquare.mk _ _ _ _ (balancing sW sZ b).hom
  have heq : TwoSquare.whiskerBottom
      ((TwoSquare.hComp α β).whiskerTop (sW.normalization.derived a.target b.target).inv)
      (sZ.normalization.derived a.source b.source).hom =
      TwoSquare.mk _ _ _ _ (balancing sW sZ (a.comp b)).hom := by
    ext K
    simpa [α, β, TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom] using
      ((finiteFreeDirectImageBalancingCoherence q sW sZ).2 R S B a b K).symm
  have h := mateEquiv_whiskerTop_whiskerBottom ar ab (TwoSquare.hComp α β)
    (sW.normalization.derived a.target b.target).inv
    (sZ.normalization.derived a.source b.source).hom
  rw [heq, mateEquiv_vcomp ar as' ab] at h
  have hc := congrArg (fun t ↦ t.app M) h
  simpa [comparison, α, β, ar, as', ab, CoefficientMap.comp, TwoSquare.vComp,
    TwoSquare.whiskerRight,
    TwoSquare.whiskerLeft, Category.assoc] using hc

/-- Finite-free scalar change commutes canonically with ordinary unbounded derived
pushforward, as an isomorphism of exact functors, with input-shift, identity and tower
coherence. All equalities take place in the enlarged coefficient module category.
The existential scalar models only present the recorded universal derived functors;
their ordinary tensors, derived counits, units, adjunctions and associators are normalized.
In particular neither a balancing isomorphism nor a shift structure is an extra hypothesis.

Source: Stacks Tags 0B56 and 0944; shift and coefficient-tower coherences are extracted
from the counit-tensor construction (blueprint: lem-sp-finite-free-direct-image-coherence).

Proof:
1. Construct normalized scalar models by transporting the recorded restriction models
through their localization factorizations. Multiplication is the counit for identity
scalars; its universal localization gives the derived unit.
2. The inverse mate of exact restriction's factorization is the universal scalar counit
on flat-term K-flat complexes, hence on all complexes by resolving and naturality.
It commutes with shifts. The left adjoint of triangulated restriction is triangulated.
3. The finite-basis column calculation gives two biproduct coordinate isomorphisms.
Biproduct extensionality identifies the restricted comparison with the inverse
mapBiproduct comparison followed by the direct image of the source coordinates.
This is invertible, including for the empty biproduct. Conservative restriction
reflects its invertibility.
4. The canonical derived geometric adjunctions commute with their canonical shifts.
The restriction/direct-image comparison is the mate of the termwise restriction/
pullback comparison. Conjugating and taking its mate therefore proves the required
shift compatibility for the specified comparison.
5. Whisker balancing by the multiplication units. Its coherence equation identifies
this square with the identity square. Compatibility of mates with whiskering and
the mate of the identity square give the displayed identity equation.
6. Horizontally paste the two balancing squares and whisker with the two scalar
associators. Balancing coherence identifies this with the composite coefficient
square. Mate pasting gives the displayed tower equation in the stated factor order.
-/
theorem finiteFreeDirectImageCoherence {Z W : Scheme.{u}} (q : Z ⟶ W) :
    ∃ (sW : ScalarModel W) (sZ : ScalarModel Z),
      (∀ {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S),
        (sW.presentation a).derived.IsTriangulated ∧
          NatTrans.CommShift (sW.presentation a).counit ℤ) ∧
      (∀ {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}} (a : R ⟶ S),
        (sZ.presentation a).derived.IsTriangulated ∧
          NatTrans.CommShift (sZ.presentation a).counit ℤ) ∧
      (∀ (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ),
        Nonempty ((proEtaleRingRestrictScalars a.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
            (ULift.{u + 1} (Fin d))) →
        IsIso (comparison sW sZ a) ∧ NatTrans.CommShift (comparison sW sZ a) ℤ ∧
          (proEtaleRingDerivedDirectImage q R.target R.source R.identification ⋙
            (sW.presentation a.target).derived).IsTriangulated ∧
          ((sZ.presentation a.source).derived ⋙
            proEtaleRingDerivedDirectImage q S.target S.source S.identification).IsTriangulated) ∧
      (∀ (R : Coefficients q) (M : DerivedCategory (proEtaleRingModules Z R.source)),
        (sW.unit R.target).inv.app
            ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≫
          (comparison sW sZ (CoefficientMap.id R)).app M ≫
          (proEtaleRingDerivedDirectImage q R.target R.source R.identification).map
            ((sZ.unit R.source).hom.app M) = 𝟙 _) ∧
      (∀ (R S B : Coefficients q) (a : CoefficientMap R S) (b : CoefficientMap S B)
        (d e : ℕ),
        Nonempty ((proEtaleRingRestrictScalars a.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
            (ULift.{u + 1} (Fin d))) →
        Nonempty ((proEtaleRingRestrictScalars b.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)
            (ULift.{u + 1} (Fin e))) →
        ∀ M : DerivedCategory (proEtaleRingModules Z R.source),
          (comparison sW sZ (a.comp b)).app M =
            (sW.normalization.derived a.target b.target).inv.app
                ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≫
              (sW.presentation b.target).derived.map ((comparison sW sZ a).app M) ≫
              (comparison sW sZ b).app ((sZ.presentation a.source).derived.obj M) ≫
              (proEtaleRingDerivedDirectImage q B.target B.source B.identification).map
                ((sZ.normalization.derived a.source b.source).hom.app M))  := by
  obtain ⟨sW⟩ := finiteFreeDirectImageScalarModels W
  obtain ⟨sZ⟩ := finiteFreeDirectImageScalarModels Z
  refine ⟨sW, sZ, ?_, ?_, ?_, ?_, ?_⟩
  · intro R S a
    exact finiteFreeDirectImageScalarShift sW a
  · intro R S a
    exact finiteFreeDirectImageScalarShift sZ a
  · intro R S a d hfree
    have hW := (finiteFreeDirectImageScalarShift sW a.target).1
    have hZ := (finiteFreeDirectImageScalarShift sZ a.source).1
    let := hW
    let := hZ
    have hi (M : DerivedCategory (proEtaleRingModules Z R.source)) :
        IsIso ((comparison sW sZ a).app M) :=
      comparison_isIso_app_private q sW sZ R S a d hfree M
    exact ⟨NatIso.isIso_of_isIso_app _, finiteFreeDirectImageShift sW sZ a,
      inferInstance, inferInstance⟩
  · exact finiteFreeDirectImageUnit q sW sZ
  · intro R S B a b d e ha hb M
    exact finiteFreeDirectImageTower q sW sZ R S B a b M

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage

namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage
/-- Public export of the private `comparison_isIso_app_private` (used by `import all` importers;
linter.privateModule). -/
alias comparison_isIso_app := comparison_isIso_app_private

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
