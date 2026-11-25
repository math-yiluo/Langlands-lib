/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfSupportedCoordinateTensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-! # The coefficient braid in the second coordinate extraction

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, second triangle: common coefficient and even symmetry.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

open MonoidalCategory BraidedCategory in
private theorem even_cyclic_braid
    {W : Type*} [Category W] [MonoidalCategory W] [SymmetricCategory W]
    {E B : W} (c : E ≅ B) (Q : W)
    (hB : (β_ B B).hom = 𝟙 _) :
    (α_ E Q B).hom ≫ E ◁ (β_ Q B).hom ≫ (β_ E (B ⊗ Q)).hom ≫
        (B ⊗ Q) ◁ c.hom = (c.hom ▷ Q) ▷ B := by
  have he : (α_ B Q B).hom ≫ B ◁ (β_ Q B).hom ≫
      (β_ B (B ⊗ Q)).hom = 𝟙 _ := by
    simp only [braiding_tensor_right_hom, hB, id_whiskerRight, Category.id_comp,
      Iso.inv_hom_id_assoc]
    rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id,
      Category.id_comp, Iso.hom_inv_id]
  rw [← braiding_naturality_left, whisker_exchange_assoc,
    ← associator_naturality_left_assoc, he, Category.comp_id]

open MonoidalCategory BraidedCategory in
private theorem coefficient_braid_formal
    {D W : Type*} [Category D] [Category W]
    [MonoidalCategory D] [MonoidalCategory W] [SymmetricCategory W]
    (R V : D ⥤ W) (B Q : D)
    (r : R.obj (B ⊗ Q) ≅ R.obj B ⊗ R.obj Q)
    (v : V.obj (B ⊗ Q) ≅ V.obj B ⊗ V.obj Q)
    (cB : R.obj B ≅ V.obj B) (cQ : R.obj Q ≅ V.obj Q)
    (cM : R.obj (B ⊗ Q) ≅ V.obj (B ⊗ Q))
    (hc : cM.hom ≫ v.hom = r.hom ≫ (cB.hom ⊗ₘ cQ.hom))
    (hB : (β_ (V.obj B) (V.obj B)).hom = 𝟙 _) :
    (whiskerRightIso
        (r ≪≫ whiskerLeftIso (R.obj B) cQ) (V.obj B) ≪≫
      α_ (R.obj B) (V.obj Q) (V.obj B) ≪≫
      whiskerLeftIso (R.obj B) (β_ (V.obj Q) (V.obj B)) ≪≫
      whiskerLeftIso (R.obj B) v.symm ≪≫
      β_ (R.obj B) (V.obj (B ⊗ Q))) =
    (whiskerRightIso cM (V.obj B) ≪≫
      whiskerLeftIso (V.obj (B ⊗ Q)) cB.symm) := by
  apply Iso.ext
  simp only [Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom, Iso.symm_hom,
    comp_whiskerRight, Category.assoc]
  apply (cancel_mono ((V.obj (B ⊗ Q) ◁ cB.hom) ≫ v.hom ▷ V.obj B)).1
  simp only [Category.assoc]
  conv_rhs =>
    rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  rw [braiding_naturality_right_assoc, ← whisker_exchange_assoc]
  simp only [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
  rw [even_cyclic_braid cB (V.obj Q) hB]
  rw [hc, MonoidalCategory.tensorHom_def']
  simp only [comp_whiskerRight]

namespace AlgebraicGeometry.Etale.SupportedTrace

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  _root_.DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions

section GeneralCoefficients

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [UpperStarPreservesFlat C]

open MonoidalCategory BraidedCategory in
private theorem pullback_even {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (hL : (((derivedTensorSymmetry C Y).app L).app L).hom = 𝟙 _) :
    (((derivedTensorSymmetry C X).app ((upperStar C f).leftDerivedFunctor.obj L)).app
      ((upperStar C f).leftDerivedFunctor.obj L)).hom = 𝟙 _ := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf Y.smallEtaleTopology C)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology C)
  change (β_ L L).hom = 𝟙 _ at hL
  have h := leftDerivedUpperStar_map_braiding_hom_δ C f L L
  rw [leftDerivedUpperStar_δ_eq] at h
  change (upperStar C f).leftDerivedFunctor.map (β_ L L).hom ≫
      (leftDerivedUpperStarTensorIso C f L L).hom =
    (leftDerivedUpperStarTensorIso C f L L).hom ≫
      (β_ ((upperStar C f).leftDerivedFunctor.obj L)
        ((upperStar C f).leftDerivedFunctor.obj L)).hom at h
  rw [hL, CategoryTheory.Functor.map_id, Category.id_comp] at h
  change (β_ ((upperStar C f).leftDerivedFunctor.obj L)
    ((upperStar C f).leftDerivedFunctor.obj L)).hom = 𝟙 _
  let U := (upperStar C f).leftDerivedFunctor
  let d : U.obj (L ⊗ L) ≅ U.obj L ⊗ U.obj L := leftDerivedUpperStarTensorIso C f L L
  change d.hom = d.hom ≫ (β_ (U.obj L) (U.obj L)).hom at h
  exact (cancel_epi d.hom).1 (h.symm.trans (Category.comp_id d.hom).symm)

omit [UpperStarPreservesFlat C] in
private theorem square_inverse {Z X Y S : Scheme.{u}}
    (a : Z ⟶ X) (b : Z ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    (w : a ≫ f = b ≫ g) :
    derivedSquareUpperStarIso C (CommSq.mk w.symm) =
      (derivedSquareUpperStarIso C (CommSq.mk w)).symm := by
  have h : ∀ (t₁ t₂ : Z ⟶ S) (h₁ : t₁ = a ≫ f) (h₂ : t₂ = b ≫ g)
      (v : t₁ = t₂),
      (leftDerivedUpperStarComp C a f t₂ (v.symm.trans h₁)).symm ≪≫
          leftDerivedUpperStarComp C b g t₂ h₂ =
        ((leftDerivedUpperStarComp C b g t₁ (v.trans h₂)).symm ≪≫
          leftDerivedUpperStarComp C a f t₁ h₁).symm := by
    intro t₁ t₂ h₁ h₂ v
    cases v
    rfl
  exact h (a ≫ f) (b ≫ g) rfl rfl w

open MonoidalCategory BraidedCategory in
private theorem coefficient_braid_generic {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (hL : (((derivedTensorSymmetry C Y).app L).app L).hom = 𝟙 _)
    {B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)}
    (e : B ≅ (upperStar C f).leftDerivedFunctor.obj L)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    ((derivedTensor C (pullback f f)).mapIso (coefficientSplit C f B K)).app
        ((upperStar C (pullback.snd f f)).leftDerivedFunctor.obj B) ≪≫
      cyclicShuffle C (pullback.snd f f)
        ((upperStar C (pullback.fst f f)).leftDerivedFunctor.obj B) B
        ((upperStar C f).leftDerivedFunctor.obj K) =
    ((derivedTensor C (pullback f f)).mapIso (tensorCoordinate C f L K e)).app
        ((upperStar C (pullback.snd f f)).leftDerivedFunctor.obj B) ≪≫
      ((derivedTensor C (pullback f f)).obj
        ((upperStar C (pullback.snd f f)).leftDerivedFunctor.obj
          (((derivedTensor C X).obj B).obj ((upperStar C f).leftDerivedFunctor.obj K)))).mapIso
            (coefficientCoordinate C f L e).symm := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf Y.smallEtaleTopology C)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology C)
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf (pullback f f).smallEtaleTopology C)
  let U := (upperStar C f).leftDerivedFunctor
  let R := (upperStar C (pullback.fst f f)).leftDerivedFunctor
  let V := (upperStar C (pullback.snd f f)).leftDerivedFunctor
  let r : ∀ N Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      R.obj (N ⊗ Q) ≅ R.obj N ⊗ R.obj Q :=
    leftDerivedUpperStarTensorIso C (pullback.fst f f)
  let v : ∀ N Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      V.obj (N ⊗ Q) ≅ V.obj N ⊗ V.obj Q :=
    leftDerivedUpperStarTensorIso C (pullback.snd f f)
  let c := derivedSquareUpperStarIso C
    (CommSq.mk (pullback.condition (f := f) (g := f)).symm)
  let Q := U.obj K
  let cB := coefficientCoordinate C f L e
  let cM := tensorCoordinate C f L K e
  have hc : cM.hom ≫ (v B Q).hom =
      (r B Q).hom ≫ (cB.hom ⊗ₘ c.hom.app K) := by
    have h := coordinateTensor C f L K e
    change cM.hom ≫ (v B Q).hom =
      (r B Q).hom ≫ (cB.hom ⊗ₘ c.hom.app K) at h
    exact h
  have hB : (β_ B B).hom = 𝟙 _ := by
    have h := pullback_even C f L hL
    change (β_ (U.obj L) (U.obj L)).hom = 𝟙 _ at h
    apply (cancel_mono (e.hom ⊗ₘ e.hom)).1
    rw [← braiding_naturality, h, Category.comp_id, Category.id_comp]
  have hvB : (β_ (V.obj B) (V.obj B)).hom = 𝟙 _ :=
    pullback_even C (pullback.snd f f) B hB
  have h := coefficient_braid_formal R V B Q (r B Q) (v B Q)
    cB (c.app K) cM hc hvB
  have hi := square_inverse C (pullback.fst f f) (pullback.snd f f) f f
    (pullback.condition (f := f) (g := f))
  apply Iso.ext
  have hh := congrArg Iso.hom h
  change (((r B Q).hom ≫ R.obj B ◁
      ((derivedSquareUpperStarIso C (IsPullback.of_hasPullback f f).toCommSq).app K).inv)
        ▷ V.obj B) ≫
      (α_ (R.obj B) (V.obj Q) (V.obj B)).hom ≫
      R.obj B ◁ (β_ (V.obj Q) (V.obj B)).hom ≫
      R.obj B ◁ (v B Q).inv ≫ (β_ (R.obj B) (V.obj (B ⊗ Q))).hom =
    cM.hom ▷ V.obj B ≫ V.obj (B ⊗ Q) ◁ cB.inv
  simpa only [Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
    c, hi, Iso.symm_hom, Iso.app_hom, Iso.app_inv] using hh

end GeneralCoefficients

variable (A : Type (u + 1)) [CommRing A]

/-- The cyclic coefficient permutation is the coordinate comparison on the full tensor,
followed by undoing the comparison on its remaining factor. This is solely an identity
of inverse images and tensor maps; it contains no projection formula or direct image.

Source: thm-amb-p1-adjunction.proof.md, second triangle, the common coefficient and
its even self-symmetry (auxiliary; not a blueprint node).

Proof in words: write the tensor comparisons for p1 and p2. Monoidality of the square
comparison expresses its value on L tensor K as the tensor of its values on L and K.
Naturality with e and e inverse therefore expresses coordinateTwisted as the tensor
of coordinate on B and the common-base comparison on f*K, conjugated by the p1 and
p2 tensor comparisons. In coefficientSplit the latter comparison already occurs.
Expand cyclicShuffle and move the B comparison through the associators and symmetries
by naturality. After these cancellations the only discrepancy is the conjugate of
the self-braiding of the two copies of p2*B. Braidedness of f* transports hL to f*L;
naturality with e transports it to B; braidedness of p2* transports it to p2*B.
Consequently this self-braiding is identity. The hexagon and symmetry identities
cancel the two crossings with p2*f*K, leaving exactly the right-hand composite.
This argument also applies to zero objects and the zero ring: no invertibility of
L or nonzero rank is required. -/
theorem coefficientBraid {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).app L).app L).hom = 𝟙 _)
    {B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (e : B ≅ (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj L)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).mapIso
        (coefficientSplit (ModuleCat.{u + 1} A) f B K)).app
          ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f f)).leftDerivedFunctor.obj B) ≪≫
        cyclicShuffle (ModuleCat.{u + 1} A) (pullback.snd f f)
          ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f f)).leftDerivedFunctor.obj B) B
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K) =
      ((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).mapIso
        (tensorCoordinate (ModuleCat.{u + 1} A) f L K e)).app
          ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f f)).leftDerivedFunctor.obj B) ≪≫
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).obj
          ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f f)).leftDerivedFunctor.obj
            (((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
              ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)))).mapIso
                (coefficientCoordinate (ModuleCat.{u + 1} A) f L e).symm := by
  exact coefficient_braid_generic (ModuleCat.{u + 1} A) f L hL e K

end AlgebraicGeometry.Etale.SupportedTrace
