/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActual
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import all WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Canonical coefficient change and ringed pullback

The recorded arbitrary ringed-topos tensor/pullback interface is reexported.
The helpers retain its ordinary adjunction and K-flat normalization for the
completed coefficient structure maps, which need not be isomorphisms.
Source: Stacks Tags 03EL, 06YY, 0D6D and 099N
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B)
    (φY : pbcAdicCompletion Y dA ⟶ pbcAdicCompletion Y dB)
    (φX : pbcAdicCompletion X dA ⟶ pbcAdicCompletion X dB)

/-- Forget commutativity in a coefficient morphism without changing its ring map.
Source: Stacks Tag 03EL
(auxiliary; not a blueprint node). -/
abbrev pbcActualCoefficientRingMap (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :=
  (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ

-- Descend a comparison from a resolving class without unfolding its concrete functors.
set_option backward.isDefEq.respectTransparency false in
private theorem comparison_on_resolutions
    {C D : Type*} [Category C] [Category D] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty (CochainComplex C ℤ))
    (hres : ∀ K : HomotopyCategory C (.up ℤ),
      ∃ (L : ObjectProperty.FullSubcategory
          (show ObjectProperty (HomotopyCategory C (.up ℤ)) from fun K ↦ P K.as))
        (s : L.obj ⟶ K), HomotopyCategory.quasiIso C (.up ℤ) s)
    (F G : DerivedCategory C ⥤ D) (U V : CochainComplex C ℤ ⥤ D)
    (l : DerivedCategory.Q ⋙ F ⟶ U) (r : DerivedCategory.Q ⋙ G ⟶ V)
    (b : U ≅ V) (hl : ∀ K : P.FullSubcategory, IsIso (l.app K.obj))
    (hr : ∀ K : P.FullSubcategory, IsIso (r.app K.obj)) :
    ∃! e : F ≅ G, ∀ K : CochainComplex C ℤ, P K →
      e.hom.app (DerivedCategory.Q.obj K) ≫ r.app K = l.app K ≫ b.hom.app K := by
  let H : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun K ↦ P K.as
  have : (H.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso C (.up ℤ)).inverseImage H.ι) :=
    CategoryTheory.restriction_localization _ _ H hres
  let f := H.lift (P.ι ⋙ HomotopyCategory.quotient C (.up ℤ)) (fun K ↦ K.property)
  have : f.Full := ⟨by
    intro K L a
    obtain ⟨b, hb⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective a.hom
    refine ⟨ObjectProperty.homMk b, ?_⟩
    apply ObjectProperty.hom_ext
    exact hb⟩
  have : f.EssSurj := ⟨by
    intro K
    obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
    refine ⟨⟨L, ?_⟩, ⟨ObjectProperty.isoMk H (eqToIso hL)⟩⟩
    change H ((HomotopyCategory.quotient C (.up ℤ)).obj L)
    exact hL.symm ▸ K.property⟩
  let ff₀ := (Localization.fullyFaithfulWhiskeringLeft (H.ι ⋙ DerivedCategory.Qh)
    ((HomotopyCategory.quasiIso C (.up ℤ)).inverseImage H.ι) D).comp
      (CategoryTheory.fullyFaithfulWhiskeringOfFullEssSurj f D)
  let ff := ff₀.ofIso ((whiskeringLeft _ _ D).mapIso
    (isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso C)))
  let el : P.ι ⋙ DerivedCategory.Q ⋙ F ≅ P.ι ⋙ U :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ (l.app K.obj) (hl K))
      (fun a ↦ l.naturality a.hom)
  let er : P.ι ⋙ DerivedCategory.Q ⋙ G ≅ P.ι ⋙ V :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ (r.app K.obj) (hr K))
      (fun a ↦ r.naturality a.hom)
  let e₀ := el ≪≫ isoWhiskerLeft P.ι b ≪≫ er.symm
  let e : F ≅ G := ff.preimageIso e₀
  have he (K : P.FullSubcategory) : e.hom.app (DerivedCategory.Q.obj K.obj) =
      e₀.hom.app K := congrArg (fun z ↦ z.app K)
      (ff.map_preimage (X := F) (Y := G) e₀.hom)
  have hn (K : CochainComplex C ℤ) (hp : P K) :
      e.hom.app (DerivedCategory.Q.obj K) ≫ r.app K = l.app K ≫ b.hom.app K := by
    rw [he ⟨K, hp⟩]
    have := hr ⟨K, hp⟩
    change (l.app K ≫ b.hom.app K ≫ CategoryTheory.inv (r.app K)) ≫ r.app K = _
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨e, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply ff.map_injective
  ext K
  apply (cancel_mono (er.hom.app K)).1
  change e'.hom.app (DerivedCategory.Q.obj K.obj) ≫ r.app K.obj =
    e.hom.app (DerivedCategory.Q.obj K.obj) ≫ r.app K.obj
  exact (he' K.obj K.property).trans (hn K.obj K.property).symm

private def complexCounit {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (eps : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso C).inv LF ≫
    whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) eps ≫
    whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    whiskerLeft (F.mapHomologicalComplex (.up ℤ)) (DerivedCategory.quotientCompQhIso D).hom

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_right
    {RA RB : Sheaf (ProEt.topology Y) RingCat.{u + 1}}
    {SA SB : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (ay : RA ⟶ RB) (ax : SA ⟶ SB)
    (aR : RA ⟶ (proEtaleSheafDirectImage g RingCat.{u + 1}).obj SA)
    (aS : RB ⟶ (proEtaleSheafDirectImage g RingCat.{u + 1}).obj SB)
    (h : ay ≫ aS = aR ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map ax) :
    ∃! δ : SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) aS ⋙
        SheafOfModules.restrictScalars ay ≅
      SheafOfModules.restrictScalars ax ⋙
        SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) aR,
      ∀ (N : SheafOfModules.{u + 1} SB) (U : Y.ProEtᵒᵖ)
        (x : ((SheafOfModules.pushforward (F := proEtaleBaseChange g) aS).obj N).val.obj U),
        (δ.hom.app N).val.app U x = x := by
  refine ⟨SheafOfModules.pushforwardCongr (F := proEtaleBaseChange g) h, ?_, ?_⟩
  · intro N U x
    rfl
  · intro e' he'
    apply Iso.ext
    ext N U x
    exact he' N U x

variable (hφ : pbcActualCoefficientRingMap Y φY ≫ pbcActualStructureMap g dB =
    pbcActualStructureMap g dA ≫
      (proEtaleSheafDirectImage g RingCat.{u + 1}).map (pbcActualCoefficientRingMap X φX))

end AlgebraicGeometry.Scheme
