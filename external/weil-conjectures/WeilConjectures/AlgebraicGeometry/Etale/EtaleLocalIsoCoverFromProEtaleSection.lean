/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalIsomorphismSheaf
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Étale covers carrying representatives of pro-étale Isom sections

Source: Stacks Project, proetale.tex, Tag 09B1 (bounded-below derived comparison);
localization of sites and exact inverse image.
(blueprint: new-lem-weil-pbc-lisse-finite-level-etale-local-representative-cover).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem iso_of_comparison_iso
    (Y : Scheme.{u}) {B : Type (u + 1)} [CommRing B]
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hM : DerivedCategory.TStructure.t.plus M)
    (e : (derivedComparison Y B).obj K ≅ (derivedComparison Y B).obj M) :
    Nonempty (K ≅ M) := by
  obtain ⟨f, hf⟩ :=
    (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map K M hM).surjective e.hom
  have hF : (derivedComparison Y B).ReflectsIsomorphisms := by
    refine ⟨fun g _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y).map
        ((DerivedCategory.homologyFunctor _ n).map g)) :=
      (NatIso.isIso_map_iff
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategoryHomologyFunctorIso
          n) g).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y)
  have : IsIso ((derivedComparison Y B).map f) := by
    change IsIso ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.map f)
    dsimp only at hf
    rw [hf]
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f (derivedComparison Y B)
  exact ⟨asIso f⟩

private noncomputable abbrev proSliceEquiv (X : Scheme.{u}) (V : X.Etale)
    (B : Type (u + 1)) [CommRing B] :=
  letI : (ProEt.sliceEquiv X ((toProEt X).obj V)).inverse.IsDenseSubsite
      (ProEt.topology V.left) ((ProEt.topology X).over ((toProEt X).obj V)) :=
    ProEt.sliceDense X ((toProEt X).obj V)
  (ProEt.sliceEquiv X ((toProEt X).obj V)).sheafCongr
    ((ProEt.topology X).over ((toProEt X).obj V))
    (ProEt.topology V.left) (ModuleCat.{u + 1} B)

private noncomputable def restrictionComparisonIso
    (X : Scheme.{u}) (V : X.Etale) (B : Type (u + 1)) [CommRing B] :
    proEtaleSheafInverseImage V.hom (ModuleCat.{u + 1} B) ≅
      (ProEt.topology X).overPullback (ModuleCat.{u + 1} B) ((toProEt X).obj V) ⋙
        (proSliceEquiv X V B).functor :=
  (restrictionComparison ((toProEt X).obj V) (ModuleCat.{u + 1} B)).sheafIso ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- With a bounded-below target, a pro-etale local derived Isom section is represented by
actual isomorphisms on an etale cover of its etale object.

Source: Stacks Project, proetale.tex, Tag 09B1 (bounded-below derived comparison);
localization of sites and exact inverse image.
(blueprint: new-lem-weil-pbc-lisse-finite-level-etale-local-representative-cover).

Proof: identify the pro-etale slice with the site of V.left, and use the canonical
comparison/pullback square to regard the supplied section as an isomorphism between the
comparison pullbacks of A|V and D|V. Exact etale restriction preserves the lower bound of D.
Comparison is full on morphisms with bounded-below target, so the hom component lifts to
A|V -> D|V. Exact comparison reflects isomorphisms by its cohomology comparison and
underived full faithfulness. Thus the lift is an isomorphism already on V. The identity
cover supplies the stated cover, including when V is empty.
-/
theorem exists_etale_iso_cover_of_proetale_local_iso_section
    (X : Scheme.{u}) (V : X.Etale)
    {B : Type (u + 1)} [CommRing B]
    (A D : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hD : DerivedCategory.TStructure.t.plus D)
    (s : (derivedLocalIsoPresheaf (ProEt.topology X) B
      ((derivedComparison X B).obj A)
      ((derivedComparison X B).obj D)).obj
        (op ((toProEt X).obj V))) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage V.left,
      ∀ i : 𝒰.I₀,
        Nonempty ((localIsomorphismRestriction X B
          (Etale.mk (𝒰.f i ≫ V.hom))).obj A ≅
          (localIsomorphismRestriction X B
            (Etale.mk (𝒰.f i ≫ V.hom))).obj D) := by
  let P := (proSliceEquiv X V B).functor
  have : P.Additive := Functor.additive_of_preserves_binary_products P
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X
  let G := Etale.upperStar (ModuleCat.{u + 1} B) V.hom
  let H := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) V.left
  let R := (ProEt.topology X).overPullback (ModuleCat.{u + 1} B) ((toProEt X).obj V)
  let T := proEtaleSheafInverseImage V.hom (ModuleCat.{u + 1} B)
  have : T.Additive := Functor.additive_of_iso (restrictionComparisonIso X V B).symm
  have : PreservesFiniteLimits T :=
    preservesFiniteLimits_of_natIso (restrictionComparisonIso X V B).symm
  have : PreservesFiniteColimits T :=
    preservesFiniteColimits_of_natIso (restrictionComparisonIso X V B).symm
  let c : G ⋙ H ≅ F ⋙ T :=
    ProEtale.supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} B) V.hom
  let d : T.mapDerivedCategory ≅ R.mapDerivedCategory ⋙ P.mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso (restrictionComparisonIso X V B) ≪≫
      (Functor.mapDerivedCategoryCompIso R P).symm
  let e := Functor.mapDerivedCategorySquareIso c
  let s' := P.mapDerivedCategory.mapIso s
  let t : H.mapDerivedCategory.obj (G.mapDerivedCategory.obj A) ≅
      H.mapDerivedCategory.obj (G.mapDerivedCategory.obj D) :=
    e.app A ≪≫ d.app (F.mapDerivedCategory.obj A) ≪≫ s' ≪≫
      (d.app (F.mapDerivedCategory.obj D)).symm ≪≫ (e.app D).symm
  have hGD : DerivedCategory.TStructure.t.plus (G.mapDerivedCategory.obj D) := by
    obtain ⟨n, hn⟩ := hD
    have : D.IsGE n := hn
    exact ⟨n, G.isGE_mapDerivedCategory_obj D n⟩
  obtain ⟨a⟩ := iso_of_comparison_iso V.left _ _ hGD t
  let 𝒰 := coverOfIsIso (P := @Etale) (𝟙 V.left)
  refine ⟨𝒰, ?_⟩
  intro i
  let W : X.Etale := Etale.mk (𝒰.f i ≫ V.hom)
  let k : W ⟶ V := MorphismProperty.Over.homMk (𝒰.f i) rfl
  exact ⟨localIsomorphismMap A D k a⟩

end AlgebraicGeometry.Scheme
