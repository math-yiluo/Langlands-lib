/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatLocalizedTensorComparisonNatural
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelIndependence
import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange

/-! # Derived naturality of localized tensor comparisons

The missing structural step in retract closure is functoriality of the comparison
arrow, rather than invertibility of any comparison. Source: Stacks Project, Tags
06Y6, 0DJ7 and 0DJA(1).
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

private theorem acyclic_tensor_of_kFlat
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.Acyclic) :
    (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic] at hP
  have hL' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic L).2 hL
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor L P (curriedTensor _))).1 (hP _ hL').2

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- The localized tensor comparisons are values of one functor to the arrow category.

Source: Stacks Project, Tag 06Y6 (derived change of rings), Tag 0BYJ
(associativity), and the comparison in Tag 0DJ7, used in Tag 0DJA(1).

Proof: on D(A), tensor with Q using A-K-flat resolutions. For the source,
restrict this tensor to R, apply derived extension to B, and take degree-i
cohomology. The commuting A and B actions give the canonical A-tensor-R-B
module. Extend this module to C. For the target, apply derived extension
from A to C, tensor over C with N, and take degree-i cohomology. Extension
of an A-K-flat complex is C-K-flat, so the target is computed by the
ordinary total tensor with N, even when N is not K-flat. The coefficient
comparison followed by the map induced by t defines a natural
transformation from source to target: on resolutions it is the ordinary
coefficient map, rebracketing, then identity tensor t. Naturality on chain
maps and homotopies gives naturality on K-flat homotopy categories;
quasi-isomorphisms between K-flat representatives induce isomorphisms on
both sides, so localization descends the transformation to D(A). Regard
it as a functor H to the arrow category. For each K-flat U, its tensor
with Q computes the derived tensor since Q is K-flat. Uniqueness of the
universal derived counit gives the source identification for every model
mU; naturality at A-multiplication makes this identification tensor-
algebra-linear. Its comparison_eq and localized_eq equations identify
the source arrow with mU.localizedComparison. The target identification
comes from the K-flat computation above; naturality of the monoidal
scalar-extension isomorphism identifies the rest of the arrow with the
displayed homology map. These two identifications give an arrow
isomorphism. No comparison is assumed invertible and no flatness of C is used.
The construction works for unbounded and zero complexes and zero rings.
(blueprint: lem-pc-localized-tensor-comparison-derived-arrow). -/
theorem exists_localizedTensorComparison_derived_arrow
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) (i : ℤ) :
    ∃ H : DerivedCategory (ModuleCat.{u} A) ⥤ Arrow (ModuleCat.{u} C),
      ∀ (U : CochainComplex (ModuleCat.{u} A) ℤ),
      (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic) →
      ∀ mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C,
      let F := (extendScalars.{u, u, u}
        ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
          (.up ℤ)
      Nonempty (Arrow.mk (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) ≅
          H.obj (DerivedCategory.Q.obj U)) := by
  classical
  let φ := (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B))
  let F := (extendScalars.{u, u, u} φ).mapHomologicalComplex (.up ℤ)
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)
  let WC := HomologicalComplex.quasiIso (ModuleCat.{u} C) (.up ℤ)
  let L := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ DerivedCategory.Q
  have (M : ModuleCat.{u} A) : CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{u} A)).flip.obj M) :=
    inferInstanceAs (CategoryTheory.Limits.PreservesColimitsOfShape ℤ (tensorRight M))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  have (M : ModuleCat.{u} C) : CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{u} C)).flip.obj M) :=
    inferInstanceAs (CategoryTheory.Limits.PreservesColimitsOfShape ℤ (tensorRight M))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} C) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} C)
      (AsSmall.equiv (C := ℤ)).symm
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} A))).reduced
  have : W.localizerMorphismKFlat.IsLocalizedEquivalence :=
    W.localizerMorphismKFlat.isLocalizedEquivalence_of_functorial_left_resolutions
      (Λ.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le)
      (fun _ ↦ by change QuasiIso _; infer_instance) rfl
  have : L.IsLocalization W.WKFlat :=
    inferInstanceAs ((W.localizerMorphismKFlat.functor ⋙ DerivedCategory.Q).IsLocalization
      W.WKFlat)
  let m (U : CochainComplex.KFlat (ModuleCat.{u} A)) :=
    baseDerivedTensorCohomologyModel R A B (U.obj ⊗ Q) C
  let T := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ F ⋙ tensorRight N ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) i
  obtain ⟨S, η, hS, he⟩ :=
    exists_kFlatLocalizedTensorComparison_natural R A B C Q N t hQ i
  change S ⟶ T at η
  have hT : W.WKFlat.IsInvertedBy T := by
    intro U V a ha
    have ha' : QuasiIso a.hom := ha
    have hFU : WC.kFlat (F.obj U.obj) := CochainComplex.kFlat_of_acyclic_tensor _
      (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ U.obj
        (acyclic_tensor_of_kFlat _ U.property))
    have hFV : WC.kFlat (F.obj V.obj) := CochainComplex.kFlat_of_acyclic_tensor _
      (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ V.obj
        (acyclic_tensor_of_kFlat _ V.property))
    have hf : QuasiIso (F.map a.hom) :=
      CochainComplex.scalarExtension_quasiIso_of_kFlat φ a.hom ha' U.property V.property
    have ht : QuasiIso ((tensorRight N).map (F.map a.hom)) :=
      WC.whiskerRight_of_kFlat (F.map a.hom) hf hFU hFV N
    change IsIso (HomologicalComplex.homologyMap
      ((tensorRight N).map (F.map a.hom)) i)
    let := ht
    infer_instance
  let G : CochainComplex.KFlat (ModuleCat.{u} A) ⥤ Arrow (ModuleCat.{u} C) :=
    { obj := fun U ↦ Arrow.mk (η.app U)
      map := fun a ↦ Arrow.homMk (S.map a) (T.map a) (η.naturality a)
      map_id := by
        intro U
        apply Arrow.hom_ext <;> simp
      map_comp := by
        intro U V Z a b
        apply Arrow.hom_ext <;> simp }
  have hG : W.WKFlat.IsInvertedBy G := by
    intro U V a ha
    have : IsIso (G.map a).left := by
      change IsIso (S.map a)
      exact hS a ha
    have : IsIso (G.map a).right := by
      change IsIso (T.map a)
      exact hT a ha
    exact Arrow.isIso_of_isIso_left_of_isIso_right (G.map a)
  let H := Localization.lift G hG L
  let eH : L ⋙ H ≅ G := Localization.fac G hG L
  refine ⟨H, ?_⟩
  intro U hU mU
  let UK : CochainComplex.KFlat (ModuleCat.{u} A) :=
    ⟨U, CochainComplex.kFlat_of_acyclic_tensor U hU⟩
  obtain ⟨e, he'⟩ := he UK
  obtain ⟨s, hs⟩ := baseDerivedTensorCohomologyModel_localized_independence
    R A B C (U ⊗ Q) mU (m UK) i
  let d : Arrow.mk (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) ≅ G.obj UK :=
    Arrow.isoMk (s ≪≫ e) (Iso.refl _) (by
      change (s.hom ≫ e.hom) ≫ η.app UK = _ ≫ 𝟙 _
      rw [Category.assoc, he', ← Category.assoc, hs, Category.comp_id]
      rfl)
  exact ⟨d ≪≫ (eH.app UK).symm⟩

end ModuleCat
