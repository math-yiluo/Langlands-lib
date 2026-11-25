/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Lifting a derived decomposition on an affine open to modules

Source: Stacks Project, Tag 06Z0, lemma-affine-compare, and the affine reduction in
Tag 08CE (blueprint: lem-pc-affine-derived-summand-models).
-/

@[expose] public section

universe u wR w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
-- Derived functor compositions need additional typeclass search budget.
-- Comparing the localizations elaborates several large exact-functor structures.
/-- A decomposition of an associated module complex on an affine open comes from a
binary decomposition in the module derived category. No boundedness, finite generation,
or pseudo-coherence is assumed.

Source: Stacks Project, Tag 06Z0, lemma-affine-compare, used in the affine reduction of
Tag 08CE (blueprint: lem-pc-affine-derived-summand-models).

Proof: Transport the localized sheaf category to Spec Gamma(U,O) by the exact
isoSpec and overEquiv equivalences. The affine derived equivalence, followed by inclusion
and this transport, gives a fully faithful G and the comparison with termwise
sheafification. Exactness of tilde follows from exactness of module localization.
The tilde/Gamma adjunction therefore induces an unbounded derived adjunction. Descend
its comparison with the affine equivalence through Q and compose with the transport
adjunction to get G left adjoint to B. The counit at E ⊞ F is invertible since this
object is isomorphic to G(Q(P)). Naturality makes the counits at E and F retracts of
that invertible counit, so they are invertible. Set C = B(E) and D = B(F); their counits
give E ≅ G(C) and F ≅ G(D). Additivity identifies G(C ⊞ D) with G(C) ⊞ G(D), and full
faithfulness lifts the resulting isomorphism G(Q(P)) ≅ G(C ⊞ D).
The empty affine open and zero summands are handled by the same adjunctions and retract
equations. No boundedness or finite-free model of C or D is used or asserted. -/
theorem affine_derived_summand_models (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U)
    [HasDerivedCategory.{wR} (ModuleCat.{u} (X.presheaf.obj (.op U)))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (P : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ)
    (E F : DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)))
    (h : Nonempty
      (DerivedCategory.Q.obj
        (((affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)).obj P) ≅
          E ⊞ F)) :
    ∃ G : DerivedCategory (ModuleCat.{u} (X.presheaf.obj (.op U))) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)),
      G.Additive ∧ Nonempty (DerivedCategory.Q ⋙ G ≅
        (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q) ∧
      ∃ C D : DerivedCategory (ModuleCat.{u} (X.presheaf.obj (.op U))),
        Nonempty (DerivedCategory.Q.obj P ≅ C ⊞ D) ∧
        Nonempty (E ≅ G.obj C) ∧ Nonempty (F ≅ G.obj D) := by
  classical
  have : HasBinaryBiproducts
      (DerivedCategory (ModuleCat.{u} (X.presheaf.obj (.op U)))) :=
    Pretriangulated.instHasBinaryBiproducts
  have : HasBinaryBiproducts
      (DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))) :=
    Pretriangulated.instHasBinaryBiproducts
  let R := X.presheaf.obj (.op U)
  let S := SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)
  let : HasDerivedCategory S := HasDerivedCategory.standard _
  let L : ModuleCat.{u} R ⥤ S := tilde.functor R
  let H := RingedSpace.globalSectionsFunctor (Spec R).toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom
  have adj : L ⊣ H := tilde.adjunction
  have : L.Additive := by constructor; intro M N f g; exact tilde.map_add (R := R) f g
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have : L.PreservesMonomorphisms := ⟨by
    intro M N f hf
    let : Mono f := hf
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro V s t hst
    apply Subtype.ext
    funext x
    apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N)
      f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance)
    exact congrArg (fun z ↦ z.val x) hst⟩
  have : L.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels L
  have : PreservesFiniteLimits L := L.preservesFiniteLimits_of_preservesHomology
  obtain ⟨e, ⟨ce⟩, _, _⟩ := exists_affineQCohDerivedEquivalence R
  let I := (schemeDerivedQCohProperty (Spec R)).ι
  let G₀ := e.functor ⋙ I
  let qe : DerivedCategory.Q ⋙ L.mapDerivedCategory ≅ DerivedCategory.Q ⋙ G₀ :=
    L.mapDerivedCategoryFactors ≪≫ ce.symm
  let q := Localization.whiskeringLeftFunctor' (DerivedCategory.Q (C := ModuleCat.{u} R))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) (DerivedCategory S)
  let ge : L.mapDerivedCategory ≅ G₀ := q.preimageIso qe
  have : G₀.Additive := Functor.additive_of_iso ge
  obtain ⟨T, ⟨ct⟩⟩ := affine_localized_site_derived_transport X U hU
  have : T.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have : T.functor.Additive := Functor.additive_of_preserves_binary_products _
  let G := G₀ ⋙ T.functor
  let B := T.inverse ⋙ H.rightDerivedFunctor
  let a : G ⊣ B := (adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft ge).comp
    T.toAdjunction
  have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBinaryProducts _
  let cmp : DerivedCategory.Q ⋙ G ≅
      (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ce T.functor ≪≫ ct
  obtain ⟨h⟩ := h
  let split : E ⊞ F ≅ G.obj (DerivedCategory.Q.obj P) :=
    h.symm ≪≫ (cmp.app P).symm
  have : IsIso (a.counit.app (E ⊞ F)) := a.isIso_counit_app_of_iso split
  let rE : Retract E (E ⊞ F) := ⟨biprod.inl, biprod.fst, by simp⟩
  let rF : Retract F (E ⊞ F) := ⟨biprod.inr, biprod.snd, by simp⟩
  have : IsIso (a.counit.app E) :=
    (MorphismProperty.isomorphisms _).of_retract (a.counit.retractArrowApp rE) inferInstance
  have : IsIso (a.counit.app F) :=
    (MorphismProperty.isomorphisms _).of_retract (a.counit.retractArrowApp rF) inferInstance
  let eE : E ≅ G.obj (B.obj E) := (asIso (a.counit.app E)).symm
  let eF : F ≅ G.obj (B.obj F) := (asIso (a.counit.app F)).symm
  have : HasBinaryBiproduct (B.obj E) (B.obj F) :=
    HasBinaryBiproducts.has_binary_biproduct (C := DerivedCategory (ModuleCat.{u} R)) _ _
  have : HasBinaryBiproduct (G.obj (B.obj E)) (G.obj (B.obj F)) :=
    HasBinaryBiproducts.has_binary_biproduct
      (C := DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))) _ _
  let dec : G.obj (DerivedCategory.Q.obj P) ≅ G.obj (B.obj E ⊞ B.obj F) :=
    split.symm ≪≫ biprod.mapIso eE eF ≪≫ (G.mapBiprod _ _).symm
  exact ⟨G, inferInstance, ⟨cmp⟩, B.obj E, B.obj F,
    ⟨G.preimageIso dec⟩, ⟨eE⟩, ⟨eF⟩⟩

end AlgebraicGeometry.Scheme
