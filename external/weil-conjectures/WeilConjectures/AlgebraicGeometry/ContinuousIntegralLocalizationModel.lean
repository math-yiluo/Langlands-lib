/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
public import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuity
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralComplexTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralDerivedUnit
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs

/-! # A strict complex model for the integral localization unit telescope -/

@[expose] public section

universe u v w x
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- A strict complex representative together with the specified scalar-telescope
colimit comparison. This record keeps its category abstract so that projections do
not unfold the construction of continuous coefficient rings.
Source: good truncation and the localization telescope of Bhatt--Scholze 6.8.2.
(auxiliary; not a blueprint node). -/
structure IntegralLocalizationComplexModel
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    [HasColimitsOfShape (ULift.{x} ℕ) A]
    (ℓ : ℕ) (K : DerivedCategory A)
    (c : Cocone (Mod.smulSequence K ℓ)) where
  complex : CochainComplex A ℤ
  bound : ℤ
  strictlyGE : complex.IsStrictlyGE bound
  representative : K ≅ DerivedCategory.Q.obj complex
  comparison : DerivedCategory.Q.obj (condensedContinuityCocone
      (integralLocalizationLiftedSequence.{max v w, w, x} ℓ complex) bound).pt ≅ c.pt
  leg (n : ULift.{x} ℕ) :
    DerivedCategory.Q.map ((condensedContinuityCocone
        (integralLocalizationLiftedSequence.{max v w, w, x} ℓ complex) bound).ι.app n) ≫
      comparison.hom = representative.inv ≫ c.ι.app n.down

/-- A bounded-below integral derived object admits a strict telescope model of its
scalar-extension unit. Only coefficient algebra is asserted here; no pushforward occurs.
Source: Bhatt--Scholze, Lemma 6.8.2; Hemo--Richarz--Scholbach, Lemma 5.3(1).
(auxiliary; not a blueprint node).

Proof. Choose a representative C zero below a by good truncation. The regular restricted
E-module is the colimit of the regular integral module under multiplication by ℓ:
on a compact profinite test the nth leg is division by ℓⁿ, and compactness gives a
single denominator for every continuous E-valued function. Monoidal sheafification
and inverse image from the point preserve this colimit. Tensoring with each term of
C, and commuting colimits with the coequalizer defining balanced tensor, gives the
termwise colimit as restriction of the termwise extension of C. The comparison on
the nth leg is the extension unit followed by division by ℓⁿ, by the formula for the
balanced tensor unit. Exactness of scalar extension identifies its left derived
functor with this termwise construction and transports the unit to the specified
derived adjunction. The diagram remains zero below a, so good truncation at a is an
isomorphism of diagrams. Reindexing along ULift ℕ ≌ ℕ preserves the colimit. These
identifications give v and the displayed leg equation. Zero complexes and empty
schemes satisfy the same construction; no finite-dimensionality or constructibility
of C is used. -/
theorem exists_integralLocalization_complex_model (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    Nonempty (IntegralLocalizationComplexModel.{u + 2, u + 1, u + 1} ℓ K
      (integralLocalizationCocone ℓ E X K)) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) X)
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let L := (Mod.extendScalars φ).leftDerivedFunctor
  let U := (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ).mapDerivedCategory
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction φ
  have : HasColimitsOfShape (ULift.{u + 1} ℕ) A := inferInstance
  have : HasColimitsOfShape (ULift.{u + 1} ℕ) (CochainComplex A ℤ) := inferInstance
  obtain ⟨a, ha⟩ := hK
  have : K.IsGE a := ha
  obtain ⟨C, hC, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a
  obtain ⟨c, ⟨hc⟩, w, hw⟩ := integralComplexLocalization_colimit ℓ E X C
  obtain ⟨z, hz⟩ := integralScalar_derivedUnit_complex ℓ E X C
  change DerivedCategory.Q.obj
      (((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        φ).mapHomologicalComplex (.up ℤ)).obj
        (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj C)) ≅
      U.obj (L.obj (DerivedCategory.Q.obj C)) at z
  let J := (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.functor
  let D := integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ C
  have : HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A) :=
    HasColimitsOfShape.has_colimit _
  let π := Functor.whiskerLeft D ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)
  have : ∀ i, IsIso (π.app i) := fun i ↦
    (HomologicalComplex.isIso_πTruncGE_iff C _).2 hC
  have : IsIso π := NatIso.isIso_of_isIso_app π
  let hc' : IsColimit (condensedContinuityCocone D a) :=
    (IsColimit.precomposeHomEquiv (asIso π) _).symm (colimit.isColimit _)
  let hcl : IsColimit (c.whisker J) := hc.whiskerEquivalence
    (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence
  let v₀ := hc'.coconePointUniqueUpToIso hcl
  let t := integralLocalizationCocone ℓ E X K
  let σ := Mod.smulSequenceCompIso DerivedCategory.Q C ℓ
  let s := (Cocone.precompose σ.inv).obj (DerivedCategory.Q.mapCocone c)
  let α : Mod.smulSequence (DerivedCategory.Q.obj C) ℓ ⟶ Mod.smulSequence K ℓ :=
    Mod.smulSequenceMap e.inv ℓ
  let r := (Cocone.precompose α).obj t
  let g : s.pt ⟶ r.pt := DerivedCategory.Q.map w.hom ≫ z.hom ≫ (L ⋙ U).map e.inv
  have : IsIso (ℓ • 𝟙 r.pt) := by
    have := derived_nsmul_isIso ℓ E X (L.obj K)
    have h : IsIso (U.map (ℓ • 𝟙 (L.obj K))) := inferInstance
    change IsIso (ℓ • 𝟙 (U.obj (L.obj K)))
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using h
  have hu : DerivedCategory.Q.map (c.ι.app 0) ≫ DerivedCategory.Q.map w.hom ≫ z.hom =
      adj.unit.app (DerivedCategory.Q.obj C) := by
    have h := (congrArg (fun k ↦ DerivedCategory.Q.map k ≫ z.hom) hw).trans hz
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using h
  have hzero : s.ι.app 0 ≫ g = r.ι.app 0 := by
    simp only [integralLocalizationCocone, scalarLocalizationUnitCocone, Functor.comp_obj,
      Functor.const_obj_obj, id_eq, Cocone.precompose_obj_pt, Mod.smulSequenceCompIso,
      NatIso.ofComponents_inv_app, Iso.refl_inv, Functor.mapCocone_pt, Cocone.precompose_obj_ι,
      NatTrans.comp_app, Mod.smulSequenceMap_app, Functor.mapCocone_ι_app,
      Functor.comp_map, Category.assoc, pow_zero, End.one_asHom, CategoryTheory.Functor.map_id,
      Category.comp_id, r, α, t, s, σ, g]
    change 𝟙 _ ≫ DerivedCategory.Q.map (c.ι.app 0) ≫
        DerivedCategory.Q.map w.hom ≫ z.hom ≫ (L ⋙ U).map e.inv =
      e.inv ≫ adj.unit.app K
    have h := (congrArg (fun k ↦ k ≫ (L ⋙ U).map e.inv) hu).trans
      (adj.unit.naturality e.inv).symm
    simpa only [Category.id_comp, Category.assoc, Functor.id_map] using h
  have hlegs := integralLocalization_coconeLegs ℓ s r g hzero
  let v := DerivedCategory.Q.mapIso v₀ ≪≫ DerivedCategory.Q.mapIso w ≪≫ z ≪≫
    (L ⋙ U).mapIso e.symm
  refine ⟨⟨C, a, hC, e, v, ?_⟩⟩
  intro n
  change DerivedCategory.Q.map ((condensedContinuityCocone D a).ι.app n) ≫
      (DerivedCategory.Q.map v₀.hom ≫ g) = e.inv ≫ t.ι.app n.down
  rw [← Category.assoc, ← DerivedCategory.Q.map_comp,
    IsColimit.comp_coconePointUniqueUpToIso_hom]
  have hh := hlegs n.down
  simp only [Cocone.precompose_obj_pt, Mod.smulSequenceCompIso, Functor.comp_obj,
    NatIso.ofComponents_inv_app, Iso.refl_inv, Functor.mapCocone_pt, Functor.const_obj_obj,
    Cocone.precompose_obj_ι, NatTrans.comp_app, Mod.smulSequenceMap_app,
    Functor.mapCocone_ι_app, Category.assoc, r, α, s, σ] at hh
  exact (Category.id_comp (DerivedCategory.Q.map (c.ι.app n.down) ≫ g)).symm.trans hh

end AlgebraicGeometry.ProEtale.CondensedRing
