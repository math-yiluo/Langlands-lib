/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Finite discrete coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

-- Upstream made these instances local in InternalSectionTensorComparison.
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

-- Match the ambient braiding used to construct the coefficient ring and relative tensor.
attribute [local instance 20000] sheafBraidedCategory
-- Use the closedness API without unfolding its large adjoint construction.
attribute [local irreducible] Mod.monoidalClosed

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

private theorem monoidal_of_comparison
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (t : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (z : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (hn : ∀ X X' Y Y' (f : X ⟶ X') (g : Y ⟶ Y'),
      F.map (f ⊗ₘ g) ≫ (t X' Y').hom =
        (t X Y).hom ≫ (F.map f ⊗ₘ F.map g))
    (ha : ∀ X Y Z, (t (X ⊗ Y) Z).hom ≫ (t X Y).hom ▷ F.obj Z ≫
      (α_ _ _ _).hom = F.map (α_ X Y Z).hom ≫ (t X (Y ⊗ Z)).hom ≫
        F.obj X ◁ (t Y Z).hom)
    (hl : ∀ X, (t (𝟙_ C) X).hom ≫ z.hom ▷ F.obj X ≫ (λ_ _).hom =
      F.map (λ_ X).hom)
    (hr : ∀ X, (t X (𝟙_ C)).hom ≫ F.obj X ◁ z.hom ≫ (ρ_ _).hom =
      F.map (ρ_ X).hom) : Nonempty F.Monoidal := by
  let c : F.CoreMonoidal := Functor.CoreMonoidal.mk' z.symm (fun X Y ↦ (t X Y).symm)
    (by
      intro X Y f Z
      simpa only [Iso.symm_inv, tensorHom_id, F.map_id] using (hn X Y Z Z f (𝟙 Z)).symm)
    (by
      intro X Y Z f
      simpa only [Iso.symm_inv, id_tensorHom, F.map_id] using (hn Z Z X Y (𝟙 Z) f).symm)
    ha
    (by
      intro X
      apply (cancel_mono (λ_ (F.obj X)).hom).mp
      rw [Iso.symm_inv, Iso.symm_inv, Iso.inv_hom_id, Category.assoc, Category.assoc, hl X,
        ← F.map_comp, Iso.inv_hom_id, F.map_id])
    (by
      intro X
      apply (cancel_mono (ρ_ (F.obj X)).hom).mp
      rw [Iso.symm_inv, Iso.symm_inv, Iso.inv_hom_id, Category.assoc, Category.assoc, hr X,
        ← F.map_comp, Iso.inv_hom_id, F.map_id])
  exact ⟨c.toMonoidal⟩

set_option backward.isDefEq.respectTransparency false in
private theorem section_monoidal
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max v w, r}] [HasSheafify J Ab.{r}]
    [(J.W (A := Ab.{r})).IsMonoidal]
    (R : Sheaf J Ab.{r}) [MonObj R] [IsCommMonObj R] :
    Nonempty ((InternalAbelianSheafModule.sectionModuleEquivalence J R).functor.Monoidal) := by
  obtain ⟨_, t, z, _, _, hn, ha, hl, hr, _⟩ :=
    InternalAbelianSheafModule.internal_section_tensor_comparison J R
  exact monoidal_of_comparison _ t z hn ha hl hr

private instance ordinary_derived (T : Scheme.{u}) : HasDerivedCategory (Ordinary A T) :=
  HasDerivedCategory.standard _

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_monoidal (T : Scheme.{u}) (e : Encoding A T) :
    Nonempty e.ordinary.functor.Monoidal := by
  obtain ⟨m⟩ := section_monoidal
    (Scheme.ProEt.topology T) (condensedRingObj (coefficient A) T)
  let := m
  let := HasDerivedCategory.standard (Ordinary A T)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (sectionRing A T)))
  obtain ⟨r⟩ := SheafOfModules.ringIso_tensor_transport e.ringIso
  let := r.monoidal
  rw [e.ordinary_functor]
  unfold sectionEncoding
  exact ⟨inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
private theorem fixed_monoidal (T : Scheme.{u}) (e : Encoding A T) :
    Nonempty e.fixed.functor.Monoidal := by
  rw [e.fixed_functor]
  change Nonempty (CategoryTheory.ConstantScalarRestriction.restriction
    (Scheme.ProEt.topology T) (ULift.{u + 1} A)).Monoidal
  exact ⟨inferInstance⟩

private instance ordinary_closed (T : Scheme.{u}) : MonoidalClosed (Ordinary A T) :=
  ConstantScalarRestriction.ringClosed (Scheme.ProEt.topology T) (ULift.{u + 1} A)

private instance ordinary_flatResolution (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (Ordinary A T) :=
  ConstantScalarRestriction.ringFlatResolutions (Scheme.ProEt.topology T) (ULift.{u + 1} A)

private instance ordinary_grothendieck (T : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Ordinary A T) :=
  ConstantScalarRestriction.ringGrothendieck (Scheme.ProEt.topology T) (ULift.{u + 1} A)

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem ordinary_kflat (T : Scheme.{u}) (P : CochainComplex (Ordinary A T) ℤ) :
    CochainComplex.IsKFlatTensor P ↔
      (HomologicalComplex.quasiIso (Ordinary A T) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff P,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  constructor
  · intro h Z hZ
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor Z P (curriedTensor _))).2 (h Z hZ)
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso
      ((HomotopyCategory.quotient _ _).mapIso (β_ Z P)) hr, hr⟩
  · intro h Z hZ
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).2 hZ)).2

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem ordinary_tor (T : Scheme.{u}) (K : Scheme.proEtaleDerivedCategory T A)
    (a b : ℤ) (hab : a ≤ b) :
    DerivedCategory.torAmplitudeIn (Ordinary A T) a b K ↔
      Scheme.HasProEtaleTorAmplitude T A K a b := by
  let C := Ordinary A T
  let := HasDerivedCategory.standard C
  have comp (L P : CochainComplex C ℤ) (eL : DerivedCategory.Q.obj L ≅ K)
      (f : P ⟶ L) (hf : QuasiIso f) (hP : CochainComplex.IsKFlatTensor P)
      (M : C) :
      Scheme.derivedTensor T A L
        ((HomologicalComplex.single C (.up ℤ) 0).obj M) P f hf hP ≅
          K ⊗ (DerivedCategory.singleFunctor C 0).obj M := by
    have : QuasiIso f := hf
    let S := (CochainComplex.singleFunctor C 0).obj M
    let d := DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P S
      ((ordinary_kflat A T P).mp hP)
    let j := (DerivedCategory.singleFunctorIsoCompQ C 0).app M
    exact d.symm ≪≫ tensorIso (asIso (DerivedCategory.Q.map f) ≪≫ eL) j.symm
  constructor
  · intro h
    refine ⟨hab, ?_⟩
    intro L P heL f hf hP M i hi
    obtain ⟨eL⟩ := heL
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor C i).mapIso
      (comp L P eL f hf hP M))
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff _ a).mp (h M).1 i hi
    · exact (DerivedCategory.isLE_iff _ b).mp (h M).2 i hi
  · intro h M
    let L := DerivedCategory.Q.objPreimage K
    let eL := DerivedCategory.Q.objObjPreimageIso K
    obtain ⟨P, f, hf, _, hk⟩ := CochainComplex.exists_quasiIso_flat_kFlat L
    have hp := (ordinary_kflat A T P).mpr hk
    have hz (i : ℤ) (hi : i < a ∨ b < i) :=
      (h.2 L P ⟨eL⟩ f hf hp M i hi).of_iso
        ((DerivedCategory.homologyFunctor C i).mapIso (comp L P eL f hf hp M)).symm
    exact ⟨(DerivedCategory.isGE_iff _ a).mpr (fun i hi ↦ hz i (Or.inl hi)),
      (DerivedCategory.isLE_iff _ b).mpr (fun i hi ↦ hz i (Or.inr hi))⟩

set_option backward.isDefEq.respectTransparency false in
/-- Tensor products and Tor intervals under the normalized section-action encoding.
Source: blueprint coefficient-identification proof, steps 5--7; Stacks Tags 08BJ and 08FZ.
(auxiliary; not a blueprint node).

Proof: section-action identifies relative tensor products by the universal property of
balanced bilinear maps. Scalar restriction along the normalized coefficient isomorphism
and restriction to constant sections preserve these balancing relations and the unit.
The pure-tensor maps respect associativity and both unitors. Termwise extension preserves
coproducts, so the same maps identify direct-sum total tensors and their signed
differentials. An additive equivalence preserves and reflects acyclicity; transporting
the tensor tests therefore preserves and reflects K-flatness. Apply the exact monoidal
derived-equivalence theorem to obtain the monoidal structure on the actual termwise
extension. For intrinsic module sheaves compute derived tensor on any K-flat resolution;
the comparison identifies it with the generic derived tensor. All degree-zero test
modules correspond under either equivalence. The homology comparison consequently
identifies vanishing in every ordered interval. Finite Tor amplitude follows by enlarging
any witnessing interval to an ordered one and applying the same argument to the inverse.
This includes the zero ring and the zero object. -/
theorem encoding_tensor_tor [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) :
    Nonempty (e.fixedDerived.functor.Monoidal) ∧
    (∀ (K : DerivedCategory (Internal A T)) (a b : ℤ), a ≤ b →
      (DerivedCategory.torAmplitudeIn _ a b K ↔
        Scheme.HasProEtaleTorAmplitude T A (e.ordinaryDerived.functor.obj K) a b)) ∧
    (∀ (K : DerivedCategory (Internal A T)) (a b : ℤ), a ≤ b →
      (DerivedCategory.torAmplitudeIn _ a b K ↔ DerivedCategory.torAmplitudeIn _ a b
        (e.fixedDerived.functor.obj K))) := by
  obtain ⟨mo⟩ := ordinary_monoidal A T e
  let := mo
  obtain ⟨mf⟩ := fixed_monoidal A T e
  let := mf
  let E := e.ordinary.trans e.fixed
  let : E.functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  let : E.inverse.Additive :=
    inferInstanceAs (e.fixed.inverse ⋙ e.ordinary.inverse).Additive
  let : E.functor.Monoidal :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Monoidal
  let : E.inverse.Monoidal := E.inverseMonoidal
  let : E.IsMonoidal := inferInstance
  obtain ⟨d⟩ := ExactMonoidalEquivalenceDerived.nonempty_data E.toAdjunction
  refine ⟨⟨d.leftMonoidal⟩, ?_, ?_⟩
  · intro K a b hab
    let := HasDerivedCategory.standard (Ordinary A T)
    let : e.ordinary.functor.PreservesFlat :=
      Functor.preservesFlat_of_isEquivalence e.ordinary.functor
    exact (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff
      e.ordinary.functor a b K).symm.trans (ordinary_tor A T _ a b hab)
  · intro K a b _
    let : E.functor.PreservesFlat := Functor.preservesFlat_of_isEquivalence E.functor
    exact (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff
      E.functor a b K).symm

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
