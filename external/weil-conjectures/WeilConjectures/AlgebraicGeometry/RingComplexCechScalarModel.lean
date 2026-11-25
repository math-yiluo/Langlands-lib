/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexSemilinearExtension
public import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.RingComplexGodementCech
import WeilConjectures.AlgebraicGeometry.RingComplexOrderedScalarIso

/-! # Scalar extension of an augmented ordered localization model -/

@[expose] public section

set_option autoImplicit false

universe u w wA

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings BigOperators

namespace AlgebraicGeometry

private theorem ringFlat_of_point_flat {A : Type u} [CommRing A]
    (M : RingSiteModules A)
    (hM : Module.Flat A (M.val.obj (op ⟨PUnit.unit⟩))) :
    SheafOfModules.IsFlat M := by
  let R := CochainComplex.onePointRingSheaf A
  let O := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  have hflat (V : (Discrete PUnit.{u + 1})ᵒᵖ) :
      Module.Flat (R.obj.obj V) (M.val.obj V) := by
    obtain rfl : V = op ⟨PUnit.unit⟩ := Subsingleton.elim _ _
    exact hM
  have hP : PreservesFiniteLimits (MonoidalCategory.tensorRight M.val) := by
    constructor
    intro K _ _
    have (V : (Discrete PUnit.{u + 1})ᵒᵖ) :
        Module.Flat (R.obj.obj V) (M.val.obj V) := hflat V
    exact ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
      (fun V ↦ isLimitOfPreserves
        (MonoidalCategory.tensorRight (show ModuleCat (R.obj.obj V) from M.val.obj V))
        (isLimitOfPreserves (PresheafOfModules.evaluation O.obj V) hc))⟩⟩⟩
  have : Presheaf.IsLocallyInjective ⊥ (𝟙 O.obj) :=
    Presheaf.isLocallyInjective_of_injective ⊥ _ (fun _ ↦ Function.injective_id)
  have : Presheaf.IsLocallySurjective ⊥ (𝟙 O.obj) :=
    Presheaf.isLocallySurjective_of_surjective ⊥ _ (fun _ ↦ Function.surjective_id)
  have hs := (PresheafOfModules.isFlat_sheafification_obj
    (R := R) (𝟙 O.obj) M.val hP).2
  let e := asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).counit.app M)
  let := SheafOfModules.monoidalCategory R
  exact (exactFunctor _ _).prop_of_iso
    ((MonoidalCategory.curriedTensor _).flip.mapIso e) hs

private theorem ring_isZero_of_point {A : Type u} [CommRing A]
    (M : RingSiteModules A) [Subsingleton (M.val.obj (op ⟨PUnit.unit⟩))] :
    IsZero M := by
  apply (IsZero.iff_id_eq_zero M).2
  apply SheafOfModules.hom_ext
  ext V : 1
  obtain rfl : V = op ⟨PUnit.unit⟩ := Subsingleton.elim _ _
  ext x
  exact Subsingleton.elim _ _

private theorem ordered_coordinates_kflat (A : CommRingCat.{u}) (r : ℕ)
    (f : Fin r → A) (K : CochainComplex (RingSiteModules A) ℤ)
    (e₀ : (K.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] A)
    (e : ∀ q : ℕ, (K.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
      ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i))))
    (hneg : ∀ n : ℤ, n < 0 → IsZero (K.X n)) :
    K.IsKFlatTensor := by
  classical
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨r, fun n hn ↦ ?_⟩
    obtain ⟨q, hq⟩ : ∃ q : ℕ, n = (q : ℤ) + 1 := by
      refine ⟨(n - 1).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    subst n
    have ht : IsEmpty (Fin (q + 1) ↪o Fin r) := by
      refine ⟨fun t ↦ ?_⟩
      have := Fintype.card_le_of_injective t t.injective
      simp only [Fintype.card_fin] at this
      omega
    let := ht
    have : Subsingleton ((K.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩)) :=
      (e q).injective.subsingleton
    exact ring_isZero_of_point _
  · intro n
    by_cases hn : n < 0
    · have hz := (SheafOfModules.evaluation
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A)) (op ⟨PUnit.unit⟩)).map_isZero (hneg n hn)
      have : Subsingleton ((K.X n).val.obj (op ⟨PUnit.unit⟩)) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      exact ringFlat_of_point_flat _ inferInstance
    · by_cases hn₀ : n = 0
      · subst n
        exact ringFlat_of_point_flat _ (Module.Flat.of_linearEquiv e₀)
      · obtain ⟨q, hq⟩ : ∃ q : ℕ, n = (q : ℤ) + 1 := by
          refine ⟨(n - 1).toNat, ?_⟩
          rw [Int.toNat_of_nonneg (by omega)]
          omega
        subst n
        have (t : Fin (q + 1) ↪o Fin r) :
            Module.Flat A (Localization.Away (∏ i, f (t i))) := inferInstance
        exact ringFlat_of_point_flat _ (Module.Flat.of_linearEquiv
          ((e q).trans DFinsupp.linearEquivFunOnFintype.symm))

private theorem augmented_iso_of_good_quasiIso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive]
    (good : CochainComplex A ℤ → Prop)
    (hres : ∀ Z : CochainComplex A ℤ,
      ∃ (W : CochainComplex A ℤ) (q : W ⟶ Z), good W ∧ QuasiIso q)
    (hF : ∀ {K L : CochainComplex A ℤ} (t : K ⟶ L),
      good K → good L → QuasiIso t →
        QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map t))
    (K L U : CochainComplex A ℤ) (a : K ⟶ U) (b : L ⟶ U)
    (hK : good K) (hL : good L)
    (α : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L)
    (hα : α.hom ≫ DerivedCategory.Q.map b = DerivedCategory.Q.map a) :
    ∃ e : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ≅
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj L),
      e.hom ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map b) =
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) := by
  classical
  obtain ⟨Z, s, hs, t, he⟩ := DerivedCategory.right_fac α.hom
  let := hs
  have hs' : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs
  have htiso : IsIso (DerivedCategory.Q.map t) := by
    have ht : DerivedCategory.Q.map t = DerivedCategory.Q.map s ≫ α.hom := by
      rw [he, IsIso.hom_inv_id_assoc]
    rw [ht]
    infer_instance
  have ht' : QuasiIso t :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).1 htiso
  have hst : DerivedCategory.Q.map (s ≫ a) = DerivedCategory.Q.map (t ≫ b) := by
    simp only [Functor.map_comp]
    rw [← hα, ← Category.assoc, he, IsIso.hom_inv_id_assoc]
  let H := HomotopyCategory.quotient A (.up ℤ)
  have hh : DerivedCategory.Qh.map (H.map (s ≫ a)) =
      DerivedCategory.Qh.map (H.map (t ≫ b)) := by
    apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app U)).1
    simp only [H, DerivedCategory.quotientCompQhIso_hom_naturality, hst]
  obtain ⟨V, v, hv, hcomm⟩ :=
    (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (.up ℤ)) _ _).1 hh
  obtain ⟨V, rfl⟩ := HomotopyCategory.quotient_obj_surjective V
  obtain ⟨v, rfl⟩ := H.map_surjective v
  have hv' : QuasiIso v :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff v).1 hv
  have hhom : Homotopy (v ≫ s ≫ a) (v ≫ t ≫ b) :=
    HomotopyCategory.homotopyOfEq _ _ (by
      simpa only [Functor.map_comp, Category.assoc] using hcomm)
  obtain ⟨W, q, hW, hq⟩ := hres V
  let := hs'
  let := ht'
  let := hv'
  let := hq
  let u := q ≫ v ≫ s
  let z := q ≫ v ≫ t
  have hu : QuasiIso u := inferInstance
  have hz : QuasiIso z := inferInstance
  let T := F.mapHomologicalComplex (.up ℤ)
  have hTu : QuasiIso (T.map u) := hF u hW hK hu
  have hTz : QuasiIso (T.map z) := hF z hW hL hz
  let := hTu
  let := hTz
  let e := (asIso (DerivedCategory.Q.map (T.map u))).symm ≪≫
    asIso (DerivedCategory.Q.map (T.map z))
  refine ⟨e, ?_⟩
  apply (cancel_epi (DerivedCategory.Q.map (T.map u))).1
  change DerivedCategory.Q.map (T.map u) ≫
      ((inv (DerivedCategory.Q.map (T.map u)) ≫
        DerivedCategory.Q.map (T.map z)) ≫ DerivedCategory.Q.map (T.map b)) = _
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  apply DerivedCategory.Q_map_eq_of_homotopy
  apply F.mapHomotopy
  simpa only [u, z, Category.assoc] using hhom.symm.compLeft q

/-- Scalar extension of a K-flat augmented Čech model has the image-ideal Čech model,
with its augmentation normalized on the actual sheafification unit.
Source: Stacks Project, dualizing.tex, Tag 0ALZ, and algebraization.tex, Tag 099D(c).
(auxiliary; not a blueprint node)

Proof: define the augmentation by extending the semilinear map obtained from εP and φ;
the extension/restriction adjunction gives its stated value on 1 tensor x. Choose finite
generators f of I. The ordered localization complex C(f) is bounded and termwise flat:
its terms are finite products of flat localizations, and increasing tuples do not exist
above the length of f. Thus C(f) is K-flat. Represent the augmented derived isomorphism
between C(f) and P by a common cochain roof, and take a K-flat resolution of the roof's
source. Its two legs are quasi-isomorphisms between K-flat complexes. Termwise scalar
extension preserves both legs by changeOfRings_kFlat_quasiIso. The augmented equations
also survive this operation: a derived equality can be checked after a further common
roof refinement, followed by a K-flat resolution; cochain homotopies are preserved by
the additive extension functor. For each product g of generators, use the localization
isomorphism B tensor_A A[1/g] = B[1/φ(g)], sending b tensor a/g^n to bφ(a)/φ(g)^n.
Its inverse sends b/φ(g)^n to b tensor 1/g^n. These maps commute with the face maps,
alternating differentials, and augmentations, so the resulting augmented derived object
is C(φ(f)). For any other generating list of J, use the common refinement of the two
principal-open covers of Spec(B) minus V(J): the augmented Čech comparison is a
quasi-isomorphism: its iterated localization rows are augmented-exact, because the
other generating list generates the unit ideal after localization. Exactness follows
by clearing finitely many denominators and expressing one as a sum of generator powers.
This gives the model property for every list, as required by RingComplexHasCechModel.
Empty lists give the ring in degree zero;
localization at zero is zero. The same constructions therefore include both cases. -/
theorem ringComplex_cech_scalar_model
    (A B : CommRingCat.{u}) [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules B)] (φ : A →+* B)
    (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
    (h : I.val.map φ = J.val)
    (P : CochainComplex (RingSiteModules A) ℤ)
    (εP : P ⟶ ringComplexSingle A)
    (hCA : RingComplexHasCechModel A I.val P εP) (hP : P.IsKFlatTensor) :
    ∃ εE : ringComplexExtensionComplex φ P ⟶ ringComplexSingle B,
      RingComplexHasCechModel B J.val (ringComplexExtensionComplex φ P) εE ∧
      ∀ x : (P.X 0).val.obj (op ⟨PUnit.unit⟩),
        ringComplexAugmentationValue εE
          ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
            (ringSiteMap φ) (P.X 0)).presheaf).app (op ⟨PUnit.unit⟩)
              ((1 : B) ⊗ₜ[A, φ] x)) = φ (ringComplexAugmentationValue εP x) := by
  classical
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.property
  obtain ⟨C, a, e₀, e, l, hneg, hd₀, hd, ha, α, hα⟩ := hCA r f hf
  have hC : C.IsKFlatTensor := ordered_coordinates_kflat A r f C e₀ e hneg
  have hfB : Ideal.span (Set.range (φ ∘ f)) = J.val := by
    rw [Set.range_comp, ← Ideal.map_span]
    exact (congrArg (Ideal.map φ)
      (show Ideal.span (Set.range f) = I.val from hf)).trans h
  have hG := ringComplex_godement_cech B J
  obtain ⟨D, b, e₀', e', l', hneg', hd₀', hd', ha', γ, hγ⟩ := hG r (φ ∘ f) hfB
  obtain ⟨β, hβ⟩ := ringComplex_ordered_scalar_iso A B φ r f C a
    e₀ e l hneg hd₀ hd ha D b e₀' e' l' hneg' hd₀' hd' ha'
  have hres : ∀ Z : CochainComplex (RingSiteModules A) ℤ,
      ∃ (W : CochainComplex (RingSiteModules A) ℤ) (q : W ⟶ Z),
        W.IsKFlatTensor ∧ QuasiIso q := by
    intro Z
    obtain ⟨W, q, hW, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := CochainComplex.onePointRingSheaf A) Z
    exact ⟨W, q, hW, hq⟩
  obtain ⟨δ, hδ⟩ := augmented_iso_of_good_quasiIso (ringComplexExtension φ)
    CochainComplex.IsKFlatTensor hres
    (fun t ht ht' hq ↦ SheafOfModules.changeOfRings_kFlat_quasiIso
      (ringSiteMap φ) (ringComplexExtension φ) (fun _ ↦ rfl) (fun _ ↦ rfl)
      t ht ht' hq) C P (ringComplexSingle A) a εP hC hP α hα
  have hδ' : δ.hom ≫ DerivedCategory.Q.map (ringComplexScalarAugmentation φ εP) =
      DerivedCategory.Q.map (ringComplexScalarAugmentation φ a) := by
    have h' := congrArg (fun t ↦ t ≫ DerivedCategory.Q.map (ringComplexScalarSingle φ)) hδ
    simpa only [ringComplexScalarAugmentation, Functor.map_comp, Category.assoc] using h'
  let η := γ.symm ≪≫ (DerivedCategory.Q.mapIso β).symm ≪≫ δ
  have hη : η.hom ≫ DerivedCategory.Q.map (ringComplexScalarAugmentation φ εP) =
      DerivedCategory.Q.map (ringComplexGodementAugmentation B J.val) := by
    dsimp only [η, Iso.trans_hom, Iso.symm_hom, Functor.mapIso]
    rw [Category.assoc, Category.assoc, hδ', ← hβ, Functor.map_comp,
      ← Category.assoc (DerivedCategory.Q.map β.inv), ← Functor.map_comp,
      β.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, ← hγ, Iso.inv_hom_id_assoc]
  refine ⟨ringComplexScalarAugmentation φ εP, ?_,
    ringComplexScalarAugmentation_one_tmul φ εP⟩
  intro s g hg
  obtain ⟨T, c, t₀, t, k, htneg, htd₀, htd, htc, ζ, hζ⟩ := hG s g hg
  refine ⟨T, c, t₀, t, k, htneg, htd₀, htd, htc, ζ ≪≫ η, ?_⟩
  rw [Iso.trans_hom, Category.assoc, hη, hζ]

end AlgebraicGeometry
