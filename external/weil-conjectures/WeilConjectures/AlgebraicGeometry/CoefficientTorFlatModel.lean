/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.Algebra.Homology.FlatCoverFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Bounded flat models for the coefficient-model Tor test

Source: Stacks Project, Tags 08G0 and 08G1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})

/-- Homology of the ordinary tensor with a degree-zero module.
Source: Stacks Tags 06YN and 08FZ (auxiliary; not a blueprint node). -/
abbrev coefficientModelTensorTest (P : ConstantCompletion.Cx R)
    (M : ConstantCompletion.Mod R) (q : ℤ) : ConstantCompletion.Mod R :=
  ((((ringedKoszulTensor R).obj P).obj
    ((HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0).obj M)).homology q)

private local instance moduleMonoidal : MonoidalCategory (ConstantCompletion.Mod R) :=
  SheafOfModules.monoidalCategory R
private local instance moduleSymmetric : SymmetricCategory (ConstantCompletion.Mod R) :=
  SheafOfModules.symmetricCategory R
private local instance moduleClosed : MonoidalClosed (ConstantCompletion.Mod R) :=
  Classical.choice (SheafOfModules.tensorClosed R).2.1
private local instance modulePreadditive : MonoidalPreadditive (ConstantCompletion.Mod R) :=
  Classical.choice (SheafOfModules.tensorClosed R).1
private local instance moduleGrothendieck : IsGrothendieckAbelian.{w} (ConstantCompletion.Mod R) :=
  SheafOfModules.isGrothendieckAbelian _

private theorem categorical_flat_iff (M : ConstantCompletion.Mod R) :
    ObjectProperty.flat M ↔ SheafOfModules.IsFlat (R := R) M := by
  constructor
  · exact fun h ↦ h.2
  · intro h
    have : PreservesFiniteLimits (tensorRight M) := h.1
    exact (ObjectProperty.flat_iff_preservesFiniteLimits M).2
      (preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight M).symm (F := tensorRight M))

private theorem moduleFlatResolution :
    Abelian.HasFunctorialFlatResolution (ConstantCompletion.Mod R) := by
  obtain ⟨T, π, hT⟩ := SheafOfModules.exists_functorial_flat_cover J R
  exact ⟨{
    F := ObjectProperty.flat.lift T (fun M ↦ (categorical_flat_iff R _).mpr (hT M).1)
    π := π
    epi_π_app := fun M ↦ (hT M).2 }⟩

private local instance standardDerived : HasDerivedCategory (ConstantCompletion.Mod R) :=
  HasDerivedCategory.standard _

private local instance flatResolution :
    Abelian.HasFunctorialFlatResolution (ConstantCompletion.Mod R) :=
  moduleFlatResolution R

private local instance smallColimits : HasColimitsOfSize.{0, 0} (ConstantCompletion.Mod R) :=
  hasColimitsOfSizeShrink.{0, 0, w, w} _

private theorem nativeKFlat_iff (P : ConstantCompletion.Cx R) :
    (HomologicalComplex.quasiIso (ConstantCompletion.Mod R) (.up ℤ)).kFlat P ↔
      P.IsKFlatIndependentCoefficients := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  constructor
  · intro h Z hZ
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
      (h ((HomotopyCategory.quotient _ (.up ℤ)).obj Z)
        ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).mpr hZ)).2
  · intro h Z hZ
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    have hZ' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).mp hZ
    have ht := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor Z P (curriedTensor _))).mpr (h Z hZ')
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) ht, ht⟩

/-- Every coefficient-model derived object has a K-flat representative with flat terms.
Source: Stacks Project, Tag 06YS
(auxiliary; not a blueprint node).
Proof: use the native functorial flat resolution of a localization representative.
The acyclic-test criterion identifies its native K-flatness with the coefficient
predicate. Localize the quasi-isomorphism and compose with the representative iso. -/
theorem exists_coefficientModelFlatKFlatRepresentative (K : ConstantCompletion.D R) :
    ∃ P : ConstantCompletion.Cx R, P.IsKFlatIndependentCoefficients ∧
      (∀ i, SheafOfModules.IsFlat (P.X i)) ∧
        Nonempty ((ConstantCompletion.Q R).obj P ≅ K) := by
  let G := (ConstantCompletion.Q R).objPreimage K
  obtain ⟨P, π, hπ, hf, hk⟩ := CochainComplex.exists_quasiIso_flat_kFlat G
  have : QuasiIso π := hπ
  have : IsIso ((ConstantCompletion.Q R).map π) := by infer_instance
  exact ⟨P, (nativeKFlat_iff R P).mp hk,
    fun i ↦ (categorical_flat_iff R _).mp (hf i),
    ⟨asIso ((ConstantCompletion.Q R).map π) ≪≫
      (ConstantCompletion.Q R).objObjPreimageIso K⟩⟩

/-- Tensor-test homology depends only on the derived class of a K-flat representative.
Source: Stacks Project, Tags 06YN and 06YY
(auxiliary; not a blueprint node).
Proof: compute the native derived tensor on both K-flat representatives, tensor the
supplied derived isomorphism with the identity of the degree-zero module, and apply
derived homology and its localization factorization. -/
theorem coefficientModelTensorTest_iso (P Q : ConstantCompletion.Cx R)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (e : (ConstantCompletion.Q R).obj P ≅ (ConstantCompletion.Q R).obj Q)
    (M : ConstantCompletion.Mod R) (q : ℤ) :
    Nonempty (coefficientModelTensorTest R P M q ≅ coefficientModelTensorTest R Q M q) := by
  let T := (HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0).obj M
  let eT :=
    (DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P T ((nativeKFlat_iff R P).mpr hP)).symm ≪≫
      tensorIso e (Iso.refl ((ConstantCompletion.Q R).obj T)) ≪≫
        DerivedCategory.QObjTensorQObjIsoOfKFlatLeft Q T ((nativeKFlat_iff R Q).mpr hQ)
  exact ⟨((DerivedCategory.homologyFunctorFactors (ConstantCompletion.Mod R) q).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ConstantCompletion.Mod R) q).mapIso eT ≪≫
      (DerivedCategory.homologyFunctorFactors (ConstantCompletion.Mod R) q).app _⟩

private theorem nativeTor_iff (K : ConstantCompletion.D R) (a b : ℤ) (hab : a ≤ b) :
    DerivedCategory.torAmplitudeIn (ConstantCompletion.Mod R) a b K ↔
      HasCoefficientModelTorAmplitude R K a b := by
  let A := ConstantCompletion.Mod R
  have modelIso {L : ConstantCompletion.D R} (P : ConstantCompletion.Cx R)
      (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P)
      (e : (ConstantCompletion.Q R).obj P ≅ L) (M : A) :
      L ⊗ (DerivedCategory.singleFunctor A 0).obj M ≅
        (ConstantCompletion.Q R).obj
          (((ringedKoszulTensor R).obj P).obj ((HomologicalComplex.single A (.up ℤ) 0).obj M)) :=
    tensorIso e.symm ((DerivedCategory.singleFunctorIsoCompQ A 0).app M) ≪≫
      DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P _ hP
  constructor
  · intro hK
    refine ⟨hab, ?_⟩
    intro P hP ⟨e⟩ M q hq
    have hp := (nativeKFlat_iff R P).mpr hP
    have ht := hK M
    have hs := (DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (modelIso P hp e M) ht
    have hz : IsZero ((DerivedCategory.homologyFunctor A q).obj
        ((ConstantCompletion.Q R).obj
          (((ringedKoszulTensor R).obj P).obj
            ((HomologicalComplex.single A (.up ℤ) 0).obj M)))) := by
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff _ a).mp hs.1 q hq
      · exact (DerivedCategory.isLE_iff _ b).mp hs.2 q hq
    exact hz.of_iso ((DerivedCategory.homologyFunctorFactors A q).symm.app _)
  · intro hK M
    let G := (ConstantCompletion.Q R).objPreimage K
    obtain ⟨P, π, hπ, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat G
    have : QuasiIso π := hπ
    have : IsIso ((ConstantCompletion.Q R).map π) := by infer_instance
    let e : (ConstantCompletion.Q R).obj P ≅ K :=
      asIso ((ConstantCompletion.Q R).map π) ≪≫ (ConstantCompletion.Q R).objObjPreimageIso K
    have hz (q : ℤ) (hq : q < a ∨ b < q) :
        IsZero ((DerivedCategory.homologyFunctor A q).obj
          (K ⊗ (DerivedCategory.singleFunctor A 0).obj M)) := by
      have ht := hK.2 P ((nativeKFlat_iff R P).mp hP) ⟨e⟩ M q hq
      exact ht.of_iso ((DerivedCategory.homologyFunctor A q).mapIso
        (modelIso P hP e M) ≪≫ (DerivedCategory.homologyFunctorFactors A q).app _)
    exact ⟨(DerivedCategory.isGE_iff _ a).mpr (fun q hq ↦ hz q (Or.inl hq)),
      (DerivedCategory.isLE_iff _ b).mpr (fun q hq ↦ hz q (Or.inr hq))⟩

/-- A coefficient-model Tor bound is exactly a flat complex in the same interval.
Source: Stacks Project, Tags 08G0 and 08G1
(auxiliary; not a blueprint node).

Proof: identify the K-flat acyclic test with preservation of quasi-isomorphisms using
cones and tensor symmetry. The native derived tensor is computed by precisely that
ordinary total tensor on every K-flat representative. Hence its Tor predicate agrees
with the coefficient-model predicate. Apply the generic bounded-flat-model criterion:
test against the unit, take a bounded-above flat resolution, and truncate at the lower
bound. The opcycle term is flat by universal tensor exactness in the preceding degree.
Conversely a bounded flat model is K-flat and its tensor with any degree-zero sheaf
vanishes termwise outside the given interval. -/
theorem coefficientModelTorAmplitude_iff_flatModel (K : ConstantCompletion.D R)
    (a b : ℤ) (hab : a ≤ b) :
    HasCoefficientModelTorAmplitude R K a b ↔
      ∃ (P : ConstantCompletion.Cx R) (_ : P.IsStrictlyGE a) (_ : P.IsStrictlyLE b),
        (∀ i, SheafOfModules.IsFlat (R := R) (P.X i)) ∧
          Nonempty ((ConstantCompletion.Q R).obj P ≅ K) := by
  rw [← nativeTor_iff R K a b hab]
  simpa only [categorical_flat_iff R] using
    (DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K)

end CategoryTheory
