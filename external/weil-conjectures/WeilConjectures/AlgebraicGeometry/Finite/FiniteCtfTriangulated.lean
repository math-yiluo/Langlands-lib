/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-!
# Finite-stage constructible complexes of finite Tor amplitude

Source: Stacks Project, Cohomology on Sites, Tag 08G2, lemma-cone-tor-amplitude (2),
and the Weil blueprint, finite-stage paragraph of `definition-constructible-sheaves`
(blueprint: lem-weil-finite-ctf-triangulated).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme

private noncomputable abbrev torRing (Y : Scheme.{u}) (A : Type u) [CommRing A] :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} A))

private noncomputable abbrev torModules (Y : Scheme.{u}) (A : Type u) [CommRing A] :=
  SheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (torRing Y A))

-- The separate site universes make the derived tensor instance terms large.
set_option synthInstance.maxSize 2048 in
private theorem tensor_functor (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (M : torModules Y A) :
    ∃ F : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y A,
      ∃ (_ : F.CommShift ℤ), F.IsTriangulated ∧
        ∀ (L P : CochainComplex (torModules Y A) ℤ) (f : P ⟶ L) (hf : QuasiIso f)
          (hP : CochainComplex.IsAcyclicTensorKFlat (R := torRing Y A) P),
          Nonempty (F.obj (DerivedCategory.Q.obj L) ≅ derivedTensor Y A L
            ((HomologicalComplex.single _ (.up ℤ) 0).obj M) P f hf hP) := by
  let R := torRing Y A
  let C := torModules Y A
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfg (R := R)
  have := SheafOfModules.monoidalPreadditive_kfg R
  have := SheafOfModules.isGrothendieckAbelian_kfg R
  have := SheafOfModules.hasFunctorialFlatResolution_kfg R
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} C
  let := HasDerivedCategory.standard C
  have := DerivedCategory.hasDerivedMonoidalCategory C
  let : MonoidalCategory (DerivedCategory C) := inferInstance
  let : (DerivedCategory.Qh (C := C)).LaxMonoidal := inferInstance
  let : (DerivedCategory.Q (C := C)).LaxMonoidal := inferInstance
  have hk (P : CochainComplex C ℤ)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P) :
      (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
        ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hright : HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (.up ℤ)).obj N ⊗
          (HomotopyCategory.quotient C (.up ℤ)).obj P) := by
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hright, hright⟩
  let S := (HomologicalComplex.single C (.up ℤ) 0).obj M
  obtain ⟨N, g, hN, _, hg, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral S
  let Nh := (HomotopyCategory.quotient C (.up ℤ)).obj N
  let F := (curriedTensor (DerivedCategory C)).flip.obj (DerivedCategory.Qh.obj Nh)
  let := DerivedCategory.commShiftTensorRightQhObj Nh (hk N hN)
  have := DerivedCategory.isTriangulated_tensorRightQhObj Nh (hk N hN)
  refine ⟨F, inferInstance, inferInstance, ?_⟩
  intro L P f hf hP
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C g).2 hg
  have : IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) P S) := by
    have hq := DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
      (DerivedCategory.Qh (C := C)) (HomotopyCategory.quasiIso C (.up ℤ))
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj S) (hk P hP)
    have : IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := C))
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj S)) := hq
    change IsIso (_ ≫ _ ≫ _)
    change IsIso (_ ≫ (_ ≫ _) ≫ _)
    infer_instance
  exact ⟨((asIso (DerivedCategory.Q.map f)).symm ⊗ᵢ
      ((DerivedCategory.quotientCompQhIso C).app N ≪≫ asIso (DerivedCategory.Q.map g))) ≪≫
    asIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) P S)⟩

private theorem tensor_homology_vanishes (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory Y A) (a b : ℤ)
    (M : torModules Y A)
    (F : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y A)
    (hF : ∀ (L P : CochainComplex (torModules Y A) ℤ) (f : P ⟶ L) (hf : QuasiIso f)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := torRing Y A) P),
      Nonempty (F.obj (DerivedCategory.Q.obj L) ≅ derivedTensor Y A L
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M) P f hf hP))
    (hK : HasProEtaleTorAmplitude Y A K a b) (i : ℤ) (hi : i < a ∨ b < i) :
    IsZero ((DerivedCategory.homologyFunctor (torModules Y A) i).obj (F.obj K)) := by
  have : (DerivedCategory.Q (C := torModules Y A)).EssSurj :=
    Localization.essSurj _ (HomologicalComplex.quasiIso _ (.up ℤ))
  let L := (DerivedCategory.Q (C := torModules Y A)).objPreimage K
  let e := (DerivedCategory.Q (C := torModules Y A)).objObjPreimageIso K
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
  obtain ⟨q⟩ := hF L P f hf hP
  exact (hK.2 L P ⟨e⟩ f hf hP M i hi).of_iso
    ((DerivedCategory.homologyFunctor (torModules Y A) i).mapIso
      ((F.mapIso e).symm ≪≫ q))

private theorem amplitude_iso
    (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory Y A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude Y A K a b) : HasProEtaleTorAmplitude Y A L a b := by
  refine ⟨h.1, ?_⟩
  intro N P hN f hf hP M i hi
  obtain ⟨q⟩ := hN
  exact h.2 N P ⟨q ≪≫ e.symm⟩ f hf hP M i hi

private theorem amplitude_mono
    (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {K : proEtaleDerivedCategory Y A} {a b c d : ℤ}
    (h : HasProEtaleTorAmplitude Y A K a b) (hc : c ≤ a) (hd : b ≤ d) :
    HasProEtaleTorAmplitude Y A K c d := by
  refine ⟨hc.trans (h.1.trans hd), ?_⟩
  intro N P hN f hf hP M i hi
  apply h.2 N P hN f hf hP M i
  rcases hi with hi | hi
  · exact Or.inl (hi.trans_le hc)
  · exact Or.inr (hd.trans_lt hi)

/-- Bounded constructibility and finite Tor amplitude cut out a strictly full triangulated
subcategory on the small pro-etale site. The last two clauses retain the precise interval
bounds under shifts and extensions.

Source: Stacks Project, Cohomology on Sites, Tag 08G2, lemma-cone-tor-amplitude (2),
Tag 08FZ, definition-tor-amplitude; Weil blueprint, finite-stage paragraph of
`definition-constructible-sheaves` (blueprint: lem-weil-finite-ctf-triangulated).

Proof:
1. Apply `Padic.finite_coefficientExtensionRing` and the existing bounded-constructibility
closure theorem.
2. Resolve a degree-zero test sheaf by a K-flat complex. Tensoring with its image in the
homotopy localization is triangulated, by the existing monoidal derived-category API.
The localized quasi-isomorphism and the invertible tensor comparison identify its value
with every K-flat presentation used by `HasProEtaleTorAmplitude`.
3. Transport vanishing across these comparisons. Tensor sends zero to zero, giving `[0,0]`.
The shift comparison and the homology shift isomorphism give `[a-m,b-m]`.
4. After enlarging endpoint intervals to their minimum/maximum interval, apply the exact
homology segment of the tensor image of a distinguished triangle. Zero endpoint homology
forces zero middle homology, with no enlargement when the intervals already agree.
5. Intersect these closure properties with bounded constructibility and use Mathlib's
triangulated-subcategory criterion.
-/
theorem finite_ctf_isTriangulated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E n hn Y ⊓
        fun K ↦ HasFiniteProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K) ∧
    ObjectProperty.IsTriangulated
      (intrinsicFiniteTorsionConstructible l E n hn Y ⊓
        fun K ↦ HasFiniteProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K) ∧
    (∀ (K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) (a b m : ℤ),
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n)
        (K⟦m⟧) (a - m) (b - m)) ∧
    (∀ (T : Triangle (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)))
      (a b : ℤ), T ∈ distTriang _ →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₁ a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₃ a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₂ a b) := by
  let A := Padic.coefficientExtensionRing l E n
  let P := intrinsicFiniteTorsionConstructible l E n hn Y
  let Q : ObjectProperty (proEtaleDerivedCategory Y A) :=
    fun K ↦ HasFiniteProEtaleTorAmplitude Y A K
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  obtain ⟨hPi, hPt⟩ := proEtale_bounded_constructible_isTriangulated Y A
  have : P.IsClosedUnderIsomorphisms := hPi
  have : P.IsTriangulated := hPt
  have hzero : HasProEtaleTorAmplitude Y A (0 : proEtaleDerivedCategory Y A) 0 0 := by
    refine ⟨le_rfl, ?_⟩
    intro L P hL f hf hP M i _hi
    obtain ⟨F, c, htri, hcomp⟩ := tensor_functor Y A M
    obtain ⟨e⟩ := hL
    obtain ⟨q⟩ := hcomp L P f hf hP
    have hz := F.map_isZero ((isZero_zero _).of_iso e)
    exact ((DerivedCategory.homologyFunctor (torModules Y A) i).map_isZero hz).of_iso
      ((DerivedCategory.homologyFunctor (torModules Y A) i).mapIso q.symm)
  have hshift : ∀ (K : proEtaleDerivedCategory Y A) (a b m : ℤ),
      HasProEtaleTorAmplitude Y A K a b →
      HasProEtaleTorAmplitude Y A (K⟦m⟧) (a - m) (b - m) := by
    intro K a b m hK
    refine ⟨by have hab := hK.1; omega, ?_⟩
    intro L P hL f hf hP M i hi
    obtain ⟨F, c, htri, hcomp⟩ := tensor_functor Y A M
    obtain ⟨e⟩ := hL
    obtain ⟨q⟩ := hcomp L P f hf hP
    have hz := tensor_homology_vanishes Y A K a b M F hcomp hK (m + i) (by omega)
    let hs := ((DerivedCategory.homologyFunctor (torModules Y A) 0).shiftIso
      m i (m + i) rfl).app (F.obj K)
    exact hz.of_iso
      ((DerivedCategory.homologyFunctor (torModules Y A) i).mapIso
        (q.symm ≪≫ F.mapIso e ≪≫ (F.commShiftIso m).app K) ≪≫ hs)
  have hext : ∀ (T : Triangle (proEtaleDerivedCategory Y A)) (a b : ℤ),
      T ∈ distTriang _ → HasProEtaleTorAmplitude Y A T.obj₁ a b →
      HasProEtaleTorAmplitude Y A T.obj₃ a b → HasProEtaleTorAmplitude Y A T.obj₂ a b := by
    intro T a b hT h₁ h₃
    refine ⟨h₁.1, ?_⟩
    intro L P hL f hf hP M i hi
    obtain ⟨F, c, htri, hcomp⟩ := tensor_functor Y A M
    obtain ⟨e⟩ := hL
    obtain ⟨q⟩ := hcomp L P f hf hP
    have hz₁ := tensor_homology_vanishes Y A T.obj₁ a b M F hcomp h₁ i hi
    have hz₃ := tensor_homology_vanishes Y A T.obj₃ a b M F hcomp h₃ i hi
    have hz := (DerivedCategory.HomologySequence.exact₂
      (F.mapTriangle.obj T) (F.map_distinguished T hT) i).isZero_of_both_isZero hz₁ hz₃
    exact hz.of_iso ((DerivedCategory.homologyFunctor (torModules Y A) i).mapIso
      (q.symm ≪≫ F.mapIso e))
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e ⟨a, b, h⟩ ↦ ⟨a, b, amplitude_iso Y A e a b h⟩⟩
  have : Q.ContainsZero := ⟨0, isZero_zero _, 0, 0, hzero⟩
  have : Q.IsStableUnderShift ℤ :=
    ⟨fun m ↦ ⟨fun K ⟨a, b, h⟩ ↦ ⟨a - m, b - m, hshift K a b m h⟩⟩⟩
  have : Q.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (by
    intro T hT h₁ h₃
    obtain ⟨a, b, h₁⟩ := h₁
    obtain ⟨c, d, h₃⟩ := h₃
    exact ⟨min a c, max b d, hext T _ _ hT
      (amplitude_mono Y A h₁ (min_le_left _ _) (le_max_left _ _))
      (amplitude_mono Y A h₃ (min_le_right _ _) (le_max_right _ _))⟩)
  have : Q.IsTriangulated := { }
  exact ⟨inferInstanceAs (P ⊓ Q).IsClosedUnderIsomorphisms,
    inferInstanceAs (P ⊓ Q).IsTriangulated, hshift, hext⟩

end AlgebraicGeometry.Scheme
