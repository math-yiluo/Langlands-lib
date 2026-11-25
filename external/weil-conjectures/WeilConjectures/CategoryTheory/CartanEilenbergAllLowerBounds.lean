/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.CategoryTheory.CartanEilenbergRowsIdentifications
import WeilConjectures.CategoryTheory.CartanEilenbergBoundaryProjection
import WeilConjectures.CategoryTheory.Abelian.HorseshoePrescribedResolutions
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-! # Cartan--Eilenberg resolutions preserving all lower support bounds

Source: Stacks Project, Derived Categories, Tags 015H and 015I.
(blueprint: lem-weil-pbc-ce-resolution-all-lower-bounds).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem supported_object_rows
    (B : Type u) [Category.{v} B] [Abelian B] [EnoughInjectives B]
    (K : CochainComplex B ℤ) :
    ∃ (IZ : ∀ p, InjectiveResolution (K.cycles p))
      (ID : ∀ p, InjectiveResolution (image (K.d (p - 1) p)))
      (IH : ∀ p, InjectiveResolution (K.homology p))
      (w : ∀ p, (ID p).cocomplex ⟶ (IZ p).cocomplex)
      (x : ∀ p, (IZ p).cocomplex ⟶ (IH p).cocomplex),
      (∀ p, IsZero (K.X p) → IsZero (IZ p).cocomplex) ∧
      (∀ p, IsZero (K.X (p - 1)) → IsZero (ID p).cocomplex) ∧
      (∃ hwx : ∀ p, w p ≫ x p = 0,
        ∀ p, (ShortComplex.mk (w p) (x p) (hwx p)).ShortExact) ∧
      (∀ p, (CochainComplex.single₀ B).map (cartanEilenbergBoundaryInclusion K p) ≫
        (IZ p).ι = (ID p).ι ≫ w p) ∧
      (∀ p, (CochainComplex.single₀ B).map (K.homologyπ p) ≫ (IH p).ι =
        (IZ p).ι ≫ x p) := by
  classical
  let b := cartanEilenbergBoundaryInclusion K
  have hb (p : ℤ) : b p ≫ K.homologyπ p = 0 := by
    apply (cancel_epi (factorThruImage (K.d (p - 1) p))).1
    have hf : factorThruImage (K.d (p - 1) p) ≫ b p = K.toCycles (p - 1) p := by
      apply (cancel_mono (K.iCycles p)).1
      simp [b]
    rw [← Category.assoc, hf]
    simp
  let T (p : ℤ) := ShortComplex.mk (b p) (K.homologyπ p) (hb p)
  have hT (p : ℤ) : (T p).ShortExact := by
    have he : (ShortComplex.mk (K.toCycles (p - 1) p) (K.homologyπ p)
        (K.toCycles_comp_homologyπ (p - 1) p)).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel (p - 1) p (by simp))
    let φ : ShortComplex.mk (K.toCycles (p - 1) p) (K.homologyπ p)
        (K.toCycles_comp_homologyπ (p - 1) p) ⟶ T p :=
      { τ₁ := factorThruImage (K.d (p - 1) p)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          dsimp [T]
          apply (cancel_mono (K.iCycles p)).1
          simp [b]
        comm₂₃ := by simp [T] }
    have hm : Mono (T p).f := by
      apply mono_of_mono_fac (cartanEilenbergBoundaryInclusion_fac K p)
    exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 he
            mono_f := hm
            epi_g := inferInstance }
  have hd (p : ℤ) (hp : IsZero (K.X (p - 1))) : IsZero (image (K.d (p - 1) p)) :=
    IsZero.of_epi (factorThruImage (K.d (p - 1) p)) hp
  have hh (p : ℤ) (hp : IsZero (K.X p)) : IsZero (K.homology p) :=
    (K.sc p).isZero_homology_of_isZero_X₂ hp
  let ID (p : ℤ) : InjectiveResolution (image (K.d (p - 1) p)) :=
    if hp : IsZero (image (K.d (p - 1) p)) then
      let _ := hp.injective
      InjectiveResolution.self _
    else InjectiveResolution.of _
  let IH (p : ℤ) : InjectiveResolution (K.homology p) :=
    if hp : IsZero (K.homology p) then
      let _ := hp.injective
      InjectiveResolution.self _
    else InjectiveResolution.of _
  have hdimage (p : ℤ) (hp : IsZero (image (K.d (p - 1) p))) :
      IsZero (ID p).cocomplex := by
    dsimp [ID]
    rw [dite_eq_left hp]
    exact Functor.map_isZero (CochainComplex.single₀ B) hp
  have hdneg (p : ℤ) (hp : IsZero (K.X (p - 1))) : IsZero (ID p).cocomplex :=
    hdimage p (hd p hp)
  have hhneg (p : ℤ) (hp : IsZero (K.X p)) : IsZero (IH p).cocomplex := by
    dsimp [IH]
    rw [dite_eq_left (hh p hp)]
    exact Functor.map_isZero (CochainComplex.single₀ B) (hh p hp)
  have hs (p : ℤ) := InjectiveResolution.exists_horseshoe_prescribed_resolutions
    (T p) (hT p) (ID p) (IH p)
  choose IZ w x hw hx hwx hrows using hs
  have hex (p : ℤ) := HomologicalComplex.shortExact_of_degreewise_shortExact
    (ShortComplex.mk (w p) (x p) (hwx p)) (fun q ↦ (hrows p q).1)
  refine ⟨IZ, ID, IH, w, x, ?_, hdneg, ⟨hwx, hex⟩, fun p ↦ (hw p).symm, fun p ↦ (hx p).symm⟩
  intro p hp
  have hi : IsIso (w p) := (hex p).isIso_f_iff.mpr (hhneg p hp)
  have hz : IsZero (image (K.d (p - 1) p)) := IsZero.of_mono
    (image.ι (K.d (p - 1) p)) hp
  exact IsZero.of_iso (hdimage p hz) (asIso (w p)).symm


private theorem supported_rows
    (B : Type u) [Category.{v} B] [Abelian B] [EnoughInjectives B]
    (K : CochainComplex B ℤ) :
    let S := ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    ∃ R : CartanEilenbergRows S,
      (∀ (b : ℤ), (∀ s : ℤ, s < b → IsZero (K.X s)) →
        ∀ s : ℤ, s < b → IsZero (R.A s)) ∧
      (∀ p : ℤ, QuasiIso (R.jA p) ∧ QuasiIso (R.jZ p) ∧
        QuasiIso (R.jD p) ∧ QuasiIso (R.jH p)) ∧
      (∀ (p : ℤ) (q : ℕ), Injective ((R.A p).X q) ∧
        Injective ((R.Z p).X q) ∧ Injective ((R.D p).X q) ∧
        Injective ((R.H p).X q)) := by
  let F := CochainComplex.single₀ B
  let S := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  classical
  obtain ⟨IZ, ID, IH, w, x, hzneg, hdneg, ⟨hwx, hex₂⟩, hbw, hx⟩ :=
    supported_object_rows B K
  have hzero (p : ℤ) : K.iCycles p ≫ cartanEilenbergBoundaryProjection K p = 0 := by
    apply (cancel_mono (image.ι (K.d ((p + 1) - 1) (p + 1)))).1
    simp
  let T (p : ℤ) := ShortComplex.mk (K.iCycles p)
    (cartanEilenbergBoundaryProjection K p) (hzero p)
  have hT (p : ℤ) : (T p).ShortExact := by
    have he : (ShortComplex.mk (K.iCycles p) (K.d p (p + 1))
        (K.iCycles_d p (p + 1))).Exact :=
      ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel p (p + 1) (by simp))
    let φ : T p ⟶ ShortComplex.mk (K.iCycles p) (K.d p (p + 1))
        (K.iCycles_d p (p + 1)) :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := image.ι (K.d ((p + 1) - 1) (p + 1))
        comm₁₂ := by simp [T]
        comm₂₃ := by simp [T] }
    have hep : Epi (T p).g := by
      dsimp [T, cartanEilenbergBoundaryProjection]
      infer_instance
    exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 he
            mono_f := inferInstance
            epi_g := hep }
  have hs (p : ℤ) := InjectiveResolution.exists_horseshoe_prescribed_resolutions
    (T p) (hT p) (IZ p) (ID (p + 1))
  choose IA u v hu hv huv hrows using hs
  have hex₁ (p : ℤ) := HomologicalComplex.shortExact_of_degreewise_shortExact
    (ShortComplex.mk (u p) (v p) (huv p)) (fun q ↦ (hrows p q).1)
  have hneg (b : ℤ) (hb : ∀ s : ℤ, s < b → IsZero (K.X s))
      (p : ℤ) (hp : p < b) : IsZero (IA p).cocomplex := by
    have hi : IsIso (u p) := (hex₁ p).isIso_f_iff.mpr (hdneg (p + 1) (by simpa using hb p hp))
    exact IsZero.of_iso (hzneg p (hb p hp)) (asIso (u p)).symm
  have hw (p : ℤ) : F.map (image.ι (K.d (p - 1) p)) ≫ (IA p).ι =
      (ID p).ι ≫ w p ≫ u p := by
    rw [← cartanEilenbergBoundaryInclusion_fac K p, F.map_comp, Category.assoc]
    rw [← hu, ← Category.assoc, hbw]
    simp only [Category.assoc]
  let eZ (p : ℤ) : S.cycles p ≅ F.obj (K.cycles p) :=
    (K.sc p).mapCyclesIso F
  let eD (p : ℤ) : image (S.d (p - 1) p) ≅ F.obj (image (K.d (p - 1) p)) :=
    PreservesImage.iso F (K.d (p - 1) p)
  let eH (p : ℤ) : S.homology p ≅ F.obj (K.homology p) :=
    ((K.sc p).leftHomologyData.map F).homologyIso ≪≫
      F.mapIso (K.sc p).leftHomologyIso
  have hz (p : ℤ) : (eZ p).hom ≫ F.map (K.iCycles p) = S.iCycles p := by
    exact (K.sc p).mapCyclesIso_hom_iCycles F
  have hd (p : ℤ) : (eD p).hom ≫ F.map (image.ι (K.d (p - 1) p)) =
      image.ι (S.d (p - 1) p) := by
    exact PreservesImage.hom_comp_map_image_ι F (K.d (p - 1) p)
  have hh (p : ℤ) : S.homologyπ p ≫ (eH p).hom =
      (eZ p).hom ≫ F.map (K.homologyπ p) := by
    change (S.sc p).homologyπ ≫
      (((K.sc p).leftHomologyData.map F).homologyIso.hom ≫
        F.map (K.sc p).leftHomologyIso.hom) =
      ((K.sc p).leftHomologyData.map F).cyclesIso.hom ≫ F.map (K.sc p).homologyπ
    rw [← Category.assoc,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
      Category.assoc]
    change ((K.sc p).leftHomologyData.map F).cyclesIso.hom ≫
      F.map (K.sc p).leftHomologyData.π ≫ F.map (K.sc p).leftHomologyIso.hom = _
    rw [← F.map_comp]
    rfl
  let R : CartanEilenbergRows S :=
    { A := fun p ↦ (IA p).cocomplex
      Z := fun p ↦ (IZ p).cocomplex
      D := fun p ↦ (ID p).cocomplex
      H := fun p ↦ (IH p).cocomplex
      u := u
      v := v
      w := w
      x := x
      uv := huv
      wx := hwx
      exact₁ := hex₁
      exact₂ := hex₂
      jA := fun p ↦ (IA p).ι
      jZ := fun p ↦ (eZ p).hom ≫ (IZ p).ι
      jD := fun p ↦ (eD p).hom ≫ (ID p).ι
      jH := fun p ↦ (eH p).hom ≫ (IH p).ι
      comm := fun p ↦ by
        change (IA p).ι ≫ v p ≫ w (p + 1) ≫ u (p + 1) =
          F.map (K.d p (p + 1)) ≫ (IA (p + 1)).ι
        rw [← Category.assoc, hv, Category.assoc, ← hw,
          ← Category.assoc, ← F.map_comp, cartanEilenbergBoundaryProjection_fac]
      commZ := fun p ↦ by
        rw [← hz, Category.assoc, ← hu]
        simp only [Category.assoc]
      commD := fun p ↦ by
        rw [← hd, Category.assoc, hw]
        simp only [Category.assoc]
      commH := fun p ↦ by
        rw [← Category.assoc, hh, Category.assoc, hx]
        simp only [Category.assoc] }
  refine ⟨R, hneg, ?_, ?_⟩
  · intro p
    exact ⟨(IA p).quasiIso, inferInstance, inferInstance, inferInstance⟩
  · intro p q
    exact ⟨(IA p).injective q, (IZ p).injective q,
      (ID p).injective q, (IH p).injective q⟩


/-- Resolve a bounded-below complex without introducing rows below its support.
Source: Stacks Project, Tag 015I, with the shift refinement in step 1 of
lem-weil-pbc-ce-supported-first-page-lifts.
(blueprint: lem-weil-pbc-ce-resolution-all-lower-bounds).

Proof. For each degree p choose an injective resolution of B^p and H^p,
using the single-degree-zero resolution when the respective object is zero.
Apply the prescribed-end horseshoe to B^p -> Z^p -> H^p, obtaining a resolution
of Z^p. Apply it again to Z^p -> K^p -> B^(p+1), retaining the same boundary and
cycle resolutions. Assemble the horizontal differential through B^(p+1) and
Z^(p+1). The exact row squares give its square zero and the augmentation.
The canonical row identifications supply the horizontal cycles, boundaries and
homology assertions. If K is zero below b, B^p and H^p are zero below b, so both
end resolutions of the first horseshoe row are zero there. Its middle resolution
is consequently zero. Below b, the second horseshoe row also has zero ends,
so its middle resolution is zero. These choices are intrinsic to the objects,
independent of b, and hence preserve every lower support bound simultaneously.
This includes the all-zero complex, without selecting a least nonzero degree. -/
theorem exists_cartanEilenberg_resolution_all_lower_bounds
    (B : Type u) [Category.{v} B] [Abelian B] [EnoughInjectives B]
    (K : CochainComplex.Plus B) :
    ∃ (I : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
      (a : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K.obj ⟶ I),
      (∀ (b : ℤ), (∀ s : ℤ, s < b → IsZero (K.obj.X s)) →
        ∀ s : ℤ, s < b → IsZero (I.X s)) ∧
      (∀ s : ℤ, QuasiIso (a.f s)) ∧
      (∀ (s : ℤ) (r : ℕ), Injective ((I.X s).X r)) ∧
      (∀ (s : ℤ) (r : ℕ),
        Injective ((I.cycles s).X r) ∧
        Injective ((image (I.d (s - 1) s)).X r) ∧
        Injective ((I.homology s).X r)) ∧
      (∀ s : ℤ,
        QuasiIso (HomologicalComplex.cyclesMap a s) ∧
        QuasiIso (image.map (Arrow.homMk' (a.f (s - 1)) (a.f s) (a.comm (s - 1) s))) ∧
        QuasiIso (HomologicalComplex.homologyMap a s)) := by
  obtain ⟨R, hneg, hqi, hinj⟩ := supported_rows B K.obj
  obtain ⟨z, d, h, hz, hd, hh⟩ := cartanEilenberg_rows_identifications R
  refine ⟨R.complex, R.augmentation, hneg, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (hqi p).1
  · intro p q
    exact (hinj p q).1
  · intro p q
    refine ⟨?_, ?_, ?_⟩
    · exact Injective.of_iso
        ((HomologicalComplex.eval B (ComplexShape.up ℕ) q).mapIso (z p)).symm
        (hinj p q).2.1
    · exact Injective.of_iso
        ((HomologicalComplex.eval B (ComplexShape.up ℕ) q).mapIso (d p)).symm
        (hinj p q).2.2.1
    · exact Injective.of_iso
        ((HomologicalComplex.eval B (ComplexShape.up ℕ) q).mapIso (h p)).symm
        (hinj p q).2.2.2
  · intro p
    refine ⟨?_, ?_, ?_⟩
    · have : QuasiIso
          (HomologicalComplex.cyclesMap R.augmentation p ≫ (z p).hom) := by
        rw [hz p]
        exact (hqi p).2.1
      exact quasiIso_of_comp_right _ (z p).hom
    · have : QuasiIso
          (image.map (Arrow.homMk' (R.augmentation.f (p - 1))
            (R.augmentation.f p) (R.augmentation.comm (p - 1) p)) ≫ (d p).hom) := by
        rw [hd p]
        exact (hqi p).2.2.1
      exact quasiIso_of_comp_right _ (d p).hom
    · have : QuasiIso
          (HomologicalComplex.homologyMap R.augmentation p ≫ (h p).hom) := by
        rw [hh p]
        exact (hqi p).2.2.2
      exact quasiIso_of_comp_right _ (h p).hom


end CategoryTheory
