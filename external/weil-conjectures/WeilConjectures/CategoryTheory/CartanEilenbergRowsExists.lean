/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergRows
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.CategoryTheory.CartanEilenbergObjectResolutionRows
import WeilConjectures.CategoryTheory.Abelian.HorseshoePrescribedResolutions
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-! # Injective resolutions of the alternating exact rows

Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--4
(blueprint: lem-sp-cartan-eilenberg-rows-exists).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

/-- The alternating cycle/term/boundary and boundary/cycle/homology rows admit
compatible resolutions. This constructs rows, not their horizontal complex.

Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--4,
using the prescribed-end version of the horseshoe lemma, Tag 013T
(blueprint: lem-sp-cartan-eilenberg-rows-exists).

Proof:
1. Write the two short exact sequences Z^p(K) -> K^p -> B^(p+1)(K) and
   B^p(K) -> Z^p(K) -> H^p(K). Start with an injective resolution of Z^0(K).
2. Choose a resolution of B^1(K). The prescribed horseshoe lemma produces
   a resolution of K^0 and a short exact row with the chosen outer columns.
   Choose a resolution of H^1(K); apply it again to obtain a resolution of
   Z^1(K), reusing the preceding resolution of B^1(K). Iterate on natural
   degrees, alternating these two applications. All row maps commute with
   augmentations and each chosen column has injective terms and is a resolution.
3. In negative horizontal degrees take zero complexes. Take the degree-zero
   boundary column to be zero, and identify H^0(K) with Z^0(K). The vanishing
   hypothesis makes these choices compatible with both rows at the boundary.
4. Apply the exact single-degree-zero functor to the source rows to identify
   their cycles, images and homology with those of the prolonged complex S.
   Transfer the object augmentations along these canonical isomorphisms.
   The row squares give commZ, commD and commH. Factoring d_K through its image
   and cycles gives comm. Exactness of the rows in the category of vertical
   complexes follows from their degreewise short exactness. -/
theorem exists_cartanEilenberg_rows
    (B : Type u) [Category.{v} B] [Abelian B] [EnoughInjectives B]
    (K : CochainComplex B ℤ) (hK : ∀ p : ℤ, p < 0 → IsZero (K.X p)) :
    let S := ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    ∃ R : CartanEilenbergRows S,
      (∀ p : ℤ, p < 0 → IsZero (R.A p)) ∧
      (∀ p : ℤ, QuasiIso (R.jA p) ∧ QuasiIso (R.jZ p) ∧
        QuasiIso (R.jD p) ∧ QuasiIso (R.jH p)) ∧
      (∀ (p : ℤ) (q : ℕ), Injective ((R.A p).X q) ∧
        Injective ((R.Z p).X q) ∧ Injective ((R.D p).X q) ∧
        Injective ((R.H p).X q)) := by
  let F := CochainComplex.single₀ B
  let S := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  classical
  obtain ⟨IZ, ID, IH, w, x, hzneg, hdneg, ⟨hwx, hex₂⟩, hbw, hx⟩ :=
    exists_cartanEilenberg_object_resolution_rows B K hK
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
  have hneg (p : ℤ) (hp : p < 0) : IsZero (IA p).cocomplex := by
    have hi : IsIso (u p) := (hex₁ p).isIso_f_iff.mpr (hdneg (p + 1) (by omega))
    exact IsZero.of_iso (hzneg p hp) (asIso (u p)).symm
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

end CategoryTheory
