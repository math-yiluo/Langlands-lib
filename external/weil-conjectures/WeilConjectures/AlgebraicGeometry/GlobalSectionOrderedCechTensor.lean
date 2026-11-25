/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarExtension
import WeilConjectures.AlgebraicGeometry.GlobalSectionTensorBaseChange

/-! # The tensor expansion of a scalar-extended ordered localization complex

Source: Stacks Project, algebraization.tex, Tags 0996 and 099D(d), and Tag 099E,
final paragraph.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped BigOperators
namespace CategoryTheory

attribute [local instance] ringFamilyGlobalExtension_additive

private theorem point_eq (V : (Discrete PUnit.{u + 1})ᵒᵖ) :
    V = op ⟨PUnit.unit⟩ := by
  rcases V with ⟨⟨⟨⟩⟩⟩
  rfl

private noncomputable def pointMap {A : Type u} [CommRing A]
    (M N : RingSiteModules A)
    (g : M.val.obj (op ⟨PUnit.unit⟩) →ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) : M ⟶ N where
  val :=
    { app := fun V ↦ by
        rw [point_eq V]
        exact ModuleCat.ofHom g
      naturality := by
        intro V W a
        obtain rfl := point_eq V
        obtain rfl := point_eq W
        obtain rfl : a = 𝟙 _ := Subsingleton.elim _ _
        ext x
        simp }

private noncomputable def pointIso {A : Type u} [CommRing A]
    {M N : RingSiteModules A}
    (g : M.val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) : M ≅ N where
  hom := pointMap M N g.toLinearMap
  inv := pointMap N M g.symm.toLinearMap
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    obtain rfl := point_eq V
    ext x
    exact g.symm_apply_apply x
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    obtain rfl := point_eq V
    ext x
    exact g.apply_symm_apply x

/-- A complex given by the actual ordered localization coordinates becomes the tensor
Čech complex after scalar extension. This is an isomorphism of augmented complexes,
without a derived-category hypothesis, a replacement complex P, or a derived comparison.
Source: Stacks Project, algebraization.tex, Tags 0996, 099D(d), and 099E, final paragraph.
(auxiliary; not a blueprint node).

Proof: put A = Gamma(O). The actual tensor localization complex over the
one-point A-ring site has ordered coordinates by ringTensorCech_coordinates.
Compose those coordinate equivalences with the inverses of the supplied coordinates
to identify its degree-zero and positive terms with those of K. Lift these linear
isomorphisms to one-point module sheaves; both negative terms are zero. Any two
A-algebra maps out of one localization agree by its universal property, so the
supplied face maps equal those in the tensor coordinates. The first-differential
and alternating-differential equations therefore make the termwise isomorphisms
commute with the differentials. The degree-zero augmentation equations identify
the two augmentations after postcomposition with the single-complex coordinate
isomorphism, which can be cancelled; all other target degrees are zero. Apply the
additive scalar-extension functor to this augmented isomorphism. Compose with
ringFamilyGlobalExtension_tensor_iso, which compares the actual tensor constructions
over A and O, to get the displayed orientation and exactly the specified
augmentation. No derived category, resolution or K-flat hypothesis is used.
The ring tensor coordinates and tensor base change both include empty lists, zero
and repeated generators, and zero rings; the reconstruction uses no exclusions. -/
theorem ringFamilyGlobalExtension_ordered_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (K : CochainComplex (RingSiteModules (ringFamilyGlobalRing O)) ℤ)
    (a : K ⟶ ringComplexSingle (ringFamilyGlobalRing O))
    (e₀ : (K.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[ringFamilyGlobalRing O]
      ringFamilyGlobalRing O)
    (e : ∀ q : ℕ, (K.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩)
      ≃ₗ[ringFamilyGlobalRing O]
        ((t : Fin (q + 1) ↪o Fin r) →
          Localization.Away (∏ i, ringFamilyGlobalList O r f (t i))))
    (l : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)),
      Localization.Away (∏ i, ringFamilyGlobalList O r f (t (Fin.succAboveOrderEmb j i)))
        →ₐ[ringFamilyGlobalRing O]
          Localization.Away (∏ i, ringFamilyGlobalList O r f (t i)))
    (hneg : ∀ n : ℤ, n < 0 → CategoryTheory.Limits.IsZero (K.X n))
    (hd₀ : ∀ (x : (K.X 0).val.obj (op ⟨PUnit.unit⟩)) (t : Fin 1 ↪o Fin r),
      e 0 ((K.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
        algebraMap (ringFamilyGlobalRing O)
          (Localization.Away (∏ i, ringFamilyGlobalList O r f (t i))) (e₀ x))
    (hd : ∀ (q : ℕ) (x : (K.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩))
      (t : Fin (q + 2) ↪o Fin r),
      e (q + 1) ((K.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app (op ⟨PUnit.unit⟩) x) t =
        ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
          l q t j (e q x ((Fin.succAboveOrderEmb j).trans t)))
    (ha : ∀ x : (K.X 0).val.obj (op ⟨PUnit.unit⟩),
      ringComplexAugmentationValue a x = e₀ x) :
    ∃ e : (ringedExtendedCech O r f).1 ≅ ringFamilyGlobalExtensionComplex O K,
      e.hom ≫ ringFamilyGlobalExtensionAugmentation O a = (ringedExtendedCech O r f).2 := by
  classical
  let A := ringFamilyGlobalRing O
  let g := ringFamilyGlobalList O r f
  let L := (ringTensorCech A r g).1
  let b := (ringTensorCech A r g).2
  obtain ⟨e₀', e', l', hneg', hd₀', hd', ha'⟩ := ringTensorCech_coordinates A r g
  have hl (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)) :
      l' q t j = l q t j := by
    apply IsLocalization.algHom_ext
      (Submonoid.powers (∏ i, g (t (Fin.succAboveOrderEmb j i))))
    ext
  let E : ∀ n : ℤ, L.X n ≅ K.X n := fun n ↦ by
    cases n with
    | ofNat n =>
      cases n with
      | zero => exact pointIso (e₀'.trans e₀.symm)
      | succ q => exact pointIso ((e' q).trans (e q).symm)
    | negSucc q =>
      exact (hneg' _ (by omega)).isoZero ≪≫ (hneg _ (by omega)).isoZero.symm
  have hE : ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      (E i).hom ≫ K.d i j = L.d i j ≫ (E j).hom := by
    intro i j hij
    have hj : j = i + 1 := hij.symm
    subst j
    by_cases hi : i < 0
    · exact (hneg' i hi).eq_of_src _ _
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hi)
      cases n with
      | zero =>
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        obtain rfl := point_eq V
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply (e 0).injective
        funext t
        change e 0 ((K.d 0 1).val.app _ (e₀.symm (e₀' x))) t =
          e 0 ((e 0).symm (e' 0 ((L.d 0 1).val.app _ x))) t
        rw [hd₀]
        simp only [LinearEquiv.apply_symm_apply]
        exact (hd₀' x t).symm
      | succ q =>
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        obtain rfl := point_eq V
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply (e (q + 1)).injective
        funext t
        change e (q + 1) ((K.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app _
            ((e q).symm (e' q x))) t =
          e (q + 1) ((e (q + 1)).symm
            (e' (q + 1) ((L.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app _ x))) t
        rw [hd]
        simp only [LinearEquiv.apply_symm_apply]
        simpa only [hl] using (hd' q x t).symm
  let α : L ≅ K := HomologicalComplex.Hom.isoOfComponents E hE
  have hα : α.hom ≫ a = b := by
    apply HomologicalComplex.hom_ext
    intro n
    by_cases hn : n = 0
    · subst n
      apply (cancel_mono
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit A)).hom).1
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro V
      obtain rfl := point_eq V
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ringComplexAugmentationValue a (e₀.symm (e₀' x)) =
        ringComplexAugmentationValue b x
      rw [ha, ha', LinearEquiv.apply_symm_apply]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (ringComplexUnit A) n hn).eq_of_tgt _ _
  obtain ⟨β, hβ⟩ := ringFamilyGlobalExtension_tensor_iso O r f
  let T := (ringFamilyGlobalExtension O).mapHomologicalComplex (.up ℤ)
  refine ⟨β ≪≫ T.mapIso α, ?_⟩
  change (β.hom ≫ T.map α.hom) ≫ (T.map a ≫ _) = _
  rw [Category.assoc, ← Category.assoc (T.map α.hom), ← Functor.map_comp, hα]
  exact hβ

end CategoryTheory
