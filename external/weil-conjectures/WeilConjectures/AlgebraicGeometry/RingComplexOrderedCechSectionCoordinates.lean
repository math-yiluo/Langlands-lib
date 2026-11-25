/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexOrderedCechConstruction

/-! # Principal-localization coordinates before taking the Čech mapping fibre

Source: Stacks Project, Tag 099D(d), and Cohomology, Tags 01EQ and 01FJ.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
namespace AlgebraicGeometry

noncomputable section

private theorem principalIntersection (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (q : ℕ) (t : Fin (q + 1) ↪o Fin r) :
    (ringComplexOpen A I).ι ''ᵁ
        alternatingCechIntersection (ringComplexPrincipalCover A I f) t =
      PrimeSpectrum.basicOpen (∏ i, f (t i)) := by
  classical
  have hmem (i : Fin r) : f i ∈ I := by
    rw [← hf]
    exact Ideal.subset_span (Set.mem_range_self i)
  ext p
  change (∃ x : ringComplexOpen A I,
    x ∈ alternatingCechIntersection (ringComplexPrincipalCover A I f) t ∧ x.val = p) ↔
      ∏ i, f (t i) ∉ p.asIdeal
  have hprod : (∏ i, f (t i) ∉ p.asIdeal) ↔ ∀ i, f (t i) ∉ p.asIdeal := by
    simp [Ideal.IsPrime.prod_mem_iff]
  rw [hprod]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact (iInf_le (fun k ↦ ringComplexPrincipalCover A I f (t k)) i) hx
  · intro hp
    have hU : p ∈ ringComplexOpen A I := by
      change ¬ I ≤ p.asIdeal
      intro h
      exact hp 0 (h (hmem (t 0)))
    refine ⟨⟨p, hU⟩, ?_, rfl⟩
    change (⟨p, hU⟩ : ringComplexOpen A I) ∈
      (↑(⨅ k, ringComplexPrincipalCover A I f (t k)) : Set (ringComplexOpen A I))
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hp

private def principalSections (A : CommRingCat.{u}) (I : Ideal A)
    (W : (ringComplexOpen A I).toScheme.Opens) (s : A)
    (h : (ringComplexOpen A I).ι ''ᵁ W = PrimeSpectrum.basicOpen s) :
    Γ((ringComplexOpen A I).toScheme, W) ≃+* Localization.Away s :=
  (CategoryTheory.Iso.commRingCatIsoToRingEquiv
    ((Spec A).presheaf.mapIso (eqToIso h.symm).op)).trans
      (IsLocalization.algEquiv (Submonoid.powers s)
        Γ(Spec A, PrimeSpectrum.basicOpen s) (Localization.Away s)).toRingEquiv

private theorem principalSections_constant (A : CommRingCat.{u}) (I : Ideal A)
    (W : (ringComplexOpen A I).toScheme.Opens) (s : A)
    (h : (ringComplexOpen A I).ι ''ᵁ W = PrimeSpectrum.basicOpen s) (a : A) :
    principalSections A I W s h
      (((ringComplexOpen A I).toScheme.presheaf.map (homOfLE le_top).op).hom
        (ringComplexOpenRingMap A I a)) =
      algebraMap A (Localization.Away s) a := by
  have hc : ((ringComplexOpen A I).toScheme.presheaf.map (homOfLE le_top).op).hom
      (ringComplexOpenRingMap A I a) =
        algebraMap A Γ(Spec A, (ringComplexOpen A I).ι ''ᵁ W) a := by
    rfl
  rw [hc]
  change (IsLocalization.algEquiv (Submonoid.powers s)
    Γ(Spec A, PrimeSpectrum.basicOpen s) (Localization.Away s))
      (((Spec A).presheaf.map (eqToHom h.symm).op).hom (algebraMap A _ a)) = _
  have hm : ((Spec A).presheaf.map (eqToHom h.symm).op).hom (algebraMap A _ a) =
      algebraMap A Γ(Spec A, PrimeSpectrum.basicOpen s) a := by
    rfl
  rw [hm, AlgEquiv.commutes]

private abbrev sectionPresheaf (A : CommRingCat.{u}) (I : Ideal A) :=
  (alternatingCechModulePresheaf (X := (ringComplexOpen A I).toScheme)).obj
    (SheafOfModules.unit (moduleRings (ringComplexOpen A I).toScheme.toRingedSpace))

private abbrev sectionComplex (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) :=
  alternatingCechComplex (ringComplexPrincipalCover A I f) (sectionPresheaf A I)

private def termCoordinates (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I) (q : ℕ) :
    ((ModuleCat.restrictScalars (ringComplexOpenRingMap A I)).obj
      ((sectionComplex A I f).X q)) ≃ₗ[A]
        ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i))) where
  toFun x t := principalSections A I _ _ (principalIntersection A I f hf q t) (x t)
  invFun y t := (principalSections A I _ _ (principalIntersection A I f hf q t)).symm (y t)
  left_inv x := by funext t; exact RingEquiv.symm_apply_apply _ _
  right_inv y := by funext t; exact RingEquiv.apply_symm_apply _ _
  map_add' x y := by funext t; exact map_add _ _ _
  map_smul' a x := by
    funext t
    change principalSections A I _ _ (principalIntersection A I f hf q t)
      ((((ringComplexOpen A I).toScheme.presheaf.map
        (homOfLE (le_top (a := alternatingCechIntersection
          (ringComplexPrincipalCover A I f) t))).op).hom
        (ringComplexOpenRingMap A I a)) *
          (show Γ((ringComplexOpen A I).toScheme,
            alternatingCechIntersection (ringComplexPrincipalCover A I f) t) from x t)) = _
    rw [map_mul, principalSections_constant]
    simp only [RingHom.id_apply, Pi.smul_apply, Algebra.smul_def]

private def faceCoordinates (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)) :
    Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i))) →ₐ[A]
      Localization.Away (∏ i, f (t i)) where
  toRingHom := (principalSections A I _ _
    (principalIntersection A I f hf (q + 1) t)).toRingHom.comp
      (((ringComplexOpen A I).toScheme.presheaf.map
        (homOfLE (alternatingCechIntersection_face_le
          (ringComplexPrincipalCover A I f) q t j)).op).hom.comp
        (principalSections A I _ _
          (principalIntersection A I f hf q ((Fin.succAboveOrderEmb j).trans t))).symm.toRingHom)
  commutes' a := by
    change principalSections A I _ _ (principalIntersection A I f hf (q + 1) t)
      (((ringComplexOpen A I).toScheme.presheaf.map
        (homOfLE (alternatingCechIntersection_face_le
          (ringComplexPrincipalCover A I f) q t j)).op).hom
        ((principalSections A I _ _
          (principalIntersection A I f hf q ((Fin.succAboveOrderEmb j).trans t))).symm
            (algebraMap A _ a))) = _
    rw [← principalSections_constant A I _ _
      (principalIntersection A I f hf q ((Fin.succAboveOrderEmb j).trans t)) a,
      RingEquiv.symm_apply_apply]
    have hres : ((ringComplexOpen A I).toScheme.presheaf.map
        (homOfLE (alternatingCechIntersection_face_le
          (ringComplexPrincipalCover A I f) q t j)).op).hom
        (((ringComplexOpen A I).toScheme.presheaf.map (homOfLE le_top).op).hom
          (ringComplexOpenRingMap A I a)) =
        ((ringComplexOpen A I).toScheme.presheaf.map (homOfLE le_top).op).hom
          (ringComplexOpenRingMap A I a) := by
      change (((ringComplexOpen A I).toScheme.presheaf.map _ ≫
        (ringComplexOpen A I).toScheme.presheaf.map _).hom (ringComplexOpenRingMap A I a)) = _
      rw [← Functor.map_comp]
      rfl
    rw [hres, principalSections_constant]

private def sectionsTermIso (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (q : ℕ) :
    (ringComplexOrderedCechSections A I f).X (q : ℤ) ≅
      (ringComplexSectionScalars A I).obj ((sectionComplex A I f).X q) :=
  (ringComplexSectionScalars A I).mapIso
    ((sectionComplex A I f).extendXIso ComplexShape.embeddingUpNat rfl)

private theorem sectionsTerm_d (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (q : ℕ) :
    (ringComplexOrderedCechSections A I f).d (q : ℤ) ((q : ℤ) + 1) ≫
        (sectionsTermIso A I f (q + 1)).hom =
      (sectionsTermIso A I f q).hom ≫
        (ringComplexSectionScalars A I).map ((sectionComplex A I f).d q (q + 1)) := by
  change (ringComplexSectionScalars A I).map
      (((sectionComplex A I f).extend ComplexShape.embeddingUpNat).d _ _) ≫
      (ringComplexSectionScalars A I).map _ =
    (ringComplexSectionScalars A I).map _ ≫ (ringComplexSectionScalars A I).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  erw [HomologicalComplex.extend_d_eq (sectionComplex A I f)
    ComplexShape.embeddingUpNat (i := q) (j := q + 1) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem sectionsTerm_first (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) :
    ringComplexOrderedCechFirst A I f ≫ (sectionsTermIso A I f 0).hom =
      ringComplexStructureRestriction A I ≫ (ringComplexSectionScalars A I).map
        (alternatingCechPresheafZero (ringComplexPrincipalCover A I f) (sectionPresheaf A I)) :=
by
  unfold ringComplexOrderedCechFirst alternatingCechZero sectionsTermIso
  simp only [Functor.mapIso_hom, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Sections on ordered intersections, before adjoining the augmentation term, have
localization coordinates compatible with restriction and with the map from A.
Source: Stacks Project, Tag 099D(d), and Cohomology, Tags 01EQ and 01FJ.
(auxiliary; not a blueprint node)

Proof: each f_i belongs to I, so D(f_i) is contained in Spec A minus V(I).
Each ordered intersection in the complement maps isomorphically onto D(product f_i).
The open-immersion section isomorphism followed by the
principal-open localization isomorphism identifies its structure-ring sections with
A localized at this product. These are A-algebra isomorphisms for the scalar map
used in ringComplexSectionScalars. Take their product in each degree, and compose
with the extension-by-zero term isomorphism from natural to integer Čech degrees.
Transport each face restriction through the two algebra isomorphisms to obtain l;
it preserves the structural map from A. The definition of the ordered differential
is the signed sum of these face restrictions. Linearity of the product coordinates
therefore proves the differential equation. The augmentation is restriction of the
structural map A to each singleton open, which proves the first equation. These
arguments also apply to empty intersections, zero or repeated generators, and the
zero ring, since the structure ring on an empty open and its localization at zero
are both the zero ring. No cone calculation or degree shift is part of this claim. -/
theorem ringComplexOrderedCech_sections_coordinates (A : CommRingCat.{u}) (I : Ideal A)
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = I) :
    let L := ringComplexOrderedCechSections A I f
    ∃ (e : ∀ q : ℕ, (L.X (q : ℤ)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
            ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i))))
          (l : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)),
            Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i))) →ₐ[A]
              Localization.Away (∏ i, f (t i))),
          (∀ (x : A) (t : Fin 1 ↪o Fin r),
            e 0 ((ringComplexOrderedCechFirst A I f).val.app (op ⟨PUnit.unit⟩) x) t =
              algebraMap A (Localization.Away (∏ i, f (t i))) x) ∧
          (∀ (q : ℕ) (x : (L.X (q : ℤ)).val.obj (op ⟨PUnit.unit⟩))
            (t : Fin (q + 2) ↪o Fin r),
            e (q + 1) ((L.d (q : ℤ) ((q : ℤ) + 1)).val.app
              (op ⟨PUnit.unit⟩) x) t =
              ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
                l q t j (e q x ((Fin.succAboveOrderEmb j).trans t))) := by
  classical
  dsimp only
  let ev : RingSiteModules A ⥤ ModuleCat.{u} A := SheafOfModules.evaluation
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf.{u} A)) (op ⟨PUnit.unit⟩)
  let J (q : ℕ) : ((ringComplexOrderedCechSections A I f).X (q : ℤ)).val.obj
      (op ⟨PUnit.unit⟩) ≃ₗ[A]
      ((ModuleCat.restrictScalars (ringComplexOpenRingMap A I)).obj
        ((sectionComplex A I f).X q)) :=
    (ev.mapIso (sectionsTermIso A I f q)).toLinearEquiv
  let e (q : ℕ) := (J q).trans (termCoordinates A I f hf q)
  refine ⟨e, faceCoordinates A I f hf, ?_, ?_⟩
  · intro x t
    have h := congrArg (fun z ↦ z.val.app (op ⟨PUnit.unit⟩) x t)
      (sectionsTerm_first A I f)
    change J 0 ((ringComplexOrderedCechFirst A I f).val.app (op ⟨PUnit.unit⟩) x) t =
      ((ringComplexOpen A I).toScheme.presheaf.map (homOfLE le_top).op).hom
        (ringComplexOpenRingMap A I x) at h
    change principalSections A I _ _ (principalIntersection A I f hf 0 t)
      (J 0 ((ringComplexOrderedCechFirst A I f).val.app (op ⟨PUnit.unit⟩) x) t) = _
    rw [h]
    exact principalSections_constant A I _ _ (principalIntersection A I f hf 0 t) x
  · intro q x t
    have h := congrArg (fun z ↦ z.val.app (op ⟨PUnit.unit⟩) x)
      (sectionsTerm_d A I f q)
    change J (q + 1) (((ringComplexOrderedCechSections A I f).d
        (q : ℤ) ((q : ℤ) + 1)).val.app (op ⟨PUnit.unit⟩) x) =
      ((sectionComplex A I f).d q (q + 1)).hom (J q x) at h
    change termCoordinates A I f hf (q + 1) (J (q + 1) _) t = _
    rw [h]
    have hd' : (sectionComplex A I f).d q (q + 1) =
        alternatingCechDifferential (ringComplexPrincipalCover A I f) (sectionPresheaf A I) q :=
      CochainComplex.of_d _ _ q
    erw [hd']
    change principalSections A I _ _ (principalIntersection A I f hf (q + 1) t)
      ((∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
        ((sectionPresheaf A I).map (homOfLE (alternatingCechIntersection_face_le
          (ringComplexPrincipalCover A I f) q t j)).op).hom.comp
          (LinearMap.proj ((Fin.succAboveOrderEmb j).trans t)))
            (show ∀ s : Fin (q + 1) ↪o Fin r,
              (sectionPresheaf A I).obj
                (op (alternatingCechIntersection (ringComplexPrincipalCover A I f) s))
              from J q x)) = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul]
    congr 1
    change principalSections A I _ _ (principalIntersection A I f hf (q + 1) t)
      (((ringComplexOpen A I).toScheme.presheaf.map
        (homOfLE (alternatingCechIntersection_face_le
          (ringComplexPrincipalCover A I f) q t j)).op).hom
        (J q x ((Fin.succAboveOrderEmb j).trans t))) =
      principalSections A I _ _ (principalIntersection A I f hf (q + 1) t)
        (((ringComplexOpen A I).toScheme.presheaf.map
          (homOfLE (alternatingCechIntersection_face_le
            (ringComplexPrincipalCover A I f) q t j)).op).hom
          ((principalSections A I _ _
            (principalIntersection A I f hf q ((Fin.succAboveOrderEmb j).trans t))).symm
              (principalSections A I _ _
                (principalIntersection A I f hf q ((Fin.succAboveOrderEmb j).trans t))
                  (J q x ((Fin.succAboveOrderEmb j).trans t)))))
    rw [RingEquiv.symm_apply_apply]

end
end AlgebraicGeometry
