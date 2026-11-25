/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedExteriorProductNaturality
public import WeilConjectures.CategoryTheory.Triangulated.BinaryBiproductCone

/-!
# Unique existence of the supported exterior product from support-acyclic resolutions

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
def-pur-supported-exterior-product.md (blueprint: proposition-purity-vector-bundles).

Suppose that every K-flat complex with bounded below cohomology admits a quasi-isomorphism to
a K-flat complex on which the support unit is invertible. Then the resolution normalization
`IsResolutionSupportedExteriorProduct` determines a unique morphism. Uniqueness: on such
representatives of both inputs the tensor product of the two units is invertible.
Existence: define the morphism on one such pair of representatives. Two such representatives
are connected by a K-flat homotopy pushout of a K-flat roof, followed by a further
resolution, and the normalization transfers along quasi-isomorphisms of K-flat complexes
(`resolutionSupportedExteriorPairing_transfer`). An arbitrary K-flat representative maps to
such a representative.

## Main statements

- `exists_kFlat_quasiIso_pushout`: K-flat homotopy pushouts of quasi-isomorphisms.
- `exists_common_kFlat_supportResolution`: two K-flat representatives map to a common
  K-flat representative on which the support unit is invertible.
- `existsUnique_isResolutionSupportedExteriorProduct_of_resolutions`: unique existence of
  the supported exterior product.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasSmallSiteSheafify C]

omit [Abelian.HasFunctorialFlatResolution C] [HasSmallSiteSheafify C] in
/-- A homotopy pushout of a span of quasi-isomorphisms between K-flat complexes: the mapping
cone of `R ⟶ P ⊞ P'` receives quasi-isomorphisms from `P` and `P'` which agree on `R` in the
derived category, and it is K-flat. -/
theorem exists_kFlat_quasiIso_pushout {T : Scheme.{u}}
    {R P P' : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ} (s : R ⟶ P) (a : R ⟶ P')
    [IsIso (DerivedCategory.Q.map s)] [IsIso (DerivedCategory.Q.map a)]
    (hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat R)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P') :
    ∃ (H : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ) (b : P ⟶ H) (c : P' ⟶ H),
      IsIso (DerivedCategory.Q.map b) ∧ IsIso (DerivedCategory.Q.map c) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat H ∧
      DerivedCategory.Q.map s ≫ DerivedCategory.Q.map b =
        DerivedCategory.Q.map a ≫ DerivedCategory.Q.map c := by
  let φ : R ⟶ P ⊞ P' := biprod.lift s (-a)
  let ψ := CochainComplex.mappingCone.inr φ
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := Sheaf T.smallEtaleTopology C)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let e := DerivedCategory.Q.mapBiprod P P'
  have hT : Pretriangulated.Triangle.mk
      (biprod.lift (DerivedCategory.Q.map s) (DerivedCategory.Q.map (-a)))
      (e.inv ≫ DerivedCategory.Q.map ψ)
      (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle φ)).mor₃ ∈
        distTriang _ := by
    refine Pretriangulated.isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished φ) _
      (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_)
    · simp only [e, φ, Pretriangulated.Triangle.mk_mor₁, Iso.symm_hom, Iso.refl_hom,
        Category.id_comp, Functor.mapBiprod_inv, biprod.lift_desc]
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add]
      exact congrArg DerivedCategory.Q.map biprod.lift_eq.symm
    · simp only [Pretriangulated.Triangle.mk_mor₂, Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      rfl
    · simp
  obtain ⟨θ, h₁, h₂⟩ := Pretriangulated.exists_iso_of_distTriang_biprod_lift _ _ _ _ hT
  have hinl : biprod.inl ≫ e.inv = DerivedCategory.Q.map (biprod.inl : P ⟶ P ⊞ P') := by
    simp [e]
  have hinr : biprod.inr ≫ e.inv = DerivedCategory.Q.map (biprod.inr : P' ⟶ P ⊞ P') := by
    simp [e]
  have hc : DerivedCategory.Q.map (biprod.inr ≫ ψ) ≫ θ.hom = 𝟙 _ := by
    rw [Functor.map_comp, ← hinr, Category.assoc, Category.assoc, ← Category.assoc e.inv]
    exact h₁
  have hb : DerivedCategory.Q.map (biprod.inl ≫ ψ) ≫ θ.hom =
      inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map a := by
    rw [Functor.map_comp, ← hinl, Category.assoc, Category.assoc, ← Category.assoc e.inv, h₂,
      Functor.map_neg, Preadditive.comp_neg, neg_neg]
  refine ⟨CochainComplex.mappingCone φ, biprod.inl ≫ ψ, biprod.inr ≫ ψ, ?_, ?_, ?_, ?_⟩
  · have : IsIso (DerivedCategory.Q.map (biprod.inl ≫ ψ) ≫ θ.hom) := by
      rw [hb]
      infer_instance
    exact IsIso.of_isIso_comp_right _ θ.hom
  · have : IsIso (DerivedCategory.Q.map (biprod.inr ≫ ψ) ≫ θ.hom) := by
      rw [hc]
      infer_instance
    exact IsIso.of_isIso_comp_right _ θ.hom
  · have h₃ := (HomotopyCategory.quasiIso (Sheaf T.smallEtaleTopology C)
      (.up ℤ)).kFlat.ext_of_isTriangulatedClosed₃
      _ (HomotopyCategory.mappingCone_triangleh_distinguished φ)
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR)
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 (CochainComplex.kFlat_biprod hP hP'))
    exact (HomotopyCategory.kFlat_quotient_obj_iff _).1 h₃
  · rw [← cancel_mono θ.hom, Category.assoc, Category.assoc, hb, hc, IsIso.hom_inv_id_assoc,
      Category.comp_id]

section Resolution

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

omit [HasSmallSiteSheafify C] in
/-- Every object of the derived category with bounded below cohomology has a K-flat
representative on which the support unit is invertible, provided K-flat complexes with
bounded below cohomology admit quasi-isomorphisms to such representatives. -/
theorem exists_kFlat_supportResolution_iso
    (hres : ∀ (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P → ∀ n : ℤ,
        (DerivedCategory.Q.obj P).IsGE n →
      ∃ (I : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) (φ : P ⟶ I), QuasiIso φ ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat I ∧
        IsIso (exteriorSupportResolutionUnit C i I))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C)) (n : ℤ) (hn : K.IsGE n) :
    ∃ (I : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) (_ : DerivedCategory.Q.obj I ≅ K),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat I ∧
        IsIso (exteriorSupportResolutionUnit C i I) := by
  obtain ⟨P, π, hπ, -, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat
    (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map π) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := π)).2 hπ
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have : (DerivedCategory.Q.obj P).IsGE n := DerivedCategory.TStructure.t.isGE_of_iso e.symm n
  obtain ⟨I, φ, hφ, hI, hu⟩ := hres P hP n this
  have : IsIso (DerivedCategory.Q.map φ) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := φ)).2 hφ
  exact ⟨I, (asIso (DerivedCategory.Q.map φ)).symm ≪≫ e, hI, hu⟩

omit [HasSmallSiteSheafify C] in
/-- Two K-flat representatives of the same object with bounded below cohomology admit
quasi-isomorphisms to a common K-flat complex on which the support unit is invertible,
compatibly with the given identification, provided K-flat complexes with bounded below
cohomology admit quasi-isomorphisms to such complexes. -/
theorem exists_common_kFlat_supportResolution
    (hres : ∀ (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P → ∀ n : ℤ,
        (DerivedCategory.Q.obj P).IsGE n →
      ∃ (I : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) (φ : P ⟶ I), QuasiIso φ ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat I ∧
        IsIso (exteriorSupportResolutionUnit C i I))
    {P P' : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ}
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P')
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') (n : ℤ)
    (hn : (DerivedCategory.Q.obj P).IsGE n) :
    ∃ (G : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) (b : P ⟶ G) (c : P' ⟶ G),
      IsIso (DerivedCategory.Q.map b) ∧ IsIso (DerivedCategory.Q.map c) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat G ∧
      IsIso (exteriorSupportResolutionUnit C i G) ∧
      DerivedCategory.Q.map b = e.hom ≫ DerivedCategory.Q.map c := by
  obtain ⟨X', s', hs', g', hfac⟩ := DerivedCategory.right_fac e.hom
  obtain ⟨R, π, hπ, -, hR⟩ := CochainComplex.exists_quasiIso_flat_kFlat X'
  have : IsIso (DerivedCategory.Q.map π) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := π)).2 hπ
  have hga : DerivedCategory.Q.map g' = DerivedCategory.Q.map s' ≫ e.hom := by
    rw [hfac, IsIso.hom_inv_id_assoc]
  have : IsIso (DerivedCategory.Q.map (π ≫ s')) := by
    rw [Functor.map_comp]
    infer_instance
  have : IsIso (DerivedCategory.Q.map (π ≫ g')) := by
    rw [Functor.map_comp, hga]
    infer_instance
  obtain ⟨H, b, c, hb, hc, hH, hcomm⟩ :=
    exists_kFlat_quasiIso_pushout C (π ≫ s') (π ≫ g') hR hP hP'
  have : (DerivedCategory.Q.obj H).IsGE n :=
    DerivedCategory.TStructure.t.isGE_of_iso (asIso (DerivedCategory.Q.map b)) n
  obtain ⟨G, t, ht, hG, hu⟩ := hres H hH n this
  have : IsIso (DerivedCategory.Q.map t) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := t)).2 ht
  have hbc : DerivedCategory.Q.map b = e.hom ≫ DerivedCategory.Q.map c := by
    rw [← cancel_epi (DerivedCategory.Q.map (π ≫ s')), hcomm]
    simp only [Functor.map_comp, hga, Category.assoc]
  refine ⟨G, b ≫ t, c ≫ t, ?_, ?_, hG, hu, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp, Functor.map_comp, hbc, Category.assoc]

end Resolution

variable {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
  [IsClosedImmersion i] [IsClosedImmersion j]

/-- The supported exterior product exists uniquely, provided K-flat complexes with bounded
below cohomology on both factors admit quasi-isomorphisms to K-flat complexes on which the
support units are invertible. -/
theorem existsUnique_isResolutionSupportedExteriorProduct_of_resolutions
    (hresi : ∀ (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P → ∀ n : ℤ,
        (DerivedCategory.Q.obj P).IsGE n →
      ∃ (I : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) (φ : P ⟶ I), QuasiIso φ ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat I ∧
        IsIso (exteriorSupportResolutionUnit C i I))
    (hresj : ∀ (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q → ∀ n : ℤ,
        (DerivedCategory.Q.obj Q).IsGE n →
      ∃ (J : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) (ψ : Q ⟶ J), QuasiIso ψ ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat J ∧
        IsIso (exteriorSupportResolutionUnit C j J))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (hK : ∃ n : ℤ, K.IsGE n) (hL : ∃ n : ℤ, L.IsGE n) :
    ∃! κ : (rightDerivedSectionsWithSupport C i).obj K ⊗
        (rightDerivedSectionsWithSupport C j).obj L ⟶
      (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).obj
        (externalProduct C f g K L),
      IsResolutionSupportedExteriorProduct C f g i j K L κ := by
  obtain ⟨n, hn⟩ := hK
  obtain ⟨m, hm⟩ := hL
  obtain ⟨I₀, eI₀, hI₀, huI₀⟩ := exists_kFlat_supportResolution_iso C i hresi K n hn
  obtain ⟨J₀, eJ₀, hJ₀, huJ₀⟩ := exists_kFlat_supportResolution_iso C j hresj L m hm
  let A₀ := tensorHom
    (exteriorSupportResolutionUnit C i I₀ ≫ (rightDerivedSectionsWithSupport C i).map eI₀.hom)
    (exteriorSupportResolutionUnit C j J₀ ≫ (rightDerivedSectionsWithSupport C j).map eJ₀.hom)
  let Ψ₀ := resolutionSupportedExteriorPairing C f g i j I₀ J₀ hI₀ hJ₀ ≫
    (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).map
      (derivedTensorHom C ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map eI₀.hom)
        ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map eJ₀.hom))
  have hA₀ : A₀ ≫ inv A₀ ≫ Ψ₀ = Ψ₀ := IsIso.hom_inv_id_assoc _ _
  refine ⟨inv A₀ ≫ Ψ₀, (isResolutionSupportedExteriorProduct_iff C f g i j K L _).2 ?_,
    fun κ hκ ↦ ?_⟩
  · intro P Q hP hQ eP eQ
    -- resolve `P` and `Q` by complexes with invertible support units
    have : (DerivedCategory.Q.obj P).IsGE n := DerivedCategory.TStructure.t.isGE_of_iso eP.symm n
    obtain ⟨I, φ, hφ, hI, -⟩ := hresi P hP n this
    have : (DerivedCategory.Q.obj Q).IsGE m := DerivedCategory.TStructure.t.isGE_of_iso eQ.symm m
    obtain ⟨J, ψ, hψ, hJ, -⟩ := hresj Q hQ m this
    have : IsIso (DerivedCategory.Q.map φ) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := φ)).2 hφ
    have : IsIso (DerivedCategory.Q.map ψ) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := ψ)).2 hψ
    let eI := (asIso (DerivedCategory.Q.map φ)).symm ≪≫ eP
    let eJ := (asIso (DerivedCategory.Q.map ψ)).symm ≪≫ eQ
    -- common resolutions of `I, I₀` and of `J, J₀`
    have : (DerivedCategory.Q.obj I).IsGE n := DerivedCategory.TStructure.t.isGE_of_iso eI.symm n
    obtain ⟨G, b, c, hb, hc, hG, huG, hbc⟩ :=
      exists_common_kFlat_supportResolution C i hresi hI hI₀ (eI ≪≫ eI₀.symm) n this
    have : (DerivedCategory.Q.obj J).IsGE m := DerivedCategory.TStructure.t.isGE_of_iso eJ.symm m
    obtain ⟨G', b', c', hb', hc', hG', huG', hbc'⟩ :=
      exists_common_kFlat_supportResolution C j hresj hJ hJ₀ (eJ ≪≫ eJ₀.symm) m this
    let eG := (asIso (DerivedCategory.Q.map c)).symm ≪≫ eI₀
    let eG' := (asIso (DerivedCategory.Q.map c')).symm ≪≫ eJ₀
    let A := tensorHom
      (exteriorSupportResolutionUnit C i G ≫ (rightDerivedSectionsWithSupport C i).map eG.hom)
      (exteriorSupportResolutionUnit C j G' ≫ (rightDerivedSectionsWithSupport C j).map eG'.hom)
    let κ := inv A ≫ resolutionSupportedExteriorPairing C f g i j G G' hG hG' ≫
      (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).map
        (derivedTensorHom C ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map eG.hom)
          ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map eG'.hom))
    have hκG : A ≫ κ = _ := IsIso.hom_inv_id_assoc _ _
    have hcG : DerivedCategory.Q.map c ≫ eG.hom = eI₀.hom := by simp [eG]
    have hcG' : DerivedCategory.Q.map c' ≫ eG'.hom = eJ₀.hom := by simp [eG']
    have hbG : DerivedCategory.Q.map b ≫ eG.hom = eI.hom := by simp [eG, hbc]
    have hbG' : DerivedCategory.Q.map b' ≫ eG'.hom = eJ.hom := by simp [eG', hbc']
    have hφI : DerivedCategory.Q.map φ ≫ eI.hom = eP.hom := by simp [eI]
    have hψJ : DerivedCategory.Q.map ψ ≫ eJ.hom = eQ.hom := by simp [eJ]
    have h₀ := resolutionSupportedExteriorPairing_transfer C f g i j c c' hI₀ hG hJ₀ hG'
      _ _ _ _ hcG hcG' κ hκG
    have hκ : inv A₀ ≫ Ψ₀ = κ := by
      rw [← cancel_epi A₀, hA₀]
      exact h₀.symm
    rw [hκ]
    exact resolutionSupportedExteriorPairing_transfer C f g i j φ ψ hP hI hQ hJ _ _ _ _ hφI hψJ κ
      (resolutionSupportedExteriorPairing_transfer C f g i j b b' hI hG hJ hG'
        _ _ _ _ hbG hbG' κ hκG)
  · have h := (isResolutionSupportedExteriorProduct_iff C f g i j K L κ).1 hκ I₀ J₀ hI₀ hJ₀ eI₀ eJ₀
    rw [← cancel_epi A₀, hA₀]
    exact h

end AlgebraicGeometry.Etale
