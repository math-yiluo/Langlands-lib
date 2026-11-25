/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.AffineComplement
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.Modules.VanishingOnOpen
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-!
# Sections vanishing on a closed subset

Let `J` be an ideal sheaf on a scheme `X` and `N` an `𝒪_X`-module. We study sections of `N`
which are images of sections of `J ⊗ N` under `J ⊗ N ⟶ 𝒪_X ⊗ N ≅ N`. Away from the support of
`J` the inclusion `J ⟶ 𝒪_X` is an isomorphism, while near a point of the support of `J` the
inclusion `J ⊗ N ⟶ N` is not an epimorphism if `N` is locally free of rank one. Consequently:

* a section of `N` coming from `J ⊗ N` does not generate `N` at any point of the support of `J`
  (`AlgebraicGeometry.Scheme.Modules.not_generatesAt_of_factors`);
* if sections `t i` of an invertible module `N` generate `N` near `x`, then one of them generates
  `N` at `x` (`AlgebraicGeometry.Scheme.Modules.exists_generatesAt_of_epi`).

These are the inputs for choosing sections of an ample module which do not vanish at finitely
many given points.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace IdealSheafData

variable (J : X.IdealSheafData)

/-- **An ideal sheaf is everything away from its support.** On an open `U` not meeting the
support of `J`, the inclusion `J ⟶ 𝒪_X` is an isomorphism: the closed subscheme cut out by `J`
does not meet `U`, so every section over `U` restricts to zero on it. -/
lemma isIso_restrictFunctor_map_toModulesι {U : X.Opens}
    (hU : (U : Set X) ⊆ (J.support : Set X)ᶜ) :
    IsIso ((Modules.restrictFunctor U.ι).map J.toModulesι) := by
  rw [Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨J.injective_toModulesι_app (U.ι ''ᵁ V), fun y ↦ ?_⟩
  have hempty : J.subschemeι ⁻¹ᵁ (U.ι ''ᵁ V) = ⊥ := by
    refine eq_bot_iff.mpr fun z hz ↦ ?_
    have h₁ : J.subschemeι z ∈ U := (U.ι.image_le_opensRange V).trans (by simp) hz
    have h₂ : J.subschemeι z ∈ (J.support : Set X) := by
      rw [← J.range_subschemeι]
      exact ⟨z, rfl⟩
    exact hU h₁ h₂
  have : Subsingleton Γ(J.subscheme, J.subschemeι ⁻¹ᵁ (U.ι ''ᵁ V)) := by
    rw [hempty]
    infer_instance
  have hy : y ∈ Set.range (J.toModulesι.app (U.ι ''ᵁ V)) := by
    rw [J.range_toModulesι_app_eq]
    exact Subsingleton.elim _ _
  exact hy

/-- **An ideal sheaf is not everything near a point of its support.** If `y ∈ W` lies in the
support of `J`, then `J|_W ⟶ 𝒪_W` is not an epimorphism: otherwise it would be an isomorphism,
so `1` would be a section of `J` over `W`, and the closed subscheme cut out by `J` would not meet
`W`. -/
lemma not_epi_restrictFunctor_map_toModulesι {W : X.Opens} {y : X} (hyW : y ∈ W)
    (hy : y ∈ (J.support : Set X)) :
    ¬ Epi ((Modules.restrictFunctor W.ι).map J.toModulesι) := by
  intro h
  have : IsIso ((Modules.restrictFunctor W.ι).map J.toModulesι) := isIso_of_mono_of_epi _
  have hb := ConcreteCategory.bijective_of_isIso
    (((Modules.restrictFunctor W.ι).map J.toModulesι).app ⊤)
  obtain ⟨a, ha⟩ := hb.2 (1 : Γ(X, W.ι ''ᵁ ⊤))
  have h1 : (1 : Γ(X, W.ι ''ᵁ ⊤)) ∈ Set.range (J.toModulesι.app (W.ι ''ᵁ ⊤)) := ⟨a, ha⟩
  rw [J.range_toModulesι_app_eq] at h1
  rw [← J.range_subschemeι] at hy
  obtain ⟨z, rfl⟩ := hy
  have hz : z ∈ J.subschemeι ⁻¹ᵁ (W.ι ''ᵁ ⊤) := by
    change J.subschemeι z ∈ W.ι ''ᵁ ⊤
    simpa using hyW
  have h2 := congrArg (J.subscheme.presheaf.germ _ z hz) (h1.symm.trans (map_one _))
  rw [map_zero, map_one] at h2
  exact zero_ne_one h2

end IdealSheafData

namespace Modules

open IdealSheafData

/-- A section `s : 𝒪_X ⟶ N` whose value at `1` is a free generator on `U` restricts to an
isomorphism `𝒪_U ≅ N|_U`. -/
lemma isIso_restrictFunctor_map_of_isFreeGenerator {N : X.Modules} (s : 𝟙_ X.Modules ⟶ N)
    {U : X.Opens} (he : IsFreeGenerator (s.app U (unitSectionsEquiv U 1))) :
    IsIso ((restrictFunctor U.ι).map s) := by
  have he' := he.map ((U.ι.image_le_opensRange ⊤).trans (by simp))
  rw [presheaf_map_app_unitSectionsEquiv_one] at he'
  have : IsIso ((restrictUnitIso U.ι).inv ≫ (restrictFunctor U.ι).map s) :=
    (isFreeGenerator_iff_isIso U.ι _).mp (by
      convert he' using 1
      rw [Hom.comp_app, ConcreteCategory.comp_apply]
      exact congrArg (Hom.app s (U.ι ''ᵁ ⊤)) (map_one (U.ι.appIso ⊤).inv.hom))
  exact IsIso.of_isIso_comp_left (restrictUnitIso U.ι).inv _

/-- A module with a free generator on `W` restricts to the structure sheaf on `W`. -/
lemma nonempty_restrict_iso_unit {N : X.Modules} {W : X.Opens} {e : Γ(N, W)}
    (he : IsFreeGenerator e) : Nonempty (N.restrict W.ι ≅ Modules.unit W) := by
  have hle : W.ι ''ᵁ ⊤ ≤ W := (W.ι.image_le_opensRange ⊤).trans (by simp)
  have := (isFreeGenerator_iff_isIso W.ι
    (unitToRestrict W.ι N (N.presheaf.map (homOfLE hle).op e))).mp
    (by rw [restrictAppIso_hom_unitToRestrict_app_top]; exact he.map hle)
  exact ⟨(asIso (unitToRestrict W.ι N (N.presheaf.map (homOfLE hle).op e))).symm⟩

/-- Epimorphisms on an open `W` are detected by the vanishing of the cokernel on `W`. -/
lemma epi_restrictFunctor_map_iff {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) :
    Epi ((restrictFunctor W.ι).map φ) ↔ IsZero ((cokernel φ).restrict W.ι) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso (restrictFunctor W.ι) φ)
  · exact Preadditive.epi_of_isZero_cokernel _
      (h.of_iso (PreservesCokernel.iso (restrictFunctor W.ι) φ).symm)

/-- **The twisted ideal sheaf is not everything near a point of its support.** If `N` has a free
generator on `W` and `y ∈ W` lies in the support of `J`, then the cokernel of
`J ⊗ N ⟶ 𝒪_X ⊗ N` does not vanish on `W`. -/
lemma not_isZero_restrict_cokernel_whiskerRight_toModulesι (J : X.IdealSheafData)
    {N : X.Modules} {W : X.Opens} {e : Γ(N, W)} (he : IsFreeGenerator e) {y : X} (hyW : y ∈ W)
    (hy : y ∈ (J.support : Set X)) :
    ¬ IsZero ((cokernel (J.toModulesι ▷ N)).restrict W.ι) := by
  intro h
  rw [← epi_restrictFunctor_map_iff] at h
  apply J.not_epi_restrictFunctor_map_toModulesι hyW hy
  obtain ⟨eN⟩ := nonempty_restrict_iso_unit he
  let P := pullback W.ι
  let r := restrictFunctorIsoPullback W.ι
  -- transport to the monoidal functor `pullback W.ι`
  have h₁ : Epi (P.map (J.toModulesι ▷ N)) := by
    rw [← NatIso.naturality_1 r (J.toModulesι ▷ N)]
    infer_instance
  have h₂ : Epi (P.map J.toModulesι ▷ P.obj N) := by
    have h := Functor.LaxMonoidal.μ_natural_left P J.toModulesι N
    have : P.map J.toModulesι ▷ P.obj N =
        Functor.LaxMonoidal.μ P _ _ ≫ P.map (J.toModulesι ▷ N) ≫
          inv (Functor.LaxMonoidal.μ P _ _) := by
      rw [← reassoc_of% h]
      simp
    rw [this]
    infer_instance
  -- `P N ≅ 𝒪_W`, and `- ▷ 𝒪_W` is isomorphic to the identity
  let eP : P.obj N ≅ 𝟙_ _ := (r.app N).symm ≪≫ eN
  have h₃ : Epi (P.map J.toModulesι ▷ 𝟙_ _) := by
    have : P.map J.toModulesι ▷ 𝟙_ _ =
        _ ◁ eP.inv ≫ P.map J.toModulesι ▷ P.obj N ≫ _ ◁ eP.hom := by
      rw [whisker_exchange_assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id,
        Category.comp_id]
    rw [this]
    infer_instance
  have h₄ : Epi (P.map J.toModulesι) := by
    have h := rightUnitor_naturality (P.map J.toModulesι)
    have : P.map J.toModulesι =
        (ρ_ _).inv ≫ (P.map J.toModulesι ▷ 𝟙_ _) ≫ (ρ_ _).hom := by
      rw [h]
      simp
    rw [this]
    infer_instance
  rw [← NatIso.naturality_2 r J.toModulesι]
  infer_instance

/-- **Sections coming from `J ⊗ N` vanish on the support of `J`.** If `t` is the image of a
section `σ` of `J ⊗ N` under `J ⊗ N ⟶ 𝒪_X ⊗ N ≅ N`, then `t` does not generate `N` at any point
of the support of `J`. -/
lemma not_generatesAt_of_factors (J : X.IdealSheafData) {N : X.Modules}
    (σ : 𝟙_ X.Modules ⟶ J.toModules ⊗ N) {y : X} (hy : y ∈ (J.support : Set X)) :
    ¬ GeneratesAt ((σ ≫ J.toModulesι ▷ N ≫ (λ_ N).hom).app ⊤ (unitSectionsEquiv ⊤ 1)) y := by
  rintro ⟨W, hyW, hW⟩
  set t := σ ≫ J.toModulesι ▷ N ≫ (λ_ N).hom
  rw [presheaf_map_app_unitSectionsEquiv_one] at hW
  have := isIso_restrictFunctor_map_of_isFreeGenerator t hW
  refine not_isZero_restrict_cokernel_whiskerRight_toModulesι J hW hyW hy ?_
  rw [← epi_restrictFunctor_map_iff]
  have h1 : Epi ((restrictFunctor W.ι).map σ ≫
      (restrictFunctor W.ι).map (J.toModulesι ▷ N ≫ (λ_ N).hom)) := by
    rw [← Functor.map_comp]
    infer_instance
  have h2 := epi_of_epi ((restrictFunctor W.ι).map σ)
    ((restrictFunctor W.ι).map (J.toModulesι ▷ N ≫ (λ_ N).hom))
  rw [Functor.map_comp] at h2
  have : (restrictFunctor W.ι).map (J.toModulesι ▷ N) =
      ((restrictFunctor W.ι).map (J.toModulesι ▷ N) ≫ (restrictFunctor W.ι).map (λ_ N).hom) ≫
        inv ((restrictFunctor W.ι).map (λ_ N).hom) := by
    simp
  rw [this]
  infer_instance

/-- A section of an invertible module generates it at `x` if and only if `x` lies outside its
zero scheme. -/
lemma generatesAt_iff_mem_compl_support {N : X.Modules} [SheafOfModules.IsInvertible.{u, u, u} N]
    (s : 𝟙_ X.Modules ⟶ N) (x : X) :
    GeneratesAt (s.app ⊤ (unitSectionsEquiv ⊤ 1)) x ↔
      x ∈ (Hom.zeroLocus s).support.compl := by
  obtain ⟨V, hxV, -, e, he⟩ := exists_isFreeGenerator N (x := x) (W := ⊤) trivial
  have h₁ := basicOpen_coeff_eq s V he
  rw [generatesAt_iff_mem_basicOpen he (c := he.coeff (s.app V.1 (unitSectionsEquiv _ 1)))
    (by rw [presheaf_map_app_unitSectionsEquiv_one, he.coeff_smul]) hxV, h₁]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hxV, h⟩⟩

/-- **Generating sections include one generating at a given point.** Let `N` be invertible and
`t i` global sections of `N`, the components of `φ : 𝒪_X^{⊕ I} ⟶ N`, which generate `N` on an
open `U ∋ x`. Then some `t i` generates `N` at `x`. Otherwise all `t i` vanish at `x`, so they
come from `J ⊗ N` for the ideal `J` of the closure of `x`, and hence the cokernel of
`J ⊗ N ⟶ N` would vanish near `x`. -/
lemma exists_generatesAt_of_epi {N : X.Modules} [SheafOfModules.IsInvertible.{u, u, u} N]
    {I : Type u} (φ : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ N) {U : X.Opens} {x : X}
    (hx : x ∈ U) (h : Epi ((restrictFunctor U.ι).map φ)) :
    ∃ i, GeneratesAt
      (Hom.app (SheafOfModules.ιFree (R := X.ringCatSheaf) i ≫ φ) ⊤ (unitSectionsEquiv ⊤ 1)) x := by
  set t : I → (𝟙_ X.Modules ⟶ N) := fun i ↦ SheafOfModules.ιFree (R := X.ringCatSheaf) i ≫ φ
  by_contra! hne
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ X.Modules) :=
    IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  let J := vanishingIdeal ⟨closure {x}, isClosed_closure⟩
  have hxJ : x ∈ (J.support : Set X) := by
    simp only [J, coe_support_vanishingIdeal]
    exact subset_closure rfl
  let q := (λ_ N).inv ≫ cokernel.π (J.toModulesι ▷ N)
  -- every `t i` is killed by `N ⟶ N ⧸ J N`
  have hq (i : I) : t i ≫ q = 0 := by
    refine hom_ext _ _ fun V ↦ ?_
    ext r
    obtain ⟨a, rfl⟩ := ((isFreeGenerator_one (X := X) ⊤).map (le_top : V ≤ ⊤)).exists_smul_eq r
    rw [Hom.app_smul, Hom.app_smul]
    erw [Hom.app_presheaf_map (t i ≫ q) (homOfLE (le_top : V ≤ ⊤)) (1 : Γ(X, ⊤))]
    rw [Hom.comp_app, ConcreteCategory.comp_apply]
    erw [app_cokernel_π_eq_zero J N ((t i).app ⊤ (unitSectionsEquiv ⊤ 1)) fun y ↦ ?_]
    · simp
    obtain ⟨W, hyW, -, e, he⟩ := exists_isFreeGenerator N (x := y) (W := ⊤) trivial
    refine ⟨W, hyW, e, he.coeff ((t i).app W.1 (unitSectionsEquiv _ 1)), ?_, ?_⟩
    · have hle : Hom.zeroLocus (t i) ≤ J := by
        rw [le_support_iff_le_vanishingIdeal.symm]
        refine (Hom.zeroLocus (t i)).support.isClosed.closure_subset_iff.mpr
          (Set.singleton_subset_iff.mpr ?_)
        by_contra hx'
        exact hne i ((generatesAt_iff_mem_compl_support (t i) x).mpr hx')
      refine hle W ?_
      rw [Hom.ideal_zeroLocus (t i) W (isFreeGenerator_one _) he (he.coeff_smul _).symm]
      exact Ideal.mem_span_singleton_self _
    · rw [presheaf_map_app_unitSectionsEquiv_one, he.coeff_smul]
  have hzero : φ ≫ q = 0 := free_hom_ext fun i ↦ by
    rw [← Category.assoc, comp_zero]
    exact hq i
  -- hence `N ⧸ J N` vanishes on `U`, which is absurd near `x`
  obtain ⟨W, hxW, hWU, e, he⟩ := exists_isFreeGenerator N hx
  refine not_isZero_restrict_cokernel_whiskerRight_toModulesι J he hxW hxJ
    (isZero_restrict_of_le hWU ?_)
  have h₁ : (restrictFunctor U.ι).map q = 0 := by
    rw [← cancel_epi ((restrictFunctor U.ι).map φ), ← Functor.map_comp, hzero,
      Functor.map_zero, comp_zero]
  have h₂ : (restrictFunctor U.ι).map (cokernel.π (J.toModulesι ▷ N)) = 0 := by
    have : (restrictFunctor U.ι).map (cokernel.π (J.toModulesι ▷ N)) =
        (restrictFunctor U.ι).map (λ_ N).hom ≫ (restrictFunctor U.ι).map q := by
      rw [← Functor.map_comp]
      simp [q]
    rw [this, h₁, comp_zero]
  have : Epi ((restrictFunctor U.ι).map (cokernel.π (J.toModulesι ▷ N))) := inferInstance
  exact IsZero.of_epi_eq_zero _ h₂

end Modules

end AlgebraicGeometry.Scheme
