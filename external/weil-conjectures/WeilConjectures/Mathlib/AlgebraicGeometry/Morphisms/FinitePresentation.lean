/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent

/-!
# The diagonal of a morphism locally of finite presentation

We prove the cancellation property of morphisms locally of finite presentation: if `f ≫ g` is
locally of finite presentation and `g` is locally of finite type, then so is `f`
(`AlgebraicGeometry.locallyOfFinitePresentation_of_comp`, Stacks Tag 02FV).
Local finite presentation also descends along flat surjections of finite presentation of the
source (`AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective`, Stacks
Tag 02KL).

Applying this to `Δ ≫ pullback.fst f f = 𝟙 X` shows that the diagonal of a morphism locally of
finite presentation is again locally of finite presentation
(`AlgebraicGeometry.locallyOfFinitePresentation_diagonal`). Since a diagonal is a monomorphism,
it is automatically quasi-separated, so it is of finite presentation as soon as it is
quasi-compact, that is, as soon as `f` is quasi-separated.

# Finite-type ideal sheaves and closed immersions of finite presentation

We also record the two directions of the correspondence between ideal sheaves whose ideal of
sections on every affine open is finitely generated (in the terminology of
`AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteType`, the finite-type ideal sheaves) and
closed immersions locally of finite presentation:
`AlgebraicGeometry.Scheme.IdealSheafData.locallyOfFinitePresentation_subschemeι` and
`AlgebraicGeometry.Scheme.Hom.fg_ideal_ker`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

/-- **Cancellation for morphisms locally of finite presentation**: if `f ≫ g` is locally of
finite presentation and `g` is locally of finite type, then `f` is locally of finite
presentation. -/
@[stacks 02FV]
theorem locallyOfFinitePresentation_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f :=
  HasRingHomProperty.of_comp' (P' := @LocallyOfFiniteType)
    (fun _ _ hf hfg ↦ hfg.of_comp_finiteType _ hf) ‹_› ‹_›

/-- The affine case of
`AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective`:
on global sections it is `Algebra.FinitePresentation.of_finitePresentation_of_faithfullyFlat`. -/
theorem LocallyOfFinitePresentation.of_comp_of_flat_of_surjective_of_isAffine
    {X' X S : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine S] (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    [LocallyOfFinitePresentation (u ≫ f)] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  have hu : u.appTop.hom.Flat := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp ‹_›
  have hu' : u.appTop.hom.FinitePresentation :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp ‹_›
  have huf : (u.appTop.hom.comp f.appTop.hom).FinitePresentation :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation) (f := u ≫ f)).mp ‹_›
  have hsurj : Function.Surjective (PrimeSpectrum.comap u.appTop.hom) := by
    intro p
    let p' : Spec Γ(X, ⊤) := p
    obtain ⟨w, hw⟩ := u.surjective (X.isoSpec.inv p')
    refine ⟨X'.isoSpec.hom w, ?_⟩
    have h₁ : (X'.isoSpec.hom ≫ Spec.map u.appTop) w = (u ≫ X.isoSpec.hom) w := by
      rw [Scheme.isoSpec_hom_naturality]
    have h₂ : X.isoSpec.hom (X.isoSpec.inv p') = p' := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw, h₂] at h₁
    exact h₁
  algebraize [f.appTop.hom, u.appTop.hom, u.appTop.hom.comp f.appTop.hom]
  have : Module.FaithfullyFlat Γ(X, ⊤) Γ(X', ⊤) := .of_comap_surjective hsurj
  exact Algebra.FinitePresentation.of_finitePresentation_of_faithfullyFlat (A := Γ(X, ⊤))
    Γ(S, ⊤) Γ(X', ⊤)

/-- The case of affine `X` and `S` of
`AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective`: since `u` is open,
finitely many affine opens of `X'` have images covering `X`, and their disjoint union is affine. -/
theorem LocallyOfFinitePresentation.of_comp_of_flat_of_surjective_of_isAffine_of_isAffine
    {X' X S : Scheme.{u}} [IsAffine X] [IsAffine S] (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    [LocallyOfFinitePresentation (u ≫ f)] : LocallyOfFinitePresentation f := by
  classical
  have hcov (x : X) : ∃ W : X'.affineOpens, x ∈ u '' (W : Set X') := by
    obtain ⟨w, rfl⟩ := u.surjective x
    obtain ⟨W, hW, hwW, -⟩ := (Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens)
      (show w ∈ (⊤ : X'.Opens) from trivial)
    exact ⟨⟨W, hW⟩, w, hwW, rfl⟩
  choose W hW using hcov
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ u '' (W x : Set X'))
    (fun x ↦ u.isOpenMap _ (W x).1.isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hW x⟩)
  let Y (i : s) : Scheme.{u} := (W i.1 : X'.Opens)
  have (i : s) : IsAffine (Y i) := (W i.1).2
  let g : ∐ Y ⟶ X := Sigma.desc fun i : s ↦ (W i.1 : X'.Opens).ι ≫ u
  have : Flat g := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have : LocallyOfFinitePresentation g := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have : LocallyOfFinitePresentation (g ≫ f) := by
    have : g ≫ f = Sigma.desc fun i : s ↦ (W i.1 : X'.Opens).ι ≫ u ≫ f := by
      ext i
      simp [g, Sigma.ι_comp_desc]
    rw [this]
    exact IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have : Surjective g := Surjective.sigmaDesc_of_union_range_eq_univ <|
    Set.eq_univ_of_forall fun x ↦ by
      obtain ⟨i, hi, w, hw, rfl⟩ : ∃ i ∈ s, ∃ w ∈ (W i : Set X'), u w = x := by
        simpa using hs (Set.mem_univ x)
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, ⟨w, hw⟩, rfl⟩
  exact of_comp_of_flat_of_surjective_of_isAffine g f

/-- **Local finite presentation descends along flat surjections of finite presentation.** Let
`u : X' ⟶ X` be surjective, flat and locally of finite presentation, and let `f : X ⟶ S`. If
`u ≫ f` is locally of finite presentation, then so is `f`. -/
@[stacks 02KL]
theorem LocallyOfFinitePresentation.of_comp_of_flat_of_surjective {X' X S : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ S) [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    [LocallyOfFinitePresentation (u ≫ f)] : LocallyOfFinitePresentation f := by
  have key (x : X) : ∃ (U : S.Opens) (V : X.Opens) (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
      LocallyOfFinitePresentation (f.resLE U V e) := by
    obtain ⟨U, hU, hfxU, -⟩ := (Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show f x ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ f ⁻¹ᵁ U from hfxU)
    refine ⟨U, V, hxV, hVU, ?_⟩
    have : IsAffine U := hU
    have : IsAffine V := hV
    have : Flat (u ∣_ V) := IsZariskiLocalAtTarget.restrict ‹_› V
    have : Surjective (u ∣_ V) := IsZariskiLocalAtTarget.restrict ‹_› V
    have : LocallyOfFinitePresentation (u ∣_ V) := IsZariskiLocalAtTarget.restrict ‹_› V
    have : LocallyOfFinitePresentation (u ∣_ V ≫ f.resLE U V hVU) := by
      rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
      exact IsZariskiLocalAtSource.resLE _ ‹_›
    exact of_comp_of_flat_of_surjective_of_isAffine_of_isAffine (u ∣_ V) (f.resLE U V hVU)
  choose U V hxV e hf using key
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun x : X ↦ V x)
    (P := @LocallyOfFinitePresentation) ?_).mpr fun x ↦ ?_
  · exact eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxV x⟩
  · rw [← Scheme.Hom.resLE_comp_ι _ (e x)]
    infer_instance

section Diagonal

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The diagonal of a morphism locally of finite presentation is locally of finite
presentation. -/
instance locallyOfFinitePresentation_diagonal [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (pullback.diagonal f) := by
  have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst]; infer_instance
  exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)

/-- **The diagonal of a morphism of finite presentation is of finite presentation.**

Mathlib has no bundled class for "of finite presentation"; a morphism is of finite presentation
if it is locally of finite presentation, quasi-compact and quasi-separated. Note that `f` itself
need not be quasi-compact for this. -/
theorem Scheme.Hom.diagonal_finitePresentation [LocallyOfFinitePresentation f]
    [QuasiSeparated f] :
    LocallyOfFinitePresentation (pullback.diagonal f) ∧ QuasiCompact (pullback.diagonal f) ∧
      QuasiSeparated (pullback.diagonal f) :=
  ⟨inferInstance, inferInstance, inferInstance⟩


end Diagonal

section IdealSheaf

variable {X Y : Scheme.{u}}

/-- The closed subscheme cut out by a finite-type ideal sheaf is locally of finite
presentation over the ambient scheme. -/
lemma Scheme.IdealSheafData.locallyOfFinitePresentation_subschemeι {I : X.IdealSheafData}
    (hI : ∀ U : X.affineOpens, (I.ideal U).FG) :
    LocallyOfFinitePresentation I.subschemeι := by
  refine IsZariskiLocalAtSource.of_openCover I.subschemeCover.openCover fun U : X.affineOpens ↦ ?_
  change LocallyOfFinitePresentation (I.subschemeCover.f U ≫ I.subschemeι)
  rw [(I.isPullback_subschemeCover_map U).w]
  have : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective
      (by simpa only [CommRingCat.hom_ofHom, Ideal.mk_ker] using hI U)
  infer_instance

/-- The ideal sheaf cut out by a closed immersion locally of finite presentation is of
finite type. -/
lemma Scheme.Hom.fg_ideal_ker (f : X ⟶ Y) [IsClosedImmersion f]
    [LocallyOfFinitePresentation f] (U : Y.affineOpens) : (f.ker.ideal U).FG := by
  rw [Scheme.Hom.ker_apply]
  have hU : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
  have hfp : (f.app U.1).hom.FinitePresentation := by
    rw [f.app_eq_appLE]
    exact f.finitePresentation_appLE U.2 hU le_rfl
  let := (f.app U.1).hom.toAlgebra
  have : Algebra.FinitePresentation Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := hfp
  have : Algebra.FinitePresentation Γ(Y, U.1) Γ(Y, U.1) := Algebra.FinitePresentation.self _
  exact Algebra.FinitePresentation.ker_fG_of_surjective
    (Algebra.ofId Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)) (f.app_surjective U.1 U.2)

end IdealSheaf

end AlgebraicGeometry
