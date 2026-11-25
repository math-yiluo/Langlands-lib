/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.SimpleRing.Field
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Descending a whole generic-fibre isomorphism to a base open

Source: Stacks Project, Tag 01ZM, morphism descent and eventual equality.
(blueprint: lem-sbc-generic-fibre-iso-spread-base-open)
-/

@[expose] public section

universe u
open CategoryTheory Limits Topology
namespace AlgebraicGeometry

private abbrev AffineNhds (S : Scheme.{u}) (η : S) :=
  {V : S.Opens // IsAffineOpen V ∧ η ∈ V}

private noncomputable def nhdsDiagram (S : Scheme.{u}) (η : S) :
    AffineNhds S η ⥤ Scheme.{u} :=
  (show Monotone (fun V : AffineNhds S η ↦ V.1) from fun _ _ h ↦ h).functor ⋙
    S.restrictFunctor ⋙ Over.forget S

private noncomputable def nhdsCone (S : Scheme.{u}) (η : S) : Cone (nhdsDiagram S η) where
  pt := Spec (S.residueField η)
  π.app V := Spec.map (S.residue η) ≫ V.1.fromSpecStalkOfMem η V.2.2
  π.naturality V T f := by
    apply (cancel_mono T.1.ι).mp
    simp [nhdsDiagram]

private theorem nhds_cofiltered (S : Scheme.{u}) (η : S) : IsCofiltered (AffineNhds S η) := by
  have : Nonempty (AffineNhds S η) := by
    obtain ⟨V, hV, hηV, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := S) (x := η) (U := ⊤) (by trivial)
    exact ⟨⟨V, hV, hηV⟩⟩
  have : IsDirected (AffineNhds S η) (· ≥ ·) := ⟨fun V T ↦ by
    obtain ⟨Z, hZ, hηZ, hZVT⟩ :=
      exists_isAffineOpen_mem_and_subset (show η ∈ V.1 ⊓ T.1 from ⟨V.2.2, T.2.2⟩)
    exact ⟨⟨Z, hZ, hηZ⟩, hZVT.trans inf_le_left, hZVT.trans inf_le_right⟩⟩
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem nhdsCone_limit (S : Scheme.{u}) [IsIntegral S] (η : S)
    (hη : IsGenericPoint η Set.univ) : Nonempty (IsLimit (nhdsCone S η)) := by
  classical
  have hf : IsField (S.presheaf.stalk η) :=
    isField_stalk_of_closure_mem_irreducibleComponents S η (by
      rw [hη]
      simp [irreducibleComponents_eq_singleton])
  have : IsSimpleRing (S.presheaf.stalk η) := (isSimpleRing_iff_isField _).mpr hf
  have : IsIso (S.residue η) := (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(S.residue η).hom.injective, IsLocalRing.residue_surjective⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := S.fromSpecStalk_limit_affine_neighbourhoods η
  let s : Cone (nhdsDiagram S η) :=
    { pt := Spec (S.presheaf.stalk η)
      π.app V := V.1.fromSpecStalkOfMem η V.2.2
      π.naturality V T f := by
        apply (cancel_mono T.1.ι).mp
        simp [nhdsDiagram] }
  have hx (t : Cone (nhdsDiagram S η)) : ∃! g : t.pt ⟶ Spec (S.presheaf.stalk η),
      ∀ V : AffineNhds S η, g ≫ V.1.fromSpecStalkOfMem η V.2.2 = t.π.app V := by
    apply h t.pt (fun V ↦ t.π.app V)
    intro V T hTV
    exact t.w (homOfLE hTV)
  let hs : IsLimit s :=
    { lift := fun t ↦ (hx t).choose
      fac := fun t V ↦ (hx t).choose_spec.1 V
      uniq := fun t g hg ↦ (hx t).choose_spec.2 g hg }
  exact ⟨hs.ofIsoLimit (Cone.ext (asIso (Spec.map (S.residue η))).symm (fun V ↦ by
    change V.1.fromSpecStalkOfMem η V.2.2 =
      inv (Spec.map (S.residue η)) ≫ Spec.map (S.residue η) ≫ _
    simp))⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism of whole affine generic fibres descends after shrinking the base.

Source: Stacks Project, Tag 01ZM, lemma-descend-finite-presentation, parts (2) and (3).
Proof: Form the cofiltered diagram of affine neighbourhoods of eta. The
spectrum of the stalk is its limit by the existing stalk-neighbourhood theorem.
The stalk is a field since eta is generic in an integral scheme. Hence its
residue quotient is an isomorphism, and transporting the limit gives the
canonical cone with point Spec kappa(eta). Take the top neighbourhood as base
stage. The fibre squares, with the second transported by e and its equation
over kappa(eta), exhibit one common limit model for X and Y. Both finite-stage
models are affine and locally of finite presentation, hence qcqs. Apply the
existing exists_iso_of_isPullback theorem: it descends the two inverse maps
by 01ZM(2), then their two inverse identities by 01ZM(3). This gives an
isomorphism of their base changes at an affine neighbourhood U of eta.
The canonical pullback comparisons identify these base changes with the
open restrictions f^{-1}(U) and g^{-1}(U). Conjugate the descended isomorphism
by those comparisons. Their projection equations give compatibility over U;
composition with U's inclusion gives the displayed equality over S. No
nonemptiness of either generic fibre is used, so the empty case is covered.

(blueprint: lem-sbc-generic-fibre-iso-spread-base-open) -/
theorem exists_base_open_iso_of_generic_fibre_iso
    {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) (g : Y ⟶ S)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (e : f.fiber η ≅ g.fiber η)
    (he : e.hom ≫ g.fiberToSpecResidueField η = f.fiberToSpecResidueField η) :
    ∃ U : S.Opens, η ∈ U ∧
      ∃ eU : (f ⁻¹ᵁ U).toScheme ≅ (g ⁻¹ᵁ U).toScheme,
        eU.hom ≫ (g ⁻¹ᵁ U).ι ≫ g = (f ⁻¹ᵁ U).ι ≫ f := by
  classical
  have : IsCofiltered (AffineNhds S η) := nhds_cofiltered S η
  let D := nhdsDiagram S η
  let c := nhdsCone S η
  obtain ⟨hc⟩ := nhdsCone_limit S η hη
  have (V : AffineNhds S η) : IsAffine (D.obj V) := V.2.1
  have {V W : AffineNhds S η} (a : V ⟶ W) : IsAffineHom (D.map a) := by
    have : IsAffine V.1.toScheme := V.2.1
    have : IsAffine W.1.toScheme := W.2.1
    exact inferInstanceAs (IsAffineHom (S.homOfLE (leOfHom a)))
  let k : AffineNhds S η := ⟨⊤, isAffineOpen_top S, by trivial⟩
  let f₀ : X ⟶ D.obj k := f ≫ S.topIso.inv
  let g₀ : Y ⟶ D.obj k := g ≫ S.topIso.inv
  have base : S.fromSpecResidueField η ≫ S.topIso.inv = c.π.app k := by
    apply (cancel_mono (⊤ : S.Opens).ι).mp
    simp [c, nhdsCone, k, Scheme.fromSpecResidueField,
      Scheme.Opens.fromSpecStalkOfMem_ι]
  have H₁ : IsPullback (f.fiberι η) (f.fiberToSpecResidueField η) f₀ (c.π.app k) := by
    exact (IsPullback.of_hasPullback f (S.fromSpecResidueField η)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) S.topIso.symm
      (by simp [Scheme.Hom.fiberι]) (by simp [Scheme.Hom.fiberToSpecResidueField])
      (by simp [f₀]) (by simpa using base)
  have H₂ : IsPullback (e.hom ≫ g.fiberι η) (f.fiberToSpecResidueField η)
      g₀ (c.π.app k) := by
    have H : IsPullback (g.fiberι η) (g.fiberToSpecResidueField η) g₀ (c.π.app k) :=
      (IsPullback.of_hasPullback g (S.fromSpecResidueField η)).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) S.topIso.symm
        (by simp [Scheme.Hom.fiberι]) (by simp [Scheme.Hom.fiberToSpecResidueField])
        (by simp [g₀]) (by simpa using base)
    exact H.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simpa using he) (by simp) (by simp)
  have : LocallyOfFinitePresentation f₀ := by dsimp [f₀]; infer_instance
  have : LocallyOfFinitePresentation g₀ := by dsimp [g₀]; infer_instance
  obtain ⟨j, t, ht⟩ := exists_iso_of_isPullback hc H₁ H₂
  obtain ⟨a, ha, _⟩ := ht (IsPullback.of_hasPullback _ _)
    (isPullbackLift_fst t H₁) (isPullbackLift_snd t H₁)
    (IsPullback.of_hasPullback _ _)
    (isPullbackLift_fst t H₂) (isPullbackLift_snd t H₂)
  have transition : j.1.ι ≫ S.topIso.inv = D.map t := by
    apply (cancel_mono (⊤ : S.Opens).ι).mp
    simp [D, nhdsDiagram, k, Scheme.homOfLE_ι]
  have HP : IsPullback (f ⁻¹ᵁ j.1).ι (f ∣_ j.1) f₀ (D.map t) := by
    exact (isPullback_morphismRestrict f j.1).flip.of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) S.topIso.symm
      (by simp) (by simp) (by simp [f₀]) (by simpa using transition)
  have HQ : IsPullback (g ⁻¹ᵁ j.1).ι (g ∣_ j.1) g₀ (D.map t) := by
    exact (isPullback_morphismRestrict g j.1).flip.of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) S.topIso.symm
      (by simp) (by simp) (by simp [g₀]) (by simpa using transition)
  let a' := HP.isoPullback ≪≫ a ≪≫ HQ.isoPullback.symm
  refine ⟨j.1, j.2.2, a', ?_⟩
  have hf : HP.isoPullback.hom ≫ pullback.snd f₀ (D.map t) = f ∣_ j.1 :=
    HP.isoPullback_hom_snd
  have hg : HQ.isoPullback.inv ≫ (g ∣_ j.1) = pullback.snd g₀ (D.map t) := by
    rw [Iso.inv_comp_eq, HQ.isoPullback_hom_snd]
  calc
    a'.hom ≫ (g ⁻¹ᵁ j.1).ι ≫ g = a'.hom ≫ (g ∣_ j.1) ≫ j.1.ι := by simp
    _ = (f ∣_ j.1) ≫ j.1.ι := by
      have heq : a'.hom ≫ (g ∣_ j.1) = f ∣_ j.1 := by
        change (HP.isoPullback.hom ≫ a.hom ≫ HQ.isoPullback.inv) ≫ (g ∣_ j.1) = _
        simp only [Category.assoc]
        erw [hg]
        erw [ha]
        exact hf
      simpa only [Category.assoc] using congrArg (· ≫ j.1.ι) heq
    _ = (f ⁻¹ᵁ j.1).ι ≫ f := morphismRestrict_ι _ _

end AlgebraicGeometry
