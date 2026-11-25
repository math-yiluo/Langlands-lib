/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.RingTheory.SimpleRing.Field
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Lifting an affine open from a generic fibre

Source: Stacks Project, Tags 01Z4 and 01Z6, descending quasi-compact opens and affineness.
(blueprint: lem-sbc-generic-fibre-affine-open-lift)
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

/-- An affine open of the generic fibre lifts to an affine open of the total space.

Source: Stacks Project, Tag 01Z4, lemma-descend-quasi-compact-open, and Tag 01Z6,
lemma-limit-affine.
Proof: The affine neighbourhoods of eta form a cofiltered diagram by the
basis of affine opens. The spectrum of the stalk is its limit, by the existing
stalk-neighbourhood theorem. Since S is integral, the stalk at eta is a field,
so the residue quotient is an isomorphism. Transport the limit along its
spectrum to get a cone with point Spec kappa(eta) and its canonical projections.
Take the top neighbourhood as base stage, identifying it with S by topIso.
Base change this limit by f, and identify its limit with f.fiber eta using the
pullback square. Apply exists_isAffineOpen_preimage_eq (01Z4 and 01Z6) to U.
This gives an affine open O in a base restriction of X with inverse image U.
The projection q from that restriction to X is an open immersion. Its image
V = q(O) is affine. Since q is injective and the limit projection followed by
q is the fibre inclusion, the inverse image of V in the generic fibre is U.
Paste the open-restriction pullback square with the fibre square. The resulting
pullback is the generic fibre of V, and its canonical comparison isomorphism
gives e and the two required projection equations. Empty U causes no problem.

(blueprint: lem-sbc-generic-fibre-affine-open-lift) -/
theorem exists_affine_open_lift_of_generic_fibre
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) (η : S) (hη : IsGenericPoint η Set.univ)
    (U : (f.fiber η).Opens) (hU : IsAffineOpen U) :
    ∃ V : X.Opens, IsAffineOpen V ∧
      ∃ e : (V.ι ≫ f).fiber η ≅ U.toScheme,
        e.hom ≫ U.ι ≫ f.fiberι η = (V.ι ≫ f).fiberι η ≫ V.ι ∧
        e.hom ≫ U.ι ≫ f.fiberToSpecResidueField η =
          (V.ι ≫ f).fiberToSpecResidueField η := by
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
  have base : S.fromSpecResidueField η ≫ S.topIso.inv = c.π.app k := by
    apply (cancel_mono (⊤ : S.Opens).ι).mp
    simp [c, nhdsCone, k, Scheme.fromSpecResidueField,
      Scheme.Opens.fromSpecStalkOfMem_ι]
  have H : IsPullback (f.fiberι η) (f.fiberToSpecResidueField η) f₀ (c.π.app k) := by
    exact (IsPullback.of_hasPullback f (S.fromSpecResidueField η)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) S.topIso.symm
      (by simp [Scheme.Hom.fiberι]) (by simp [Scheme.Hom.fiberToSpecResidueField])
      (by simp [f₀]) (by simpa using base)
  let E := baseChangeDiagram D f₀
  let d := (baseChangeCone D c f₀).extend H.isoPullback.hom
  have hd : IsLimit d := (isLimitBaseChangeCone D c f₀ hc).ofIsoLimit
    (Cone.ext H.isoPullback.symm (fun j ↦ by
      change _ = H.isoPullback.inv ≫ H.isoPullback.hom ≫ _
      simp))
  have (j : Over k) : IsAffine (E.obj j) := by
    dsimp [E, baseChangeDiagram]
    infer_instance
  have {j l : Over k} (a : j ⟶ l) : IsAffineHom (E.map a) := by
    dsimp [E, baseChangeDiagram]
    infer_instance
  obtain ⟨j, O, hO, hpre⟩ := exists_isAffineOpen_preimage_eq E d hd U hU
  let q : E.obj j ⟶ X := pullback.fst f₀ (D.map j.hom)
  have : IsOpenImmersion (D.map j.hom) := by
    dsimp [D, nhdsDiagram]
    infer_instance
  have : IsOpenImmersion q := by dsimp [q]; infer_instance
  let V := q ''ᵁ O
  have hV : IsAffineOpen V := hO.image_of_isOpenImmersion q
  have fac : d.π.app j ≫ q = f.fiberι η := by
    change (H.isoPullback.hom ≫ (baseChangeCone D c f₀).π.app j) ≫
      pullback.fst f₀ (D.map j.hom) = _
    rw [Category.assoc, baseChangeCone_π_app_fst, H.isoPullback_hom_fst]
  have hUV : f.fiberι η ⁻¹ᵁ V = U := by
    rw [← fac, Scheme.Hom.comp_preimage]
    change d.π.app j ⁻¹ᵁ (q ⁻¹ᵁ q ''ᵁ O) = U
    rw [q.preimage_image_eq, hpre]
  refine ⟨V, hV, ?_⟩
  rw [← hUV]
  let HV := (isPullback_morphismRestrict (f.fiberι η) V).paste_vert
    (IsPullback.of_hasPullback f (S.fromSpecResidueField η))
  let e := HV.isoPullback.symm
  refine ⟨e, ?_, ?_⟩
  · have hh : e.hom ≫ (f.fiberι η ∣_ V) = (V.ι ≫ f).fiberι η :=
      HV.isoPullback_inv_fst
    simpa only [Category.assoc, morphismRestrict_ι] using congrArg (· ≫ V.ι) hh
  · exact HV.isoPullback_inv_snd

end AlgebraicGeometry
