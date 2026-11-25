/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoefficientIntersectionRingData
public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Affine coefficient intersection computation

Source: Stacks Project, Tags 0097, 01I9, 01IA and 02KG.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback composition and open restriction transport sections and their unit generators.
No affineness or quasi-coherence is required.
Source: Stacks Project, Tags 0096 and 0097.

Proof: Uniqueness of left adjoints identifies tensorPullback k with pullback k.
The open-immersion restriction adjunction identifies F restricted to U with
pullback U.ι F. Pullback composition, followed by congruence for hk, identifies
pullback k (F restricted to U) with pullback g' F. Evaluate the inverse composite
on I. This is a linear isomorphism over Gamma(X',I), since each comparison is a
morphism of O_X'-modules. For the generator equation, expand coefficientPullbackGenerator.
The unit equation for restriction identifies the section s, after restrictAppIso,
with its open-immersion pullback unit. The composition unit equation identifies
its subsequent k-pullback unit with the g'-pullback unit. The tensorPullback
left-adjoint uniqueness unit equation identifies the remaining unit. Naturality
of all three module morphisms commutes with restriction to I. Restriction maps
compose, and proof irrelevance identifies the two inclusion proofs. This gives
the displayed equation, also for empty opens, without any affine argument. -/
private theorem exists_coefficientPullback_section_transport
    {X X' : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (Z : U.toScheme.Opens) (g' : X' ⟶ X) (k : X' ⟶ U.toScheme)
    (hk : k ≫ U.ι = g') (W I : X'.Opens)
    (hW : W = g' ⁻¹ᵁ (U.ι ''ᵁ Z)) (hIW : I ≤ W) (hIZ : I ≤ k ⁻¹ᵁ Z) :
    ∃ e : Γ((pullback g').obj F, I) ≃ₗ[Γ(X', I)]
        Γ((tensorPullback k).obj (F.restrict U.ι), I),
      ∀ s : Γ(F.restrict U.ι, Z),
        e (((pullback g').obj F).presheaf.map (homOfLE hIW).op
          (coefficientPullbackGenerator F U Z g' W hW s)) =
        ((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hIZ).op
          (((Classical.choose (exists_tensorPullbackAdjunction k)).unit.app
            (F.restrict U.ι)).val.app (op Z) s) := by
  classical
  let adjk := Classical.choose (exists_tensorPullbackAdjunction k)
  let adj₁ := (restrictAdjunction U.ι).comp adjk
  let adj₂ := pullbackPushforwardAdjunction g'
  let rightIso : pushforward k ⋙ pushforward U.ι ≅ pushforward g' :=
    pushforwardComp k U.ι ≪≫ pushforwardCongr hk
  let q := (adj₁.leftAdjointUniq (adj₂.ofNatIsoRight rightIso.symm)).app F
  let l : Γ((pullback g').obj F, I) →ₗ[Γ(X', I)]
      Γ((tensorPullback k).obj (F.restrict U.ι), I) := (q.inv).val.app (op I) |>.hom
  have hl : Function.Bijective l := by
    exact ConcreteCategory.bijective_of_isIso ((q.inv).app I)
  let e := LinearEquiv.ofBijective l hl
  refine ⟨e, ?_⟩
  intro s
  apply (ConcreteCategory.bijective_of_isIso ((q.hom).app I)).injective
  change (q.hom).app I ((q.inv).app I _) = (q.hom).app I _
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, q.inv_hom_id, Hom.id_app,
    ConcreteCategory.id_apply]
  let J := U.ι ''ᵁ Z
  let V := U.ι ⁻¹ᵁ J
  let P := k ⁻¹ᵁ V
  have hV : V = Z := U.ι.preimage_image_eq Z
  have hIP : I ≤ P := by simpa only [P, hV] using hIZ
  have hu := adj₁.unit_leftAdjointUniq_hom_app
    (adj₂.ofNatIsoRight rightIso.symm) F
  have hv := congrArg (fun a ↦ a.app J ((F.restrictAppIso U.ι Z).hom s)) hu
  simp only [adj₁, Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    Hom.comp_app, pushforward_map_app, Functor.comp_map, ConcreteCategory.comp_apply,
    NatTrans.comp_app] at hv
  have H := congrArg (fun x ↦ ((pullback g').obj F).presheaf.map
    (homOfLE hIP).op x) hv
  have hR (z : Γ((pullback g').obj F, g' ⁻¹ᵁ J)) :
      ((pullback g').obj F).presheaf.map (homOfLE hIP).op
        ((rightIso.inv.app ((pullback g').obj F)).app J z) =
      ((pullback g').obj F).presheaf.map
        (homOfLE (hIW.trans hW.le)).op z := by
    simp only [rightIso, Iso.trans_inv, NatTrans.comp_app, Hom.comp_app,
      ConcreteCategory.comp_apply, pushforwardComp_inv_app_app,
      pushforwardCongr_inv_app_app]
    have hPG : P = g' ⁻¹ᵁ J := congrArg (fun a ↦ a ⁻¹ᵁ J) hk
    change ((pullback g').obj F).presheaf.map (homOfLE hIP).op
      (((pullback g').obj F).presheaf.map (eqToHom hPG).op z) = _
    erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hη := (adjk.unit.app (F.restrict U.ι)).mapPresheaf.naturality
    (homOfLE hV.ge).op
  have hη' := congrArg (fun a ↦ a
    (((restrictAdjunction U.ι).unit.app F).app J
      ((F.restrictAppIso U.ι Z).hom s))) hη
  have hres : (F.restrict U.ι).presheaf.map (homOfLE hV.ge).op
      (((restrictAdjunction U.ι).unit.app F).app J
        ((F.restrictAppIso U.ι Z).hom s)) = s := by
    change F.presheaf.map (U.ι.opensFunctor.map (homOfLE hV.ge)).op
      (F.presheaf.map (homOfLE (U.ι.image_preimage_le J)).op s) = s
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    change F.presheaf.map (𝟙 (op J)) s = s
    simp only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  simp only [ConcreteCategory.comp_apply, Functor.id_obj] at hη'
  erw [hres] at hη'
  have hq := q.hom.mapPresheaf.naturality (homOfLE hIP).op
  have hq' := congrArg (fun a ↦ a
    ((adjk.unit.app (F.restrict U.ι)).app V
      (((restrictAdjunction U.ι).unit.app F).app J
        ((F.restrictAppIso U.ι Z).hom s)))) hq
  simp only [Functor.comp_obj, ConcreteCategory.comp_apply] at hq'
  change ((pullback g').obj F).presheaf.map (homOfLE hIP).op
      ((q.hom).app P ((adjk.unit.app (F.restrict U.ι)).app V
        (((restrictAdjunction U.ι).unit.app F).app J
          ((F.restrictAppIso U.ι Z).hom s)))) = _ at H
  erw [← hq'] at H
  change (q.hom).app I
      (((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hIP).op
        ((adjk.unit.app (F.restrict U.ι)).app V
          (((restrictAdjunction U.ι).unit.app F).app J
            ((F.restrictAppIso U.ι Z).hom s)))) =
    ((pullback g').obj F).presheaf.map (homOfLE hIP).op
      ((rightIso.inv.app ((pullback g').obj F)).app J
        ((adj₂.unit.app F).app J ((F.restrictAppIso U.ι Z).hom s))) at H
  erw [hR] at H
  have hZP : k ⁻¹ᵁ Z ≤ P := by
    dsimp only [P]
    rw [hV]
  have hηI := congrArg (fun x ↦
    ((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hIZ).op x) hη'
  change ((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hIZ).op
      ((adjk.unit.app (F.restrict U.ι)).app Z s) =
    ((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hIZ).op
      (((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hZP).op
        ((adjk.unit.app (F.restrict U.ι)).app V
          (((restrictAdjunction U.ι).unit.app F).app J
            ((F.restrictAppIso U.ι Z).hom s)))) at hηI
  have hcomp :
      ((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hZP).op ≫
        ((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hIZ).op =
      ((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hIP).op := by
    rw [← Functor.map_comp]
    rfl
  erw [← ConcreteCategory.comp_apply
    (f := ((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hZP).op)
    (g := ((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hIZ).op),
    hcomp] at hηI
  change _ = ((tensorPullback k).obj (F.restrict U.ι)).presheaf.map (homOfLE hIP).op
    ((adjk.unit.app (F.restrict U.ι)).app V
      (((restrictAdjunction U.ι).unit.app F).app J
        ((F.restrictAppIso U.ι Z).hom s))) at hηI
  erw [← hηI] at H
  change ((pullback g').obj F).presheaf.map (homOfLE hIW).op
    (((pullback g').obj F).presheaf.map (homOfLE hW.le).op
      ((adj₂.unit.app F).app J ((F.restrictAppIso U.ι Z).hom s))) = _
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact H.symm


/-- Affine pullback sections, before the ring pushout and tensor contraction.
Source: Stacks Project, Tags 0097, 01I9 and 01IA.
(blueprint: aux-pc-coefficient-intersection-section-model).

Proof: The intersection I = W intersect f' inverse image B is affine by the
intersection base-change theorem. Restrict F to the affine open Z of f inverse
image U. Apply the affine pullback sections theorem to the restricted lift
X' -> f inverse image U on Z and I. Compare tensorPullback with pullback by
uniqueness of left adjoints, and compare open-immersion pullback with
restriction. Pullback composition identifies the resulting module with M|I.
The conjugate-isomorphism unit equation and restriction naturality identify
the image of the restricted pullback-unit generator with 1 tensor s.
The inverse of the affine sections comparison is the required map, linear
for the intersection ring. Empty intersections satisfy the same formula. -/
theorem exists_coefficientIntersection_section_model
    {X T : Scheme.{u}} (f : X ⟶ T) [IsSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) (hB : IsAffineOpen B) :
    let D := Γ((f ⁻¹ᵁ U).toScheme, Z)
    let S := Γ(X', W ⊓ f' ⁻¹ᵁ B)
    let : Algebra D S := (coefficientIntersectionRingMap f U Z g g' f' sq W hW B).toAlgebra
    let M := (pullback g').obj F
    ∃ e : Γ(M, W ⊓ f' ⁻¹ᵁ B) →ₗ[S]
        (S ⊗[D] Γ(F.restrict (f ⁻¹ᵁ U).ι, Z)),
      ∀ s : Γ(F.restrict (f ⁻¹ᵁ U).ι, Z),
        e (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
          (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s)) =
        (1 : S) ⊗ₜ[D] s := by
  classical
  dsimp only
  let k := coefficientRestrictedLift f U g g' f' sq
  let I := W ⊓ f' ⁻¹ᵁ B
  let D := Γ((f ⁻¹ᵁ U).toScheme, Z)
  let S := Γ(X', I)
  let G := F.restrict (f ⁻¹ᵁ U).ι
  let : Algebra D S :=
    (coefficientIntersectionRingMap f U Z g g' f' sq W hW B).toAlgebra
  have hk : k ≫ (f ⁻¹ᵁ U).ι = g' :=
    ((isPullback_morphismRestrict f U).flip).lift_fst _ _ _
  have hIZ : I ≤ k ⁻¹ᵁ Z := coefficientIntersection_le f U Z g g' f' sq W hW B
  have ha := finiteAffineCech_intersection_baseChange f U hU Z hZ g g' f' sq
  have : IsAffineHom (W.ι ≫ f') := by
    rw [hW]
    exact ha.2
  have hI : IsAffineOpen I := by
    have hb := hB.preimage (W.ι ≫ f')
    have he : W.ι ''ᵁ ((W.ι ≫ f') ⁻¹ᵁ B) = I := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι]
    rw [← he]
    exact W.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hb
  obtain ⟨t, ht⟩ := exists_coefficientPullback_section_transport F (f ⁻¹ᵁ U) Z g' k
    hk W I hW inf_le_left hIZ
  obtain ⟨c, hc, hs, hp, _⟩ :=
    exists_tensorPullback_affine_sections k ⟨Z, hZ⟩ ⟨I, hI⟩ hIZ
  let c' : (S ⊗[D] Γ(G, Z)) →ₗ[S] Γ((tensorPullback k).obj G, I) :=
    { toFun := fun x ↦ c G inferInstance ((TensorProduct.comm D _ S).symm x)
      map_add' := by intros; simp
      map_smul' := by
        intro b x
        have H := hs G inferInstance b ((TensorProduct.comm D _ S).symm x)
        change c G _ ((TensorProduct.comm D _ S).symm
          (b • (TensorProduct.comm D _ S)
            ((TensorProduct.comm D _ S).symm x))) = _ at H
        simpa only [LinearEquiv.apply_symm_apply, RingHom.id_apply] using H }
  have hc' : Function.Bijective c' := (hc G inferInstance).comp
    (TensorProduct.comm D _ S).symm.bijective
  let e := LinearEquiv.ofBijective c' hc'
  refine ⟨e.symm.toLinearMap.comp t.toLinearMap, ?_⟩
  intro s
  change e.symm (t _) = _
  apply e.injective
  rw [e.apply_symm_apply, ht]
  change _ = c G inferInstance (s ⊗ₜ[D] (1 : S))
  rw [hp]
  simp only [one_smul]
  rfl

end
end AlgebraicGeometry.Scheme.Modules
