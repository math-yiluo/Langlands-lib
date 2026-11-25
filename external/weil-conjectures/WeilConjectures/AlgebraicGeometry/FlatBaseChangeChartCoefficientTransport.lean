/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeChartUnitIso

/-! # Coefficient h-maps on the affine scalar-extension chart

Source: Stacks Project, Tags 02KH, 0096 and 0097.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

set_option backward.isDefEq.respectTransparency false in
private theorem exists_pushforward_iso_coefficient_inverse
    {L T : Scheme.{u}} (σ : L ≅ T) (A : T.Modules) (M : L.Modules)
    (β : A ≅ (pushforward σ.hom).obj M) :
    ∃ ψ : M ⟶ (pushforward σ.inv).obj A,
      (β.hom ≫ (pushforward σ.hom).map ψ ≫
        (pushforwardComp σ.inv σ.hom).hom.app A ≫
        (pushforwardCongr σ.inv_hom_id).hom.app A = (pushforwardId T).inv.app A) ∧
      (ψ ≫ (pushforward σ.inv).map β.hom ≫
        (pushforwardComp σ.hom σ.inv).hom.app M ≫
        (pushforwardCongr σ.hom_inv_id).hom.app M = (pushforwardId L).inv.app M) := by
  let ψ := (pushforwardId L).inv.app M ≫
    (pushforwardCongr σ.hom_inv_id).inv.app M ≫
    (pushforwardComp σ.hom σ.inv).inv.app M ≫ (pushforward σ.inv).map β.inv
  refine ⟨ψ, ?_, ?_⟩
  · ext U x
    have eU : σ.inv ⁻¹ᵁ σ.hom ⁻¹ᵁ U = U := by
      rw [← Scheme.Hom.comp_preimage, σ.inv_hom_id]
      simp
    have hn := β.inv.mapPresheaf.naturality (eqToHom eU).op
    have hx := ConcreteCategory.congr_hom hn (β.hom.app U x)
    simp only [mapPresheaf_app, pushforward_obj_presheaf_map,
      ConcreteCategory.comp_apply] at hx
    simp only [ψ, Hom.comp_app, pushforward_map_app, pushforward_obj_obj,
      Hom.id_base, Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
      pushforwardComp_hom_app_app, pushforwardComp_inv_app_app, Functor.comp_obj,
      pushforwardCongr_hom_app_app, pushforwardCongr_inv_app_app,
      eqToHom_op, Category.id_comp, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
      Function.comp_apply, pushforwardId_inv_app_app, Functor.id_obj,
      AddCommGrpCat.hom_id]
    erw [hx]
    simp only [← ConcreteCategory.comp_apply, ← Hom.comp_app,
      β.hom_inv_id, Hom.id_app, Category.id_comp]
    rw [← Functor.map_comp]
    simp
  · simp [ψ]


private theorem chart_geometry
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V) [Algebra Γ(S, V) Γ(S', W)]
    (hAlgebra : algebraMap Γ(S, V) Γ(S', W) = (g.appLE V W eVW).hom) :
    let L := (Limits.pullback.fst g f) ⁻¹ᵁ W
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    ∃ σ : L.toScheme ≅ baseChangedScheme (S := Γ(S', W)) h,
      σ.hom ≫ baseChangeFst (S := Γ(S', W)) h =
        (Limits.pullback.snd g f).resLE (f ⁻¹ᵁ V) L (by
          rw [flatBaseChangeOpenEquality f g V]
          exact (Limits.pullback.fst g f).preimage_mono eVW) ∧
      σ.hom ≫ baseChangeSnd (S := Γ(S', W)) h =
        (Limits.pullback.fst g f).resLE W L le_rfl ≫ W.toSpecΓ := by
  let L := (Limits.pullback.fst g f) ⁻¹ᵁ W
  have e : L ≤ (Limits.pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [flatBaseChangeOpenEquality f g V]
    exact (Limits.pullback.fst g f).preimage_mono eVW
  have H := Scheme.Hom.isPullback_resLE
    (IsPullback.of_hasPullback g f).flip eVW le_rfl
    (show L = (Limits.pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓
      (Limits.pullback.fst g f) ⁻¹ᵁ W from (inf_eq_right.mpr e).symm)
  have ha : baseChangeMap Γ(S, V) Γ(S', W) = Spec.map (g.appLE V W eVW) := by
    unfold baseChangeMap
    congr 1
    exact CommRingCat.hom_ext hAlgebra
  have H' : IsPullback
      ((Limits.pullback.snd g f).resLE (f ⁻¹ᵁ V) L e)
      ((Limits.pullback.fst g f).resLE W L le_rfl ≫ W.toSpecΓ)
      (f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ)
      (baseChangeMap Γ(S, V) Γ(S', W)) := H.of_iso (Iso.refl _) (Iso.refl _) hW.isoSpec hV.isoSpec
    (by simp) (by simp [IsAffineOpen.isoSpec_hom])
    (by simp [IsAffineOpen.isoSpec_hom])
    (by simp [ha, IsAffineOpen.isoSpec_hom])
  exact ⟨H'.isoPullback, H'.isoPullback_hom_fst, H'.isoPullback_hom_snd⟩

attribute [local irreducible] pushforward pushforwardComp pushforwardCongr pushforwardId

set_option backward.isDefEq.respectTransparency false in
-- Elaborating the coefficient comparisons uses several module functors.
/-- The affine base-change chart and its coefficient h-maps, before taking cohomology.
Source: Stacks Project, Tags 02KH (first paragraph), 0096 and 0097.
(blueprint: new-flat-base-change-chart-coefficient-transport)

Proof: Restrict the original fibre-product square using isPullback_resLE. The
inequality L <= U identifies L with the intersection of the two inverse-image
opens. Transport this square by hV.isoSpec and hW.isoSpec; hAlgebra and
Scheme.Opens.toSpecΓ_SpecMap_appLE identify its lower map with baseChangeMap.
The resulting isoPullback supplies sigma and both projection equations.

Undo the restriction/pullback comparison and the pushforward composition and
congruence comparisons on D.psi followed by restriction to L, obtaining b.
Define phi to be the inverse pullback adjunction hom-equivalence applied to b.
The fixed-chart theorem isIso_flatBaseChange_chart_unit_adjoint supplies its
invertibility. Construct psi using pushforward of phi inverse along sigma.inv
and the inverse identity/composition comparisons. Naturality on sections and
cancellation of equality transports prove the two reciprocal identities.
The second projection equation on global sections identifies the scalars;
pushforward_map_smulHom and smulHom_naturality then prove the scalar square.
Finally apply_symm_apply for the adjunction gives its unit followed by
pushforward(phi)=b. Cancel the comparison isomorphisms to obtain the displayed
unit square. No cohomology, Leray edge or invertibility of a base-change unit
is used. Only invertibility of this explicitly constructed coefficient map is
split off in the new fixed-chart theorem.
The construction also applies to empty opens and zero modules. -/
theorem exists_flatBaseChange_chart_coefficient_transport
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (F : X.Modules) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V) (D : FlatBaseChangeOpenChoices f g F I J V)
    [Algebra Γ(S, V) Γ(S', W)]
    (hAlgebra : algebraMap Γ(S, V) Γ(S', W) = (g.appLE V W eVW).hom) :
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (pullback (f ⁻¹ᵁ V).ι).obj F
    let T := baseChangedScheme (S := Γ(S', W)) h
    let A := baseChangedModule (S := Γ(S', W)) h N
    let G := (tensorPullback (pullback.snd g f)).obj F
    let U := (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
    let L := (pullback.fst g f) ⁻¹ᵁ W
    let e : L ≤ U := by
      change (pullback.fst g f) ⁻¹ᵁ W ≤ (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
      rw [flatBaseChangeOpenEquality f g V]
      exact (pullback.fst g f).preimage_mono eVW
    let M := (restrictFunctor L.ι).obj G
    let k := (pullback.fst g f).resLE W L le_rfl ≫ W.toSpecΓ
    let j := (Limits.pullback g f).homOfLE e
    let c := (restrictFunctorComp j U.ι).symm.app G ≪≫
      (restrictFunctorCongr ((Limits.pullback g f).homOfLE_ι e)).app G
    let r := (restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj G) ≫
      (pushforward j).map c.hom
    let q := (pullback.snd g f).resLE (f ⁻¹ᵁ V) U le_rfl
    let α := ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F).hom
    ∃ (σ : L.toScheme ≅ T)
      (φ : A ⟶ (pushforward σ.hom).obj M)
      (ψ : M ⟶ (pushforward σ.inv).obj A),
      (φ ≫ (pushforward σ.hom).map ψ ≫ (pushforwardComp σ.inv σ.hom).hom.app A ≫
        (pushforwardCongr σ.inv_hom_id).hom.app A = (pushforwardId T).inv.app A) ∧
      (ψ ≫ (pushforward σ.inv).map φ ≫ (pushforwardComp σ.hom σ.inv).hom.app M ≫
        (pushforwardCongr σ.hom_inv_id).hom.app M =
          (pushforwardId L.toScheme).inv.app M) ∧
      (∀ a : Γ(S', W),
        A.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫
          (baseChangeSnd (S := Γ(S', W)) h).appTop).hom a) ≫ φ =
        φ ≫ (pushforward σ.hom).map
          (M.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫ k.appTop).hom a))) ∧
      ∃ ef : σ.hom ≫ baseChangeFst (S := Γ(S', W)) h = j ≫ q,
        α ≫ baseChangeUnit (S := Γ(S', W)) h N ≫
          (pushforward (baseChangeFst (S := Γ(S', W)) h)).map φ ≫
          (pushforwardComp σ.hom (baseChangeFst (S := Γ(S', W)) h)).hom.app M ≫
          (pushforwardCongr ef).hom.app M =
        D.psi ≫ (pushforward q).map r ≫ (pushforwardComp j q).hom.app M := by
  let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
  let N := (pullback (f ⁻¹ᵁ V).ι).obj F
  let T := baseChangedScheme (S := Γ(S', W)) h
  let A := baseChangedModule (S := Γ(S', W)) h N
  let G := (tensorPullback (pullback.snd g f)).obj F
  let U := (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
  let L := (pullback.fst g f) ⁻¹ᵁ W
  let e : L ≤ U := by
      change (pullback.fst g f) ⁻¹ᵁ W ≤ (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
      rw [flatBaseChangeOpenEquality f g V]
      exact (pullback.fst g f).preimage_mono eVW
  let M := (restrictFunctor L.ι).obj G
  let k := (pullback.fst g f).resLE W L le_rfl ≫ W.toSpecΓ
  let j := (Limits.pullback g f).homOfLE e
  let c := (restrictFunctorComp j U.ι).symm.app G ≪≫
      (restrictFunctorCongr ((Limits.pullback g f).homOfLE_ι e)).app G
  let r := (restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj G) ≫
      (pushforward j).map c.hom
  let q := (pullback.snd g f).resLE (f ⁻¹ᵁ V) U le_rfl
  let a := (restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F
  obtain ⟨σ, hf, hk⟩ := chart_geometry f g V W hV hW eVW hAlgebra
  have ef : σ.hom ≫ baseChangeFst (S := Γ(S', W)) h = j ≫ q := by
    simpa only [j, q, Scheme.Hom.map_resLE] using hf
  let b : N ⟶ (pushforward (baseChangeFst (S := Γ(S', W)) h)).obj
      ((pushforward σ.hom).obj M) :=
    a.inv ≫ D.psi ≫ (pushforward q).map r ≫ (pushforwardComp j q).hom.app M ≫
      (pushforwardCongr ef).inv.app M ≫
      (pushforwardComp σ.hom (baseChangeFst (S := Γ(S', W)) h)).inv.app M
  let φ : A ⟶ (pushforward σ.hom).obj M :=
    (pullbackPushforwardAdjunction (baseChangeFst (S := Γ(S', W)) h)).homEquiv _ _ |>.symm b
  have hi : IsIso φ := isIso_flatBaseChange_chart_unit_adjoint
    f g F I J V W eVW D σ ef
  obtain ⟨ψ, hφψ, hψφ⟩ := exists_pushforward_iso_coefficient_inverse σ A M (asIso φ)
  refine ⟨σ, φ, ψ, hφψ, hψφ, ?_, ef, ?_⟩
  · intro z
    have hs := congrArg Scheme.Hom.appTop hk
    rw [Scheme.Hom.comp_appTop] at hs
    have hz : σ.hom.appTop
        (((Scheme.ΓSpecIso Γ(S', W)).inv ≫
          (baseChangeSnd (S := Γ(S', W)) h).appTop).hom z) =
        (((Scheme.ΓSpecIso Γ(S', W)).inv ≫ k.appTop).hom z) := by
      change (((Scheme.ΓSpecIso Γ(S', W)).inv ≫
        (baseChangeSnd (S := Γ(S', W)) h).appTop ≫ σ.hom.appTop).hom) z = _
      rw [hs]
    rw [← hz, pushforward_map_smulHom]
    exact smulHom_naturality φ _
  · have hu := (pullbackPushforwardAdjunction
        (baseChangeFst (S := Γ(S', W)) h)).homEquiv _ _ |>.apply_symm_apply b
    rw [Adjunction.homEquiv_unit] at hu
    change a.hom ≫ baseChangeUnit (S := Γ(S', W)) h N ≫
      (pushforward (baseChangeFst (S := Γ(S', W)) h)).map φ ≫
      (pushforwardComp σ.hom (baseChangeFst (S := Γ(S', W)) h)).hom.app M ≫
      (pushforwardCongr ef).hom.app M = _
    change a.hom ≫ (pullbackPushforwardAdjunction
      (baseChangeFst (S := Γ(S', W)) h)).unit.app N ≫ _ = _
    rw [reassoc_of% hu]
    simp only [b, Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_app, Category.comp_id]
    rfl


end AlgebraicGeometry.Scheme.Modules
