/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

public import Mathlib.AlgebraicGeometry.Modules.Tilde

import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoHartogsAlgebraComparison
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineDepthTwoLocallyFreeModel
import WeilConjectures.AlgebraicGeometry.Morphisms.OpenRestrictionPushforwardComparison
import WeilConjectures.AlgebraicGeometry.Morphisms.OpenBaseChangeStructureModule

/-! # Affine depth-two hull of a finite etale pushforward

## References

* Stacks Project, Tags 0EBI and 0EBJ
* Stacks Project, Tag 0EY6 proof of (1), Tag 0G41(2), and Tag 0E9I

## Implementation details

The local kernel argument in `affine_depth_two_pushforward_hull` expands the depth calculation
of Tag 0EBI and does not require the integrality hypotheses of Tags 0EBI and 0EBJ.
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Depth is invariant under a semilinear equivalence of finite modules. -/
private theorem depth_eq_of_semilinear_equiv
    {R S M P : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [AddCommGroup M] [AddCommGroup P] [Module R M] [Module S P]
    [Module.Finite R M] [Module.Finite S P]
    (e : R ≃+* S) (a : M ≃+ P) (ha : ∀ r m, a (r • m) = e r • a m) :
    IsLocalRing.depth (R := R) M = IsLocalRing.depth (R := S) P := by
  have hle {R S M P : Type u}
      [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
      [AddCommGroup M] [AddCommGroup P] [Module R M] [Module S P]
      [Module.Finite R M] [Module.Finite S P]
      (e : R ≃+* S) (a : M ≃+ P)
      (ha : ∀ r m, a (r • m) = e r • a m) :
      IsLocalRing.depth (R := R) M ≤ IsLocalRing.depth (R := S) P := by
    classical
    cases subsingleton_or_nontrivial P with
    | inl hP =>
      have := hP
      have ht : IsLocalRing.maximalIdeal S • (⊤ : Submodule S P) = ⊤ :=
        Subsingleton.elim _ _
      simp [IsLocalRing.depth, Ideal.depth, ht]
    | inr hP =>
      have := hP
      have : Nontrivial M := a.surjective.nontrivial
      have hM : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson _)).symm
      have hP' : IsLocalRing.maximalIdeal S • (⊤ : Submodule S P) ≠ ⊤ :=
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson _)).symm
      simp only [IsLocalRing.depth, Ideal.depth, hM, hP', ↓reduceIte]
      apply sSup_le
      rintro n ⟨rs, hreg, hmem, rfl⟩
      apply le_sSup
      refine ⟨rs.map e, ?_, ?_, by simp⟩
      · apply (a.isRegular_congr ?_).mp hreg
        exact List.forall₂_map_right_iff.mpr
          (List.forall₂_same.mpr (fun r _ m ↦ ha r m))
      · intro r hr
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
        rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
        exact Ideal.mem_map_of_mem e (hmem t ht)
  apply le_antisymm (hle e a ha)
  apply hle e.symm a.symm
  intro r m
  apply a.injective
  simp only [a.apply_symm_apply]
  rw [ha, e.apply_symm_apply, a.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def direct_image_algebra_module_iso {L X : Scheme.{u}} (g : X ⟶ L) :
    let B : L.CommAlgebraSheaf := Under.mk
      (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
    B.toModule ≅ (Modules.pushforward g).obj (SheafOfModules.unit X.ringCatSheaf) := by
  exact Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- On an affine chart the actual pushforward is the coherent depth-two hull. -/
theorem affine_depth_two_pushforward_hull
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (hboundary : ∀ y : L, y ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y) (L.presheaf.stalk y))
    {X : Scheme.{u}} (f : X ⟶ U.toScheme) [IsFinite f] [Etale f]
    (V : L.Opens) (hV : IsAffineOpen V) :
    let g := f ≫ U.ι
    let B : L.CommAlgebraSheaf := Under.mk
      (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
    let N := Modules.restrict B.toModule hV.fromSpec
    N.IsQuasicoherent ∧
      Module.Finite (L.presheaf.obj (op V)) Γ(N, ⊤) ∧
      (∀ x : Spec (L.presheaf.obj (op V)), hV.fromSpec x ∉ U →
        ∃ hfinite : Module.Finite ((Spec (L.presheaf.obj (op V))).presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf x),
          letI := hfinite
          (2 : ℕ∞) ≤ IsLocalRing.depth
            (R := (Spec (L.presheaf.obj (op V))).presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf x)) := by
  classical
  dsimp only
  let A := L.presheaf.obj (op V)
  let j := hV.fromSpec
  let W := j ⁻¹ᵁ U
  let t := j ∣_ U
  let P := (Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  have : (SheafOfModules.unit X.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit X.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : P.IsFiniteLocallyFree :=
    Modules.isFiniteLocallyFree_pushforward f (SheafOfModules.unit X.ringCatSheaf)
  have : ((Modules.pullback t).obj P).IsFiniteLocallyFree := inferInstance
  have : (Modules.restrict P t).IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u}
      ((Modules.restrictFunctorIsoPullback t).app P).symm
  have hA : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hW (x : Spec A) (hx : x ∉ W) :
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec A).presheaf.stalk x) ((Spec A).presheaf.stalk x) := by
    let e := (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
    exact (hboundary (j x) hx).trans
      (depth_eq_of_semilinear_equiv e e.toAddEquiv (fun r m => e.map_mul r m)).le
  obtain ⟨H, hqc, hsections, hdepth, ⟨r⟩⟩ :=
    exists_affine_depth_two_locally_free_model A W hW (Modules.restrict P t)
  let g := f ≫ U.ι
  let B : L.CommAlgebraSheaf := Under.mk
    (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
  let N := Modules.restrict B.toModule j
  obtain ⟨c⟩ := Modules.nonempty_restrict_pushforward_open_iso j U P
  let b : N ≅ (Modules.pushforward W.ι).obj (Modules.restrict P t) :=
    (Modules.restrictFunctor j).mapIso
      (direct_image_algebra_module_iso g ≪≫
        ((Modules.pushforwardComp f U.ι).app (SheafOfModules.unit X.ringCatSheaf)).symm) ≪≫ c
  let f' := CategoryTheory.Limits.pullback.snd f t
  let g' := f' ≫ W.ι
  let C : (Spec A).CommAlgebraSheaf := Under.mk
    (⟨g'.c⟩ : (Spec A).sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).obj
        (CategoryTheory.Limits.pullback f t).sheaf)
  obtain ⟨d⟩ := Modules.nonempty_open_base_change_structure_module_iso j U f
  let d' : N ≅ C.toModule := d
  let rr : Modules.restrict H W.ι ≅ Modules.restrict C.toModule W.ι :=
    r ≪≫ ((Modules.restrictFunctorAdjCounitIso W.ι).app
      (Modules.restrict P t)).symm ≪≫ (Modules.restrictFunctor W.ι).mapIso (b.symm ≪≫ d')
  obtain ⟨⟨e'⟩, _⟩ := depth_two_hartogs_algebra_comparison W f' H hqc hsections hdepth ⟨rr⟩
  let e : H ≅ N := e' ≪≫ d'.symm
  refine ⟨?_, ?_, ?_⟩
  · exact (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso e hqc
  · have htop : Module.Finite Γ(Spec A, ⊤) Γ(H, ⊤) :=
      hsections ⊤ (isAffineOpen_top (Spec A))
    have hfinA : Module.Finite A Γ(H, ⊤) :=
      @Modules.finite_sections_top_of_finite A H htop
    let a : Γ(H, ⊤) ≃ₗ[A] Γ(N, ⊤) :=
      ((moduleSpecΓFunctor (R := A)).mapIso e).toLinearEquiv
    have := hfinA
    exact Module.Finite.of_surjective a.toLinearMap a.surjective
  · intro x hx
    obtain ⟨hfinite, hd⟩ := hdepth x hx
    let a : (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x) ≃ₗ[
        (Spec A).presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf x) :=
      ((RingedSpace.moduleStalkFunctor (Spec A).toRingedSpace x).mapIso e).toLinearEquiv
    have hfinite' : Module.Finite ((Spec A).presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf x) := by
      have := hfinite
      exact Module.Finite.of_surjective a.toLinearMap a.surjective
    exact ⟨hfinite', hd.trans_eq (depth_eq_of_semilinear_equiv (RingEquiv.refl _)
      a.toAddEquiv (fun r m => a.map_smul r m))⟩

end AlgebraicGeometry.Scheme
