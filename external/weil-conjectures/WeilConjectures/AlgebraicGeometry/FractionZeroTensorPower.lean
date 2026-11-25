/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
import WeilConjectures.Topology.ModuleCohomologyTopComparison

/-! # Tensor-power annihilation from zero cohomology fractions

Source: Stacks Project, Cohomology of Schemes, Tags 01XR and 09MR
(blueprint: lem-sc-section-affine-open-kills-cohomology-localization-step).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

-- The next two coherence proofs are reused from the private helpers of
-- WeilConjectures.AlgebraicGeometry.InvertibleSectionRing; neither requires invertibility.
private theorem tensorPowAddIso_zero_inv {X : Scheme.{u}} (L : X.Modules) (n : ℕ) :
    (L.tensorPowAddIso n 0).inv = (ρ_ (L.tensorPow n)).hom := by
  induction n with
  | zero =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      eqToHom_refl, Category.comp_id]
    exact unitors_equal
  | succ n ih =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      eqToHom_refl, Category.comp_id, tensorIso_inv, Iso.refl_inv, ih]
    simp only [id_tensorHom, rightUnitor_tensor_hom, tensorPow_succ]
    rfl

private theorem tensorPowAddIso_assoc_inv {X : Scheme.{u}} (L : X.Modules) (i j k : ℕ) :
    (L.tensorPowAddIso i j).inv ▷ L.tensorPow k ≫
      (L.tensorPowAddIso (i + j) k).inv =
    (α_ (L.tensorPow i) (L.tensorPow j) (L.tensorPow k)).hom ≫
      L.tensorPow i ◁ (L.tensorPowAddIso j k).inv ≫
      (L.tensorPowAddIso i (j + k)).inv ≫
      eqToHom (congrArg L.tensorPow (Nat.add_assoc i j k).symm) := by
  induction i with
  | zero =>
    dsimp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv]
    rw [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc,
      ← eqToHom_iso_inv_naturality (fun n ↦ L.tensorPowAddIso n k) (Nat.zero_add j).symm]
    simp only [Category.assoc, eqToHom_trans]
    simp only [← Category.assoc]
    congr 1
    monoidal
  | succ i ih =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorPow_succ, tensorIso_inv, Iso.refl_inv, id_tensorHom]
    rw [comp_whiskerRight, comp_whiskerRight, eqToHom_whiskerRight,
      Category.assoc, Category.assoc,
      ← eqToHom_iso_inv_naturality (fun n ↦ L.tensorPowAddIso n k)
        (Nat.succ_add i j).symm]
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorIso_inv, Iso.refl_inv, id_tensorHom, Category.assoc, eqToHom_trans]
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc, ih]
    simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_eqToHom, eqToHom_trans]
    simp only [← Category.assoc]
    congr 1
    monoidal

private theorem tensorPowSection_add {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (a b : ℕ) :
    (λ_ (𝟙_ X.Modules)).inv ≫ (tensorPowSection s a ⊗ₘ tensorPowSection s b) ≫
      (L.tensorPowAddIso a b).inv = tensorPowSection s (a + b) := by
  apply (SheafOfModules.unitHomEquiv _).injective
  apply Subtype.ext
  funext U
  change ((λ_ (𝟙_ X.Modules)).inv ≫
    (tensorPowSection s a ⊗ₘ tensorPowSection s b) ≫
      (L.tensorPowAddIso a b).inv).app U.unop (unitSectionsEquiv U.unop 1) = _
  rw [Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, leftUnitor_inv_app, tensorHom_app_tmulSection]
  exact tensorPowAddIso_inv_app_tmulSection s a b U.unop

private theorem mulTensorPowSection_zero {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules) (a : ℕ) :
    mulTensorPowSection s F a 0 = 𝟙 _ := by
  simp only [mulTensorPowSection, tensorPowSection_zero, tensorPowAddIso_zero_inv,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  change (ρ_ (F ⊗ L.tensorPow a)).inv ≫
    (α_ F (L.tensorPow a) (𝟙_ X.Modules)).hom ≫ F ◁ (ρ_ (L.tensorPow a)).hom = _
  monoidal

private theorem mulTensorPowSection_comp {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules) (a b c : ℕ) :
    mulTensorPowSection s F a b ≫ mulTensorPowSection s F (a + b) c =
      mulTensorPowSection s F a (b + c) ≫
        eqToHom (congrArg (fun n ↦ F ⊗ L.tensorPow n) (Nat.add_assoc a b c).symm) := by
  simp only [mulTensorPowSection, Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    associator_naturality_middle_assoc]
  rw [← whiskerLeft_comp, tensorPowAddIso_assoc_inv]
  simp only [whiskerLeft_comp]
  rw [← tensorPowSection_add s b c]
  simp only [whiskerLeft_comp, Category.assoc, tensorHom_def, whiskerLeft_eqToHom]
  monoidal

private noncomputable def tensorSectionTransition {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules) (i j : ℕ) (h : i ≤ j) :
    F ⊗ L.tensorPow i ⟶ F ⊗ L.tensorPow j :=
  mulTensorPowSection s F i (j - i) ≫
    eqToHom (congrArg (fun n ↦ F ⊗ L.tensorPow n) (Nat.add_sub_of_le h))

private theorem mulTensorPowSection_cast {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules) (a : ℕ) {b c : ℕ} (h : b = c) :
    mulTensorPowSection s F a b ≫
      eqToHom (congrArg (fun n ↦ F ⊗ L.tensorPow (a + n)) h) =
        mulTensorPowSection s F a c := by
  subst c
  simp only [eqToHom_refl, Category.comp_id]

private theorem tensorSectionTransition_add {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules) (i b : ℕ) :
    tensorSectionTransition s F i (i + b) (Nat.le_add_right i b) =
      mulTensorPowSection s F i b := by
  change mulTensorPowSection s F i (i + b - i) ≫ _ = _
  exact mulTensorPowSection_cast s F i (Nat.add_sub_cancel_left i b)

private theorem tensorSectionTransition_eq {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules) (i j b : ℕ) (h : i ≤ j)
    (hb : i + b = j) :
    tensorSectionTransition s F i j h = mulTensorPowSection s F i b ≫
      eqToHom (congrArg (fun n ↦ F ⊗ L.tensorPow n) hb) := by
  subst j
  simpa only [eqToHom_refl, Category.comp_id] using tensorSectionTransition_add s F i b

private theorem tensorSectionTransition_self {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules) (i : ℕ) :
    tensorSectionTransition s F i i le_rfl = 𝟙 _ := by
  rw [tensorSectionTransition_eq s F i i 0 le_rfl rfl]
  simp only [eqToHom_refl, Category.comp_id, mulTensorPowSection_zero]

private theorem tensorSectionTransition_comp {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    tensorSectionTransition s F i j hij ≫ tensorSectionTransition s F j k hjk =
      tensorSectionTransition s F i k (hij.trans hjk) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hij
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [tensorSectionTransition_add, tensorSectionTransition_add, mulTensorPowSection_comp]
  exact (tensorSectionTransition_eq s F i (i + b + c) (b + c) _
    (Nat.add_assoc i b c).symm).symm

private theorem eqToHom_tmul_tensorPowSectionOne {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules) {a b : ℕ} (h : a = b)
    (U : X.Opens) (x : Γ(F, U)) :
    (eqToHom (congrArg (fun n ↦ F ⊗ L.tensorPow n) h)).app U
      (tmulSection x (tensorPowSectionOne s a U)) =
        tmulSection x (tensorPowSectionOne s b U) := by
  subst b
  rfl

private theorem tensorSectionTransition_from_zero {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules) (n : ℕ) (h : 0 ≤ n) :
    (ρ_ F).inv ≫ tensorSectionTransition s F 0 n h =
      (ρ_ F).inv ≫ F ◁ tensorPowSection s n := by
  apply hom_ext
  intro U
  ext x
  rw [rightUnitor_inv_comp_whiskerLeft_app]
  change (tensorSectionTransition s F 0 n h).app U ((ρ_ F).inv.app U x) = _
  rw [tensorSectionTransition_eq s F 0 n n h (Nat.zero_add n), Hom.comp_app,
    ConcreteCategory.comp_apply, rightUnitor_inv_app]
  change (eqToHom (congrArg (fun i ↦ F ⊗ L.tensorPow i) (Nat.zero_add n))).app U
    ((mulTensorPowSection s F 0 n).app U (tmulSection x (tensorPowSectionOne s 0 U))) = _
  rw [mulTensorPowSection_app_tmulSection]
  exact eqToHom_tmul_tensorPowSectionOne s F (Nat.zero_add n) U x

/-- If the degree-zero fraction presentation is zero, each global cohomology class
is killed by a tensor power of the section. This is only the denominator-clearing
step; it assumes neither an affine nonvanishing open nor a localization comparison.

Source: Stacks Project, Cohomology of Schemes, Lemma 01XR, conclusion from the
localization of Lemma 09MR (https://stacks.math.columbia.edu/tag/01XR).
(blueprint: lem-sc-section-affine-open-kills-cohomology-localization-step).

Proof: Forget the scalar action on module cohomology. Global module sections with
scalars forgotten are sections on the top open. Forgetting scalars is exact, so it
commutes with cohomology of an injective module resolution and gives a natural
additive isomorphism from global module cohomology to open module cohomology at top.
Transport xi through this isomorphism and through the map induced by the inverse
right unitor F -> F tensor L^0, obtaining a numerator eta in degree zero.
The hypothesis makes the fraction [0, eta] zero. The fraction presentation is the
additive direct limit of the groups H^p(X,F tensor L^n), with transitions induced
by mulTensorPowSection. These transitions compose because section powers multiply
and the tensor associators and unitors satisfy coherence. Its defining relations
are exactly the relations of cohomologyFractionRelations. In a directed colimit,
a component representing zero becomes zero at some later index e: equivalently,
write its relation as a finite sum of defining relations and push all terms to a
common index, where each relation cancels. Thus the transition from degree zero
to degree e kills eta. By the tensor coherence identities, its composite with the
inverse right unitor is (rho F).inv followed by F tensor s^e. Naturality of the
comparison with global module cohomology transports this equality back to the
claimed map applied to xi. -/
theorem exists_tensorPowSection_cohomology_eq_zero_of_subsingleton_fractions
    (X : Scheme.{u}) (L F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    (hsub : Subsingleton (CohomologyFractionPresentation L F s p ⊤))
    (xi : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    ∃ e : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace p).map
      ((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) e) xi = 0 := by
  classical
  let H := RingedSpace.openModuleCohomology X.toRingedSpace p ⊤
  let G (n : ℕ) : Type u := H.obj (F ⊗ L.tensorPow n : X.Modules)
  let f (i j : ℕ) (h : i ≤ j) : G i →+ G j :=
    (H.map (tensorSectionTransition (homOfGlobalSection L s) F i j h)).hom
  have : DirectedSystem G (fun i j h ↦ f i j h) := {
    map_self := fun {i} x ↦ by
      dsimp only [f]
      rw [tensorSectionTransition_self, H.map_id]
      rfl
    map_map := fun {k j i} hij hjk x ↦ by
      change (H.map (tensorSectionTransition (homOfGlobalSection L s) F j k hjk))
        ((H.map (tensorSectionTransition (homOfGlobalSection L s) F i j hij)) x) = _
      rw [← ConcreteCategory.comp_apply, ← H.map_comp, tensorSectionTransition_comp]
  }
  let v : (DirectSum ℕ G) →+ AddCommGroup.DirectLimit G f :=
    DirectSum.toAddMonoid (fun n ↦ AddCommGroup.DirectLimit.of G f n)
  have hv : cohomologyFractionRelations L F s p ⊤ ≤ v.ker := by
    apply (AddSubgroup.closure_le v.ker).2
    rintro z ⟨n, b, η, rfl⟩
    change v (DirectSum.of G n η - DirectSum.of G (n + b)
      (H.map (mulTensorPowSection (homOfGlobalSection L s) F n b) η)) = 0
    dsimp only [v]
    rw [map_sub, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    have he := AddCommGroup.DirectLimit.of_f (f := f) (Nat.le_add_right n b) η
    dsimp only [f] at he
    rw [tensorSectionTransition_add] at he
    exact sub_eq_zero.mpr he.symm
  let vbar := QuotientAddGroup.lift (cohomologyFractionRelations L F s p ⊤) v hv
  obtain ⟨e⟩ := RingedSpace.nonempty_moduleCohomology_top_iso X.toRingedSpace p
  let η : G 0 := H.map (ρ_ F).inv ((e.hom.app F).hom xi)
  have hη : cohomologyFraction L F s p ⊤ 0 η = 0 := hsub.elim _ _
  have hlim : AddCommGroup.DirectLimit.of G f 0 η = 0 := by
    have hz := congrArg vbar hη
    rw [map_zero] at hz
    change v (DirectSum.of G 0 η) = 0 at hz
    exact (DirectSum.toAddMonoid_of
      (fun n ↦ AddCommGroup.DirectLimit.of G f n) 0 η).symm.trans hz
  obtain ⟨n, hn, hz⟩ := AddCommGroup.DirectLimit.of.zero_exact 0 η hlim
  refine ⟨n, ?_⟩
  have hz' : H.map ((ρ_ F).inv ≫
      tensorSectionTransition (homOfGlobalSection L s) F 0 n hn)
        ((e.hom.app F).hom xi) = 0 := by
    rw [H.map_comp, ConcreteCategory.comp_apply]
    exact hz
  rw [tensorSectionTransition_from_zero] at hz'
  let m := (ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app (F ⊗ L.tensorPow n : X.Modules))).1
  rw [map_zero]
  have hnat := congrArg (fun f ↦ f.hom xi) (e.hom.naturality m)
  change (e.hom.app (F ⊗ L.tensorPow n : X.Modules)).hom
    ((RingedSpace.moduleCohomology X.toRingedSpace p).map m xi) =
      H.map m ((e.hom.app F).hom xi) at hnat
  exact hnat.trans hz'

end AlgebraicGeometry.Scheme.Modules
