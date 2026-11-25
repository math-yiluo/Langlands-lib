/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange

/-! # Affine coefficient generators

Source: Stacks Project, Tags 02KG, 01I9, 01IA and 0097.
(blueprint: lem-pc-coefficient-target-section-generators).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct BigOperators
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Affine pullback sections are finite sums of section-ring multiples of unit sections.
Source: Stacks Project, Tags 01I9 and 01IA (affine pullback), 0097 (restriction).
(blueprint: lem-pc-coefficient-target-section-generators).

Proof: Let I = W intersect fprime inverse image B and V be the image of Z in X.
The affine intersection base-change theorem makes I affine. The open V is affine
because it is isomorphic to Z. Its restricted module is quasi-coherent. Apply the
affine pullback sections theorem to I -> V: its tensor comparison is surjective,
so tensor induction writes each section as a finite sum of target-ring multiples
of the pullback unit of sections on V. Transport tensorPullback to pullback by
uniqueness of left adjoints, with the unit equation. The restriction isomorphism
identifies sections on V with sections on Z; naturality of the unit and composition
of restrictions give precisely the displayed generators. Empty opens give the
zero module, represented by a sum indexed by Fin 0. -/
theorem coefficientTarget_section_generators
    {X T : Scheme.{u}} (f : X ⟶ T) [IsSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) (hB : IsAffineOpen B) :
    letI : Algebra Γ(U.toScheme, ⊤) Γ(T', B) :=
      (g.appLE ⊤ B (by simp)).hom.toAlgebra
    let N := (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
          ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
    let M := (pullback g').obj F
    ∀ y : Γ(M, W ⊓ f' ⁻¹ᵁ B),
      ∃ (n : ℕ) (a : Fin n → Γ(X', W ⊓ f' ⁻¹ᵁ B)) (s : Fin n → N),
        y = ∑ i, a i •
          (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW (s i))) := by
  classical
  dsimp only
  let V := (f ⁻¹ᵁ U).ι ''ᵁ Z
  let I := W ⊓ f' ⁻¹ᵁ B
  have hV : IsAffineOpen V := hZ.image_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  obtain ⟨_, ha⟩ := finiteAffineCech_intersection_baseChange f U hU Z hZ g g' f' sq
  have : IsAffineHom (W.ι ≫ f') := by rw [hW]; exact ha
  have hI : IsAffineOpen I := by
    have h := (hB.preimage (W.ι ≫ f')).image_of_isOpenImmersion W.ι
    simpa only [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, I] using h
  have hIV : I ≤ g' ⁻¹ᵁ V := by rw [← hW]; exact inf_le_left
  let adj := Classical.choose (exists_tensorPullbackAdjunction g')
  let e := (adj.leftAdjointUniq (pullbackPushforwardAdjunction g')).app F
  let er := F.restrictAppIso (f ⁻¹ᵁ U).ι Z
  let : Algebra Γ(X, V) Γ(X', I) := (g'.appLE V I hIV).hom.toAlgebra
  obtain ⟨c, hc, _, ht, _⟩ := exists_tensorPullback_affine_sections
    g' ⟨V, hV⟩ ⟨I, hI⟩ hIV
  have hunit (s : Γ(F, V)) :
      e.hom.app (g' ⁻¹ᵁ V) ((adj.unit.app F).app V s) =
        ((pullbackPushforwardAdjunction g').unit.app F).app V s := by
    have h := adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction g') F
    exact congrArg (fun q ↦ q.app V s) h
  have hgen (s : Γ(F, V)) (a : Γ(X', I)) :
      e.hom.app I (c F inferInstance (s ⊗ₜ[Γ(X, V)] a)) =
        a • (((pullback g').obj F).presheaf.map (homOfLE inf_le_left).op
          (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW (er.inv s))) := by
    rw [ht, Hom.app_smul]
    congr 1
    have hn := e.hom.val.naturality (homOfLE hIV).op
    have hn' := congrArg (fun q ↦ q ((adj.unit.app F).app V s)) hn
    simp only [ConcreteCategory.comp_apply] at hn'
    change e.hom.app I
        (((tensorPullback g').obj F).presheaf.map (homOfLE hIV).op
          ((adj.unit.app F).app V s)) = _
    change e.hom.app I
        (((tensorPullback g').obj F).presheaf.map (homOfLE hIV).op
          ((adj.unit.app F).app V s)) =
        ((pullback g').obj F).presheaf.map (homOfLE hIV).op
          (e.hom.app (g' ⁻¹ᵁ V) ((adj.unit.app F).app V s)) at hn'
    rw [hn', hunit]
    dsimp only [coefficientPullbackGenerator]
    have her : er.hom (er.inv s) = s := by
      exact ConcreteCategory.comp_apply er.inv er.hom s |>.symm.trans
        (by simp)
    rw [her]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  intro y
  obtain ⟨t, ht'⟩ := (hc F inferInstance).2 (e.inv.app I y)
  have hy : e.hom.app I (c F inferInstance t) = y := by
    rw [ht']
    exact (ConcreteCategory.comp_apply (e.inv.app I) (e.hom.app I) y).symm.trans
      (by simp [← Hom.comp_app])
  rw [← hy]
  clear ht' hy y
  induction t using TensorProduct.inductionOn with
  | tmul s a =>
    refine ⟨1, fun _ ↦ a, fun _ ↦ er.inv s, ?_⟩
    simpa using hgen s a
  | add t t' h h' =>
    obtain ⟨n, a, s, hs⟩ := h
    obtain ⟨n', a', s', hs'⟩ := h'
    refine ⟨n + n', Fin.addCases a a', Fin.addCases s s', ?_⟩
    simp only [map_add, hs, hs', Fin.sum_univ_add, Fin.addCases_left,
      Fin.addCases_right]

end
end AlgebraicGeometry.Scheme.Modules
