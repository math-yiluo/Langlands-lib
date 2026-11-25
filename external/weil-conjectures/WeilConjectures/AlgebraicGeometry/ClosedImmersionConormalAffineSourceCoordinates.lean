/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalAffineTensorCoordinates
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.AffineConormalSections

/-! # Normalized affine coordinates for conormal sections

Source: Stacks Project, Morphisms, Lemma 0473 and Schemes, Lemma 01JU (1).
(blueprint: lem-weil-pbc-closed-immersion-conormal-affine-source-coordinates).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

noncomputable local instance {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (j : U ⟶ V) :
    SMul Γ(X, U)
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map j.op).hom).obj
        (M.val.obj (.op U))) :=
  inferInstanceAs (SMul Γ(X, U) Γ(M, U))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine source coordinate for the iterated tensor pullback, normalized on
scalar multiples of the successive adjunction units of ideal sections.
No conormal morphism or target coordinate occurs in this statement.

Source: Stacks Project, Morphisms, Lemma 0473, affine reduction; Schemes,
Lemma 01JU (1); Morphisms, Lemma 01R3 (2).
(blueprint: lem-weil-pbc-closed-immersion-conormal-affine-source-coordinates).

Proof:
1. The tensor-coordinate lemma identifies the ambient tensor B tensor_A J/J² with
   the tensor of conormal sections over the affine source chart rings. Its formula
   sends b tensor class(a) to unit(s') tensor i.app(b).
2. The conormal is quasi-coherent by affine_conormal_sections. Apply the affine
   pullback section comparison to f on V' = i' inverse image U' and V = i inverse
   image U, and turn its bijective linear map into an additive equivalence d.
   Compose the tensor-coordinate equivalence with d and invert to obtain eS.
3. The pure-tensor formulas of both equivalences give the successive units and
   scalar i.app(b). Expand the pushforward composition and equality-transport
   components. The restriction followed by equality transport equals the direct
   restriction: use the presheaf composition law and uniqueness of arrows in the
   opposite category of opens. This proves the displayed normalization. -/
theorem closedImmersion_conormal_affine_source_coordinates
    {X Z X' Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (hc : IsLimit (PullbackCone.mk i f h))
    (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1) :
    letI : Algebra Γ(X', U'.1) Γ(X, U.1) := (g.appLE U'.1 U.1 H).hom.toAlgebra
    let S := (tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules)
    ∃ eS : Γ(S, i ⁻¹ᵁ U.1) ≃+ Γ(X, U.1) ⊗[Γ(X', U'.1)]
        (i'.ker.ideal U').Cotangent,
      (∀ (b : Γ(X, U.1)) (a : i'.ker.ideal U') (s' : Γ(i'.ker.toModules, U'.1)),
        i'.ker.toModulesι.app U'.1 s' = (a : Γ(X', U'.1)) →
        eS.symm (b ⊗ₜ[Γ(X', U'.1)] (i'.ker.ideal U').toCotangent a) =
          i.app U.1 b • S.val.map (homOfLE (i.preimage_mono H)).op
            ((((Classical.choose (exists_tensorPullbackAdjunction i')).unit.app
                i'.ker.toModules) ≫
              (pushforward i').map
                (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
                  ((tensorPullback i').obj i'.ker.toModules))) ≫
              (pushforwardComp f i').hom.app S ≫
              (pushforwardCongr h.symm).hom.app S).app U'.1 s')) := by
  classical
  dsimp only
  let : Algebra Γ(X', U'.1) Γ(X, U.1) := (g.appLE U'.1 U.1 H).hom.toAlgebra
  let V' : Z'.affineOpens := ⟨i' ⁻¹ᵁ U'.1, U'.2.preimage i'⟩
  let V : Z.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  have K : V.1 ≤ f ⁻¹ᵁ V'.1 := by
    change i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ i' ⁻¹ᵁ U'.1
    rw [← Scheme.Hom.comp_preimage, ← h, Scheme.Hom.comp_preimage]
    exact i.preimage_mono H
  let : Algebra Γ(Z', V'.1) Γ(Z, V.1) := (f.appLE V'.1 V.1 K).hom.toAlgebra
  let : ∀ G : Z'.Modules, Module Γ(Z', V'.1) Γ((tensorPullback f).obj G, V.1) :=
    fun G ↦ Module.compHom _ (f.appLE V'.1 V.1 K).hom
  let T := (tensorPullback i').obj i'.ker.toModules
  let S := (tensorPullback f).obj T
  obtain ⟨e, he⟩ := closedImmersion_conormal_affine_tensor_coordinates
    i i' g f h hc U U' H
  obtain ⟨c, hc, _, hp, _⟩ := exists_tensorPullback_affine_sections f V' V K
  let d := (LinearEquiv.ofBijective (c T (affine_conormal_sections.{u, u} i').1)
    (hc T (affine_conormal_sections.{u, u} i').1)).toAddEquiv
  refine ⟨(e.trans d).symm, ?_⟩
  intro b a s' hs'
  change d (e (b ⊗ₜ[Γ(X', U'.1)] (i'.ker.ideal U').toCotangent a)) = _
  rw [he b a s' hs']
  rw [show d _ = _ from hp T (affine_conormal_sections.{u, u} i').1 _ _]
  congr 1
  simp only [Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app, ConcreteCategory.comp_apply]
  change S.val.map (homOfLE K).op _ =
    S.val.map (homOfLE (i.preimage_mono H)).op (S.val.map _ _)
  rw [← PresheafOfModules.map_comp_apply]
  apply congrArg (fun k ↦ S.val.map k _)
  exact Subsingleton.elim _ _

end AlgebraicGeometry.Scheme.Modules
