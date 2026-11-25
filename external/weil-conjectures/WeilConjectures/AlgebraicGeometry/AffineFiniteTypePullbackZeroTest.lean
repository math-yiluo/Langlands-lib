/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# A finite test for vanishing after pullback from an affine open

Source: Stacks Project, Properties, Tag 01PB; Schemes, Tags 01I9 and 01IA;
Sheaves, Tag 0097.
(blueprint: lem-pc-affine-finite-type-pullback-zero-test).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite family of sections on an affine open tests vanishing after every pullback.
Source: Stacks Project, Properties, Tag 01PB; Schemes, Tags 01I9 and 01IA;
Sheaves, Tag 0097.
(blueprint: lem-pc-affine-finite-type-pullback-zero-test).

Proof: finite type and quasi-coherence imply that F(V) is a finite module over O(V).
Choose a finite spanning family. For any g, naturality of its pullback adjunction unit
identifies the image of each pulled-back generator with the pullback of its image
under δ. Hence the hypothesis kills all generators. On any affine open A contained
in g⁻¹(V), the affine pullback-sections comparison identifies sections of g*F with
F(V) tensor O(A); pure tensors of the spanning family generate this module. The
pulled-back map therefore vanishes on A. Affine opens contained in an arbitrary
W cover W. Naturality of δ with respect to restriction, followed by separatedness
of the target sheaf, implies its component on W is zero. No finiteness assumption
on G or g is required. An empty spanning family covers the zero module, and the
empty affine open causes no exception. -/
theorem exists_affine_finiteType_pullback_zero_test
    {Y : Scheme.{u}} (F : Y.Modules) (hF_ft : F.IsFiniteType)
    (hF_qc : F.IsQuasicoherent) (V : Y.Opens) (hV : IsAffineOpen V) :
    ∃ s : Finset Γ(F, V),
      ∀ (G : Y.Modules) (_hG_qc : G.IsQuasicoherent) (δ : F ⟶ G)
        (X : Scheme.{u}) (g : X ⟶ Y),
        (∀ x ∈ s, ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app G).val.app
          (op V) (δ.app V x) = 0) →
        ∀ (W : X.Opens), W ≤ g ⁻¹ᵁ V → ((tensorPullback g).map δ).app W = 0 := by
  classical
  have : Module.Finite Γ(Y, V) Γ(F, V) := finite_sections_of_finiteType F hV
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := Γ(Y, V)) (M := Γ(F, V)))
  refine ⟨s, ?_⟩
  intro G hG_qc δ X g hzero W hW
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  let e := ((δ ≫ adj.unit.app G).val.app (op V)).hom
  have he : ∀ x : Γ(F, V), e x = 0 := by
    have hk : Submodule.span Γ(Y, V) (s : Set Γ(F, V)) ≤ LinearMap.ker e := by
      apply Submodule.span_le.mpr
      intro x hx
      exact hzero x hx
    rw [hs] at hk
    intro x
    exact hk (Submodule.mem_top : x ∈ (⊤ : Submodule Γ(Y, V) Γ(F, V)))
  have hAffine (A : X.affineOpens) (hA : A.1 ≤ g ⁻¹ᵁ V) :
      ((tensorPullback g).map δ).app A.1 = 0 := by
    let : Algebra Γ(Y, V) Γ(X, A.1) := (g.appLE V A.1 hA).hom.toAlgebra
    let : ∀ H : Y.Modules, Module Γ(Y, V) Γ((tensorPullback g).obj H, A.1) :=
      fun H ↦ Module.compHom _ (g.appLE V A.1 hA).hom
    obtain ⟨c, hc, _, hpure, hn⟩ := exists_tensorPullback_affine_sections g ⟨V, hV⟩ A hA
    ext y
    obtain ⟨t, rfl⟩ := (hc F hF_qc).2 y
    rw [hn F G hF_qc hG_qc δ t]
    change c G hG_qc (TensorProduct.map (δ.val.app (op V)).hom LinearMap.id t) = 0
    induction t using TensorProduct.inductionOn with
    | tmul x b =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, hpure]
      have hx : (adj.unit.app G).val.app (op V) (δ.app V x) = 0 := he x
      change b • ((tensorPullback g).obj G).presheaf.map (homOfLE hA).op
        ((adj.unit.app G).val.app (op V) (δ.app V x)) = 0
      rw [hx]
      simp
    | add t t' ht ht' => simp [ht, ht']
  let S : Sieve W :=
    { arrows := fun Z _ ↦ ∃ A : X.affineOpens, Z ≤ A.1 ∧ A.1 ≤ W
      downward_closed := by
        intro Z Z' f hf t
        obtain ⟨A, hZA, hAW⟩ := hf
        exact ⟨A, (leOfHom t).trans hZA, hAW⟩ }
  have hS : S ∈ Opens.grothendieckTopology X W := by
    intro x hx
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact ⟨A, homOfLE hAW, ⟨⟨A, hA⟩, le_rfl, hAW⟩, hxA⟩
  ext x
  apply (((tensorPullback g).obj G).isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext
  intro Z l hl
  obtain ⟨A, hZA, hAW⟩ := hl
  have hcomp : l = homOfLE hZA ≫ homOfLE hAW := Subsingleton.elim _ _
  have hnat := Hom.app_presheaf_map ((tensorPullback g).map δ) (homOfLE hAW) x
  rw [hAffine A (hAW.trans hW)] at hnat
  rw [hcomp, op_comp, Functor.map_comp]
  change ((tensorPullback g).obj G).presheaf.map (homOfLE hZA).op
    (((tensorPullback g).obj G).presheaf.map (homOfLE hAW).op
      (((tensorPullback g).map δ).app W x)) = _
  rw [← hnat]
  simp

end AlgebraicGeometry.Scheme.Modules
