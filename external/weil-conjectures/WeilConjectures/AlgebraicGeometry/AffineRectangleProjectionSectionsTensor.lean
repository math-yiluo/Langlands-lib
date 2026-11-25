/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.IsTensorProduct

/-! # Projection sections on an affine rectangle -/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency.types false in
/-- The external tensor identity over a pushout of commutative rings. -/
private noncomputable def externalTensorAlgebraEquiv
    (R A B C M N : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.IsPushout R A B C]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] :
    (C ⊗[A] M) ⊗[C] (C ⊗[B] N) ≃ₗ[R] M ⊗[R] N := by
  let e₁ := (TensorProduct.comm C (C ⊗[A] M) (C ⊗[B] N)).restrictScalars R
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A C C (C ⊗[B] N) M
  let e₃ := TensorProduct.congr (Algebra.IsPushout.cancelBaseChange R A B C N)
    (LinearEquiv.refl A M)
  let e₄ := TensorProduct.comm A (A ⊗[R] N) M
  let e₅ := TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M N
  exact e₁ ≪≫ₗ e₂.restrictScalars R ≪≫ₗ e₃.restrictScalars R ≪≫ₗ
    e₄.restrictScalars R ≪≫ₗ e₅.restrictScalars R

set_option backward.isDefEq.respectTransparency.types false in
private theorem externalTensorAlgebraEquiv_tmul
    (R A B C M N : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.IsPushout R A B C]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] (m : M) (n : N) :
    externalTensorAlgebraEquiv R A B C M N ((1 ⊗ₜ[A] m) ⊗ₜ[C] (1 ⊗ₜ[B] n)) = m ⊗ₜ[R] n := by
  simp only [externalTensorAlgebraEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.congr_tmul, Algebra.IsPushout.cancelBaseChange_tmul, one_smul,
    LinearEquiv.refl_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary section modules of the two projection pullbacks on an affine rectangle
have tensor product over its coordinate ring equal to the tensor of the factor sections.
Source: Stacks Project, Tag 0BED, affine computation in lemma-kunneth; Tags 01IA and 01I9.
(blueprint: lem-sc-affine-rectangle-projection-sections-tensor).

Proof: Put A = Gamma(X,U), B = Gamma(Y,V), C = Gamma(X times_k Y,W),
M = Gamma(F,U), and N = Gamma(G,V). The rectangle W is affine. The affine
fibre-product section square says C is the pushout of A and B over k, with
its actual projection ring maps. Affine pullback sections identify the two
projection-section modules with C tensor_A M and C tensor_B N, taking
1 tensor s to the restricted adjunction unit of s. Tensor these C-linear
bijections over C. The standard pushout base-change cancellation, tensor
commutativity, and base-change cancellation give an isomorphism from their
source to M tensor_k N. Its inverse sends s tensor t to
(1 tensor s) tensor (1 tensor t). Compose that inverse with the two
pullback-section comparisons to obtain e, with the stated formula. The
formula determines e on pure tensors and hence on all tensors. This uses
no sheaf tensor-section comparison. All identities hold over zero rings;
empty opens and zero coefficient modules therefore need no exception. -/
theorem exists_affine_rectangle_projection_sections_tensor
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    let W := pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V
    ∃ e : (scalarObj f F (op U) ⊗[k] scalarObj g G (op V)) ≃+
        (Γ((tensorPullback (pullback.fst f g)).obj F, W) ⊗[Γ(Limits.pullback f g, W)]
          Γ((tensorPullback (pullback.snd f g)).obj G, W)),
      ∀ (s : scalarObj f F (op U)) (t : scalarObj g G (op V)),
        e (s ⊗ₜ[k] t) =
          (((tensorPullback (pullback.fst f g)).obj F).presheaf.map
            (homOfLE (show W ≤ pullback.fst f g ⁻¹ᵁ U from inf_le_left)).op
            (((Classical.choose (exists_tensorPullbackAdjunction
              (pullback.fst f g))).unit.app F).app U s)) ⊗ₜ[Γ(Limits.pullback f g, W)]
            (((tensorPullback (pullback.snd f g)).obj G).presheaf.map
            (homOfLE (show W ≤ pullback.snd f g ⁻¹ᵁ V from inf_le_right)).op
            (((Classical.choose (exists_tensorPullbackAdjunction
              (pullback.snd f g))).unit.app G).app V t)) := by
  classical
  dsimp only
  let W := pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V
  have hW := isAffineOpen_preimage_inf_preimage_pullback f g hU hV
  let Z := Limits.pullback f g
  let A := Γ(X, U)
  let B := Γ(Y, V)
  let C := Γ(Z, W)
  let i := (pullback.fst f g).appLE U W inf_le_left
  let j := (pullback.snd f g).appLE V W inf_le_right
  let : Algebra k A := (scalarMap f U).toAlgebra
  let : Algebra k B := (scalarMap g V).toAlgebra
  let : Algebra k C := (scalarMap (pullback.fst f g ≫ f) W).toAlgebra
  let : Algebra A C := i.hom.toAlgebra
  let : Algebra B C := j.hom.toAlgebra
  have hi : (scalarMap (pullback.fst f g ≫ f) W) = i.hom.comp (scalarMap f U) := by
    change ((ΓSpecIso (.of k)).inv ≫ (pullback.fst f g ≫ f).appLE ⊤ W (by simp)).hom =
      ((ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp) ≫ i).hom
    dsimp only [i]
    rw [Scheme.Hom.appLE_comp_appLE]
  have hj : (scalarMap (pullback.fst f g ≫ f) W) = j.hom.comp (scalarMap g V) := by
    rw [pullback.condition]
    change ((ΓSpecIso (.of k)).inv ≫ (pullback.snd f g ≫ g).appLE ⊤ W (by simp)).hom =
      ((ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ V (by simp) ≫ j).hom
    dsimp only [j]
    rw [Scheme.Hom.appLE_comp_appLE]
  let : IsScalarTower k A C := IsScalarTower.of_algebraMap_eq' hi
  let : IsScalarTower k B C := IsScalarTower.of_algebraMap_eq' hj
  have hs := (isIso_pushoutSection_iff (IsPullback.of_hasPullback f g)
    (UT := V) (UX := U) (US := ⊤) (by simp) (by simp) (UY := W) rfl).mp
    (isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback f g)
      (UT := V) (UX := U) (US := ⊤) (by simp) (by simp) (UY := W) rfl
      (isAffineOpen_top _) hV hU)
  have hs' : IsPushout (CommRingCat.ofHom (scalarMap f U))
      (CommRingCat.ofHom (scalarMap g V)) i j := by
    refine hs.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by rfl) (by rfl)
    · simp [scalarMap, Scheme.Hom.appLE]
    · simp [scalarMap, Scheme.Hom.appLE]
  let : Algebra.IsPushout k A B C := CommRingCat.isPushout_iff_isPushout.mp hs'
  obtain ⟨cF, hcF, hlinF, hpF, _⟩ := exists_tensorPullback_affine_sections
    (pullback.fst f g) ⟨U, hU⟩ ⟨W, hW⟩ inf_le_left
  obtain ⟨cG, hcG, hlinG, hpG, _⟩ := exists_tensorPullback_affine_sections
    (pullback.snd f g) ⟨V, hV⟩ ⟨W, hW⟩ inf_le_right
  let M : Type w := Γ(F, U)
  let N : Type w := Γ(G, V)
  let P : Type w := Γ((tensorPullback (pullback.fst f g)).obj F, W)
  let Q : Type w := Γ((tensorPullback (pullback.snd f g)).obj G, W)
  let : Module k M := Module.compHom _ (scalarMap f U)
  let : Module k N := Module.compHom _ (scalarMap g V)
  let : Module A M := inferInstanceAs (Module Γ(X, U) Γ(F, U))
  let : Module B N := inferInstanceAs (Module Γ(Y, V) Γ(G, V))
  let : Module C P := inferInstanceAs
    (Module Γ(Z, W) Γ((tensorPullback (pullback.fst f g)).obj F, W))
  let : Module C Q := inferInstanceAs
    (Module Γ(Z, W) Γ((tensorPullback (pullback.snd f g)).obj G, W))
  let eF : C ⊗[A] M ≃ₗ[C] P := LinearEquiv.ofBijective
    { toFun := fun z ↦ cF F inferInstance (TensorProduct.comm A C M z)
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro c z
        have h := hlinF F inferInstance c (TensorProduct.comm A C M z)
        change cF F inferInstance ((TensorProduct.comm A M C).symm
          (c • (TensorProduct.comm A M C) ((TensorProduct.comm A M C).symm z))) =
            c • cF F inferInstance ((TensorProduct.comm A M C).symm z) at h
        rw [LinearEquiv.apply_symm_apply] at h
        exact h }
    ((hcF F inferInstance).comp (TensorProduct.comm A C M).bijective)
  let eG : C ⊗[B] N ≃ₗ[C] Q := LinearEquiv.ofBijective
    { toFun := fun z ↦ cG G inferInstance (TensorProduct.comm B C N z)
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro c z
        have h := hlinG G inferInstance c (TensorProduct.comm B C N z)
        change cG G inferInstance ((TensorProduct.comm B N C).symm
          (c • (TensorProduct.comm B N C) ((TensorProduct.comm B N C).symm z))) =
            c • cG G inferInstance ((TensorProduct.comm B N C).symm z) at h
        rw [LinearEquiv.apply_symm_apply] at h
        exact h }
    ((hcG G inferInstance).comp (TensorProduct.comm B C N).bijective)
  have hF (s : M) : eF (1 ⊗ₜ[A] s) = (((tensorPullback (pullback.fst f g)).obj F).presheaf.map
            (homOfLE (show W ≤ pullback.fst f g ⁻¹ᵁ U from inf_le_left)).op
            (((Classical.choose (exists_tensorPullbackAdjunction
              (pullback.fst f g))).unit.app F).app U s)) := by
    change cF F inferInstance (s ⊗ₜ[A] (1 : C)) = _
    have h := hpF F inferInstance s (1 : C)
    rw [one_smul] at h
    exact h
  have hG (t : N) : eG (1 ⊗ₜ[B] t) = (((tensorPullback (pullback.snd f g)).obj G).presheaf.map
            (homOfLE (show W ≤ pullback.snd f g ⁻¹ᵁ V from inf_le_right)).op
            (((Classical.choose (exists_tensorPullbackAdjunction
              (pullback.snd f g))).unit.app G).app V t)) := by
    change cG G inferInstance (t ⊗ₜ[B] (1 : C)) = _
    have h := hpG G inferInstance t (1 : C)
    rw [one_smul] at h
    exact h
  let : IsScalarTower k A M := IsScalarTower.of_algebraMap_smul (by intros; rfl)
  let : IsScalarTower k B N := IsScalarTower.of_algebraMap_smul (by intros; rfl)
  let d := externalTensorAlgebraEquiv k A B C M N
  let e := d.symm.toAddEquiv.trans (TensorProduct.congr eF eG).toAddEquiv
  refine ⟨e, ?_⟩
  intro s t
  change M at s
  change N at t
  have hd : d.symm (s ⊗ₜ[k] t) = (1 ⊗ₜ[A] s) ⊗ₜ[C] (1 ⊗ₜ[B] t) := by
    apply d.injective
    rw [d.apply_symm_apply]
    exact (externalTensorAlgebraEquiv_tmul k A B C M N s t).symm
  change (TensorProduct.congr eF eG) (d.symm (s ⊗ₜ[k] t)) = _
  exact (congrArg (TensorProduct.congr eF eG) hd).trans
    ((TensorProduct.congr_tmul eF eG _ _).trans
      (congrArg₂ (fun x y ↦ x ⊗ₜ[C] y) (hF s) (hG t)))


end AlgebraicGeometry.Scheme.Modules
