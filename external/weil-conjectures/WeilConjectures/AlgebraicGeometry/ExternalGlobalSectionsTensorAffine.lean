/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.RingTheory.IsTensorProduct
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # External global sections on two affine factors

Source: Stacks Project, Tag 0BED, affine charts of equation-kunneth-on-cech.
(blueprint: lem-sc-external-global-sections-tensor-affine).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

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
/-- Before taking the sheaf tensor product, the two projection-pullback section modules
have tensor product equal to the tensor product of the original sections over the field.
Source: Stacks Project, Tag 0BED, affine computation in lemma-kunneth.

Proof: Put A = Gamma(X,O), B = Gamma(Y,O), M = Gamma(X,F), N = Gamma(Y,G),
and C = Gamma(X times_k Y,O). The affine spectrum fibre-product formula identifies C
with A tensor_k B, compatibly with both projection ring maps. Apply the affine pullback
section comparison to each projection: its canonical formula takes m tensor c to
c times the projection pullback of m. These comparisons are C-linear bijections,
so tensoring them over C gives a bijection of tensor products of section modules.
The algebraic identification (M tensor_A C) tensor_C (N tensor_B C) with M tensor_k N
sends (m tensor (a tensor b)) tensor (n tensor (a' tensor b')) to
(a*a') times m tensor (b*b') times n. Its inverse sends m tensor n to
(m tensor 1) tensor (n tensor 1). Balance over A, B, and C makes these maps
well-defined; induction on the ring tensors and module tensors proves both inverse
identities. Compose the inverse with the two pullback-section comparisons and forget
scalar linearity. The pure-tensor formula follows from the comparisons at c = 1.
No sheaf tensor-section comparison is used here: the codomain is a tensor product
of ordinary section modules. If either scheme is empty, its coordinate ring and
section modules vanish, so the same formulas and inverse identities still apply.
Zero coefficients are covered by these identities as well. -/
private theorem exists_affine_projection_sections_tensor
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffine X] [IsAffine Y]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ∃ e : (scalarObj f F (op ⊤) ⊗[k] scalarObj g G (op ⊤)) ≃+
        (Γ((tensorPullback (pullback.fst f g)).obj F, ⊤) ⊗[Γ(Limits.pullback f g, ⊤)]
          Γ((tensorPullback (pullback.snd f g)).obj G, ⊤)),
      ∀ (s : scalarObj f F (op ⊤)) (t : scalarObj g G (op ⊤)),
        e (s ⊗ₜ[k] t) =
          tensorPullbackTopSection (pullback.fst f g) F s ⊗ₜ[Γ(Limits.pullback f g, ⊤)]
            tensorPullbackTopSection (pullback.snd f g) G t := by
  classical
  let Z := Limits.pullback f g
  let A := Γ(X, ⊤)
  let B := Γ(Y, ⊤)
  let C := Γ(Z, ⊤)
  let i := (pullback.fst f g).appLE ⊤ ⊤ (by simp)
  let j := (pullback.snd f g).appLE ⊤ ⊤ (by simp)
  let : Algebra k A := (scalarMap f ⊤).toAlgebra
  let : Algebra k B := (scalarMap g ⊤).toAlgebra
  let : Algebra k C := (scalarMap (pullback.fst f g ≫ f) ⊤).toAlgebra
  let : Algebra A C := i.hom.toAlgebra
  let : Algebra B C := j.hom.toAlgebra
  have hi : (scalarMap (pullback.fst f g ≫ f) ⊤) = i.hom.comp (scalarMap f ⊤) := by
    simp [scalarMap, i, Scheme.Hom.appTop, Scheme.Hom.appLE, RingHom.comp_assoc]
  have hj : (scalarMap (pullback.fst f g ≫ f) ⊤) = j.hom.comp (scalarMap g ⊤) := by
    rw [pullback.condition]
    simp [scalarMap, j, Scheme.Hom.appTop, Scheme.Hom.appLE, RingHom.comp_assoc]
  let : IsScalarTower k A C := IsScalarTower.of_algebraMap_eq' hi
  let : IsScalarTower k B C := IsScalarTower.of_algebraMap_eq' hj
  have hs := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f g)
  have hs' : IsPushout (CommRingCat.ofHom (scalarMap f ⊤))
      (CommRingCat.ofHom (scalarMap g ⊤)) i j := by
    refine hs.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp [i, Scheme.Hom.appLE, Scheme.Hom.appTop])
      (by simp [j, Scheme.Hom.appLE, Scheme.Hom.appTop])
    · simp [scalarMap]
    · simp [scalarMap]
  let : Algebra.IsPushout k A B C := CommRingCat.isPushout_iff_isPushout.mp hs'
  obtain ⟨cF, hcF, hlinF, hpF, _⟩ := exists_tensorPullback_affine_sections
    (pullback.fst f g) ⟨⊤, isAffineOpen_top X⟩ ⟨⊤, isAffineOpen_top Z⟩ (by simp)
  obtain ⟨cG, hcG, hlinG, hpG, _⟩ := exists_tensorPullback_affine_sections
    (pullback.snd f g) ⟨⊤, isAffineOpen_top Y⟩ ⟨⊤, isAffineOpen_top Z⟩ (by simp)
  let M : Type w := Γ(F, ⊤)
  let N : Type w := Γ(G, ⊤)
  let P : Type w := Γ((tensorPullback (pullback.fst f g)).obj F, ⊤)
  let Q : Type w := Γ((tensorPullback (pullback.snd f g)).obj G, ⊤)
  let : Module k M := Module.compHom _ (scalarMap f ⊤)
  let : Module k N := Module.compHom _ (scalarMap g ⊤)
  let : Module A M := inferInstanceAs (Module Γ(X, ⊤) Γ(F, ⊤))
  let : Module B N := inferInstanceAs (Module Γ(Y, ⊤) Γ(G, ⊤))
  let : Module C P := inferInstanceAs
    (Module Γ(Z, ⊤) Γ((tensorPullback (pullback.fst f g)).obj F, ⊤))
  let : Module C Q := inferInstanceAs
    (Module Γ(Z, ⊤) Γ((tensorPullback (pullback.snd f g)).obj G, ⊤))
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
  have hF (s : M) : eF (1 ⊗ₜ[A] s) = tensorPullbackTopSection (pullback.fst f g) F s := by
    change cF F inferInstance (s ⊗ₜ[A] (1 : C)) = _
    have h := hpF F inferInstance s (1 : C)
    rw [one_smul] at h
    unfold tensorPullbackTopSection
    rw [← PresheafOfModules.presheaf_map_apply_coe]
    exact h
  have hG (t : N) : eG (1 ⊗ₜ[B] t) = tensorPullbackTopSection (pullback.snd f g) G t := by
    change cG G inferInstance (t ⊗ₜ[B] (1 : C)) = _
    have h := hpG G inferInstance t (1 : C)
    rw [one_smul] at h
    unfold tensorPullbackTopSection
    rw [← PresheafOfModules.presheaf_map_apply_coe]
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
  rw [hd, TensorProduct.congr_tmul, hF, hG]


/-- On two affine schemes the canonical external tensor comparison is bijective.
Source: Stacks Project, Tag 0BED, affine computation in lemma-kunneth.
(blueprint: lem-sc-external-global-sections-tensor-affine).

Proof: Write A = Gamma(X,O), B = Gamma(Y,O), M = Gamma(X,F), N = Gamma(Y,G).
The affine chart isomorphisms identify the product with Spec(A tensor_k B). The affine
pullback-section comparisons identify the two pulled-back modules with the scalar
extensions of M and N to A tensor_k B. The affine tensor-section comparison identifies
the external coefficient sections with their tensor product over A tensor_k B.
The algebraic isomorphism from this tensor product to M tensor_k N sends
(m tensor b) tensor (a tensor n) to (a*m) tensor (b*n). Its inverse sends m tensor n
to (m tensor 1) tensor (1 tensor n). The balance relations over A, B and A tensor_k B
make these well-defined, and tensor induction proves the two inverse identities.
The pure-tensor formulas for the pullback-section comparisons and tensor-section map
show that the composite inverse is precisely the external section map: it takes
s tensor t to the tensor of the two projection pullbacks. Tensor induction identifies
these linear maps on all inputs. Thus the canonical map is bijective. Zero rings,
empty affine schemes and zero coefficients satisfy the same algebraic identities. -/
theorem externalGlobalSectionsTensor_bijective_of_isAffine
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffine X] [IsAffine Y]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (externalGlobalSectionsTensor f g F G) := by
  classical
  let P := (tensorPullback (pullback.fst f g)).obj F
  let Q := (tensorPullback (pullback.snd f g)).obj G
  have hP : P.IsQuasicoherent := by
    let e := (nonempty_tensorPullbackAdjunction (pullback.fst f g)).some.leftAdjointUniq
      (pullbackPushforwardAdjunction (pullback.fst f g))
    exact (SheafOfModules.isQuasicoherent (Limits.pullback f g).ringCatSheaf).prop_of_iso
      (e.app F).symm (by infer_instance)
  have hQ : Q.IsQuasicoherent := by
    let e := (nonempty_tensorPullbackAdjunction (pullback.snd f g)).some.leftAdjointUniq
      (pullbackPushforwardAdjunction (pullback.snd f g))
    exact (SheafOfModules.isQuasicoherent (Limits.pullback f g).ringCatSheaf).prop_of_iso
      (e.app G).symm (by infer_instance)
  let := hP
  let := hQ
  have ht := (quasiCoherent_tensor_product_affine_sections P Q).2
    ⊤ (isAffineOpen_top (Limits.pullback f g))
  obtain ⟨e, he⟩ := exists_affine_projection_sections_tensor k X Y f g F G
  have hc (z : scalarObj f F (op ⊤) ⊗[k] scalarObj g G (op ⊤)) :
      tensorSectionsMap P Q ⊤ (e z) = externalGlobalSectionsTensor f g F G z := by
    induction z using TensorProduct.inductionOn with
    | tmul s t =>
      rw [he, tensorSectionsMap_tmul]
      rfl
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have hc' : (tensorSectionsMap P Q ⊤) ∘ e = externalGlobalSectionsTensor f g F G :=
    funext hc
  rw [← hc']
  exact ht.comp e.bijective

end AlgebraicGeometry.Scheme.Modules
