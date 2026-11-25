/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra

import WeilConjectures.AlgebraicGeometry.AffineCoherentTildePresentation
import WeilConjectures.AlgebraicGeometry.AffineCompletionBaseChangeUnit
import WeilConjectures.AlgebraicGeometry.AffineFormalMapLimitDictionary
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedLimit

/-! # Affine formal gluing comparison

Source: Stacks Project, Tags 087W, 0888 and 0889(1).
(blueprint: lem-weil-pbc-affine-formal-map-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem annihilators_of_linear_square
    {A : Type u} [CommRing A] {M N M' N' : ModuleCat.{u} A}
    (f : M →ₗ[A] N) (g : M' →ₗ[A] N')
    (a : M ≃ₗ[A] M') (b : N ≃ₗ[A] N')
    (hs : ∀ x, b (f x) = g (a x)) (K : Ideal A)
    (hk : K ≤ Module.annihilator A g.ker)
    (hc : K ≤ Module.annihilator A (N' ⧸ g.range)) :
    K ≤ Module.annihilator A f.ker ∧
      K ≤ Module.annihilator A (N ⧸ f.range) := by
  constructor
  · intro r hr
    rw [Module.mem_annihilator] at *
    intro x
    apply Subtype.ext
    change r • (x : M) = 0
    apply a.injective
    rw [map_smul, map_zero]
    have hx : a (x : M) ∈ g.ker := by
      rw [LinearMap.mem_ker, ← hs, x.property, map_zero]
    exact congrArg Subtype.val (Module.mem_annihilator.mp (hk hr) ⟨a x, hx⟩)
  · intro r hr
    rw [Module.mem_annihilator]
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective f.range x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hy : r • b y ∈ g.range := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      rw [Submodule.Quotient.mk_smul]
      exact Module.mem_annihilator.mp (hc hr) (Submodule.Quotient.mk (b y))
    obtain ⟨z, hz⟩ := hy
    obtain ⟨x, hx⟩ := a.surjective z
    refine ⟨x, b.injective ?_⟩
    rw [map_smul, hs, hx]
    exact hz

/-- A completed-module presentation of a formal map, before algebraic gluing.

Source: Stacks Project, Tags 087W, 0888, 00MA and 0889(1).
(blueprint: lem-weil-pbc-affine-formal-map-presentation).

Proof: the affine coherent tilde presentation gives P and epsilon by the proved
quasi-coherent counit. The completion base-change unit lemma makes eta the asIso
of C applied to p ↦ 1 tensor p; its hom equation is reflexive. The torsion-free
formal-map limit dictionary supplies Q, phi, rho and A-linear comparisons a,b with
the actual inverse limits of section modules, including their commuting square.
Apply the fixed-exponent affine-limit implication of Remark 0888 to the top open
to get the common positive power 2 * t for the section-limit kernel and cokernel.
For the kernel, a takes every
kernel vector of phi to a kernel vector of the limit map; injectivity of a then
reflects annihilation. For the cokernel, b takes each ideal multiple into the
limit range; surjectivity of a lifts a preimage and injectivity of b reflects the
range equation. The quotient criterion gives annihilation of the cokernel.
Assemble these bounds with the presentation witnesses. This is a decomposition:
only the torsion-free affine dictionary remains open in a new module. No algebraic
candidate is constructed. The same proof includes I=0, I=A and the zero ring.
-/
theorem affine_formal_map_presentation
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op e))))) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let S := AdicCompletion I A
    let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
    let C := L ⋙ formalCompletionFunctor J
    ∃ (P : ModuleCat.{u} A) (Q : ModuleCat.{u} S),
      letI := Module.restrictScalars A S Q
      letI := IsScalarTower.restrictScalars A S Q
      ∃ (φ : Q →ₗ[S] S ⊗[A] P) (ε : L.obj P ≅ H.obj)
        (ρ : N.obj ≅ C.obj (ModuleCat.of A Q))
        (η : C.obj P ≅ C.obj (ModuleCat.of A (S ⊗[A] P))),
        η.hom = C.map (ModuleCat.ofHom (TensorProduct.mk A S P (1 : S))) ∧
        δ.hom = ρ.hom ≫ C.map (ModuleCat.ofHom (φ.restrictScalars A)) ≫
          η.inv ≫ (formalCompletionFunctor J).map ε.hom ∧
        ∃ t : ℕ, 1 ≤ t ∧
          I ^ t ≤ Module.annihilator A (φ.restrictScalars A).ker ∧
          I ^ t ≤ Module.annihilator A ((S ⊗[A] P) ⧸ (φ.restrictScalars A).range) := by
  classical
  let A := Γ(X, ⊤)
  let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
  let S := AdicCompletion I A
  let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
  let C := L ⋙ formalCompletionFunctor J
  obtain ⟨P, ⟨ε⟩⟩ := affine_coherent_tilde_presentation H
  have hu : IsIso (C.map (ModuleCat.ofHom (TensorProduct.mk A S P (1 : S)))) :=
    affine_completion_baseChange_unit J P
  let η := asIso (C.map (ModuleCat.ofHom (TensorProduct.mk A S P (1 : S))))
  obtain ⟨Q, φ, ρ, a, b, hδ, hs⟩ :=
    affine_formal_map_limit_dictionary J H N δ P ε η
  let := Module.restrictScalars A S Q
  let := IsScalarTower.restrictScalars A S Q
  obtain ⟨t, ht, hcomponents⟩ := htorsion
  obtain ⟨hk, hc⟩ := coherentFormalModule_annihilated_affine_limit X J J N
    ((completion X J).obj H) δ t ht hcomponents ⟨⊤, isAffineOpen_top X⟩
  refine ⟨P, Q, φ, ε, ρ, η, rfl, hδ, 2 * t, by omega, ?_⟩
  exact annihilators_of_linear_square (A := A)
    (M := ModuleCat.of A Q) (N := ModuleCat.of A (S ⊗[A] P))
    (φ.restrictScalars A)
    (lim.map (Functor.whiskerRight δ.hom
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))).hom a b hs (I ^ (2 * t)) hk hc

end AlgebraicGeometry
