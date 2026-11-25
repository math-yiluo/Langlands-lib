/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.AffineFormalMapPresentation
import WeilConjectures.AlgebraicGeometry.AffineCompletionBaseChangeUnit
import WeilConjectures.AlgebraicGeometry.AffineMapAnnihilationSheafification
import WeilConjectures.RingTheory.FormalGlueingIsogeny
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Quasi-coherent candidate from affine formal gluing

Source: Stacks Project, Tags 0889(1), 0ALK(1) and 0888.
(blueprint: lem-weil-pbc-torsion-controlled-affine-candidate).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem completion_quotientMap_bijective {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) :
    Function.Bijective (Ideal.quotientMap
      (I.map (algebraMap A (AdicCompletion I A)))
      (algebraMap A (AdicCompletion I A)) Ideal.le_comap_map) := by
  let S := AdicCompletion I A
  let f : S →+* A ⧸ I := (AdicCompletion.evalOneₐ I).toRingHom
  have hker : RingHom.ker f = I.map (algebraMap A S) :=
    AdicCompletion.ker_evalOneₐ_eq_map I hI
  have hkill : ∀ x ∈ I.map (algebraMap A S), f x = 0 := by
    intro x hx
    apply RingHom.mem_ker.mp
    rwa [hker]
  let g : S ⧸ I.map (algebraMap A S) →+* A ⧸ I :=
    Ideal.Quotient.lift _ f hkill
  have hg : Function.Injective g :=
    RingHom.lift_injective_of_ker_le_ideal _ hkill hker.le
  let q : A ⧸ I →+* S ⧸ I.map (algebraMap A S) :=
    Ideal.quotientMap _ (algebraMap A S) Ideal.le_comap_map
  have hleft : Function.LeftInverse g q := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change f (algebraMap A S a) = Ideal.Quotient.mk I a
    rfl
  refine ⟨hleft.injective, ?_⟩
  intro y
  refine ⟨g y, hg ?_⟩
  exact hleft (g y)

-- Transporting the completed-module presentation requires unfolding several functor layers.
/-- Formal gluing constructs a quasi-coherent candidate, without a finiteness assertion.

Source: Stacks Project, Tag 0889(1), affine construction using 0ALK(1), 087W and 0888.
(blueprint: lem-weil-pbc-torsion-controlled-affine-candidate).

Proof: identify X with Spec A by its canonical affine isomorphism and let I be J's
ideal of global sections. Under 087W, N corresponds to a finite completed module Q,
and H to a finite A-module P. The tensor comparison for finite P identifies the
formal map with Q -> S tensor P, where S is the I-adic completion. Remark 0888
transfers the given bound to its kernel and cokernel. The map A -> S is flat,
I is finitely generated, and A/I -> S/IS is an isomorphism. Apply 0ALK(1) to obtain
T -> P and Q isomorphic to S tensor T. Its kernel and cokernel are canonically
isomorphic as A-modules to those of the formal map, so the same positive power
of I kills them. Sheafify T and this map. Exactness of tilde and the affine
ideal-product formula give the asserted sheaf annihilation.

For each positive n the completion ring map gives A/I^n isomorphic to S/I^n S.
Consequently T/I^n T is naturally isomorphic to (S tensor T)/I^n(S tensor T),
without requiring T to be finite. Compose with the quotients of Q and the
reconstruction isomorphism of 087W to give beta. These quotient comparisons
commute with all reductions and with the glued map, hence form an isomorphism
of inverse systems and satisfy the factorization. This argument does not use
finiteness of T. When I is the unit ideal, take T=P and the identity; when I=0,
use the original module map since the completion ring is A. The zero ring and
empty spectrum satisfy the same formulas. -/
theorem torsionControlled_affine_candidate
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op e))))) :
    ∃ (F : X.Modules) (_ : F.IsQuasicoherent) (a : F ⟶ H.obj)
      (β : N.obj ≅ (formalCompletionFunctor J).obj F),
      δ.hom = β.hom ≫ (formalCompletionFunctor J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (kernel a)) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (cokernel a))) := by
  classical
  let A := Γ(X, ⊤)
  let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
  let S := AdicCompletion I A
  let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
  let C := L ⋙ formalCompletionFunctor J
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian
    ⟨⊤, isAffineOpen_top X⟩
  have hflat : (algebraMap A S).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hI : I.FG := I.fg_of_isNoetherianRing
  have hquot := completion_quotientMap_bijective I hI
  obtain ⟨P, Q, hdata⟩ :=
    affine_formal_map_presentation J H N δ htorsion
  let := Module.restrictScalars A S Q
  let := IsScalarTower.restrictScalars A S Q
  obtain ⟨φ, ε, ρ, η, hη, hδ, t, ht, hk, hc⟩ := hdata
  have hker : ∀ x : (φ.restrictScalars A).ker,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0 := by
    intro x
    refine ⟨t, ?_⟩
    intro r hr
    exact (Module.mem_annihilator.mp (hk hr)) x
  have hcoker : ∀ x : (TensorProduct A S P) ⧸ (φ.restrictScalars A).range,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0 := by
    intro x
    refine ⟨t, ?_⟩
    intro r hr
    exact (Module.mem_annihilator.mp (hc hr)) x
  obtain ⟨T, ψ, β, hβ, _, _, _, _, ⟨ek, _⟩, ⟨ec, _⟩⟩ :=
    FormalGlueing.exists_map_to_of_torsion_baseChange hflat I hI hquot P Q φ hker hcoker
  have hkψ : I ^ t ≤ Module.annihilator A ψ.ker :=
    hk.trans (ek.toLinearMap.annihilator_le_of_injective ek.injective)
  have hcψ : I ^ t ≤ Module.annihilator A (P ⧸ ψ.range) :=
    hc.trans (ec.toLinearMap.annihilator_le_of_injective ec.injective)
  let ιT : T ⟶ ModuleCat.of A (TensorProduct A S T) :=
    ModuleCat.ofHom (TensorProduct.mk A S T (1 : S))
  let ιP : P ⟶ ModuleCat.of A (TensorProduct A S P) :=
    ModuleCat.ofHom (TensorProduct.mk A S P (1 : S))
  let e : ModuleCat.of A Q ≅ ModuleCat.of A (TensorProduct A S T) :=
    (β.restrictScalars A).toModuleIso
  have : IsIso (C.map ιT) := affine_completion_baseChange_unit J T
  let b : C.obj (ModuleCat.of A Q) ≅ C.obj T :=
    C.mapIso e ≪≫ (asIso (C.map ιT)).symm
  have hunit : ModuleCat.ofHom ψ ≫ ιP =
      ιT ≫ ModuleCat.ofHom ((ψ.baseChange S).restrictScalars A) := by
    ext x
    change TensorProduct.tmul A (1 : S) (ψ x) = (ψ.baseChange S) (TensorProduct.tmul A (1 : S) x)
    exact (LinearMap.baseChange_tmul ψ (1 : S) x).symm
  have hφ : e.hom ≫ ModuleCat.ofHom ((ψ.baseChange S).restrictScalars A) =
      ModuleCat.ofHom (φ.restrictScalars A) := by
    ext x
    exact congrArg (fun f ↦ f x) hβ
  have hb : C.map (ModuleCat.ofHom (φ.restrictScalars A)) ≫ η.inv =
      b.hom ≫ C.map (ModuleCat.ofHom ψ) := by
    apply (cancel_mono η.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hη]
    change C.map (ModuleCat.ofHom (φ.restrictScalars A)) =
      (C.map e.hom ≫ inv (C.map ιT)) ≫ C.map (ModuleCat.ofHom ψ) ≫ C.map ιP
    rw [Category.assoc, ← C.map_comp, hunit, C.map_comp]
    simp only [IsIso.inv_hom_id_assoc]
    rw [← C.map_comp, hφ]
  let F : X.Modules := L.obj T
  have hF : F.IsQuasicoherent := by
    dsimp [F, L]
    infer_instance
  let a : F ⟶ H.obj := L.map (ModuleCat.ofHom ψ) ≫ ε.hom
  have habound := affine_map_annihilation_sheafification J T P ψ H.obj ε t hkψ hcψ
  refine ⟨F, hF, a, ρ ≪≫ b, ?_, t, ht, habound.1, habound.2⟩
  rw [hδ]
  change ρ.hom ≫ C.map (ModuleCat.ofHom (φ.restrictScalars A)) ≫ η.inv ≫
      (formalCompletionFunctor J).map ε.hom =
    (ρ.hom ≫ b.hom) ≫ (formalCompletionFunctor J).map
      (L.map (ModuleCat.ofHom ψ) ≫ ε.hom)
  change C.map (ModuleCat.ofHom (φ.restrictScalars A)) ≫ η.inv =
    b.hom ≫ (formalCompletionFunctor J).map (L.map (ModuleCat.ofHom ψ)) at hb
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ ρ.hom ≫ f ≫ (formalCompletionFunctor J).map ε.hom) hb

end AlgebraicGeometry
