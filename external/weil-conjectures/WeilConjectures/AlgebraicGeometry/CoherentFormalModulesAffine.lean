/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra

import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineLimit
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineComplete
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineReconstruction

/-! # Coherent formal modules on an affine scheme

Source: Stacks Project, Cohomology of Schemes, Lemma 087W and its proof
(blueprint: lem-weil-pbc-coherent-formal-modules-affine).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Coherent formal modules on Spec A are finite modules over the I-adic completion.
The cones specify the underlying inverse limits and their maps, while the scalar equation
specifies the componentwise action of the completion. Index `op n` means level `n + 1`.
The inverse is naturally the sheaf quotient system of the tilde of the restricted module;
on an affine scheme this is canonically the tilde of the module quotient N/I^(n+1)N,
with the canonical reductions on objects and maps.

Source: Stacks Project, Lemma 087W
(blueprint: lem-weil-pbc-coherent-formal-modules-affine).
Proof, following the seven steps of the node:
1. Global sections identify coherent sheaves with finite A-modules (01XZ), and ideal
products and quotients on an affine with the corresponding module products and quotients.
Thus the formal object conditions become I^n M_n = 0 and M_(n+1)/I^n M_(n+1) = M_n.
2. The tilde/global-sections adjunction (01I7, 01IA, 01IB) gives an equivalence on these
systems, including their compatible families of morphisms.
3. Surjective transitions make the limit project onto M_1. Lift finite generators of M_1;
Nakayama for the nilpotent ideal I/I^n (00DV) makes (A/I^n)^t -> M_n surjective at each level.
4. The kernels K_n have surjective transitions: adjust a lift by an element of I^n.
Mittag-Leffler exactness (02N1) gives K -> (A-completion)^t -> M -> 0, so M is finite.
5. By completeness of A-completion (05GG), the free-module projection has kernel I^n.
Surjectivity K -> K_n then gives ker(M -> M_n) = I^n M and surjectivity of that projection.
6. The completion is Noetherian (0316) and complete (05GG); finite modules over it are
complete (00MA). Therefore N -> lim N/I^n N is a natural linear isomorphism.
7. The projections give the other natural isomorphism of systems. Assemble both with
the tilde/global-sections equivalence. Scalar multiplication and morphisms act componentwise.
-/
theorem coherentFormalModules_affine (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) :
    ∃ E : CoherentFormalModule (Spec (CommRingCat.of A)) J ≌
      ObjectProperty.FullSubcategory
        (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N),
    ∃ p : ∀ F : CoherentFormalModule (Spec (CommRingCat.of A)) J,
      (Functor.const ℕᵒᵖ).obj
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
          (E.functor.obj F).obj) ⟶ F.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A),
    (∀ F, Nonempty (IsLimit (Cone.mk _ (p F)))) ∧
    (∀ (F G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (f : F ⟶ G)
      (n : ℕ),
      (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map
        (E.functor.map f).hom ≫ (p G).app (op n) =
      (p F).app (op n) ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map (f.hom.app (op n))) ∧
    (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ),
      Function.Surjective ((p F).app (op n)) ∧
      LinearMap.ker ((p F).app (op n)).hom =
        I ^ (n + 1) • (⊤ : Submodule A
          ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
            (E.functor.obj F).obj))) ∧
    (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ)
      (r : AdicCompletion I A) (a : A) (x : (E.functor.obj F).obj),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (p F).app (op n) (r • x) = a • (p F).app (op n) x) ∧
    Nonempty (E.inverse ⋙ ObjectProperty.ι (IsCoherentFormalModule J) ≅
      ObjectProperty.ι
        (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N) ⋙
      ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A)) ⋙
      tilde.functor (CommRingCat.of A) ⋙ formalCompletionFunctor J) := by
  obtain ⟨L, p, hlimit, hnatural, hquotient, hscalar⟩ :=
    coherentFormalModules_affine_limit A I J hJ
  obtain ⟨ε⟩ := coherentFormalModules_affine_complete A I J hJ L p
    hlimit hnatural hscalar
  obtain ⟨η⟩ := coherentFormalModules_affine_reconstruction A I J hJ L p
    hnatural hquotient
  let Q := coherentFormalModules_affine_quotientFunctor A I J hJ
  let E := CategoryTheory.Equivalence.mk L Q η.symm ε
  refine ⟨E, p, hlimit, hnatural, hquotient, hscalar, ?_⟩
  exact ⟨Iso.refl _⟩

end AlgebraicGeometry
