/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemComparison

/-! # Completed comparison in the original index

Source: Stacks Project, Tag 088A, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Double quotient comparison gives an isomorphism after K-completion, natural in
all I-levels. No torsion hypothesis is needed for this purely quotient-theoretic step.
Source: Stacks Project, Tag 088A, final paragraph
(blueprint: lem-weil-pbc-devissage-completed-comparison).

Proof: the two iterated quotients of any module by I^(n+1) and K^(e+1) are the
cokernel quotient by the sum of these ideal products. The universal cokernel maps
in both directions give an interchange isomorphism characterized by the composite
projection from that module. Cancel this composite epimorphism to check both inverse
identities and naturality in module maps and in both indices. Apply interchange to F,
compose with the I-reductions of beta inverse and sigma, and transpose the indices.
This gives the asserted isomorphism Xi of K-completed diagrams indexed by I-levels.
For the map equation, the equation delta = beta.hom followed by completed a and the
supplied comparison square give the equation after quotienting. Naturality of the
interchange for a reduces the remaining comparison on H to theta. The projection
equation htheta forces the supplied theta to equal this canonical interchange, again
by cancelling the composite quotient epimorphism. Thus Xi respects the two maps to
the K-completion of H/I^(n+1)H at every index. Naturality follows from that of beta,
sigma and the quotient interchange. No algebraization or choice of coherent witness
is involved: only isomorphisms between specified quotient systems are asserted.
-/
theorem grothendieckDevissage_completedComparison
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I) (H : CoherentModules X)
    (α : M ⟶ (completion X I).obj H)
    (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
    (σ : N.obj ⋙ formalCompletionFunctor I ≅ (M.obj ⋙ formalCompletionFunctor K).flip)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    (hθ : ∀ e n : ℕ,
      formalModuleQuotientπ K (e + 1) H.obj ≫
        formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) H.obj) ≫
        (θ.hom.app (op e)).app (op n) =
      formalModuleQuotientπ I (n + 1) H.obj ≫
        formalModuleQuotientπ K (e + 1) (formalModuleQuotient I (n + 1) H.obj))
    (hsquare : ∀ e n : ℕ,
      (σ.hom.app (op e)).app (op n) ≫
        formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
      formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
        (θ.hom.app (op e)).app (op n))
    (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X K).obj F)
    (hβ : δ = β.hom ≫ (completion X K).map a) :
    ∃ Ξ : ((completion X I).obj F).obj ⋙ formalCompletionFunctor K ≅
        M.obj ⋙ formalCompletionFunctor K,
      ∀ n : ℕᵒᵖ,
        Ξ.hom.app n ≫ formalCompletionMap K (α.hom.app n) =
          formalCompletionMap K (((completion X I).map a).hom.app n) := by
  obtain ⟨τ, hτ⟩ := grothendieckDevissage_secondAdicSystem_comparison I K F.obj
  let b : N.obj ≅ formalCompletionSystem K F.obj :=
    (ObjectProperty.ι (IsCoherentFormalModule K)).mapIso β
  let γ := Functor.isoWhiskerRight b.symm (formalCompletionFunctor I) ≪≫ σ
  let Ξ := (flipFunctor _ _ _).mapIso (τ.symm ≪≫ γ)
  refine ⟨Ξ, ?_⟩
  intro n
  apply NatTrans.ext
  funext e
  have ht := hτ e.unop n.unop
  simp only [← Category.assoc] at ht
  have hh := hθ e.unop n.unop
  have hs := hsquare e.unop n.unop
  have hnat : (τ.hom.app e).app n ≫
      formalModuleQuotientMap K
        (formalModuleQuotientMap I a.hom (Nat.le_refl (n.unop + 1)))
        (Nat.le_refl (e.unop + 1)) =
      formalModuleQuotientMap I
        (formalModuleQuotientMap K a.hom (Nat.le_refl (e.unop + 1)))
        (Nat.le_refl (n.unop + 1)) ≫ (θ.hom.app e).app n := by
    have : Epi (formalModuleQuotientπ K (e.unop + 1) F.obj) := by
      dsimp [formalModuleQuotientπ]
      infer_instance
    have : Epi (formalModuleQuotientπ I (n.unop + 1)
        (formalModuleQuotient K (e.unop + 1) F.obj)) := by
      dsimp [formalModuleQuotientπ]
      infer_instance
    apply (cancel_epi (formalModuleQuotientπ I (n.unop + 1)
      (formalModuleQuotient K (e.unop + 1) F.obj))).1
    apply (cancel_epi (formalModuleQuotientπ K (e.unop + 1) F.obj)).1
    simp only [← Category.assoc]
    rw [ht]
    simp only [Category.assoc, formalModuleQuotientMap, formalModuleQuotientπ,
      cokernel.π_desc, cokernel.π_desc_assoc]
    simpa only [formalModuleQuotientπ, Category.assoc] using
      congrArg (fun t ↦ a.hom ≫ t) hh.symm
  have hb : b.inv.app e ≫ δ.hom.app e =
      formalModuleQuotientMap K a.hom (Nat.le_refl (e.unop + 1)) := by
    rw [hβ]
    change b.inv.app e ≫ (b.hom.app e ≫
      formalModuleQuotientMap K a.hom (Nat.le_refl (e.unop + 1))) = _
    simp
  change ((τ.inv.app e).app n ≫
      formalModuleQuotientMap I (b.inv.app e) (Nat.le_refl (n.unop + 1)) ≫
      (σ.hom.app e).app n) ≫
      formalModuleQuotientMap K (α.hom.app n) (Nat.le_refl (e.unop + 1)) =
    formalModuleQuotientMap K
      (formalModuleQuotientMap I a.hom (Nat.le_refl (n.unop + 1)))
      (Nat.le_refl (e.unop + 1))
  rw [Category.assoc, Category.assoc, hs, ← Category.assoc
    (formalModuleQuotientMap I (b.inv.app e) _), ← formalModuleQuotientMap_comp, hb]
  rw [← hnat]
  simp


end AlgebraicGeometry
