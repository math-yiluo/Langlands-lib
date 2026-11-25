/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Coproducts of K-projective complexes. -/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Coproducts of K-projective complexes are K-projective.
Source: Stacks Project, Tag 09KM, coproduct null-homotopy argument.
(blueprint: lem-pc-coproduct-kprojective)

Proof: restrict a map to each summand and choose a null homotopy by K-projectivity.
Evaluation preserves coproducts, so the homotopy components assemble degreewise.
The homotopy identity and support condition hold on every coproduct injection,
and hence on the coproduct. No boundedness or nonempty-index assumption is used. -/
theorem isKProjective_coproduct {A : Type u} [CommRing A] {I : Type}
    (F : I → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hF : ∀ n, (F n).IsKProjective) : (∐ F).IsKProjective := by
  classical
  refine ⟨fun {N} f hN ↦ ?_⟩
  let h (n : I) : Homotopy (Sigma.ι F n ≫ f) 0 := by
    haveI := hF n
    exact IsKProjective.homotopyZero _ hN
  let c (i : ℤ) := isColimitOfHasCoproductOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{max u v} A) (.up ℤ) i) F
  let H (i j : ℤ) : (∐ F).X i ⟶ N.X j :=
    (c i).desc (Cofan.mk _ (fun n ↦ (h n).hom i j))
  have hc (n : I) (i j : ℤ) : (Sigma.ι F n).f i ≫ H i j = (h n).hom i j :=
    (c i).fac _ ⟨n⟩
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    apply (c i).hom_ext
    intro ⟨n⟩
    change (Sigma.ι F n).f i ≫ H i j = (Sigma.ι F n).f i ≫ 0
    rw [hc, (h n).zero i j hij, comp_zero]
  · intro i
    apply (c i).hom_ext
    intro ⟨n⟩
    change (Sigma.ι F n).f i ≫ f.f i =
      (Sigma.ι F n).f i ≫ (dNext i H + prevD i H + (0 : (∐ F) ⟶ N).f i)
    change (Sigma.ι F n).f i ≫ f.f i =
      (Sigma.ι F n).f i ≫ ((∐ F).d i _ ≫ H _ i + H i _ ≫ N.d _ i + 0)
    simp only [Preadditive.comp_add, add_zero]
    rw [(Sigma.ι F n).comm_assoc, hc, ← Category.assoc, hc]
    have hh := (h n).comm i
    dsimp [dNext, prevD, AddMonoidHom.mk'] at hh
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, add_zero] using hh

end CochainComplex
