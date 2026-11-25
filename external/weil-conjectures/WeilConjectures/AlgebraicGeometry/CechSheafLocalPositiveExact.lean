/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.CechSheafLocalPositiveSections
/-! # Positive-degree exactness of a locally restricted Cech complex

Source: blueprint `lemma-coherent-base-change-invertible-sheaves`, proof paragraph 1.
(blueprint: lem-pc-cech-local-positive-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The restricted Cech-model complex is exact in every positive degree.
Source: blueprint `lemma-coherent-base-change-invertible-sheaves`, proof paragraph 1 (insertion
homotopy). (blueprint: lem-pc-cech-local-positive-exact)

Proof: On an open V contained in U_i, insert i at the front of each tuple to define
h from degree p+1 to degree p. The extra intersection with U_i does not change V.
For p > 0, the alternating differential satisfies d h + h d = identity: deleting the
new first entry gives identity, and every other deletion cancels the corresponding
shifted deletion in the other composite. Hence any positive-degree cocycle is a
boundary. These operators are natural in V and linear for the global section ring.
Transport them through e, using hd, after forgetting to abelian sheaves (e need not
be linear for the full local structure ring). This proves exactness of the underlying
abelian sheaf complex on U_i. Forgetting module sheaves to abelian sheaves reflects
exactness, since kernels are sectionwise kernels and cokernels are sheafified
sectionwise cokernels. It follows that the module-sheaf complex is exact in degree
p+1. Empty U_i and zero F give zero sheaves and satisfy the same equations. The
argument uses no augmentation, no covering assumption, and no interchange of stalks
with infinite products. -/
theorem cech_sheaf_restrict_exact_positive
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules)
    (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor U).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor U).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d p (p + 1))
    (i : ι) (p : ℕ) :
    (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D).ExactAt (p + 1) := by
  let K := ((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj D
  change (K.sc (p + 1)).Exact
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  apply Scheme.Modules.hom_ext
  intro W
  ext y
  let x := (kernel.ι (K.sc (p + 1)).g).app W y
  have hx : (K.sc (p + 1)).g.app W x = 0 := by
    have h := congrArg (fun f ↦ f.app W y) (kernel.condition (K.sc (p + 1)).g)
    simpa [x, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h
  obtain ⟨z, hz⟩ := cech_sheaf_restrict_positive_section_boundary U F D e hd i p W x hx
  change (cokernel.π (K.sc (p + 1)).f).app W x = 0
  rw [← hz]
  have h := congrArg (fun f ↦ f.app W z) (cokernel.condition (K.sc (p + 1)).f)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.zero_app] at h
  exact h

end AlgebraicGeometry
