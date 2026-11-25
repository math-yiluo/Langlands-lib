/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.Projective
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.CategoryTheory.Sites.Subcanonical
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Equivalent forms of weak contractibility

## References

* Stacks Project, Tags 001P and 00WN
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The three equivalent lifting and evaluation formulations of weak contractibility.

An object satisfying the equivalent conditions is called weakly contractible.
-/
theorem proetale_weakContractible_equivalences
    (X : Scheme.{u}) (W : X.ProEt) :
    ((∀ (F : Sheaf (ProEt.topology X) (Type (u + 1)))
          (φ : F ⟶ (ProEt.topology X).uliftYoneda.{u + 1}.obj W) [Epi φ],
        ∃ s : (ProEt.topology X).uliftYoneda.{u + 1}.obj W ⟶ F,
          s ≫ φ = 𝟙 _) ↔
      Projective ((ProEt.topology X).uliftYoneda.{u + 1}.obj W)) ∧
    (Projective ((ProEt.topology X).uliftYoneda.{u + 1}.obj W) ↔
      (∀ (F G : Sheaf (ProEt.topology X) (Type (u + 1)))
          (φ : F ⟶ G) [Epi φ],
        Function.Surjective (φ.hom.app (op W)))) ∧
    (∀ (D : Type u) [CommRing D] [IsWContractibleRing D]
      (f : Spec (.of D) ⟶ X) [WeaklyEtale f],
      ∀ (F : Sheaf (ProEt.topology X) (Type (u + 1)))
        (φ : F ⟶ (ProEt.topology X).uliftYoneda.{u + 1}.obj (ProEt.mk f)) [Epi φ],
      ∃ s : (ProEt.topology X).uliftYoneda.{u + 1}.obj (ProEt.mk f) ⟶ F,
        s ≫ φ = 𝟙 _) := by
  let J := ProEt.topology X
  constructor
  · constructor
    · intro hsplit
      constructor
      intro F G y φ hφ
      have : Sheaf.IsLocallySurjective φ :=
        (Sheaf.isLocallySurjective_iff_epi φ).2 hφ
      have : Epi (Limits.pullback.snd φ y) := by
        apply (Sheaf.isLocallySurjective_iff_epi _).1
        constructor
        intro V t
        apply J.superset_covering _ (Presheaf.imageSieve_mem J φ.hom (y.hom.app _ t))
        intro U g hg
        obtain ⟨a, ha⟩ := hg
        let ev := sheafToPresheaf J (Type (u + 1)) ⋙
          (CategoryTheory.evaluation X.ProEtᵒᵖ (Type (u + 1))).obj (op U)
        have hpb := (IsPullback.of_hasPullback φ y).map ev
        obtain ⟨z, _, hz⟩ := Limits.Types.exists_of_isPullback hpb a
          (((J.uliftYoneda.obj W).obj.map g.op) t) (by
            change φ.hom.app _ a = y.hom.app _ (((J.uliftYoneda.obj W).obj.map g.op) t)
            rw [ha]
            exact (ConcreteCategory.congr_hom (y.hom.naturality g.op) t).symm)
        exact ⟨z, hz⟩
      obtain ⟨s, hs⟩ := hsplit _ (Limits.pullback.snd φ y)
      refine ⟨s ≫ Limits.pullback.fst φ y, ?_⟩
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs, Category.id_comp]
    · intro hP F φ hφ
      have := hP
      exact Projective.factors (𝟙 _) φ
  · constructor
    · constructor
      · intro hP F G φ hφ y
        have := hP
        obtain ⟨s, hs⟩ := Projective.factors (J.uliftYonedaEquiv.symm y) φ
        refine ⟨J.uliftYonedaEquiv s, ?_⟩
        rw [← J.uliftYonedaEquiv_comp, hs, Equiv.apply_symm_apply]
      · intro hEval
        constructor
        intro F G y φ hφ
        obtain ⟨a, ha⟩ := hEval F G φ (J.uliftYonedaEquiv y)
        refine ⟨J.uliftYonedaEquiv.symm a, ?_⟩
        apply J.uliftYonedaEquiv.injective
        rw [J.uliftYonedaEquiv_comp, Equiv.apply_symm_apply, ha]
    · intro D _ _ f _
      exact (proetale_wContractible_projective X D f).1

/-- **Weak contractibility and projectivity of the representable sheaf.** An object `W` of the
small pro-étale site of `X` is weakly contractible (every epimorphism of sheaves of sets is
surjective on sections over `W`) if and only if the representable sheaf `h_W` is projective:
epimorphisms of sheaves of sets are the locally surjective morphisms
(`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`), and the second equivalence of
`AlgebraicGeometry.Scheme.proetale_weakContractible_equivalences` identifies the surjectivity
condition with projectivity. -/
theorem isWeaklyContractible_iff_projective (X : Scheme.{u}) (W : X.ProEt) :
    (ProEt.topology X).IsWeaklyContractible.{u + 1} W ↔
      Projective ((ProEt.topology X).uliftYoneda.{u + 1}.obj W) := by
  rw [(proetale_weakContractible_equivalences X W).2.1]
  constructor
  · intro h F G φ _
    exact h φ ((Sheaf.isLocallySurjective_iff_epi φ).2 inferInstance)
  · intro h F G φ hφ
    have : Epi φ := (Sheaf.isLocallySurjective_iff_epi φ).1 hφ
    exact h F G φ

/-- **Weak contractibility by splitting of epimorphisms onto the representable sheaf.** An object
`W` of the small pro-étale site of `X` is weakly contractible if and only if every epimorphism
of sheaves of sets `F ⟶ h_W` admits a section: both conditions are equivalent to the
projectivity of `h_W` (`AlgebraicGeometry.Scheme.isWeaklyContractible_iff_projective` and the
first equivalence of `AlgebraicGeometry.Scheme.proetale_weakContractible_equivalences`). -/
theorem isWeaklyContractible_iff_forall_epi_splits (X : Scheme.{u}) (W : X.ProEt) :
    (ProEt.topology X).IsWeaklyContractible.{u + 1} W ↔
      ∀ (F : Sheaf (ProEt.topology X) (Type (u + 1)))
        (φ : F ⟶ (ProEt.topology X).uliftYoneda.{u + 1}.obj W) [Epi φ],
        ∃ s : (ProEt.topology X).uliftYoneda.{u + 1}.obj W ⟶ F, s ≫ φ = 𝟙 _ :=
  (isWeaklyContractible_iff_projective X W).trans
    (proetale_weakContractible_equivalences X W).1.symm

end AlgebraicGeometry.Scheme
