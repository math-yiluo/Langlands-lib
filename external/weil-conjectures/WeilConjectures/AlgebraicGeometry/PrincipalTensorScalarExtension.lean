/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.Algebra.Homology.InternalKFlatScalarTowerRealization

/-! # Derived tensor and extension-restriction with their specified maps

Source: blueprint, derived Nakayama resolution, On X paragraph.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PrincipalNormalization

attribute [local irreducible] upperStarFromPoint
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Tensor with the pulled-back finite quotient agrees with derived extension followed
by restriction, preserving the quotient transitions and the adjunction units.

Source: blueprint derived Nakayama resolution, On X paragraph; principal reduction
normalization proof steps 2 and 3.
(auxiliary; not a blueprint node).

Proof: the coequalizer for extension followed by restriction is the balanced tensor
with the restricted regular quotient. Its inverse sends the class of b tensor x to
the extension generator b tensor x; the two balancing relations coincide. The
braiding puts the quotient in the second variable. This identifies the ordinary
unit with the right unitor inverse followed by tensoring the quotient unit.
For a K-flat representative P the derived computation counit is invertible, and
exact restriction commutes with localization. Compose these with the ordinary
balanced comparison and the K-flat tensor computation. Naturality extends through
roofs of K-flat complexes and gives the stated natural isomorphism. On generators
the quotient transition sends b tensor x to its image tensor x. Taking its mate
under the extension-restriction adjunction gives precisely integralStep: the
composition of restrictions is restrictComp and uniqueness of left adjoints gives
reductionComp. Compatibility of the derived adjunction with its computation counit
identifies the unit, so no unit or transition is chosen anew. Zero complexes and
the empty scheme require no exception. -/
theorem principal_tensor_scalar_extension :
    ∃ e : ∀ n : ℕ, DerivedNakayama.reductionFunctor l E X (n + 1) ≅
        AdicCompletion.derivedReduction l E X n ⋙ AdicCompletion.restrict l E X n,
      (∀ (n : ℕ) (K : DerivedNakayama.Derived l E X),
        (DerivedNakayama.reductionMap l E X (AdicCompletion.quotientStep l E n)).app K ≫
            (e n).hom.app K =
          (e (n + 1)).hom.app K ≫ AdicCompletion.integralStep l E X K n) ∧
      (∀ (n : ℕ) (K : DerivedNakayama.Derived l E X),
        ((ρ_ K).inv ≫ K ◁
          (Functor.LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map
            ((HomologicalComplex.single _ (.up ℤ) 0).map
              (AdicCompletion.finiteUnit l E X n)))) ≫ (e n).hom.app K =
          (Mod.derivedExtendMapDerivedCategoryAdjunction
            (AdicCompletion.quotient l E X n)).unit.app K)  := by
  exact Mod.KFlatScalarTower.derived_realization
    (AdicCompletion.ring l E X) (AdicCompletion.finiteRing l E X)
    (AdicCompletion.quotient l E X) (AdicCompletion.transition l E X)
    (AdicCompletion.quotient_transition l E X) (AdicCompletion.finiteModule l E X)
    (AdicCompletion.finiteUnit l E X)
    (fun n ↦ (DerivedNakayama.pullback l E X).map (AdicCompletion.quotientStep l E n))
    (fun n ↦ (Functor.mapModComapIso (upperStarFromPoint X)
      (DerivedNakayama.reductionRing l E (n + 1))).app
        (Mod.regular (DerivedNakayama.quotientRing l E (n + 1))))
    (by
      intro n
      change (𝟙 _ ≫ (upperStarFromPoint X).map
        (DerivedNakayama.reductionRing l E (n + 1))) ≫ 𝟙 _ =
          AdicCompletion.quotient l E X n
      simp only [Category.id_comp, Category.comp_id])
    (by
      intro n
      change (upperStarFromPoint X).map (AdicCompletion.transitionRing l E n) ≫ 𝟙 _ =
        𝟙 _ ≫ (upperStarFromPoint X).map (AdicCompletion.transitionRing l E n)
      simp only [Category.id_comp, Category.comp_id])

end AlgebraicGeometry.ProEtale.PrincipalNormalization
