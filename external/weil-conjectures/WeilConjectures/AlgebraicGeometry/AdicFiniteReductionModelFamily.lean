/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.AlgebraicGeometry.AdicResiduePerfectReductionComparison
import WeilConjectures.AlgebraicGeometry.AdicResidueStalkTowerFamily
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-! # A covering family with one perfect model for all finite reductions

Source: Stacks Project, proetale.tex, Tag 09C6, first half of the proof.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

/-- Apply algebraic reconstruction before passing to a constant sheaf or a slice. -/
private theorem adicResidueAlgebraTower_model
    {A : Type w} [CommRing A] (J : Ideal A) [IsAdicComplete J A]
    (T : AdicResidueAlgebraTower J) :
    ∃ (P : CochainComplex (ModuleCat.{w} A) ℤ) (c d : ℤ),
      P.IsStrictlyGE c ∧ P.IsStrictlyLE d ∧
      (∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) ∧
      ∀ n : ℕ, Nonempty ((T.extension n).obj (DerivedCategory.Q.obj P) ≅ T.level n) := by
  classical
  obtain ⟨hprod, _, _⟩ := derivedCategory_countableProducts_core.{0} (ModuleCat.{w} A)
  let := hprod
  obtain ⟨E, p, δ, hlim⟩ :=
    (exists_isDerivedLimit_and_iso
      (fun n ↦ (DerivedCategory.adicLevelRestriction J n).obj (T.level n))
      (DerivedCategory.adicTowerTransition J T.level T.transition)).1
  obtain ⟨hE, _, hred, _⟩ := DerivedCategory.rlim_perfect_complete J T.level T.transition
    T.extension T.adjunction T.stepExtension T.stepAdjunction T.normalized
    T.residuePerfect E p δ hlim
  obtain ⟨P, c, d, hc, hd, hP, ⟨e⟩⟩ := hE
  refine ⟨P, c, d, hc, hd, fun q ↦ ⟨(hP q).2, (hP q).1⟩, ?_⟩
  intro n
  exact ⟨(T.extension n).mapIso e.symm ≪≫ @asIso _ _ _ _
    (DerivedCategory.adicLimitReduction J T.level T.extension T.adjunction E p n) (hred n)⟩

/-- A covering family with a bounded finite-projective algebraic model for all
finite reductions. Completeness of either object on the slice is a separate assertion.
Source: Stacks Project, proetale.tex, Tag 09C6, first paragraph through the choice of
an affine weakly contractible cover; Tags 09C2, 094I, 09BI and 09AW.
(auxiliary; not a blueprint node).

Proof: Restrict scalars to the constant A-sheaf using the constant-completion
comparison. Lisse finite-type cohomology is constructible on the one-stratum
stratification, so the finite-reduction theorem gives etale lifts C_n, with a common
Tor interval and normalized quotient maps. Cover X by connected clopen components
of Noetherian affine charts. Slice localization is exact and preserves the quotient
completion unit and finite reductions. Nilpotent-reduction lissity makes each C_n
lisse. On each nonempty component choose a geometric point and take the stalks of
this normalized system. Connected perfect constancy makes these stalks perfect,
and exact tensor-compatible stalks give their consecutive derived reduction
isomorphisms. Apply algebraic perfect inverse-limit reconstruction over the complete
ring A and choose a bounded finite-projective representative P. Cover the component
by affine weakly contractible objects. The weakly contractible clause of connected
perfect constancy identifies every restricted C_n with the constant stalk complex.
The algebraic reduction isomorphisms for P and the scalar-extension/pullback
comparisons identify the actual slice reductions of B tensor P and M at every level.
Take the composite covering family, retaining the chosen P on each member. Empty
charts contribute the empty family. No compatible local markings are needed. -/
theorem adicResidue_finite_reduction_model_family
    (X : Scheme.{u}) [IsNoetherian X]
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [IsAdicComplete J A]
    (M : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J))
    (_hcomplete : CategoryTheory.ConstantCompletion.IsComplete
      (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X) A
        J 0) M)
    (C : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A J 0))
    (_hbounded : ∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (_hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) (A ⧸ J ^ (0 + 1))
      ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (a b : ℤ) (_hab : a ≤ b)
    (_htor : ∀ P : CategoryTheory.ConstantCompletion.Cx
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := smallModelComparisonEtaleTopology.{u, v} X)
        (R := CategoryTheory.ConstantCompletion.finite
          (smallModelComparisonEtaleTopology.{u, v} X) A J 0) P →
      Nonempty ((CategoryTheory.ConstantCompletion.Q
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)).obj P ≅ C) →
      ∀ (N : CategoryTheory.ConstantCompletion.Mod
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0))
        (q : ℤ), q < a ∨ b < q →
        IsZero (adicResidueTensorCohomology.{max v (u + 1)}
          (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X)
            A J 0) P N q))
    (_hres : Nonempty
      ((CategoryTheory.ConstantCompletion.extend
        (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X)
          A J 0)).obj M ≅
        (adicResidueComparison.{u, v} X (A ⧸ J ^ (0 + 1))).obj C)) :
    ∃ (I : Type (max v (u + 1)))
      (V : I → coefficientProEtaleSiteModel.{u, v} X)
      (f : ∀ i : I, V i ⟶
        (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj (⊤_ X.ProEt)),
      Sieve.ofArrows V f ∈ coefficientProEtaleModelTopology.{u, v} X _ ∧
      ∀ i : I,
        IsAffine ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj
          (V i)).left ∧
        AdicResidueSliceWeaklyContractible.{u, v} X (V i) ∧
        ∃ (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (c d : ℤ),
          P.IsStrictlyGE c ∧ P.IsStrictlyLE d ∧
          (∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) ∧
          ∀ n : ℕ, Nonempty
            ((adicResidueLocalReduction.{u, v} X J (V i) n).obj
              ((adicResidueRestriction
                (CategoryTheory.ConstantCompletion.completed
                  (coefficientProEtaleModelTopology.{u, v} X) A J) (V i)).obj
                    (adicResidueConstantPerfect X J P)) ≅
              (adicResidueLocalReduction.{u, v} X J (V i) n).obj
                ((adicResidueRestriction
                  (CategoryTheory.ConstantCompletion.completed
                    (coefficientProEtaleModelTopology.{u, v} X) A J) (V i)).obj M)) := by
  classical
  obtain ⟨I, V, f, hcover, hlocal⟩ := adicResidue_stalk_tower_family.{u, v}
    X J M _hcomplete C _hbounded _hlisse a b _hab _htor _hres
  refine ⟨I, V, f, hcover, ?_⟩
  intro i
  obtain ⟨haffine, hcontractible, T, hT⟩ := hlocal i
  obtain ⟨P, c, d, hc, hd, hP, e⟩ := adicResidueAlgebraTower_model J T
  refine ⟨haffine, hcontractible, P, c, d, hc, hd, hP, ?_⟩
  intro n
  obtain ⟨r⟩ := adicResidue_perfect_reduction_comparison.{u, v}
    X J (V i) n (T.extension n) (T.adjunction n) P c d hc hd hP
  exact ⟨r ≪≫ (adicResidueFiniteConstant.{u, v} X J (V i) n).mapIso (e n).some ≪≫
    (hT n).some⟩

end AlgebraicGeometry.Scheme
