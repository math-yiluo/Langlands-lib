/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Exactness of the supplied integral stage comparison

Source: trace-definition coefficient-category comparison, integral steps 1--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem commShift_eqToIso
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (F G : A ⥤ B) [sF : F.CommShift ℤ] [sG : G.CommShift ℤ] (h : F = G)
    (hs : ∀ (n : ℤ) K,
      HEq ((F.commShiftIso n).hom.app K) ((G.commShiftIso n).hom.app K)) :
    NatTrans.CommShift (eqToIso h).hom ℤ := by
  cases h
  have hi (n : ℤ) : Functor.commShiftIso F (self := sF) n =
      Functor.commShiftIso F (self := sG) n := by
    apply Iso.ext
    ext K
    exact eq_of_heq (hs n K)
  have he : sF = sG := by
    cases sF
    cases sG
    congr 1
    funext n
    exact hi n
  cases he
  change NatTrans.CommShift (𝟙 F) ℤ
  infer_instance

/-- The supplied integral identity equivalence is exact for its normalized shift.
Source: trace-definition coefficient comparison, integral identity step
(blueprint: lem-fd-integral-stage-exact).

Proof: the full intrinsic integral inclusion and the exact coefficient restriction
induce an exact derived composite J. The supplied integral_identity identifies I
followed by the PBC inclusion with J. Equality elimination and the supplied
integral_shift_normalization identify their two integer-shift structures, so this
identity is an exact natural isomorphism. The target full inclusion is exact and
fully faithful; reflection of distinguished triangles gives exactness of I.
-/
theorem fdIntegralStageExact
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (E : Padic.FiniteCoefficientFields l Ω) : (stage E).integral.functor.IsTriangulated := by
  let J := (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
    integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)
  have : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).IsTriangulated :=
    sfIntegralConstructible_isTriangulated l (pbcFiniteField.{u} l Ω E) T
  let sDetailed : (integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).CommShift ℤ := by
    change Functor.CommShift
      (fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapDerivedCategory ℤ
    exact Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt _
  let sJ : J.CommShift ℤ := Functor.CommShift.comp
    (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι
    (integralDetailedTransport T l (pbcFiniteField.{u} l Ω E))
  have : (integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).IsTriangulated := by
    change Functor.IsTriangulated
      (fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapDerivedCategory
    exact Functor.instIsTriangulatedDerivedCategoryMapDerivedCategory _
  have : J.IsTriangulated := by dsimp only [J]; infer_instance
  have e : (stage E).integral.functor ⋙ pbcStageInclusion l Ω T E = J :=
    (stage E).integral_identity
  have hc : NatTrans.CommShift (eqToIso e).hom ℤ := by
    apply commShift_eqToIso _ _ e
    intro n K
    simp only [sJ, J, Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
      ObjectProperty.ι_obj]
    dsimp only [sDetailed, integralDetailedTransport, fdCoefficientTransport]
    exact (stage E).integral_shift_normalization n K
  have := hc
  exact (Functor.isTriangulated_iff_comp_right (eqToIso e)).2 inferInstance

end WeilConjectures
