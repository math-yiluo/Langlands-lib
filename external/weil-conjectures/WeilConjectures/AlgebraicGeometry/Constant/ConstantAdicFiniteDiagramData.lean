/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement

/-! # Finite reductions over the constant completion ring

These constructions involve the constant ring of the algebraic completion, without
passing to the completed sheaf of rings. Source: Stacks Tags 06YY and 093J--093M.
(blueprint: def-weil-pbc-constant-adic-finite-diagram-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Completion evaluation commutes with consecutive quotient maps.
Source: Stacks Tag 093M
(blueprint: def-weil-pbc-constant-adic-finite-diagram-data).
Proof: represent a completion element by an adic Cauchy sequence and apply its
compatibility equation to the two consecutive coordinates. -/
theorem constantAdicCompletion_eval_step
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ) :
    CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 2)).toRingHom ≫
        CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)) =
      CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  change Ideal.Quotient.factorPowSucc I (n + 1)
    (AdicCompletion.evalₐ I (n + 2) (AdicCompletion.mk I A s)) =
      AdicCompletion.evalₐ I (n + 1) (AdicCompletion.mk I A s)
  simp only [AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk _ (s.val (n + 2)) = Ideal.Quotient.mk _ (s.val (n + 1))
  apply Ideal.Quotient.eq.mpr
  have hs := (Submodule.Quotient.eq _).mp
    (AdicCompletion.AdicCauchySequence.mk_eq_mk (Nat.le_succ (n + 1)) s)
  simpa [smul_eq_mul, Ideal.mul_top] using hs

/-- Evaluation from the constant algebraic completion to the finite coefficient diagram.
Source: Stacks Tags 06YY and 093M
(blueprint: def-weil-pbc-constant-adic-finite-diagram-data). -/
def constantAdicFiniteCone (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    Cone (pbcAdicRings X d) :=
  { pt := adicLisseConstantRing X (AdicCompletion d.ideal A)
    π := (NatTrans.ofOpSequence (G := adicLisseRingSystem X d.ideal)
      (fun n ↦ (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ d.ideal (n + 1)).toRingHom))
      (fun n ↦ by
        refine (Category.id_comp _).trans ?_
        simpa only [adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ,
          ← Functor.map_comp] using congrArg
            (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
              (constantAdicCompletion_eval_step d.ideal n).symm)) ≫
      (pbcConstantSystemComparison X d).hom }

/-- The finite quotient projections after inverse image, with their actual coefficients.
Source: Stacks Tags 06YY and 093M
(blueprint: def-weil-pbc-constant-adic-finite-diagram-data). -/
def constantAdicFiniteProjection {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  (adicTowerInverseImage g).map ((constantAdicFiniteCone X d).π.app (op n))

/-- The finite projections commute with every quotient map, including equal indices.
Source: Stacks Tag 06YY
(blueprint: def-weil-pbc-constant-adic-finite-diagram-data).
Proof: apply inverse image to the naturality equation of the explicitly constructed
cone. The two inverse-image maps compose by functoriality. -/
theorem constantAdicFiniteProjection_comp {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (m n : ℕ) (h : n ≤ m) :
    constantAdicFiniteProjection g d m ≫
        (adicTowerInverseImage g).map (pbcAdicQuotient X d m n h) =
      constantAdicFiniteProjection g d n := by
  rw [constantAdicFiniteProjection, constantAdicFiniteProjection, ← Functor.map_comp]
  exact congrArg (adicTowerInverseImage g).map
    ((constantAdicFiniteCone X d).w (homOfLE h).op)

/-- Constant module sheafification is exact.
Source: Stacks Tag 093J
(blueprint: def-weil-pbc-constant-adic-finite-diagram-data).
Proof: use the existing proof that constant module presheaves preserve finite
limits and colimits and that associated-module-sheafification is exact. -/
theorem constantAdicFinite_constant_exact (X : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] :
    PreservesFiniteLimits (adicLisseConstantModules X B) ∧
      PreservesFiniteColimits (adicLisseConstantModules X B) :=
  CompletedConstantReduction.constant_exact X B

/-- Constant algebraic complexes, restricted by exact inverse image. The base ring is
inverse image of the constant algebraic completion, rather than the completed sheaf.
Source: Stacks Tags 093J and 06YY
(blueprint: def-weil-pbc-constant-adic-finite-diagram-data). -/
def constantAdicFiniteRealization {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A)) ⥤
      DerivedCategory (pbcModules Y ((adicTowerInverseImage g).obj
        (adicLisseConstantRing X (AdicCompletion d.ideal A)))) :=
  letI := CompletedConstantReduction.constant_additive X (AdicCompletion d.ideal A)
  letI := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).1
  letI := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).2
  (adicLisseConstantModules X (AdicCompletion d.ideal A)).mapDerivedCategory ⋙
    adicTowerPullback g (adicLisseConstantRing X (AdicCompletion d.ideal A))

end AlgebraicGeometry.Scheme
