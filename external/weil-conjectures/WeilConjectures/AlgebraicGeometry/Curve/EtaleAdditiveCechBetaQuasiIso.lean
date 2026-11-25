/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechCoefficientColumns
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-! # The affine coefficient augmentation is a quasi-isomorphism

Source: Stacks Project, Tags 03P2 and 01EQ. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The usual sign (-1)^(pq) also gives total-complex symmetry over the naturals.
@[instance_reducible]
private def natTotalSymmetry :
    TotalComplexShapeSymmetry (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p _ rfl q
    change (-1 : ℤˣ) ^ (p * q) * 1 =
      (-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ ((p + 1) * q)
    rw [mul_one, Nat.add_mul, one_mul, pow_add]
    calc
      _ = (-1 : ℤˣ) ^ (p * q) *
          ((-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ q) := by rw [Int.units_mul_self, mul_one]
      _ = _ := mul_left_comm _ _ _
  σ_ε₂ := by
    rintro p q _ rfl
    change (-1 : ℤˣ) ^ (p * q) * (-1 : ℤˣ) ^ p =
      1 * (-1 : ℤˣ) ^ (p * (q + 1))
    rw [one_mul, Nat.mul_add, Nat.mul_one, pow_add]

/-- The fixed coefficient augmentation extends to a quasi-isomorphism from the
lifted ordinary unit Cech complex. No covering or compactness assumption is needed.
Source: Stacks Project, Theorem 59.22.4 (Tag 03P2), separated affine intersections;
Lemma 20.11.2 (Tag 01EQ), the beta augmentation, and Homology Lemma 12.25.4.
(blueprint: lem-pbc-additive-cech-beta-quasi-iso)

Proof: Forget the scalars of the ordinary unit Cech complex and apply ULift.
For every tuple of opens the inverse of restrictFunctorGamma identifies unit
sections with functions on the corresponding open subscheme. These maps commute
with restrictions, including the structural scalar restriction along toSpecGamma.
Since the tuple index sets are finite, forgetting scalars and ULift commute with
these products. Thus this identifies the lifted complex with the Cech complex of
etaleAdditiveSheaf restricted to opens, with exactly the coordinates displayed
in additiveCechBeta. Apply the resolution augmentation into I^0 on every tuple.
Naturality makes these maps commute with the alternating horizontal differential;
the augmentation followed by the vertical differential is zero. Inclusion into
bidegree (n,0) therefore yields a chain map b with the displayed components.
Each tuple intersection is affine by hU (categorical products of opens agree with
their infima). Positive derived evaluation of the additive structure sheaf there
vanishes by affine quasi-coherent acyclicity, while degree zero is evaluation of
the sheaf itself. Products of abelian groups are exact, so every augmented
vertical column is a resolution. The first-quadrant augmentation comparison,
applied after exchanging indices, makes b a quasi-isomorphism. This does not use
exactness of augmented horizontal rows or a covering condition. For degree zero
it is the kernel computation of the resolution. Empty tuple families give zero
complexes; empty intersections have zero sections; repeated opens cause no change.
The component equation determines b uniquely, so no arbitrary existence witness
is used as data in a definition. -/
theorem exists_additiveCech_beta_quasiIso
    (X : Scheme.{u}) [X.IsSeparated] {ι : Type u} [Finite ι]
    (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf) :
    ∃ b : (((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
          (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf))) ⟶
        additiveCechTotal U I,
      (∀ (n : ℕ) (x : (cechOver X.toSpecΓ U
        (SheafOfModules.unit X.ringCatSheaf)).X n),
        b.f n (ULift.up x) = additiveCechBeta U I n x) ∧ QuasiIso b := by
  let D := etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I
  let K := D.flip
  let A := additiveCechCoefficientComplex U
  let a : A ⟶ K.X 0 :=
    { f := additiveCechCoefficientMap U I
      comm' := fun n m _ ↦ additiveCechCoefficientMap_comm U I n m }
  have ha : a ≫ K.d 0 1 = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    exact additiveCechCoefficientMap_vertical U I n
  let b : A ⟶ K.total (.up ℕ) :=
    { f := fun n ↦ a.f n ≫ K.ιTotal (.up ℕ) 0 n n (by simp)
      comm' := by
        intro n m h
        have hm : n + 1 = m := h
        subst m
        simp only [HomologicalComplex₂.total_d, Category.assoc,
          Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
        rw [K.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel 0 1)
          n (n + 1) (by simp [Nat.add_comm]),
          K.d₂_eq (.up ℕ) 0
            (by simp : (ComplexShape.up ℕ).Rel n (n + 1)) (n + 1) (by simp)]
        have hz := congrArg (fun f ↦ f.f n) ha
        simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
        have hs₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (0, n) = 1 := rfl
        have hs₂ : ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (0, n) = 1 := by
          change (-1 : ℤˣ) ^ 0 = 1
          exact pow_zero _
        simp only [hs₁, hs₂, one_smul, ← Category.assoc, hz,
          CategoryTheory.Limits.zero_comp, zero_add]
        rw [a.comm n (n + 1)] }
  have hb : QuasiIso b := HomologicalComplex₂.quasiIso_of_column_augmentation
    K A a ha b (fun _ ↦ rfl) (fun n ↦ additiveCechCoefficientMap_column_quasiIso X U hU I n)
  let : TotalComplexShapeSymmetry (.up ℕ) (.up ℕ) (.up ℕ) := natTotalSymmetry
  let e := D.totalFlipIso (.up ℕ)
  refine ⟨b ≫ e.hom, ?_, ?_⟩
  · intro n x
    have he : K.ιTotal (.up ℕ) 0 n n (by simp) ≫ e.hom.f n =
        D.ιTotal (.up ℕ) n 0 n (by simp) := by
      rw [HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
      change (-1 : ℤˣ) ^ (n * 0) • D.ιTotal (.up ℕ) n 0 n _ = _
      simp only [Nat.mul_zero, pow_zero, one_smul]
    change (a.f n ≫ K.ιTotal (.up ℕ) 0 n n (by simp) ≫ e.hom.f n) (ULift.up x) = _
    rw [he]
    rfl
  · infer_instance


end AlgebraicGeometry.Scheme.Modules
