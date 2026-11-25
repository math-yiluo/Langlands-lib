/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.AlgebraicGeometry.PerfectSummand
import all WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-! # Perfect complexes form a thick subcategory

Source: literature/stacks-project/cohomology.tex, Tags 08CR (lemma-two-out-of-three-perfect)
and 08CS (lemma-summands-perfect), and Definition 08CM (blueprint: lem-pc-perfect-thick-closure).
-/

@[expose] public section

universe u w v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

/-- Perfect complexes are closed under distinguished triangles, direct summands, shifts, and
finite direct sums.
Source: Stacks Project, Cohomology of Sheaves, Tags 08CR and 08CS and Definition 08CM
(blueprint: lem-pc-perfect-thick-closure).

Proof: Apply `lem-pc-perfect-two-out-of-three` (Tag 08CR) to each pair of perfect terms
of a distinguished triangle. Apply `lem-pc-perfect-summand` (Tag 08CS) to the decomposition
of a perfect binary direct sum to obtain perfectness of both summands. Reuse `perfect_shift`,
which shifts local strictly perfect representatives by reindexing their terms. The explicit
zero complex represents zero. Perfectness is invariant under isomorphisms by `perfect_of_iso`.
Split distinguished triangles give perfectness of binary sums. Mathlib's finite-product
closure theorem then gives perfectness of finite biproducts, including the empty biproduct.
-/
theorem perfect_thick_closure (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    (∀ (T : Triangle (schemeDerivedCategory X)),
      T ∈ distTriang (schemeDerivedCategory X) →
      (IsPerfect X T.obj₁ → IsPerfect X T.obj₂ → IsPerfect X T.obj₃) ∧
      (IsPerfect X T.obj₂ → IsPerfect X T.obj₃ → IsPerfect X T.obj₁) ∧
      (IsPerfect X T.obj₁ → IsPerfect X T.obj₃ → IsPerfect X T.obj₂)) ∧
    (∀ (K L : schemeDerivedCategory X),
      IsPerfect X (K ⊞ L) → IsPerfect X K ∧ IsPerfect X L) ∧
    (∀ (K : schemeDerivedCategory X) (n : ℤ),
      IsPerfect X K → IsPerfect X (K⟦n⟧)) ∧
    (∀ (I : Type v) [Finite I] (K : I → schemeDerivedCategory X),
      (∀ i : I, IsPerfect X (K i)) → IsPerfect X (⨁ K)) := by
  have htri := fun T hT => isPerfect_two_out_of_three X T hT
  have hsum : ∀ (K L : schemeDerivedCategory X),
      IsPerfect X (K ⊞ L) → IsPerfect X K ∧ IsPerfect X L := by
    intro K L hKL
    exact perfect_of_directSum X (K ⊞ L) K L ⟨Iso.refl _⟩ hKL
  refine ⟨?_, hsum, ?_, ?_⟩
  · exact htri
  · intro K n hK
    exact perfect_shift X hK n
  · intro I _ K hK
    classical
    let : Zero (schemeDerivedCategory X) := HasZeroObject.zero' _
    let P := perfectSubcategory X
    have hiso : P.IsClosedUnderIsomorphisms := by
      constructor
      intro E F e hE
      exact perfect_of_iso X e hE
    have hzero : P (0 : schemeDerivedCategory X) := by
      intro x
      let U : X.Opens := ⊤
      let A : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ := HomologicalComplex.zero
      have hA : IsStrictlyPerfect X U A := by
        constructor
        · exact ⟨0, 0, fun n _ ↦ Functor.map_isZero
            (HomologicalComplex.eval _ _ n)
            (show IsZero A from HomologicalComplex.isZero_zero)⟩
        · intro n
          refine ⟨0, 0, 0, ?_⟩
          have hn := Functor.map_isZero (HomologicalComplex.eval _ _ n)
            (show IsZero A from HomologicalComplex.isZero_zero)
          exact hn.eq_of_src _ _
      refine ⟨U, by simp [U], A, hA, ?_⟩
      exact ⟨IsZero.iso (Functor.map_isZero _ (isZero_zero _))
        (Functor.map_isZero DerivedCategory.Q HomologicalComplex.isZero_zero)⟩
    have : P.ContainsZero := ⟨0, isZero_zero _, hzero⟩
    have hbin (E F : schemeDerivedCategory X) (hE : P E) (hF : P F) : P (E ⊞ F) :=
      (htri (binaryBiproductTriangle E F)
        (binaryBiproductTriangle_distinguished E F)).2.2 hE hF
    have : P.IsClosedUnderBinaryProducts := by
      apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
      rintro _ ⟨F, hF⟩
      let E := F.obj ⟨WalkingPair.left⟩
      let G := F.obj ⟨WalkingPair.right⟩
      exact P.prop_of_iso
        (biprod.isoProd E G ≪≫ (HasLimit.isoOfNatIso (diagramIsoPair F)).symm)
        (hbin E G (hF _) (hF _))
    have : P.IsClosedUnderFiniteProducts := ObjectProperty.IsClosedUnderFiniteProducts.mk'
    exact P.prop_of_isLimit_fan (biproduct.isLimit K) hK

end AlgebraicGeometry.Scheme
