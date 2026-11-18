import Langlands.Representation.MatrixCoefficient.LatticeFaceTools
import Langlands.Representation.MatrixCoefficient.UnipotentLatticeBoundProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrableOfUpperBound

/-! # Height control on translated cocharacter sublattices -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Coordinates in any cocharacter sublattice are controlled by matrix height,
also after a fixed translation in the ambient lattice. The basis is chosen
before the translation. -/
theorem exists_submodule_basis_coord_height
    (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) (hi : IsClosedSubgroup i)
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (K : Submodule ℤ (cocharacterLattice S)) :
    letI : Module ℤ K := K.module
    ∃ (d : ℕ) (bK : Module.Basis (Fin d) ℤ K),
      ∀ m : cocharacterLattice S, ∃ C : ℝ, 0 < C ∧ ∀ x : K,
        1 + ∑ j, |(bK.repr x j : ℝ)| ≤
          C * (1 + rationalHeight (F := F) ρ
            (Aubert.General.uniformizerPowers i (.ofAdd ((x : cocharacterLattice S) + m)))) := by
  classical
  let : Module ℤ K := K.module
  obtain ⟨I, hI, ⟨e⟩⟩ := hS.exists_cocharacterCoordinates
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨d, bK, ell, hell⟩ :=
    LatticeFaceTools.exists_basis_coord_bound ((Pi.basisFun ℤ I).map e.symm) K
  have := CocharacterUniformizer.latticePairing_isPerfPair F S hS
  have hα : ∀ j : Fin d, ∃ α : characterLattice S, ∀ y,
      latticePairing S α y = ell j y := by
    intro j
    obtain ⟨α, hα⟩ := (LinearMap.IsPerfPair.bijective_left (latticePairing S)).2 (ell j)
    exact ⟨α, fun y => LinearMap.congr_fun hα y⟩
  choose α hα using hα
  choose C hC hb using fun j => exists_abs_latticePairing_le i hi ρ hρ (α j)
  refine ⟨d, bK, fun m => ?_⟩
  let Cs : ℝ := ∑ j, C j
  let Ms : ℝ := ∑ j, |(ell j m : ℝ)|
  have hCs : 0 ≤ Cs := Finset.sum_nonneg fun j _ => (hC j).le
  have hMs : 0 ≤ Ms := Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨1 + Cs + Ms, by linarith, fun x => ?_⟩
  let H := rationalHeight (F := F) ρ
    (Aubert.General.uniformizerPowers i (.ofAdd ((x : cocharacterLattice S) + m)))
  have hH : 0 ≤ H := rationalHeight_nonneg ρ _
  have hcoord (j : Fin d) : |(bK.repr x j : ℝ)| ≤
      C j * (1 + H) + |(ell j m : ℝ)| := by
    have heq : (ell j (x : cocharacterLattice S) : ℝ) =
        (ell j ((x : cocharacterLattice S) + m) : ℝ) - (ell j m : ℝ) := by
      simp only [map_add, Int.cast_add, add_sub_cancel_right]
    calc
      _ ≤ |(ell j x : ℝ)| := hell x j
      _ ≤ |(ell j ((x : cocharacterLattice S) + m) : ℝ)| + |(ell j m : ℝ)| := by
        rw [heq]
        exact abs_sub _ _
      _ ≤ _ := add_le_add (by
        simpa only [hα] using (hb j ((x : cocharacterLattice S) + m))) le_rfl
  have hs : ∑ j, |(bK.repr x j : ℝ)| ≤ Cs * (1 + H) + Ms := by
    calc
      _ ≤ ∑ j, (C j * (1 + H) + |(ell j m : ℝ)|) :=
        Finset.sum_le_sum fun j _ => hcoord j
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  change 1 + ∑ j, |(bK.repr x j : ℝ)| ≤ (1 + Cs + Ms) * (1 + H)
  nlinarith

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A uniformly unipotent action of any cocharacter sublattice has coefficient
bounds in the actual height on each translated lattice. The exponent is fixed
before the vector, functional, and translation. -/
theorem exists_unipotent_submodule_coefficient_height
    (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) (hi : IsClosedSubgroup i)
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (K : Submodule ℤ (cocharacterLattice S))
    (π : Representation ℂ (Multiplicative K) V)
    (r : ℕ) (hr : ∀ x, (π x - 1) ^ r = 0) :
    ∃ d : ℕ, ∀ (v : V) (ell : Module.Dual ℂ V) (m : cocharacterLattice S),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : K,
        ‖ell (π (.ofAdd x) v)‖ ≤ C *
          (1 + rationalHeight (F := F) ρ
            (Aubert.General.uniformizerPowers i (.ofAdd ((x : cocharacterLattice S) + m)))) ^ d := by
  classical
  let : Module ℤ K := K.module
  obtain ⟨d, bK, hbK⟩ := exists_submodule_basis_coord_height i hS hi ρ hρ K
  let f : Multiplicative (Fin d → ℤ) →* Multiplicative K :=
    { toFun := fun a => .ofAdd (bK.equivFun.symm a.toAdd)
      map_one' := by simp
      map_mul' := by
        intro a b
        apply Multiplicative.toAdd.injective
        change bK.equivFun.symm (a.toAdd + b.toAdd) =
          bK.equivFun.symm a.toAdd + bK.equivFun.symm b.toAdd
        exact map_add _ _ _ }
  let π' : Representation ℂ (Multiplicative (Fin d → ℤ)) V := π.comp f
  refine ⟨d * r, fun v ell m => ?_⟩
  obtain ⟨C, hC, hbound⟩ := unipotentLatticeCoefficientBound d r V π'
    (fun j => hr (f (.ofAdd (Pi.single j 1)))) v ell
  obtain ⟨A, hA, hheight⟩ := hbK m
  refine ⟨C * A ^ (d * r), mul_nonneg hC (pow_nonneg hA.le _), fun x => ?_⟩
  have heq : π' (.ofAdd (bK.equivFun x)) = π (.ofAdd x) := by
    change π (.ofAdd (bK.equivFun.symm (bK.equivFun x))) = π (.ofAdd x)
    rw [LinearEquiv.symm_apply_apply]
  have hbase : 0 ≤ 1 + ∑ j, |(bK.repr x j : ℝ)| := by positivity
  have hbound' := hbound (bK.equivFun x)
  change ‖ell (π' (.ofAdd (bK.equivFun x)) v)‖ ≤
    C * (1 + ∑ j, |(bK.equivFun x j : ℝ)|) ^ (d * r) at hbound'
  rw [heq] at hbound'
  simp only [Module.Basis.equivFun_apply] at hbound'
  calc
    _ ≤ C * (1 + ∑ j, |(bK.repr x j : ℝ)|) ^ (d * r) := hbound'
    _ ≤ C * (A * (1 + rationalHeight (F := F) ρ
        (Aubert.General.uniformizerPowers i (.ofAdd ((x : cocharacterLattice S) + m))))) ^
          (d * r) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase (hheight x) (d * r)) hC
    _ = _ := by rw [mul_pow, ← mul_assoc]

end Langlands.HarishChandraSchwartz
