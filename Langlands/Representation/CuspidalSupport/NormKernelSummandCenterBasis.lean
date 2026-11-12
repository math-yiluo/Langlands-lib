import Langlands.Representation.CuspidalSupport.NormalHeckeHomDetection
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement
import Langlands.Representation.CuspidalSupport.LeviCenterDescent

/-! # A finite center basis for the actual norm-kernel summand induction

The VI.4.4 argument supplies this basis without choosing a standard family. A separate
algebraic lemma composes finite unique right expansions. Neither constructs the
endomorphism basis of parabolic induction.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u v

/-- A finite basis over the center gives unique right-coefficient expansions. -/
theorem unique_center_right_expansion {R : Type*} [Ring R] {n : ℕ}
    (c : Module.Basis (Fin n) (Subring.center R) R) (x : R) :
    ∃! z : Fin n → Subring.center R, x = ∑ i, c i * (z i : R) := by
  have hsum (z : Fin n → Subring.center R) :
      (∑ i, c i * (z i : R)) = c.equivFun.symm z := by
    rw [Module.Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (Subring.mem_center_iff.mp (z i).property (c i))
  refine ⟨c.equivFun x, (hsum _).trans (c.equivFun.symm_apply_apply x) |>.symm, ?_⟩
  intro z hz
  apply c.equivFun.symm.injective
  exact ((hsum z).symm.trans hz.symm).trans (c.equivFun.symm_apply_apply x).symm

/-- Compose two finite unique right expansions, without requiring a central image in
the larger ring. -/
theorem unique_right_expansion_trans {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {n m : ℕ} (b : Fin n → S) (c : Fin m → R)
    (hb : ∀ x : S, ∃! a : Fin n → R, x = ∑ i, b i * f (a i))
    (hc : ∀ a : R, ∃! z : Fin m → Subring.center R, a = ∑ j, c j * (z j : R)) :
    ∀ x : S, ∃! z : Fin n × Fin m → Subring.center R,
      x = ∑ k, (b k.1 * f (c k.2)) * f (z k : R) := by
  classical
  have hsum (z : Fin n × Fin m → Subring.center R) :
      (∑ k, (b k.1 * f (c k.2)) * f (z k : R)) =
        ∑ i, b i * f (∑ j, c j * (z (i, j) : R)) := by
    simp only [Fintype.sum_prod_type, map_sum, map_mul, Finset.mul_sum, mul_assoc]
  intro x
  obtain ⟨a, ha, huniq⟩ := hb x
  choose z hz hzu using fun i => hc (a i)
  refine ⟨fun k => z k.1 k.2, ?_, ?_⟩
  · change x = ∑ k : Fin n × Fin m, (b k.1 * f (c k.2)) * f (z k.1 k.2 : R)
    rw [hsum]
    simpa only [← hz] using ha
  · intro z' hz'
    have heq : (fun i => ∑ j, c j * (z' (i, j) : R)) = a :=
      huniq _ (hz'.trans (hsum z'))
    funext k
    exact congrFun (hzu k.1 (fun j => z' (k.1, j))
      (congrFun heq k.1).symm) k.2

/-- Reindex the composed right expansion by `Fin (n * m)`. -/
theorem finite_unique_right_expansion_trans {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {n m : ℕ} (b : Fin n → S) (c : Fin m → R)
    (hb : ∀ x : S, ∃! a : Fin n → R, x = ∑ i, b i * f (a i))
    (hc : ∀ a : R, ∃! z : Fin m → Subring.center R, a = ∑ j, c j * (z j : R)) :
    ∃ d : Fin (n * m) → S, ∀ x : S, ∃! z : Fin (n * m) → Subring.center R,
      x = ∑ i, d i * f (z i : R) := by
  let e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv
  let d : Fin (n * m) → S := fun i => b (e.symm i).1 * f (c (e.symm i).2)
  have hs (z : Fin (n * m) → Subring.center R) :
      (∑ i, d i * f (z i : R)) =
        ∑ k : Fin n × Fin m, (b k.1 * f (c k.2)) * f (z (e k) : R) := by
    simpa only [d, e.symm_apply_apply] using
      (e.sum_comp (fun i => d i * f (z i : R))).symm
  refine ⟨d, fun x => ?_⟩
  obtain ⟨z, hz, hzu⟩ := unique_right_expansion_trans f b c hb hc x
  refine ⟨fun i => z (e.symm i), ?_, ?_⟩
  · change x = ∑ i, d i * f (z (e.symm i) : R)
    rw [hs]
    simpa only [e.symm_apply_apply] using hz
  · intro z' hz'
    have heq : (fun k => z' (e k)) = z := hzu _ (hz'.trans (hs z'))
    funext i
    simpa only [e.apply_symm_apply] using congrFun heq (e.symm i)

/-- The actual compact induction of an irreducible norm-kernel summand is finite free
over its center for any connected reductive group. Its rank is the square of the
multiplicity in the restriction of `π`. No standard-family data are required. -/
theorem exists_rationalNormKernelSummandEndCenterBasis
    {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : GroupScheme.IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology k G.X
    ∀ (π : SmoothRep.{0, u, v} ℂ (GroupScheme.rationalPoints G)),
      π.IsIrreducible →
      ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalCommonNormKernel G)),
        ρ.IsIrreducible →
        ∀ j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π,
          Function.Injective (SmoothRep.hom j) →
          ∃ m : ℕ,
            Module.rank ℂ (ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π) = m ∧
            Nonempty (Module.Basis (Fin (m ^ 2))
              (Subring.center (End (rationalNormKernelSummandInduction G ρ)))
              (End (rationalNormKernelSummandInduction G ρ))) := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology k G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) := rationalPoint_isTopologicalGroup k G
  intro π hπ ρ hρ j hj
  classical
  have hlen := (rationalNormKernelFiniteRestriction k G hG π hπ).2.1
  have : ρ.representation.IsIrreducible := hρ
  have := finiteDimensional_rationalSummandHom hρ hlen
  have := nontrivial_rationalSummandHom hρ j hj
  let e := NormalHecke.inducedLiftHomEquiv (rationalCommonNormKernel G) ρ
    (isOpen_rationalCommonNormKernel G) π
  have : FiniteDimensional ℂ (ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π) :=
    Module.Finite.equiv e
  refine ⟨Module.finrank ℂ (ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π),
    (Module.finrank_eq_rank ℂ _).symm, ?_⟩
  rw [← e.finrank_eq]
  exact NormalHecke.exists_basis_center ρ (isOpen_rationalCommonNormKernel G)
    (isDegree_rationalValuation G) (rank_le_aleph0_of_rationalCommonNormKernel G ρ hρ) _
    (rationalSummand_cyclic_of_isIrreducible hπ hρ)

/-- A chosen finite center basis of the actual norm-kernel summand induction,
bundled with its multiplicity and the equality identifying that multiplicity. -/
def rationalNormKernelSummandEndCenterBasis
    {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : GroupScheme.IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology k G.X
    (π : SmoothRep.{0, u, v} ℂ (GroupScheme.rationalPoints G)) →
      π.IsIrreducible →
      (ρ : SmoothRep.{0, u, v} ℂ (rationalCommonNormKernel G)) →
        ρ.IsIrreducible →
        (j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π) →
          Function.Injective (SmoothRep.hom j) →
          Σ m : ℕ, {_c : Module.Basis (Fin (m ^ 2))
            (Subring.center (End (rationalNormKernelSummandInduction G ρ)))
            (End (rationalNormKernelSummandInduction G ρ)) //
            Module.rank ℂ (ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π) = m} := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology k G.X
  intro π hπ ρ hρ j hj
  let m := Classical.choose (exists_rationalNormKernelSummandEndCenterBasis G hG π hπ ρ hρ j hj)
  have hm := Classical.choose_spec
    (exists_rationalNormKernelSummandEndCenterBasis G hG π hπ ρ hρ j hj)
  exact ⟨m, Classical.choice hm.2, hm.1⟩

end Langlands.CuspidalSupport

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.CuspidalSupport

universe u v

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M N : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance summandCenterAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- For the actual rational Levi induction, a finite unique expansion over `End Π_D`
implies the final finite-center expansion of VI.10.4, without a standard-family
premise. The expansion over `End Π_D` remains an explicit input. -/
theorem leviInducedEndCenterExpansion_of_endExpansion
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints M)), π.IsIrreducible →
      ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalCommonNormKernel M)), ρ.IsIrreducible →
        ∀ j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel M) π,
          Function.Injective (SmoothRep.hom j) →
          let piD := rationalNormKernelSummandInduction M ρ
          let I := leviInductionFunctor p l r hp hr hl hmul
          ∀ (n : ℕ) (b : Fin n → End (I.obj piD)),
            (∀ x : End (I.obj piD),
              ∃! a : Fin n → End piD, x = ∑ i, I.map (a i) ≫ b i) →
            ∃ (s : ℕ) (c : Fin s → End (I.obj piD)),
              ∀ x : End (I.obj piD), ∃! z : Fin s → Subring.center (End piD),
                x = ∑ i, I.map ((z i : End piD) : piD ⟶ piD) ≫ c i := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  intro π hπ ρ hρ j hj piD I n b hb
  let ⟨m, c⟩ := rationalNormKernelSummandEndCenterBasis M
    hl.isConnectedReductive π hπ ρ hρ j hj
  let := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
  let f : End piD →+* End (I.obj piD) :=
    { I.mapEnd piD with
      map_zero' := I.map_zero _ _
      map_add' := fun _ _ => I.map_add }
  obtain ⟨d, hd⟩ := finite_unique_right_expansion_trans f b c.val hb
    (unique_center_right_expansion c.val)
  exact ⟨n * (m ^ 2), d, hd⟩

end Langlands.Aubert.General.RepresentedParabolic
