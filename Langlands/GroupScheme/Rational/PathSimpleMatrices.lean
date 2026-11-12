import Langlands.GroupScheme.Rational.PathNormalizedMatrices

/-! # Explicit matrices for simple path factors -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  {d : Type} [Fintype d] [DecidableEq d] {ρ : MatrixRepresentation G d}
  {L : ℕ} {β : Fin L → p.base.support} {lam : characterLattice p.torus}
  (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
  (hlam : IsPathFundamental β lam) (x : p.NormalizedSimpleRootParametrizations)
  (v₀ : p.representationWeightSpace ρ (pathWeight β lam 0)) (hv₀ : v₀ ≠ 0)

/-- The signed transposition matrix on consecutive path lines. -/
def pathReflectionMatrix (i : Fin L) : Matrix (Fin (L + 1)) (Fin (L + 1)) k :=
  fun a b => if b = i.castSucc then -(if a = i.succ then 1 else 0)
    else if b = i.succ then (if a = i.castSucc then 1 else 0)
    else if a = b then 1 else 0

/-- The column at the first of the transposed lines. -/
theorem normalizedPathMatrix_canonicalReflection_self (i : Fin L) (a : Fin (L + 1)) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀
        (x (β i)).reflectionRepresentative.point a i.castSucc =
      -(if i.succ = a then 1 else 0) := by
  let b := normalizedPathBasis hρ hβ hlam x v₀ hv₀
  have hm := normalizedPathMatrix_apply hρ hβ hlam x v₀ hv₀
    (x (β i)).reflectionRepresentative.point a i.castSucc
  have ha := canonicalReflection_normalizedPathVector_self hρ hβ hlam x v₀ i.2
  have hc := congrArg (fun z : d → k => b.repr z a) ha
  have hb := congrArg (fun z : d → k => b.repr (-z) a)
    (normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ i.succ).symm
  have he : b.repr (-(b i.succ)) a = -(if i.succ = a then 1 else 0) := by
    rw [map_neg, Finsupp.neg_apply, Module.Basis.repr_self_apply]
  exact hm.trans (hc.trans (hb.trans he))

/-- The column at the second of the transposed lines. -/
theorem normalizedPathMatrix_canonicalReflection_succ (i : Fin L) (a : Fin (L + 1)) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀
        (x (β i)).reflectionRepresentative.point a i.succ =
      (if i.castSucc = a then 1 else 0) := by
  let b := normalizedPathBasis hρ hβ hlam x v₀ hv₀
  have hm := normalizedPathMatrix_apply hρ hβ hlam x v₀ hv₀
    (x (β i)).reflectionRepresentative.point a i.succ
  have ha := canonicalReflection_normalizedPathVector_succ hρ hβ hlam x v₀ i.2
  have hc := congrArg (fun z : d → k => b.repr z a) ha
  have hb := congrArg (fun z : d → k => b.repr z a)
    (normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ i.castSucc).symm
  exact hm.trans (hc.trans (hb.trans (b.repr_self_apply i.castSucc a)))

/-- Columns outside the two transposed path lines are unchanged. -/
theorem normalizedPathMatrix_canonicalReflection_other (i : Fin L) (a b : Fin (L + 1))
    (hb : b ≠ i.castSucc) (hb' : b ≠ i.succ) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀
        (x (β i)).reflectionRepresentative.point a b =
      (if b = a then 1 else 0) := by
  let B := normalizedPathBasis hρ hβ hlam x v₀ hv₀
  have hm := normalizedPathMatrix_apply hρ hβ hlam x v₀ hv₀
    (x (β i)).reflectionRepresentative.point a b
  have ha := canonicalReflection_path_fixes hρ hβ hlam i (x (β i)) (j := b.val)
    (by omega : (b : ℕ) ≤ L)
    (fun h => hb (Fin.ext h)) (fun h => hb' (Fin.ext h))
    (normalizedPathVector hρ hβ hlam x v₀ b).2
  have hc := congrArg (fun z : d → k => B.repr z a) ha
  have hB := congrArg (fun z : d → k => B.repr z a)
    (normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ b).symm
  exact hm.trans (hc.trans (hB.trans (B.repr_self_apply b a)))

/-- The canonical representative of a path vertex is its signed transposition matrix. -/
theorem normalizedPathMatrix_canonicalReflection (i : Fin L) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀
        (x (β i)).reflectionRepresentative.point = pathReflectionMatrix i := by
  apply Matrix.ext
  intro a b
  by_cases hb : b = i.castSucc
  · subst b
    have h := normalizedPathMatrix_canonicalReflection_self hρ hβ hlam x v₀ hv₀ i a
    simpa [pathReflectionMatrix, eq_comm] using h
  · by_cases hb' : b = i.succ
    · subst b
      have h := normalizedPathMatrix_canonicalReflection_succ hρ hβ hlam x v₀ hv₀ i a
      simpa [pathReflectionMatrix, hb, eq_comm] using h
    · have h := normalizedPathMatrix_canonicalReflection_other hρ hβ hlam x v₀ hv₀ i a b hb hb'
      simpa [pathReflectionMatrix, hb, hb', eq_comm] using h

end Langlands.GroupScheme.SplitPinning
