import Langlands.AlgebraicGeometry.InfinitesimalKernel
import Langlands.GroupScheme.Lie.AffineCoordinates

/-! # Powers in square-zero coefficient kernels -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.SquareZero

namespace Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
  {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Encode a point in the kernel of coefficient change by its identity and
original coordinates in the algebra of congruent pairs. -/
def affineKernelPairsPoint (f : A →ₐ[R] B) (x : AffinePoints G A)
    (hx : affineMap G f x = 1) : AffinePoints G (pairs R (RingHom.ker f)) :=
  (pointCoordinates G).symm
    (pairsLift (pointCoordinates G (1 : AffinePoints G A)) (pointCoordinates G x)
      fun a => by
        have h := DFunLike.congr_fun
          (congrArg (pointCoordinates G) hx) a
        rw [pointCoordinates_naturality, pointCoordinates_one] at h
        change f (pointCoordinates G x a - pointCoordinates G 1 a) = 0
        rw [map_sub, pointCoordinates_one]
        exact sub_eq_zero.mpr (by simpa only [AlgHom.comp_apply,
          Algebra.ofId_apply, f.commutes] using h))

theorem affineKernelPairsPoint_fst (f : A →ₐ[R] B) (x : AffinePoints G A)
    (hx : affineMap G f x = 1) :
    affineMap G (fst R (RingHom.ker f)) (affineKernelPairsPoint G f x hx) = 1 := by
  apply (pointCoordinates G).injective
  rw [pointCoordinates_naturality]
  simp only [affineKernelPairsPoint, Equiv.apply_symm_apply, fst_comp_pairsLift]

theorem affineKernelPairsPoint_snd (f : A →ₐ[R] B) (x : AffinePoints G A)
    (hx : affineMap G f x = 1) :
    affineMap G (snd R (RingHom.ker f)) (affineKernelPairsPoint G f x hx) = x := by
  apply (pointCoordinates G).injective
  rw [pointCoordinates_naturality]
  simp only [affineKernelPairsPoint, Equiv.apply_symm_apply, snd_comp_pairsLift]

variable (I : Ideal A) (hI : I ^ 2 = ⊥)

private theorem affineTriples_ext {x y : AffinePoints G (triples R I)}
    (h₁ : affineMap G (pr₁ R I) x = affineMap G (pr₁ R I) y)
    (h₂ : affineMap G (pr₂ R I) x = affineMap G (pr₂ R I) y) : x = y := by
  apply affineMap_jointly_injective G (pr₁ R I) (pr₂ R I) _ h₁ h₂
  intro a b h
  exact triples_ext
    (congrArg (fun z : pairs R I × pairs R I => (z.1 : A × A).1) h)
    (congrArg (fun z : pairs R I × pairs R I => (z.1 : A × A).2) h)
    (congrArg (fun z : pairs R I × pairs R I => (z.2 : A × A).2) h)

omit [IsAffineHom G.X.hom] in
/-- The sum map on congruent triples realizes multiplication of two
independent identity directions. -/
theorem affinePairs_sum (x y : AffinePoints G (pairs R I)) :
    affineMap G (sum R I hI)
        (affineMap G
            (pair (AlgHom.id R (pairs R I)) ((diag R I).comp (fst R I))
              fst_comp_id_eq) x *
          affineMap G
            (pair ((diag R I).comp (fst R I)) (AlgHom.id R (pairs R I))
              fst_comp_id_eq.symm) y) = x * y := by
  rw [map_mul, ← affineMap_comp, ← affineMap_comp,
    sum_comp_pair_id_diag, sum_comp_pair_diag_id, affineMap_id, affineMap_id]

/-- Scaling an infinitesimal direction by a sum is multiplication of the
two scalings. -/
theorem affinePairs_scale_add (x : AffinePoints G (pairs R I))
    (hx : affineMap G (fst R I) x = 1) (c d : A) :
    affineMap G (scale R I hI (c + d)) x =
      affineMap G (scale R I hI c) x * affineMap G (scale R I hI d) x := by
  let s := pair (scale R I hI c) (scale R I hI d) (fst_comp_scale_eq hI c d)
  let a := pair (AlgHom.id R (pairs R I)) ((diag R I).comp (fst R I))
    fst_comp_id_eq
  let b := pair ((diag R I).comp (fst R I)) (AlgHom.id R (pairs R I))
    fst_comp_id_eq.symm
  have hz : affineMap G s x =
      affineMap G a (affineMap G (scale R I hI c) x) *
        affineMap G b (affineMap G (scale R I hI d) x) := by
    apply affineTriples_ext G I
    · simp only [s, a, b, map_mul, ← affineMap_comp, ← AlgHom.comp_assoc,
        pr₁_comp_pair, AlgHom.id_comp]
      rw [AlgHom.comp_assoc, fst_comp_scale, affineMap_comp, hx, map_one, mul_one]
    · simp only [s, a, b, map_mul, ← affineMap_comp, ← AlgHom.comp_assoc,
        pr₂_comp_pair, AlgHom.id_comp]
      rw [AlgHom.comp_assoc, fst_comp_scale, affineMap_comp, hx, map_one, one_mul]
  rw [← sum_comp_pair_scale hI c d, affineMap_comp]
  change affineMap G (sum R I hI) (affineMap G s x) = _
  rw [hz]
  exact affinePairs_sum G I hI _ _

/-- Scaling by a natural number computes the corresponding power. -/
theorem affinePairs_scale_natCast (x : AffinePoints G (pairs R I))
    (hx : affineMap G (fst R I) x = 1) (n : ℕ) :
    affineMap G (scale R I hI (n : A)) x = x ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, scale_zero, affineMap_comp, hx, map_one, pow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, affinePairs_scale_add G I hI x hx, ih, scale_one,
      affineMap_id, pow_succ]

/-- A coefficient kernel killed by `n` has its group-valued identity kernel
killed by the same `n` when its ideal is square-zero. -/
theorem affineKernel_pow_eq_one (f : A →ₐ[R] B)
    (hker : (RingHom.ker f) ^ 2 = ⊥) (n : ℕ)
    (hn : ∀ a ∈ RingHom.ker f, (n : A) * a = 0)
    (x : AffinePoints G A) (hx : affineMap G f x = 1) : x ^ n = 1 := by
  let y := affineKernelPairsPoint G f x hx
  have hy := affineKernelPairsPoint_fst G f x hx
  have hs : scale R (RingHom.ker f) hker (n : A) =
      scale R (RingHom.ker f) hker 0 := by
    apply AlgHom.ext
    intro a
    apply pairs_ext
    · rfl
    · simp only [scale_apply, hn _ (mem_pairs a), zero_mul]
  rw [← affineKernelPairsPoint_snd G f x hx, ← map_pow,
    ← affinePairs_scale_natCast G (RingHom.ker f) hker y hy n,
    hs, scale_zero, affineMap_comp, hy, map_one, map_one]

end Langlands.GroupScheme.Lie
