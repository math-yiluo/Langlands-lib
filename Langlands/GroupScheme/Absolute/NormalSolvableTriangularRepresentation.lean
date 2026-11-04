import Langlands.GroupScheme.Absolute.SolvableTriangularEmbeddingReduction
import Langlands.GroupScheme.Absolute.LieKolchinRationalTriangularization
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Triangular ambient representations of solvable subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace MatrixRepresentation

/-- An endomorphism fixing the original diagonal and specializing the conjugate
diagonal to it rules out any nontrivial permutation of diagonal entries. -/
theorem diagonal_eq_of_charpoly_of_retraction
    {R : Type*} [CommRing R] [IsDomain R] {n : Type*}
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (B C : Matrix n n R) (hB : B.IsUpperTriangular) (hC : C.IsUpperTriangular)
    (hchar : C.charpoly = B.charpoly) (p : R →+* R)
    (hpB : ∀ i, p (B i i) = B i i) (hpC : ∀ i, p (C i i) = B i i) :
    ∀ i, C i i = B i i := by
  intro i
  have hzero : (∏ j : n, (C i i - B j j)) = 0 := by
    have h := congrArg (Polynomial.eval (C i i)) hchar
    rw [Matrix.charpoly_of_isUpperTriangular C hC,
      Matrix.charpoly_of_isUpperTriangular B hB] at h
    simp only [Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at h
    have hz : (∏ j : n, (C i i - C j j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    exact h.symm.trans hz
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hzero
  have hij : C i i = B j j := sub_eq_zero.mp hj
  have hsame : B i i = B j j := by
    have h := congrArg p hij
    rwa [hpC, hpB] at h
  exact hij.trans hsame.symm

end MatrixRepresentation

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A faithful representation of the whole ambient group in which the given
solvable subgroup is represented by upper triangular matrices. -/
structure SolvableSubgroupTriangularRepresentation (i : H ⟶ G) where
  dimension : ℕ
  ambient : MatrixRepresentation G (Fin dimension)
  closed_ambient : IsClosedSubgroup ambient
  triangular : H ⟶ GeneralLinear.blockParabolicScheme (Fin dimension) (CommRingCat.of k)
    (fun j => -(j.val : ℤ))
  closed_triangular : IsClosedSubgroup triangular
  factorization : triangular ≫ GeneralLinear.blockParabolicHom
    (Fin dimension) (CommRingCat.of k) (fun j => -(j.val : ℤ)) = i ≫ ambient

/-- Lie–Kolchin applied to the restriction of a faithful ambient representation
provides compatible ambient and triangular closed embeddings. -/
def IsSolvableGroupScheme.ambientTriangularRepresentation
    [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hH : IsSolvableGroupScheme H) (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    SolvableSubgroupTriangularRepresentation i :=
  Classical.choice (by
    obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
    obtain ⟨g, hg⟩ := lieKolchinRationalTriangularization k H hH.rationalPoints N
      (ρ.restrict i)
    have hρg : IsClosedSubgroup (ρ.conjugate g) := by
      have : IsClosedImmersion ρ.hom.hom.left := hρ
      have : IsIso
          ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso g).hom.hom.hom.left :=
        inferInstanceAs (IsIso ((Over.forget _).map
          ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso g).hom.hom.hom))
      change IsClosedImmersion (ρ.hom.hom.left ≫ _)
      infer_instance
    have hrestrict : IsClosedSubgroup ((ρ.restrict i).conjugate g) := by
      rw [MatrixRepresentation.conjugate_restrict]
      have : IsClosedImmersion i.hom.hom.left := hi
      have : IsClosedImmersion (ρ.conjugate g).hom.hom.left := hρg
      change IsClosedImmersion (i.hom.hom.left ≫ (ρ.conjugate g).hom.hom.left)
      infer_instance
    obtain ⟨j, hj, hfac⟩ :=
      MatrixRepresentation.exists_closed_blockParabolic_factor_of_rational
        ((ρ.restrict i).conjugate g) hrestrict hg
    exact ⟨⟨N, ρ.conjugate g, hρg, j, hj, hfac⟩⟩)

end Langlands.GroupScheme
