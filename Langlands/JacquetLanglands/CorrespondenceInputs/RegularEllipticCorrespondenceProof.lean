import Langlands.JacquetLanglands.CorrespondenceInputs.RegularEllipticCorrespondence
import Langlands.ClassFieldTheory.Local.LocalDivisionBrauerOrder
import Langlands.ClassFieldTheory.Local.DivisionEmbeddingFromSplitting
import Langlands.ClassFieldTheory.Local.FiniteUnramifiedLocalField
import Langlands.Algebra.DivisionReducedCharpoly

/-!
# Proof that regular elliptic elements of `GL_n(F)` correspond to units of `D`

The theorem `regularEllipticCorrespondence` proves
`RegularEllipticCorrespondenceStatement`. For a regular elliptic `g`, the field
`L = F[X]/(P)`, `P` the characteristic polynomial of `g`, has degree `n` over `F`. With its
spectral local-field structure it kills the Brauer class of `D`, whose order is `n`, so it embeds
in `D`. The image of the class of `X` is a unit of `D` with reduced characteristic polynomial `P`.
-/

noncomputable section

namespace Langlands.JacquetLanglands

open _root_.Polynomial
open Langlands.Brauer Langlands.CentralDivision Langlands.CentralSimple
open Langlands.ClassFieldTheory.Local Langlands.LocalField

universe u

/-- Every regular elliptic element of `GL_n(F)` corresponds to a unit of a central division
algebra of dimension `n^2` over a nonarchimedean local field `F`. -/
theorem regularEllipticCorrespondence : RegularEllipticCorrespondenceStatement.{u} := by
  intro F _ _ _ _ D _ _ _ _ n hdim g hg
  set P : F[X] := (g : Matrix (Fin n) (Fin n) F).charpoly with hP
  have hPm : P.Monic := Matrix.charpoly_monic _
  have hP0 : P ≠ 0 := hPm.ne_zero
  have hPdeg : P.natDegree = n := by
    rw [hP, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hPirr : Irreducible P := hg.2
  -- The constant term of `P` is `± det g`, which is nonzero.
  have hPcoeff : P.coeff 0 ≠ 0 := by
    intro h
    have hdet := Matrix.det_eq_sign_charpoly_coeff (g : Matrix (Fin n) (Fin n) F)
    rw [← hP, h, mul_zero] at hdet
    exact (Matrix.GeneralLinearGroup.det_ne_zero g) hdet
  -- The reduced degree of `D` is `n`.
  have hdim' : Module.finrank F D = n * n := by rw [hdim, sq]
  have hred : reducedDegree F D = n :=
    Nat.mul_self_inj.mp ((finrank_eq_reducedDegree_mul_self F D).symm.trans hdim')
  -- The field `L = F[X]/(P)` of degree `n`.
  have : Fact (Irreducible P) := ⟨hPirr⟩
  let L := AdjoinRoot P
  let pb := AdjoinRoot.powerBasis (K := F) hP0
  have : FiniteDimensional F L := pb.finite
  have hLdeg : Module.finrank F L = n := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim, hPdeg]
  -- Its spectral local-field structure.
  let := FiniteExtension.normedField F L
  let := FiniteExtension.valuativeRel F L
  let := FiniteExtension.isLocalField F L
  let := spectralFiniteExtension_valuativeExtension F L
  -- `L` splits `D`, since the Brauer class of `D` has order `n = [L : F]`.
  let x := classOf (divisionAlgebraCSA F D)
  have hx : n • x = 0 := by
    rw [← addOrderOf_localDivisionClass F D hdim']
    exact addOrderOf_nsmul_eq_zero x
  have hsplit : scalarExtension L x = 0 := by
    apply (scalarExtension_eq_zero_iff_degree_nsmul F L
      (spectralFiniteExtension_algebraMap_continuous F L) x).2
    rw [hLdeg]
    exact hx
  have hSplit : IsSplit (baseChange L (divisionAlgebraCSA F D)) :=
    (classOf_eq_zero_iff _).1 hsplit
  -- The embedding `ι : L → D` and the element `ι (root P)`.
  let ι : L →ₐ[F] D :=
    embeddingOfSplitOfReducedDegree F D L (hLdeg.trans hred.symm) hSplit
  let a : D := ι (AdjoinRoot.root P)
  have hmin : minpoly F a = P := by
    rw [minpoly.algHom_eq ι ι.injective, AdjoinRoot.minpoly_root hP0, hPm.leadingCoeff,
      inv_one, map_one, mul_one]
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, minpoly.zero] at hmin
    apply hPcoeff
    rw [← hmin, coeff_X_zero]
  -- The reduced characteristic polynomial of `a` is `P`.
  have hred_a : reducedCharpoly F D a = P := by
    have h := Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic
      (Algebra.IsIntegral.isIntegral a)) (reducedCharpoly_monic F D a)
      (minpoly_dvd_reducedCharpoly F D a) (by rw [reducedCharpoly_natDegree, hmin, hPdeg, hred])
    rw [h, hmin]
  refine ⟨Units.mk0 a ha0, (corresponds_iff F D g _).2 ⟨hg.1, ?_, ?_⟩⟩
  · change (reducedCharpoly F D a).Separable
    rw [hred_a]
    exact hg.1
  · change P = reducedCharpoly F D a
    rw [hred_a]

end Langlands.JacquetLanglands
