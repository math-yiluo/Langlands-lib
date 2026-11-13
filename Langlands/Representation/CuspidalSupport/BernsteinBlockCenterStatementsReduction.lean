import Langlands.Representation.CuspidalSupport.BernsteinBlockCenterStatements
import Langlands.Representation.CuspidalSupport.BernsteinCenterFunctionsStatements
import Langlands.Representation.CuspidalSupport.BernsteinComponentVarietyProof
import Langlands.CategoryTheory.Renard.DecompositionCenterIdempotent

/-! # Renard VI.10.4, Corollary and Remark 3, from the Theorem of VI.10.4

The centre of the Bernstein block `M(G)_Ω` of a cuspidal datum `a` is identified by the
Theorem of VI.10.4 (published `BernsteinBlockCenterFunctionsStatement`) with the algebra of
functions on `X(M)` constant on association classes. By VI.7.1 (the proved
`bernsteinComponentVariety`) this algebra is a finitely generated `ℂ`-algebra and a domain.
Hence the centre is a Noetherian ring (Corollary), and every two-factor decomposition of the
block has a zero factor (Remark 3), because the central idempotent of a decomposition is `0`
or `1` in a domain. The Theorem of VI.10.4 is not proved in the Library at the time of
writing; this module proves the two statements of `BernsteinBlockCenterStatements` from it.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Renard

universe v u w

/-- Indecomposability from the centre: if the centre of a preadditive category is
isomorphic, as a ring, to a domain, then every two-factor decomposition
in the sense of A.IX has a factor containing only zero objects. -/
theorem exists_isZero_of_decomposition_of_centerEquiv {C : Type u} [Category.{v} C]
    [Preadditive C] {R : Type w} [Ring R] [IsDomain R] (e : CatCenter C ≃+* R)
    {P : Bool → ObjectProperty C} (hP : IsCategoryDecomposition P) :
    ∃ b : Bool, ∀ X : C, P b X → IsZero X := by
  have hidem : IsIdempotentElem (e (decompositionIdem hP)) :=
    (decompositionIdem_isIdempotentElem hP).map e
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with h | h
  · refine ⟨true, fun X hX => isZero_of_decompositionIdem_eq_zero hP ?_ hX⟩
    exact e.injective (by rw [h, map_zero])
  · refine ⟨false, fun X hX => isZero_of_decompositionIdem_eq_one hP ?_ hX⟩
    exact e.injective (by rw [h, map_one])

end Langlands.Renard

namespace Langlands.CuspidalSupport

universe uF uV

/-- The implication proved in this module: the Theorem of Renard VI.10.4 (first sentence)
implies its Corollary and Remark 3, at the same field and carrier universes. -/
def BernsteinBlockCenterStatementsReductionStatement : Prop :=
  BernsteinBlockCenterFunctionsStatement.{uF, uV} → BernsteinBlockCenterStatements.{uF, uV}

/-- Renard VI.10.4, Corollary and Remark 3, from the Theorem of VI.10.4 (first sentence) and
the proved VI.7.1 Theorem `bernsteinComponentVariety`. -/
theorem bernsteinBlockCenterStatements_of_centerFunctions
    (hS1 : BernsteinBlockCenterFunctionsStatement.{uF, uV}) :
    BernsteinBlockCenterStatements.{uF, uV} := by
  constructor
  · intro F _ _ _ _ G _ _ T i ν hLC hNA family a
    obtain ⟨-, O, hO, e, -⟩ := @hS1 F _ _ _ _ G _ _ T i ν hLC hNA family a
    obtain ⟨-, ⟨O', hO', hfin, -, -, -⟩, -⟩ :=
      @bernsteinComponentVariety.{uF, max uF uV} F _ _ _ _ G _ _ T i ν hLC hNA family a
    have hOO' : O = O' := SetLike.coe_injective (hO.trans hO'.symm)
    subst hOO'
    have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing ℂ O
    exact isNoetherianRing_of_ringEquiv O e.symm
  · intro F _ _ _ _ G _ _ T i ν hLC hNA family a P hP
    obtain ⟨-, O, hO, e, -⟩ := @hS1 F _ _ _ _ G _ _ T i ν hLC hNA family a
    obtain ⟨-, ⟨O', hO', -, hdom, -, -⟩, -⟩ :=
      @bernsteinComponentVariety.{uF, max uF uV} F _ _ _ _ G _ _ T i ν hLC hNA family a
    have hOO' : O = O' := SetLike.coe_injective (hO.trans hO'.symm)
    subst hOO'
    exact Renard.exists_isZero_of_decomposition_of_centerEquiv e hP

theorem bernsteinBlockCenterStatementsReductionStatement_holds :
    BernsteinBlockCenterStatementsReductionStatement.{uF, uV} :=
  bernsteinBlockCenterStatements_of_centerFunctions

end Langlands.CuspidalSupport
