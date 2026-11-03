import Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceStatement
import Langlands.GroupScheme.SimplyConnected.SplitCriterionStatement
import Langlands.GroupScheme.Reductive.SplitClassificationStatement
import Langlands.LinearAlgebra.SimplyConnectedRootDatum

/-! # Simply connected central covers of split semisimple groups from the classification -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.LinearAlgebra

/-- The inputs of the split case of Milne Remark 23.60 at universe `u`: existence of the root
datum (Milne Theorem 21.11), the Existence Theorem (Milne Theorem 23.55), the existence half of
the central Isogeny Theorem (Milne Theorem 23.9), the semisimplicity criterion (Milne
Proposition 21.48) and the sufficiency half of the coroot criterion (Milne Proposition 23.29). -/
def SplitSimplyConnectedCoverInputsStatement : Prop :=
  RootDatumExistenceStatement.{u} ∧ SplitReductiveExistenceStatement.{u} ∧
    SplitCentralIsogenyExistenceStatement.{u} ∧ SplitSemisimpleRootDatumStatement.{u} ∧
      SplitCorootSpanSimplyConnectedStatement.{u}

/-- **Simply connected central covers of split semisimple groups** (Milne Remark 23.60, split
case), assuming `SplitSimplyConnectedCoverInputsStatement`. The cover is the split group with
the simply connected root datum `SimplyConnectedRootDatum.rootDatum P` of a root datum `P` of
`G`. -/
theorem splitSimplyConnectedCoverExistence_of_inputs
    (h : SplitSimplyConnectedCoverInputsStatement.{u}) :
    SplitSimplyConnectedCoverExistenceStatement.{u} := by
  obtain ⟨hRD, hEx, hIso, hSS, hSC⟩ := h
  intro k _ G T hG hT i hi
  have hGr := hG.isConnectedReductive
  have := hGr.isAffineHom
  obtain ⟨J, hJ, P, hP, hPred⟩ := hRD k G hGr T hT i hi
  -- The coroots of `P` span a subgroup of finite index in the cocharacter lattice.
  have hfin : Finite (cocharacterLattice T ⧸ P.corootSpan ℤ) :=
    ((hSS k G hGr T hT i hi J P hP).2.mp hG)
  -- The split group `C` with the simply connected root datum of `P`.
  obtain ⟨C, hC, TC, iC, hTC, hiC, Q, hQ, ⟨e⟩⟩ :=
    hEx k J (Module.Dual ℤ (P.corootSpan ℤ)) (P.corootSpan ℤ)
      (SimplyConnectedRootDatum.rootDatum P) inferInstance
  -- The central isogeny of root data `P → Q`.
  let f : RootPairing.Hom P Q := e.toHom.comp (SimplyConnectedRootDatum.toRootDatum P)
  have hfw : Function.Injective f.weightMap :=
    e.bijective_weightMap.injective.comp
      (SimplyConnectedRootDatum.injective_toRootDatum_weightMap P hfin)
  have hfc : Function.Injective f.coweightMap :=
    (SimplyConnectedRootDatum.injective_toRootDatum_coweightMap P).comp
      e.bijective_coweightMap.injective
  obtain ⟨π, -, -, -, hπ⟩ := hIso k C G hC hGr TC T hTC hT iC i hiC hi J J Q P hQ hP f hfw hfc
  -- `C` is semisimple and simply connected, since the coroots of `Q` span its cocharacters.
  have hQtop : Q.corootSpan ℤ = ⊤ :=
    SimplyConnectedRootDatum.corootSpan_eq_top_of_equiv e
      (SimplyConnectedRootDatum.corootSpan_rootDatum P)
  have hCss : IsSemisimple C := by
    have := hC.isAffineHom
    refine (hSS k C hC TC hTC iC hiC J Q hQ).2.mpr ?_
    rw [hQtop]
    infer_instance
  exact ⟨C, π, hSC k C hCss TC hTC iC hiC J Q hQ hQtop, hπ⟩

end Langlands.GroupScheme
