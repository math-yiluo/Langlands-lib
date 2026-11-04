import Langlands.GroupScheme.SimplyConnected.SplitNecessityStatement
import Langlands.GroupScheme.Reductive.SplitClassificationStatement
import Langlands.GroupScheme.Reductive.RootDatumHomLattices
import Langlands.LinearAlgebra.SimplyConnectedRootDatum

/-! # Integral coroot generation for simply connected split groups from the classification -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.LinearAlgebra

/-- The inputs of the necessity half of Milne Proposition 23.59 at universe `u`: the Existence
Theorem (Milne Theorem 23.55), the existence half of the central Isogeny Theorem (Milne
Theorem 23.9) and the semisimplicity criterion (Milne Proposition 21.48). -/
def SplitSimplyConnectedCorootSpanInputsStatement : Prop :=
  SplitReductiveExistenceStatement.{u} ∧ SplitCentralIsogenyExistenceStatement.{u} ∧
    SplitSemisimpleRootDatumStatement.{u}

/-- **Simple connectedness forces integral coroot generation** (Milne Proposition 23.59,
necessity, split case), assuming `SplitSimplyConnectedCorootSpanInputsStatement`. The split
group `C` with the simply connected root datum `SimplyConnectedRootDatum.rootDatum P` maps to
`G` by a central isogeny; simple connectedness of `G` makes it and its torus map isomorphisms,
so the inclusion of the coroot span into the cocharacter lattice is surjective. -/
theorem splitSimplyConnectedCorootSpan_of_inputs
    (h : SplitSimplyConnectedCorootSpanInputsStatement.{u}) :
    SplitSimplyConnectedCorootSpanStatement.{u} := by
  obtain ⟨hEx, hIso, hSS⟩ := h
  intro k _ G hG T hT i hi J _ P hP hPred
  have hGr := hG.isSemisimple.isConnectedReductive
  have := hGr.isAffineHom
  -- The coroots of `P` span a subgroup of finite index in the cocharacter lattice.
  have hfin : Finite (cocharacterLattice T ⧸ P.corootSpan ℤ) :=
    (hSS k G hGr T hT i hi J P hP).2.mp hG.isSemisimple
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
  obtain ⟨φ, t, hsq, hwt, hφ⟩ :=
    hIso k C G hC hGr TC T hTC hT iC i hiC hi J J Q P hQ hP f hfw hfc
  -- `C` is semisimple, since the coroots of `Q` span its cocharacters.
  have hQtop : Q.corootSpan ℤ = ⊤ :=
    SimplyConnectedRootDatum.corootSpan_eq_top_of_equiv e
      (SimplyConnectedRootDatum.corootSpan_rootDatum P)
  have hCss : IsSemisimple C := by
    have := hC.isAffineHom
    refine (hSS k C hC TC hTC iC hiC J Q hQ).2.mpr ?_
    rw [hQtop]
    infer_instance
  -- Simple connectedness of `G` makes the central isogeny and its torus map isomorphisms.
  have : IsIso φ := hG.central_isogeny_isIso C φ hCss hφ
  have : IsIso t := IsMaximalTorus.isIso_factor_of_isIso hiC hi.1 hi.2.1 φ t hsq
  -- Hence the coweight map `Y(TC) → Y(T)`, which factors through the coroot span, is surjective.
  have hsurj : Function.Surjective f.coweightMap :=
    RootDatumHom.surjective_coweightMap_of_isIso hP.1 hQ.1 f t hwt
  have hsub : Function.Surjective (P.corootSpan ℤ).subtype := by
    intro y
    obtain ⟨z, hz⟩ := hsurj y
    exact ⟨e.toHom.coweightMap z, hz⟩
  rw [← LinearMap.range_eq_top, Submodule.range_subtype] at hsub
  exact hsub

end Langlands.GroupScheme
