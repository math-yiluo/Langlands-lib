import Langlands.GroupScheme.Reductive.TitsIndexChoiceStatement
import Langlands.GroupScheme.Reductive.RegularCocharacterPinning
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction

/-! # Existence of actual Tits-index data -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace TitsIndexExistence

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The pairing of a descended restricted character with a cocharacter of the
split torus equals the pairing, over `K`, of the original character with the
pushed-forward base-changed cocharacter. -/
theorem latticePairing_restriction
    {S T : CommGroupScheme (Spec (CommRingCat.of k))} (hS : IsSplitTorus S.toGrp)
    (f : S ⟶ T)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (c₀ : cocharacterLattice S) :
    latticePairing S
        ((characterLattice.baseChangeEquiv (algebraBaseMap k K) S hS).symm
          ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f ≫ χ)) c₀ =
      latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ
        (cocharacterLattice.baseChange (algebraBaseMap k K) S c₀ ≫
          (CommGroupScheme.baseChange (algebraBaseMap k K)).map f) := by
  rw [← latticePairing_baseChange (algebraBaseMap k K) S, ← characterLattice.baseChangeEquiv_apply
    (algebraBaseMap k K) S hS, AddEquiv.apply_symm_apply, latticePairing_apply,
    latticePairing_apply, Category.assoc]

end TitsIndexExistence

set_option maxHeartbeats 400000 in
open TitsIndexExistence in
/-- Every actual semisimple group over an arbitrary field admits compatible
Tits-index data. -/
theorem titsIndexExistence : TitsIndexExistenceStatement.{u} := by
  intro k _ G _ _ hG
  have hCR := hG.isConnectedReductive
  have := hCR.smooth
  obtain ⟨S, j, hj⟩ := exists_maximalSplitTorus G
  have hS : IsSplitTorus S.toGrp := hj.1.1
  obtain ⟨T, i, f, hi, hf⟩ :=
    EnvelopeInfiniteReduction.exists_isMaximalTorus_factor G j hS.isTorus hj.1.2
  let K := SeparableClosure k
  let b := algebraBaseMap k K
  have hGE := connectedReductiveFieldExtensionStatement k K G hCR
  have hsplit := GaloisPinningData.isSplitTorus_separableClosure T hi.1
  have hiE := (maximalTorusBaseChange k K G T i hi.1 hi.2.1).mp hi
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence K _ hGE _ hsplit _ hiE
  let fK : (CommGroupScheme.baseChange b).obj S ⟶ (CommGroupScheme.baseChange b).obj T :=
    (CommGroupScheme.baseChange b).map (Additive.ofMul f)
  let r : J → characterLattice S := fun a =>
    (characterLattice.baseChangeEquiv b S hS).symm (fK ≫ P.root a)
  let s : Set (characterLattice S) := relativeRoots j ∪ (Set.range r \ {0})
  have hs : s.Finite := (hS.finite_relativeRoots j).union ((Set.finite_range r).sdiff)
  have hs0 : ∀ α ∈ s, α ≠ 0 := by
    rintro α (hα | ⟨-, hα⟩)
    · exact hα.1
    · exact hα
  obtain ⟨c₀, hc₀⟩ := hS.exists_pairings_ne_zero s hs hs0
  let cK : cocharacterLattice ((CommGroupScheme.baseChange b).obj T) :=
    cocharacterLattice.baseChange b S c₀ ≫ fK
  have hpair (a : J) : P.root' a cK = latticePairing S (r a) c₀ := by
    rw [latticePairing_restriction hS (Additive.ofMul f) (P.root a) c₀, ← hP.1]
  let := Fintype.ofFinite J
  obtain ⟨ν, hν, hface⟩ :=
    Langlands.LinearAlgebra.RootDatumCoweightFace.exists_regular_refinement P cK
  have := hred
  let B : P.Base := IsRootDatumOf.regularCocharacterBase k K (P := P) ν hν
  have hB (a : J) : B.IsPos a ↔ 0 < P.root' a ν := by
    rw [IsRootDatumOf.regularCocharacterBase_isPos k K i hP ν hν a, ← hP.1]
  let pd : GaloisPinningData k K G :=
    { torus := T
      inclusion := i
      isConnectedReductive := hGE
      isSplitTorus := hsplit
      isMaximalTorus := hiE
      rootIndex := J
      finiteRootIndex := hJ
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := B
      pinning := RootPinning.ofSplitMaximalTorus hGE hsplit _ hiE P hP B }
  refine ⟨{
    isSemisimple := hG
    pinning := pd
    maximalTorus := hi
    splitTorus := S
    splitInclusion := j
    maximalSplit := hj
    torusMap := Additive.ofMul f
    square := hf
    positiveCocharacter := c₀
    generic := fun α hα => hc₀ α (Or.inl hα)
    compatible := ?_ }⟩
  intro a ha
  change r a ≠ 0 at ha
  change B.IsPos a ↔ 0 < latticePairing S (r a) c₀
  have h0 : latticePairing S (r a) c₀ ≠ 0 := hc₀ (r a) (Or.inr ⟨⟨a, rfl⟩, ha⟩)
  rw [hB a, ← hpair a]
  exact hface a (by rwa [hpair a])

end Langlands.GroupScheme
