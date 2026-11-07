import Langlands.GroupScheme.Rational.ParabolicBoundaryModels
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.Representation.Exponents.BoundaryUnitaryJacquetExponent

/-! # A proper unitary Jacquet witness from a nonstrict tempered exponent -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

open RealTorusSpace

variable {k : Type u} [Field k]
  {G P M Q L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {B A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {m : M ⟶ P} {b : B.toGrp ⟶ M}
  {q : Q ⟶ G} {l : L ⟶ Q} {a : A.toGrp ⟶ L}
  (fine : ParabolicRootPresentation p m b)
  (outer : ParabolicRootPresentation q l a)
  (i : M ⟶ L) (hi : i ≫ l ≫ q = m ≫ p)
  (hG : IsConnectedReductive G)

include hG in
/-- Any presentation of the actual boundary parabolic has a transported zero
face containing the original positive coefficient support. -/
theorem boundaryRootIndex_subset_outerFace_of_boundaryParabolic
    {x : Vstar B} (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone)
    (hQ : SubgroupFunctor.range q =
      Dynamic.parabolic
        (CommGroupScheme.groupHom (fine.boundaryCocharacterInTorus hx hstrict) ≫
          fine.data.i)) :
    fine.boundaryRootIndex hx ⊆ fine.outerSimpleRootFace outer i hi := by
  intro α hα
  have hs := fine.boundaryRootIndex_subset_boundaryCocharacterFace hx hstrict hα
  have hle :
      Dynamic.parabolic
          (CommGroupScheme.groupHom (fine.boundaryCocharacterInTorus hx hstrict) ≫
            fine.data.i) ≤
        Dynamic.parabolic
          (CommGroupScheme.groupHom (fine.outerCocharacterInFineTorus outer i hi) ≫
            fine.data.i) := by
    rw [← hQ, ← fine.parabolic_eq_outerCocharacterInFineTorus outer i hi]
  have hsign := (relativeRootSignInclusions k G hG fine.data.T fine.data.i
    fine.isCompatible.maximalSplit (fine.boundaryCocharacterInTorus hx hstrict)
      (fine.outerCocharacterInFineTorus outer i hi)).1.mp hle
  have hnonneg := hsign α hs.1.1.1 (le_of_eq hs.2.symm)
  have hnegroot := relativeRootNegation k G hG fine.data.T fine.data.i
    fine.isCompatible.maximalSplit α hs.1.1.1
  have hzneg : 0 ≤ latticePairing fine.data.T (-α)
      (fine.boundaryCocharacterInTorus hx hstrict) := by
    simp only [map_neg, LinearMap.neg_apply, hs.2, neg_zero, le_refl]
  have hnonpos := hsign (-α) hnegroot hzneg
  simp only [map_neg, LinearMap.neg_apply] at hnonpos
  exact ⟨hs.1, le_antisymm (neg_nonneg.mp hnonpos) hnonneg⟩

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance boundaryWitnessAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- An actual proper parabolic with a specified unitary normalized Jacquet
exponent of the original representation. -/
structure ProperUnitaryJacquetWitness
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) where
  Q : GroupScheme (Spec (CommRingCat.of k))
  L : GroupScheme (Spec (CommRingCat.of k))
  U : GroupScheme (Spec (CommRingCat.of k))
  A : CommGroupScheme (Spec (CommRingCat.of k))
  q : Q ⟶ G
  l : L ⟶ Q
  r : U ⟶ Q
  a : A.toGrp ⟶ L
  hq : IsParabolicSubgroup q
  hl : IsRationalLeviSubgroup l
  hr : LeviSubgroup.IsGeometricUnipotentRadical r
  hmul : IsIso (subgroupMultiplication l r)
  ha : IsSplitComponent a
  proper : ¬ IsIso q
  exponent : unitaryJacquetExponents q l r hq hl hr hmul ha π

variable {P M N : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G)
  (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
  (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hmul : IsIso (subgroupMultiplication m n))
  {B : CommGroupScheme (Spec (CommRingCat.of k))}
  {b : B.toGrp ⟶ M} (hb : IsSplitComponent b)
  (fine : ParabolicRootPresentation p m b)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  (hπ : IsNormalizedExponentTempered hG π)
  (χ : rationalPoints B.toGrp →* ℂˣ)
  (hχ : IsNormalizedJacquetExponent p m n hp hm hn hmul hb π χ)

/-- A nonstrict normalized exponent of a tempered representation constructs
a unitary exponent at an actual proper coarser parabolic. -/
def boundaryUnitaryJacquetWitness
    (hx : haveI := hG.smooth
      Plancherel.SplitTorus.normalizedRealPart hb.isCentralSplitTorus.1.1 χ ∈
        fine.nonnegCone)
    (hstrict : haveI := hG.smooth
      Plancherel.SplitTorus.normalizedRealPart hb.isCentralSplitTorus.1.1 χ ∉
        fine.positiveCone) :
    ProperUnitaryJacquetWitness π := by
  have := hG.smooth
  let model := fine.boundaryParabolicModels hG hx hstrict
  let split := (splitComponentStatement k model.L model.hl.isConnectedReductive).1
  let A := split.choose
  let a : A.toGrp ⟶ model.L := split.choose_spec.choose
  have ha : IsSplitComponent a := split.choose_spec.choose_spec
  let outer := (hπ.nonempty_presentation model.q model.l a model.hq model.hl ha).some
  have hface : fine.boundaryRootIndex hx ⊆
      fine.outerSimpleRootFace outer (model.mL ≫ model.pL) model.hM :=
    fine.boundaryRootIndex_subset_outerFace_of_boundaryParabolic
      outer (model.mL ≫ model.pL) model.hM hG hx hstrict model.parabolic_range
  let ψ := boundaryUnitaryJacquetExponent hG p m n hp hm hn hmul
    model.q model.l model.r model.hq model.hl model.hr model.hmulQ
    model.pL model.mL model.nL model.hpL model.hmL model.hnL model.hmulL
    model.hP model.hM model.hPL ha hb fine outer π hπ χ hχ hx hface
  exact
    { Q := model.Q
      L := model.L
      U := model.U
      A := A
      q := model.q
      l := model.l
      r := model.r
      a := a
      hq := model.hq
      hl := model.hl
      hr := model.hr
      hmul := model.hmulQ
      ha := ha
      proper := model.proper
      exponent := ψ }

namespace ProperUnitaryJacquetWitness

/-- The supplied exponent certifies nonvanishing of the original unitary
Jacquet part at this actual proper parabolic. -/
theorem unitaryJacquetPart_ne_bot
    {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    (w : ProperUnitaryJacquetWitness π) :
    unitaryJacquetPart w.q w.l w.r w.hq w.hl w.hr w.hmul w.ha π ≠ ⊥ := by
  apply (unitaryJacquetExponents_nonempty_iff
    w.q w.l w.r w.hq w.hl w.hr w.hmul w.ha π).mp
  exact ⟨w.exponent.val, w.exponent.property⟩

end ProperUnitaryJacquetWitness

end Langlands.Aubert.General.RepresentedParabolic
