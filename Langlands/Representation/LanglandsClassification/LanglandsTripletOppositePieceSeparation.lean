import Langlands.Representation.LanglandsClassification.LanglandsTripletSpectralReduction
import Langlands.Representation.LanglandsClassification.UnramifiedPieceDisplacement
import Langlands.GroupScheme.Rational.ParabolicOppositeNonnegCone
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof
import Langlands.Representation.Exponents.NormalizedTemperedTwistExponent

/-! # Separation of the actual opposite geometric-lemma pieces -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands

/-- A nonzero compact-open generalized weight space contains a generic
uniform generalized eigenvector, even without ambient smoothness. -/
theorem isGeneralizedEigencharacter_of_isGeneralizedWeight
    {R A H V : Type*} [CommRing R] [Group A] [TopologicalSpace A]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup V] [Module R V]
    (π : Representation R H V) (j : A →* H) (χ : A →* Rˣ)
    (hj : ∀ t, j t ∈ Subgroup.center H) (hχ : IsGeneralizedWeight π j χ hj) :
    IsGeneralizedEigencharacter (π.comp j) χ := by
  by_contra h
  have hchar (d : ℕ) : characterSpace (π.comp j) χ d = ⊥ := by
    by_contra hd
    exact h ⟨d, hd⟩
  apply hχ.2
  apply Subrepresentation.toSubmodule_injective
  change (⨆ K : HarishChandraSchwartz.CompactOpenSubgroup H,
    ⨆ d : ℕ, fixedVectors π K.toSubgroup ⊓ characterSpace (π.comp j) χ d) = ⊥
  simp only [hchar, inf_bot_eq, iSup_bot]

end Langlands

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

namespace GeometricLemmaIntersectionDatum

section Offset

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (E : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
  {A A' : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ L}

/-- The real part of a test character minus the actual unramified piece parameter.
For an exponent of a tempered twisted piece this is the tempered cone contribution. -/
def temperedPieceRealPartOffset (ha : IsSplitComponent a) (a' : A'.toGrp ⟶ E.L')
    (f : A ⟶ A') (ψ : leviUnramifiedCharacters l hl)
    (χ : rationalPoints A.toGrp →* ℂˣ) : Vstar A :=
  Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ -
    E.unramifiedPieceRealPart ha a' f ψ

end Offset

end GeometricLemmaIntersectionDatum

set_option backward.isDefEq.respectTransparency false in
/-- Every nonidentity actual opposite piece has split-component spectrum disjoint
from the inducing twist of a Langlands triplet. No intersection presentation,
component factorization or Jacquet admissibility is left as a premise. -/
theorem langlandsTripletOppositePieceSeparation :
    LanglandsTripletOppositePieceSeparationStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν R P M N A p l r a hp hl hr hmul ha J f σ ψ
    Q U q lQ rQ hq hlQ hrQ hmulQ hLevi hOpp hTrip
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let : TopologicalSpace (rationalPoints A.toGrp) := RationalPointFamily.splitComponentPointTopology ha
  let pres : ParabolicRootPresentation p l a := ⟨⟨T, i, ν, J, f⟩, hTrip.1⟩
  obtain ⟨presQ⟩ := parabolicRootPresentationExistence k G hG Q M A q lQ a hq hlQ ha
  have hpoints : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) ⊓
      (SubgroupFunctor.range q).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)) := by
    simpa only [pointImage_eq_range_carrier] using hOpp
  intro τ z hz E w h
  have hadm : τ.IsAdmissible :=
    (SmoothRep.isAdmissible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.2.1.isAdmissible
  set E₀ := E w h
  obtain ⟨A', a', g, ha', hg⟩ := E₀.exists_isSplitComponent_factor ha
  let := leviPointTopology E₀.l' E₀.hl'
  have hJ := arbitraryParabolicJacquetAdmissibility k M hl.isConnectedReductive
    E₀.P' E₀.M' E₀.N' E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hl' E₀.hr' E₀.hmul' τ hadm
  have hJ' : ((leviJacquetFunctor E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hr' E₀.hl' E₀.hmul').obj τ).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hr' E₀.hl' E₀.hmul').obj τ).representation
      (leviPointsEquiv E₀.p' E₀.l' E₀.hp' E₀.hl') hJ
  have hz0 : DoubleCoset.mk (pointImage p) (pointImage q) (z w) ≠
      DoubleCoset.mk (pointImage p) (pointImage q) 1 := by
    rw [hz w]
    exact h.2
  have hδ := E₀.unramifiedPieceDisplacement_mem_nonnegCone_and_ne_zero pres
    hLevi hG R ψ hTrip.2.2.2 a' (Additive.ofMul g) hg hz0
  refine Set.disjoint_left.mpr ?_
  intro χ hχ hχE
  have hEigen := isGeneralizedEigencharacter_of_isGeneralizedWeight
    ((E₀.pieceFunctor.obj τ).ρ) (rationalPoints.map a) χ
    ha.isCentralSplitTorus.isCentral.map_mem_center hχE
  have hxQ : E₀.temperedPieceRealPartOffset ha a' (Additive.ofMul g) ψ χ ∈ presQ.nonnegCone :=
    E₀.normalizedRealPart_sub_unramifiedPieceRealPart_mem_nonnegCone
      ha ha' (Additive.ofMul g) hg presQ
      (relativeRootNegation k G hG presQ.data.T presQ.data.i presQ.isCompatible.maximalSplit)
      σ ψ hTrip.2.2.1 hJ' χ hEigen
  have hxP := pres.neg_mem_nonnegCone_of_opposite presQ hG hLevi hpoints hxQ
  have hne := pres.add_ne_zero_of_mem_nonnegCone hxP hδ.1 hδ.2
  have hreal := normalizedTemperedTwist_groupExponent_realPart
    hl.isConnectedReductive a ha σ hTrip.2.2.1 hTrip.2.1 ψ.val.toMonoidHom
    (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) χ hχ
  apply hne
  dsimp only [GeometricLemmaIntersectionDatum.temperedPieceRealPartOffset,
    GeometricLemmaIntersectionDatum.unramifiedPieceDisplacement, leviUnramifiedRealPart]
  rw [hreal]
  abel

end Langlands.Aubert.General.RepresentedParabolic
