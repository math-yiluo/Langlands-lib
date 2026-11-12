import Langlands.Representation.Exponents.UnramifiedJacquetExponentTwist
import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.Exponents.RadicalWeightTransfer
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws
import Langlands.GroupScheme.Rational.ParabolicWeylDisplacement

/-! # The cone offset of an actual tempered unramified geometric-lemma piece -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance temperedTwistedPieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
  {A A' : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ L} {a' : A'.toGrp ⟶ D.L'}

/-- The real part of the original unramified character pulled back through the
actual full-piece intersection maps to the target split component. -/
def unramifiedPieceRealPart (ha : IsSplitComponent a) (a' : A'.toGrp ⟶ D.L')
    (f : A ⟶ A') :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    Plancherel.unramifiedCharacters
      (fun c : rationalCharacters M => (Plancherel.rationalNormCharacters M c).toMul) →
      Vstar A := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  intro ψ
  exact Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
    (ψ.val.toMonoidHom.comp (rationalPoints.map
      (CommGroupScheme.groupHom f ≫ a' ≫ D.φ.hom ≫ D.l' ≫ D.p')))

/-- For a tempered source, the real part of every exponent of an actual twisted
full piece is the actual twist parameter plus a vector of the target root cone. -/
theorem exists_normalizedRealPart_eq_cone_add_unramifiedPieceRealPart
    (ha : IsSplitComponent a) (ha' : IsSplitComponent a') (f : A ⟶ A')
    (hf : CommGroupScheme.groupHom f ≫ a' ≫ D.lQ' ≫ D.q' = a)
    (presQ : ParabolicRootPresentation q lQ a)
    (hneg : ∀ α ∈ relativeRoots presQ.data.i, -α ∈ relativeRoots presQ.data.i) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : Plancherel.unramifiedCharacters
        (fun c : rationalCharacters M => (Plancherel.rationalNormCharacters M c).toMul)),
      IsNormalizedExponentTempered hl.isConnectedReductive σ →
      let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj τ).IsAdmissible →
      ∀ χ : rationalPoints A.toGrp →* ℂˣ,
        IsGeneralizedEigencharacter ((D.pieceFunctor.obj τ).ρ.comp (rationalPoints.map a)) χ →
        ∃ x : Vstar A, x ∈ presQ.nonnegCone ∧
          Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ =
            x + D.unramifiedPieceRealPart ha a' f ψ := by
  have := hl.isConnectedReductive.isAffineHom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  intro σ ψ hσ τ hJ χ hχ
  obtain ⟨θ, hθ, _, hreal⟩ :=
    exists_untwisted_sourceJacquetExponent_of_twisted_piece p l r hp hl hr hmul
      D ha ha' f hf σ ψ hJ χ hχ
  have hcone := hσ.parabolic D.p' D.l' (a' ≫ D.φ.hom) D.hp' D.hl' (ha'.comp_iso D.φ)
  obtain ⟨presM⟩ := hcone.1
  have hmem := hcone.2 presM _ D.r' D.hr' D.hmul' θ hθ
  have hopen := ((isNormalizedJacquetExponent_iff_isOpen_ker_and
    _ _ _ _ _ _ _ _ σ θ).mp hθ).1
  have := (ha'.comp_iso D.φ).isAffine
  refine ⟨Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
    (θ.comp (rationalPoints.map (CommGroupScheme.groupHom f))), ?_, hreal⟩
  rw [Plancherel.SplitTorus.normalizedRealPart_comp_points
    ha.isCentralSplitTorus.1.1 (ha'.comp_iso D.φ).isCentralSplitTorus.1.1 f θ hopen]
  exact D.restrictReal_mem_nonnegCone f hf presQ presM hneg hmem

/-- The cone offset can equivalently be read as membership of the difference
between a full-piece exponent's real part and the actual twist parameter. -/
theorem normalizedRealPart_sub_unramifiedPieceRealPart_mem_nonnegCone
    (ha : IsSplitComponent a) (ha' : IsSplitComponent a') (f : A ⟶ A')
    (hf : CommGroupScheme.groupHom f ≫ a' ≫ D.lQ' ≫ D.q' = a)
    (presQ : ParabolicRootPresentation q lQ a)
    (hneg : ∀ α ∈ relativeRoots presQ.data.i, -α ∈ relativeRoots presQ.data.i) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : Plancherel.unramifiedCharacters
        (fun c : rationalCharacters M => (Plancherel.rationalNormCharacters M c).toMul)),
      IsNormalizedExponentTempered hl.isConnectedReductive σ →
      let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj τ).IsAdmissible →
      ∀ χ : rationalPoints A.toGrp →* ℂˣ,
        IsGeneralizedEigencharacter ((D.pieceFunctor.obj τ).ρ.comp (rationalPoints.map a)) χ →
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ -
          D.unramifiedPieceRealPart ha a' f ψ ∈ presQ.nonnegCone := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  intro σ ψ hσ τ hJ χ hχ
  obtain ⟨x, hx, hreal⟩ := D.exists_normalizedRealPart_eq_cone_add_unramifiedPieceRealPart
    ha ha' f hf presQ hneg σ ψ hσ hJ χ hχ
  simpa only [hreal, add_sub_cancel_right] using hx

/-- A nonzero cone displacement of the actual twist parameter from a test
parameter excludes that test parameter as the real part of a full-piece exponent. -/
theorem normalizedRealPart_ne_of_unramifiedPieceRealPart_sub_mem_nonnegCone
    (ha : IsSplitComponent a) (ha' : IsSplitComponent a') (f : A ⟶ A')
    (hf : CommGroupScheme.groupHom f ≫ a' ≫ D.lQ' ≫ D.q' = a)
    (presQ : ParabolicRootPresentation q lQ a)
    (hneg : ∀ α ∈ relativeRoots presQ.data.i, -α ∈ relativeRoots presQ.data.i) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : Plancherel.unramifiedCharacters
        (fun c : rationalCharacters M => (Plancherel.rationalNormCharacters M c).toMul)),
      IsNormalizedExponentTempered hl.isConnectedReductive σ →
      let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj τ).IsAdmissible →
      ∀ paramA : Vstar A,
        D.unramifiedPieceRealPart ha a' f ψ - paramA ∈ presQ.nonnegCone →
        D.unramifiedPieceRealPart ha a' f ψ - paramA ≠ 0 →
        ∀ χ : rationalPoints A.toGrp →* ℂˣ,
          IsGeneralizedEigencharacter ((D.pieceFunctor.obj τ).ρ.comp (rationalPoints.map a)) χ →
          Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠ paramA := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  intro σ ψ hσ τ hJ paramA hδ hδ0 χ hχ heq
  obtain ⟨x, hx, hreal⟩ := D.exists_normalizedRealPart_eq_cone_add_unramifiedPieceRealPart
    ha ha' f hf presQ hneg σ ψ hσ hJ χ hχ
  apply presQ.add_ne_zero_of_mem_nonnegCone hx hδ hδ0
  rw [← add_sub_assoc, ← hreal, heq, sub_self]

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
