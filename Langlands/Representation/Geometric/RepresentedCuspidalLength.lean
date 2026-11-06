import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.Representation.Filtration.GluedLength

/-! # Proper-source vanishing and length for represented geometric pieces -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance representedLengthPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)}

/-- Transported normalized induction preserves a zero carrier. -/
theorem leviInductionFunctor_subsingleton
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hz : Subsingleton σ) :
    letI := leviPointTopology l hl
    Subsingleton ((leviInductionFunctor p l r hp hr hl hmul).obj σ) := by
  let := leviPointTopology l hl
  refine ⟨fun f g => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact hz.elim _ _

section Source

variable (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
  (hc : haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (P' M' N' : GroupScheme (Spec (CommRingCat.of k)))
    (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : N' ⟶ P')
    (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
    (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
    (hmul' : IsIso (subgroupMultiplication l' r')),
    ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ))

namespace GeometricLemmaIntersectionDatum

variable {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)

/-- A piece with proper source parabolic has zero actual carrier. -/
def ProperSourceVanishingStatement : Prop :=
  ¬ IsIso D.p' → Subsingleton (D.pieceFunctor.obj ρ)

include hc

/-- The original proper-Jacquet vanishing condition kills the transported source
Jacquet module, since pullback retains its carrier. -/
theorem sourceJacquet_subsingleton_of_proper (hproper : ¬ IsIso D.p') :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    Subsingleton ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ) := by
  exact hc D.P' D.M' D.N' D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' hproper

/-- Source vanishing survives conjugation pullback and normalized induction. -/
theorem pieceFunctor_subsingleton_of_proper (hproper : ¬ IsIso D.p') :
    Subsingleton (D.pieceFunctor.obj ρ) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  exact leviInductionFunctor_subsingleton
    (p := D.q') (l := D.lQ') (r := D.rQ') (hp := D.hq')
    (hl := D.hlQ') (hr := D.hrQ') (hmul := D.hmulQ')
    ((SmoothRep.pullbackFunctor D.e).obj
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ))
    (D.sourceJacquet_subsingleton_of_proper ρ hc hproper)

/-- The proper-source vanishing proposition follows from the original cusp input. -/
theorem properSourceVanishing : D.ProperSourceVanishingStatement ρ :=
  fun hproper => D.pieceFunctor_subsingleton_of_proper ρ hc hproper

end GeometricLemmaIntersectionDatum

variable {m : ℕ} {z : Fin m → rationalPoints G}
  (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ (z i))
  (hglue : IsGluedFrom
    (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
    (fun i => (D i).pieceFunctor))

/-- The original indices whose source parabolic is the full source Levi. -/
def fullSourceIndices : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => IsIso (D i).p')

omit [T2Space k] [IsAffineHom G.X.hom]
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
@[simp] theorem mem_fullSourceIndices (i : Fin m) :
    i ∈ fullSourceIndices D ↔ IsIso (D i).p' := by
  classical
  simp only [fullSourceIndices, Finset.mem_filter, Finset.mem_univ, true_and]

include hc hglue

/-- In a supplied actual geometric-lemma filtration, only indices with full
source parabolic contribute to the composition length. -/
theorem representedJacquetInduction_repLength_eq_sum_fullSource :
    repLength ((leviJacquetInductionFunctor.{u, v}
      p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj ρ).ρ =
      ∑ i ∈ fullSourceIndices D,
        repLength (((D i).pieceFunctor).obj ρ).ρ := by
  classical
  apply hglue.repLength_eq_sum_on ρ
  intro i hi
  apply (D i).pieceFunctor_subsingleton_of_proper ρ hc
  simpa only [mem_fullSourceIndices] using hi

/-- If every full-source piece is irreducible, the actual length is their
number, with all multiplicities retained. -/
theorem representedJacquetInduction_repLength_eq_card_fullSource
    (hirr : ∀ i, IsIso (D i).p' → (((D i).pieceFunctor).obj ρ).ρ.IsIrreducible) :
    repLength ((leviJacquetInductionFunctor.{u, v}
      p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj ρ).ρ =
      ((fullSourceIndices D).card : ℕ∞) := by
  classical
  apply hglue.repLength_eq_card ρ
  · intro i hi
    apply (D i).pieceFunctor_subsingleton_of_proper ρ hc
    simpa only [mem_fullSourceIndices] using hi
  · intro i hi
    exact hirr i ((mem_fullSourceIndices D i).mp hi)

end Source

end Langlands.Aubert.General.RepresentedParabolic
