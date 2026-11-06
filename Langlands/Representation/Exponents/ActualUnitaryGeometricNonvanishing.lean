import Langlands.Representation.Exponents.TemperedGeometricLemmaStatement
import Langlands.Representation.Filtration.NonzeroMapGradedPiece

/-! # Nonzero maps and actual unitary geometric pieces -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitaryGeometricNonvanishingAmbientTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)}

namespace GeometricLemmaIntersectionDatum

variable {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
  {A' : CommGroupScheme (Spec (CommRingCat.of k))} {a' : A'.toGrp ⟶ D.M'}
  (ha' : IsSplitComponent a')
  (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
  (τ : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, w} ℂ (rationalPoints L))

/-- An actual nonzero map from the unitary piece of one intersection datum. -/
structure NonzeroUnitaryPieceMap where
  map : letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    Representation.IntertwiningMap (D.unitaryPieceRep ha' σ).ρ τ.representation
  nonzero : map ≠ 0

set_option maxHeartbeats 800000 in
/-- A nonzero map out of the induced unitary piece forces its original
unitary Jacquet summand to be nonzero. No intersection fullness is assumed. -/
theorem NonzeroUnitaryPieceMap.unitaryJacquetPart_ne_bot
    (F : D.NonzeroUnitaryPieceMap ha' σ τ) :
    letI := leviPointTopology l hl
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    unitaryJacquetPart D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' σ ≠ ⊥ := by
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  intro hbot
  apply F.nonzero
  ext f
  have hf : f = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply Subtype.ext
    have hval := (f.1.1 g).property
    change (f.1.1 g).val ∈
      unitaryJacquetPart D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' σ at hval
    exact hbot.le hval
  change F.map f = 0
  rw [hf, map_zero]

end GeometricLemmaIntersectionDatum

set_option maxHeartbeats 800000 in
/-- Choose an actual nonzero unitary-piece map from a finite object filtration
with the supplied graded-piece equivalences. This consumes a filtration and
does not assert the tempered geometric lemma itself. -/
def nonzeroUnitaryPieceMapOfFiltration
    {m : ℕ} {z : Fin m → rationalPoints G}
    (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ (z i))
    {A' : Fin m → CommGroupScheme (Spec (CommRingCat.of k))}
    {a' : ∀ i, (A' i).toGrp ⟶ (D i).M'} (ha' : ∀ i, IsSplitComponent (a' i))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (τ : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, w} ℂ (rationalPoints L))
    {V : Rep.{max u v} ℂ (rationalPoints L)} (s : ObjectRepFiltration V m)
    (e : Equiv.Perm (Fin m))
    (hs : letI := leviPointTopology l hl
      ∀ j, Nonempty ((s.gradedRepresentation j).ρ.Equiv
        ((D (e j)).unitaryPieceRep (ha' (e j)) σ).ρ))
    (F : letI := leviPointTopology lQ hlQ
      Representation.IntertwiningMap V.ρ τ.representation) (hF : F ≠ 0) :
    Σ i, (D i).NonzeroUnitaryPieceMap (ha' i) σ τ := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  apply Classical.choice
  obtain ⟨j, h, hj⟩ := s.exists_mapFromGraded_ne_zero F hF
  let E := Classical.choice (hs j)
  let f := (s.mapFromGraded F j h).comp E.symm.toIntertwiningMap
  refine ⟨⟨e j, f, ?_⟩⟩
  intro hf
  apply hj
  ext x
  have hz := congrArg (fun t : Representation.IntertwiningMap
    ((D (e j)).unitaryPieceRep (ha' (e j)) σ).ρ τ.representation => t (E x)) hf
  change s.mapFromGraded F j h (E.symm (E x)) = 0 at hz
  change s.mapFromGraded F j h x = 0
  simpa only [Representation.Equiv.symm_apply_apply] using hz

end Langlands.Aubert.General.RepresentedParabolic
