import Langlands.Representation.Geometric.DegenerateJacquetPieces
import Langlands.Representation.Geometric.SelfIntersectionLevi
import Langlands.Representation.Aubert.General.FullParabolicInductionIrreducible

/-! # Irreducibility of full intersection pieces -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}

namespace GeometricLemmaIntersectionDatum

variable {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)

/-- If the outer Levis are isomorphic and the source intersection is full,
the target intersection Levi maps isomorphically to the outer target Levi. -/
theorem isIso_lQ'_comp_q'_of_isIso_p'_of_iso (E : M ≅ L) [IsIso D.p'] :
    IsIso (D.lQ' ≫ D.q') := by
  have := D.isIso_l'_of_isIso_p'
  let e : D.L' ≅ L := D.φ ≪≫ asIso (D.l' ≫ D.p') ≪≫ E
  let f : L ⟶ L := e.inv ≫ D.lQ' ≫ D.q'
  have hf : IsClosedSubgroup f :=
    (IsClosedSubgroup.of_iso e.symm).comp
      (D.hlQ'.isClosedSubgroup.comp D.hq'.isClosedSubgroup)
  have := hlQ.isConnectedReductive.isIso_of_isClosedSubgroup f hf
  have hcomp : D.lQ' ≫ D.q' = e.hom ≫ f := by
    simp only [f, Iso.hom_inv_id_assoc]
  rw [hcomp]
  infer_instance

/-- Full source intersection and an isomorphism of the outer Levis force the
target intersection parabolic to be full. -/
theorem isIso_q'_of_isIso_p'_of_iso (E : M ≅ L) [IsIso D.p'] : IsIso D.q' := by
  have := D.isIso_lQ'_comp_q'_of_isIso_p'_of_iso E
  exact D.hq'.isClosedSubgroup.isIso_of_isIso_comp D.lQ'

/-- Under the same hypotheses the target intersection Levi is full too. -/
theorem isIso_lQ'_of_isIso_p'_of_iso (E : M ≅ L) [IsIso D.p'] : IsIso D.lQ' := by
  have := D.isIso_lQ'_comp_q'_of_isIso_p'_of_iso E
  have := D.isIso_q'_of_isIso_p'_of_iso E
  exact IsIso.of_isIso_comp_right D.lQ' D.q'

end GeometricLemmaIntersectionDatum

variable [T2Space k] [IsAffineHom G.X.hom]

local instance fullIntersectionPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- The full-Levi Jacquet equivalence is equivariant for the original action
pulled back along the actual Levi inclusion. -/
def fullLeviJacquetRepresentationEquiv
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) [IsIso l]
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    ((leviJacquetFunctor p l r hp hr hl hmul).obj A).representation.Equiv
      (A.representation.comp (rationalPoints.map (l ≫ p))) :=
  Representation.Equiv.mk (fullLeviJacquetEquiv p l r hp hr hl hmul A) fun m => by
    ext x
    exact fullLeviJacquetEquiv_representation p l r hp hr hl hmul A m x

/-- When both the parabolic and its Levi inclusions are isomorphisms, actual
normalized Jacquet restriction preserves irreducibility. -/
theorem leviJacquet_isIrreducible_of_isIso
    (p : P ⟶ G) [IsIso p] (l : M ⟶ P) [IsIso l] (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (hA : A.IsIrreducible) :
    letI := leviPointTopology l hl
    ((leviJacquetFunctor p l r hp hr hl hmul).obj A).IsIrreducible := by
  let := leviPointTopology l hl
  let : A.representation.IsIrreducible := hA
  have hsurj : Function.Surjective (rationalPoints.map (l ≫ p)) := by
    intro x
    refine ⟨rationalPoints.map (inv (l ≫ p)) x, ?_⟩
    rw [← pointMap_comp_apply, IsIso.inv_hom_id]
    rfl
  exact (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv
    (fullLeviJacquetRepresentationEquiv p l r hp hr hl hmul A)).mpr
      (CuspidalSupport.isIrreducible_comp_of_surjective A.representation _ hsurj)

namespace GeometricLemmaIntersectionDatum

variable {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
  (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))

/-- A geometric piece with full source and target intersection parabolics is
irreducible on an irreducible inducing representation. -/
def FullIntersectionPieceIrreducibleStatement : Prop :=
  letI := leviPointTopology l hl
  IsIso D.p' → IsIso D.q' → ρ.IsIrreducible → (D.pieceFunctor.obj ρ).ρ.IsIrreducible

theorem pieceFunctor_isIrreducible_of_isIso [IsIso D.p'] [IsIso D.q']
    (hρ : letI := leviPointTopology l hl; ρ.IsIrreducible) :
    (D.pieceFunctor.obj ρ).ρ.IsIrreducible := by
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
  have := D.isIso_l'_of_isIso_p'
  have hjac : ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ).IsIrreducible :=
    leviJacquet_isIrreducible_of_isIso D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' ρ hρ
  have hpull : ((SmoothRep.pullbackFunctor D.e).obj
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ)).IsIrreducible :=
    CuspidalSupport.isIrreducible_comp_of_surjective _ D.e.toMonoidHom D.e.surjective
      (hρ := hjac)
  exact leviInduction_isIrreducible_of_isIso D.q' D.lQ' D.rQ'
    D.hq' D.hlQ' D.hrQ' D.hmulQ' _ hpull

theorem fullIntersectionPieceIrreducible : D.FullIntersectionPieceIrreducibleStatement ρ := by
  intro hp' hq' hρ
  let : IsIso D.p' := hp'
  let : IsIso D.q' := hq'
  exact D.pieceFunctor_isIrreducible_of_isIso ρ hρ

/-- For isomorphic outer Levis a full source intersection suffices for
irreducibility of the piece. -/
theorem pieceFunctor_isIrreducible_of_isIso_source_of_iso (E : M ≅ L) [IsIso D.p']
    (hρ : letI := leviPointTopology l hl; ρ.IsIrreducible) :
    (D.pieceFunctor.obj ρ).ρ.IsIrreducible := by
  have := D.isIso_q'_of_isIso_p'_of_iso E
  exact D.pieceFunctor_isIrreducible_of_isIso ρ hρ

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
