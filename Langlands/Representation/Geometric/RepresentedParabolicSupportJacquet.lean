import Langlands.Representation.Geometric.RepresentedParabolicSupportOrbit
import Langlands.Representation.Geometric.RepresentedParabolicCoinvariantsExact

/-! # Jacquet comparison for the actual represented support-image quotients -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

private theorem repSubfunctor_eq_of_obj_eq
    {R : Type*} [CommRing R] {H : Type*} [Monoid H]
    {C : Type*} [Category C] {F : C ⥤ Rep R H} {S T : RepSubfunctor F}
    (h : ∀ X, S.obj X = T.obj X) : S = T := by
  cases S with
  | mk Sobj Smap =>
    cases T with
    | mk Tobj Tmap =>
      have heq : Sobj = Tobj := funext h
      cases heq
      rfl

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance supportJacquetAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))

/-- The canonical comparison between parabolic coinvariants of the restricted
actual induction and the ambient induction–Jacquet composite. -/
def leviInductionCoinvariantsRestrictionIso :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    (leviInductionFunctor.{u, v} p l r hp hr hl hmul ⋙
      SmoothRep.restrictSubgroupFunctor (pointImage q)) ⋙
        smoothLeviParabolicCoinvariantsFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ ⋙
          SmoothRep.toRep ≅
      leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ := by
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  exact Functor.isoWhiskerLeft (leviInductionFunctor p l r hp hr hl hmul)
    (leviParabolicCoinvariantsRestrictionIso q lQ rQ hq hrQ hlQ hmulQ)

variable
  (S T : letI := leviPointTopology l hl
    RepSubfunctor
      (leviInductionFunctor.{u, v} p l r hp hr hl hmul ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (pointImage q).subtype))

set_option maxHeartbeats 800000 in
/-- Transporting the mapped-inclusion image along the same-vector-class
comparison gives exactly the original ambient support-image subfunctor. -/
theorem leviJacquetImage_eq_isoTransport_exactImage :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    (S.exactImage
        (smoothLeviParabolicCoinvariantsFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ)).isoTransport
        (leviInductionCoinvariantsRestrictionIso p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ) =
      leviJacquetImageSubfunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ S := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  let I := leviInductionFunctor.{u, v} p l r hp hr hl hmul
  let e := leviInductionCoinvariantsRestrictionIso p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ
  apply repSubfunctor_eq_of_obj_eq
  intro A
  apply SetLike.ext
  intro x
  change (∃ y, SmoothRep.hom
      ((smoothLeviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ).map
        ((S.smoothInclusion (F := I ⋙ SmoothRep.restrictSubgroupFunctor (pointImage q))).app A))
        y = (e.inv.app A).hom x) ↔
    ∃ y ∈ (S.obj A), Jacquet.Localization.mk (I.obj A).representation
      (pointImage (rQ ≫ q)) 1 y = x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Jacquet.Localization.mk_surjective
      (S.obj A).toRepresentation (parabolicRadicalPoints q rQ) 1 y
    refine ⟨z.val, z.property, ?_⟩
    have he := congrArg (e.hom.app A).hom hy
    exact he.trans (Rep.hom_inv_apply _ _ (e.app A) x)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Jacquet.Localization.mk (S.obj A).toRepresentation
      (parabolicRadicalPoints q rQ) 1 ⟨y, hy⟩, ?_⟩
    apply (Representation.equivOfIso (e.app A)).injective
    exact (Rep.hom_inv_apply _ _ (e.app A) _).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Exactness on the target parabolic identifies the actual ambient image
quotient with normalized coinvariants of the actual induction support quotient. -/
def leviJacquetImageQuotientIso
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups (parabolicRadicalPoints q rQ))
    (hST : ∀ A, S.obj A ≤ T.obj A) :
    letI := leviPointTopology l hl
    (leviJacquetImageSubfunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ S).quotientFunctor
        (leviJacquetImageSubfunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ T) ≅
      S.quotientFunctor T ⋙
        leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ := by
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  let J := smoothLeviParabolicCoinvariantsFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ
  let e := leviInductionCoinvariantsRestrictionIso p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ
  let SI := S.exactImage
    (F := leviInductionFunctor p l r hp hr hl hmul ⋙
      SmoothRep.restrictSubgroupFunctor (pointImage q)) J
  let TI := T.exactImage
    (F := leviInductionFunctor p l r hp hr hl hmul ⋙
      SmoothRep.restrictSubgroupFunctor (pointImage q)) J
  let A := leviJacquetImageSubfunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ S
  let B := leviJacquetImageSubfunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ T
  have hS : SI.isoTransport e = A :=
    leviJacquetImage_eq_isoTransport_exactImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ S
  have hT : TI.isoTransport e = B :=
    leviJacquetImage_eq_isoTransport_exactImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ T
  have hExact : SI.quotientFunctor TI ≅ S.quotientFunctor T ⋙
      leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ :=
    leviParabolicCoinvariantsImageQuotientIso
      (F := leviInductionFunctor p l r hp hr hl hmul ⋙
        SmoothRep.restrictSubgroupFunctor (pointImage q))
      q lQ rQ hq hrQ hlQ hmulQ hU S T hST
  have hTransport : (SI.isoTransport e).quotientFunctor (TI.isoTransport e) ≅
      SI.quotientFunctor TI := (SI.isoTransportQuotientIso TI e).symm
  change A.quotientFunctor B ≅ _
  clear_value SI TI A B e
  exact eqToIso (congrArg₂ (fun X Y => X.quotientFunctor Y) hS.symm hT.symm) ≪≫
    hTransport ≪≫ hExact

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- At each original support-filtration index, the same natural quotient comparison. -/
def leviJacquetSupportGradedIso
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups (parabolicRadicalPoints q rQ))
    {m : ℕ} (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m) (i : Fin m) :
    letI := leviPointTopology l hl
    (leviJacquetSupportFiltration.{u, v} p l r hp hr hl hmul
        q lQ rQ hq hrQ hlQ hmulQ s).graded i ≅
      (leviInductionSupportFiltration p l r hp hr hl hmul q s).graded i ⋙
        leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ := by
  letI := leviPointTopology l hl
  let t := leviInductionSupportFiltration.{u, v} p l r hp hr hl hmul q s
  exact leviJacquetImageQuotientIso p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (t.step i.castSucc) (t.step i.succ) hU (fun A => t.step_le_next A i)

variable [CompactSpace (Induction.LeftQuotient (pointImage p))]
  [T2Space (rationalPoints G)] [SigmaCompactSpace (rationalPoints G)]

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- The actual normalized Jacquet support grade is the normalized target-radical
coinvariant functor of its compact stabilizer orbit piece. -/
def leviJacquetSupportOrbitIso
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups (parabolicRadicalPoints q rQ))
    {m : ℕ} (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m) (i : Fin m) :
    letI := leviPointTopology l hl
    (leviJacquetSupportFiltration.{u, v} p l r hp hr hl hmul
        q lQ rQ hq hrQ hlQ hmulQ s).graded i ≅
      smoothLeviInducingFunctor p l r hp hr hl hmul ⋙
        Geometric.orbitPiece (pointImage p) (pointImage q) (s.representative i) ⋙
          leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ := by
  letI := leviPointTopology l hl
  exact leviJacquetSupportGradedIso p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ hU s i ≪≫
    Functor.isoWhiskerRight (leviInductionSupportOrbitIso p l r hp hr hl hmul q hq s i)
      (leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ) ≪≫
    Functor.associator _ _ _

end Langlands.Aubert.General.RepresentedParabolic
