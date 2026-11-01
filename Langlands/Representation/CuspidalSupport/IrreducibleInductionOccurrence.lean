import Langlands.Representation.CuspidalSupport.ConstituentProof
import Langlands.Representation.Parabolic.NaturalFirstAdjointness
import Langlands.Representation.Classification.FiniteLengthProof
import Langlands.Representation.Classification.SupercuspidalSupport

/-! Actual cuspidal Jacquet occurrences and irreducible parabolic induction. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- An actual cuspidal constituent of the Jacquet module identifies an
irreducible ambient object with its irreducible normalized induction. -/
def irreducibleInductionIsoOfCuspidalOccurrence :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (D : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)),
      X.IsIrreducible → X.IsAdmissible →
      D.IsIrreducible → IsLeviCuspidal B D.representation →
      SmoothRep.IsSubquotient D ((T.normalizedJacquetFunctor B).obj X) →
      ((T.normalizedParabolicInductionFunctor B).obj D).IsIrreducible →
      (X ≅ (T.normalizedParabolicInductionFunctor B).obj D) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro X D hXi hXa hDi hDc hDX hIi
  have hJa : ((T.normalizedJacquetFunctor B).obj X).IsAdmissible :=
    FiniteLengthAssembly.isAdmissible_normalizedJacquet T B X.representation hXa
  let hquot :=
    (leviCuspidalConstituentTheorem F T B _ D hJa hDi hDc hDX).2
  let q := Classical.choose hquot
  have hq := Classical.choose_spec hquot
  let q' : (T.normalizedJacquet B X.representation).IntertwiningMap D.representation :=
    SmoothRep.hom q
  letI := hDi
  letI : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (B.Levi F.Carrier))
      D.representation.asModule
  have hq0 : q' ≠ 0 := by
    intro h
    obtain ⟨d, hd⟩ := exists_ne (0 : D)
    obtain ⟨v, hv⟩ := hq d
    exact hd (hv.symm.trans (congrArg (fun f => f v) h))
  let e := Parabolic.FirstAdjointness.equiv T B X.isSmooth
    (σ := D.representation)
  let f := e.symm q'
  have hf0 : f ≠ 0 := by
    intro h
    apply hq0
    have hh := congrArg e h
    simpa only [f, e.apply_symm_apply, map_zero] using hh
  letI := hXi
  letI : (T.normalizedParabolicInduced B D.representation).IsIrreducible := hIi
  exact SmoothRep.mkIso
    (f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf0))

/-- A nonzero map into induction of an irreducible Levi representation gives
an actual quotient of the normalized Jacquet module. -/
theorem isQuotient_normalizedJacquet_of_inductionHom :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (D : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)),
      D.IsIrreducible →
      ∀ f : X.representation.IntertwiningMap
        (T.normalizedParabolicInduced B D.representation),
        f ≠ 0 → SmoothRep.IsQuotient D ((T.normalizedJacquetFunctor B).obj X) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro X D hDi f hf
  letI := hDi
  let q := jacquetEvaluation T B f
  have hq : q ≠ 0 := jacquetEvaluation_ne_zero T B f hf
  exact ⟨SmoothRep.ofHom q,
    (Representation.IsIrreducible.surjective_or_eq_zero q).resolve_right hq⟩

/-- Transport an actual cuspidal Jacquet occurrence through an isomorphism
of irreducible induced objects, allowing a different standard block shape. -/
theorem cuspidalOccurrence_transfer_of_inductionIso (C : BlockShape n) :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (D : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier))
      (E : SmoothRep.{0, uF, max uF uV} ℂ (C.Levi F.Carrier)),
      X.IsIrreducible → X.IsAdmissible →
      D.IsIrreducible → IsLeviCuspidal B D.representation → E.IsIrreducible →
      SmoothRep.IsSubquotient D ((T.normalizedJacquetFunctor B).obj X) →
      ((T.normalizedParabolicInductionFunctor B).obj D).IsIrreducible →
      Nonempty ((T.normalizedParabolicInductionFunctor B).obj D ≅
        (T.normalizedParabolicInductionFunctor C).obj E) →
      SmoothRep.IsSubquotient E ((T.normalizedJacquetFunctor C).obj X) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro X D E hXi hXa hDi hDc hEi hDX hIi ⟨e⟩
  let eX := irreducibleInductionIsoOfCuspidalOccurrence F T B X D
    hXi hXa hDi hDc hDX hIi ≪≫ e
  let f := SmoothRep.hom eX.hom
  have hf : f ≠ 0 := by
    intro h
    letI := hXi
    letI : Nontrivial X :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
        X.representation.asModule
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    apply hx
    apply (SmoothRep.equivOfIso eX).injective
    exact (congrArg (fun g => g x) h).trans (map_zero f).symm
  exact (isQuotient_normalizedJacquet_of_inductionHom F T C X E hEi f hf).isSubquotient

end Langlands.CuspidalSupport
