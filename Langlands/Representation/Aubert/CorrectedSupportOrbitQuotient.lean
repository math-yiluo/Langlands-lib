import Langlands.Representation.Aubert.CorrectedSupportOrbitSteps
import Langlands.Representation.Geometric.ParabolicSupportTransport
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.CountabilityProof

/-! Actual corrected support quotients and their orbit restriction formula. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open CategoryTheory

namespace Langlands.Geometric.OpenOrbitSupportPair

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [SigmaCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  {P Q : Subgroup G} {w : G} (s : OpenOrbitSupportPair P Q w)
  (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
  [CompactSpace (Induction.LeftQuotient P)]

/-- Canonical transport of the raw compact-support quotient to the raw smooth
support quotient on the same actual support pair. -/
def compactSmoothQuotientIso :
    (rawSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.lower
      s.lower_invariant).quotientFunctor
      (rawSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.upper s.upper_invariant) ≅
    (rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.lower
      s.lower_invariant).quotientFunctor
      (rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.upper s.upper_invariant) :=
  RepSubfunctor.quotientNatIso
    (rawSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.lower s.lower_invariant)
    (rawSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.upper s.upper_invariant)
    (rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.lower s.lower_invariant)
    (rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.upper s.upper_invariant)
    (rawSupportCompactSmoothIso.{0, uG, uV} (R := ℂ) P Q s.upper s.upper_invariant)
    (fun _ _ => Iff.rfl)

/-- The same actual support quotient for smooth induction is the orbit piece,
through the canonical compact-to-smooth comparison. -/
def smoothQuotientIso :
    SmoothRep.toRep ⋙
      (rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.lower
        s.lower_invariant).quotientFunctor
        (rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.upper s.upper_invariant) ≅
      orbitPiece.{0, uG, uV} (R := ℂ) P Q w := by
  let e :
      SmoothRep.toRep ⋙
        (rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.lower
          s.lower_invariant).quotientFunctor
          (rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.upper s.upper_invariant) ≅
      SmoothRep.toRep ⋙
        (rawSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.lower
          s.lower_invariant).quotientFunctor
          (rawSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.upper s.upper_invariant) :=
    Functor.isoWhiskerLeft SmoothRep.toRep s.compactSmoothQuotientIso.symm
  let e' :
      SmoothRep.toRep ⋙
        (rawSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.lower
          s.lower_invariant).quotientFunctor
          (rawSupportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.upper s.upper_invariant) ≅
      orbitPiece.{0, uG, uV} (R := ℂ) P Q w := s.quotientIso hP hQ
  exact e ≪≫ e'

/-- On every representative, the smooth support quotient isomorphism evaluates
by restriction along the actual orbit. -/
theorem smoothQuotientIso_hom_projection_eval
    (A : SmoothRep.{0, uG, uV} ℂ P)
    (f : (rawSmoothSupportSubfunctor (R := ℂ) P Q s.upper
      s.upper_invariant).representation A.obj) (q : Q) :
    Induction.eval _ _
      (((s.smoothQuotientIso hP hQ).hom.app A).hom
        (((rawSmoothSupportSubfunctor (R := ℂ) P Q s.lower
          s.lower_invariant).quotientProjection
          (rawSmoothSupportSubfunctor P Q s.upper s.upper_invariant) A.obj).hom f)).val q =
      Induction.eval P A.obj.ρ f.val (w⁻¹ * (q : G)) := by
  change Induction.eval P A.obj.ρ
    (((rawSupportCompactSmoothIso P Q s.upper s.upper_invariant).inv.app A.obj).hom f).val.val
    (w⁻¹ * (q : G)) = _
  rw [rawSupportCompactSmoothIso_inv_apply_val]

end Langlands.Geometric.OpenOrbitSupportPair

namespace Langlands.Aubert.Support

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
  (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
  (hLower : ∀ v ∈ θ \ {w}, ∀ z, inversionLength v < inversionLength z → z ∈ θ \ {w})
  (hw : w ∈ weylSupport B C θ)

/-- The actual normalized-induction quotient for an active corrected support step
is the conjugated compact orbit piece, naturally in the inducing representation. -/
def correctedInductionOrbitIso :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (correctedInductionSupport.{uF, uV} T B C (θ \ {w})).quotientFunctor
        (correctedInductionSupport T B C θ) ≅
      B.inducingFunctor (T.leviHalfCharacter B) ⋙
        rawOrbitPiece (B.parabolic F.Carrier) (C.parabolic F.Carrier)
          (permutation n F.Carrier w) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearT2Space n
  let := T.generalLinearSigmaCompactSpace n
  let : CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier)) :=
    Parabolic.parabolicQuotientCompact F T B
  exact Functor.isoWhiskerLeft (B.smoothInducingFunctor (T.leviHalfCharacter B))
    ((correctedOpenOrbitSupportPair T B C θ w hθ hLower hw).smoothQuotientIso
      (B.isClosed_parabolic F.Carrier) (C.isClosed_parabolic F.Carrier))

/-- The preceding isomorphism retains the actual inverse-permutation restriction
on every normalized-induction support representative. -/
theorem correctedInductionOrbitIso_hom_projection_eval :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (f : (correctedInductionSupport T B C θ).representation A)
      (q : C.parabolic F.Carrier),
      Induction.eval _ _
        (((correctedInductionOrbitIso T B C θ w hθ hLower hw).hom.app A).hom
          (((correctedInductionSupport T B C (θ \ {w})).quotientProjection
            (correctedInductionSupport T B C θ) A).hom f)).val q =
        Induction.eval (B.parabolic F.Carrier)
          (B.inducingRepresentation (T.leviHalfCharacter B) A.representation)
          f.val ((permutation n F.Carrier w)⁻¹ * (q : GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearT2Space n
  let := T.generalLinearSigmaCompactSpace n
  let : CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier)) :=
    Parabolic.parabolicQuotientCompact F T B
  intro A f q
  exact (correctedOpenOrbitSupportPair T B C θ w hθ hLower hw).smoothQuotientIso_hom_projection_eval
    (B.isClosed_parabolic F.Carrier) (C.isClosed_parabolic F.Carrier)
    ((B.smoothInducingFunctor (T.leviHalfCharacter B)).obj A) f q

/-- The actual quotient between corrected normalized Jacquet support images is
the actual normalized Jacquet orbit functor. -/
def correctedJacquetOrbitIso :
    letI := T.topology
    (correctedJacquetSupport.{uF, uV} T B C (θ \ {w})).quotientFunctor
        (correctedJacquetSupport T B C θ) ≅
      parabolicOrbitJacquetFunctor T B C w := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact correctedSupportQuotientIso T B C (Set.sdiff_subset (s := θ) (t := {w})) ≪≫
    Functor.isoWhiskerRight (correctedInductionOrbitIso T B C θ w hθ hLower hw)
      (Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C))

end Langlands.Aubert.Support
