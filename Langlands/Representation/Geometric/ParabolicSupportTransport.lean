import Langlands.Representation.Geometric.CompactSmoothComparison
import Langlands.Representation.Geometric.ParabolicSupportFiltration
import Langlands.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Twist.SmoothProof

/-! Smooth inducing covariance and transport of the actual support quotients. -/

noncomputable section
open CategoryTheory

namespace Langlands.GeneralLinear.BlockShape

universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B : BlockShape n)

/-- Inflation along the continuous Levi projection and a smooth character
preserve smoothness of the inducing covariance representation. -/
theorem isSmooth_inducingRepresentation (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F)) :
    IsSmooth (B.inducingRepresentation χ A.representation) :=
  (isSmooth_twist_iff (B.inflateCharacter χ).toMonoidHom _
    (B.inflateCharacter χ).isOpen_ker).mpr
      (isSmooth_comp (B.leviProjection F) (B.leviProjectionContinuous F).continuous A.isSmooth)

/-- The same inducing functor, bundled with its established smoothness. -/
def smoothInducingFunctor (χ : Induction.SmoothCharacter ℂ (B.Levi F)) :
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤ SmoothRep.{0, uF, uV} ℂ (B.parabolic F) where
  obj A := SmoothRep.of (B.inducingRepresentation χ A.representation)
    (B.isSmooth_inducingRepresentation χ A)
  map f := SmoothRep.ofHom (B.inducingMap χ (SmoothRep.hom f))
  map_id A := by ext v; rfl
  map_comp f g := by ext v; rfl

@[simp]
theorem smoothInducingFunctor_toRep (χ : Induction.SmoothCharacter ℂ (B.Levi F)) :
    B.smoothInducingFunctor.{uF, uV} χ ⋙ SmoothRep.toRep = B.inducingFunctor χ := rfl

end Langlands.GeneralLinear.BlockShape

namespace Langlands.Geometric

open GeneralLinear
universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- At the same index, compact support with smooth inducing covariance and
actual normalized parabolic smooth induction have naturally isomorphic quotients. -/
def parabolicSupportGradedCompactSmoothIso {m : ℕ}
    (s : letI := T.topology
      OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m)
    (i : Fin m) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    B.smoothInducingFunctor (T.leviHalfCharacter B) ⋙
        (s.supportFiltration.{0, uF, uV} (R := ℂ)).graded i ≅
      (parabolicInductionSupportFiltration.{uF, uV} T B C s).graded i := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI : CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier)) :=
    Parabolic.parabolicQuotientCompact F T B
  exact Functor.isoWhiskerLeft (B.inducingFunctor (T.leviHalfCharacter B))
    (s.rawSupportGradedCompactSmoothIso (R := ℂ) i)

end Langlands.Geometric
