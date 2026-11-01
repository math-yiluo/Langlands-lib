import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.DeterminantTwistFiniteSlice
import Langlands.Automorphic.PresentedDeterminantUnramifiedData
import Langlands.Automorphic.OperatorDeterminantTwistClasses
import Langlands.Representation.Category.Twist

/-! # Actual determinant twists of supplied cuspidal spectral presentations -/

noncomputable section
open scoped Classical
universe uF uV uW

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance spectralTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance spectralTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance spectralTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance spectralTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

namespace CuspidalSpectralPresentation

variable {r : ℕ} {S : CuspidalOperatorRealization F r}
variable (P : CuspidalSpectralPresentation.{uF, uV} S)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

/-- Bundle the genuine local character twist on the original factor carrier. -/
def determinantTwistLocalFactor (v : FinitePlace F) :
    Langlands.SmoothRep.{0, uF, uV} ℂ (FiniteLocalGL F (r + 1) v) :=
  (P.localFactor v).twist (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom
    (χ.finiteLocalDeterminant_isOpen_ker (r + 1) hχ v)

@[simp]
theorem determinantTwistLocalFactor_representation (v : FinitePlace F) :
    (P.determinantTwistLocalFactor χ hχ v).representation =
      Langlands.twist (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom
        (P.localFactor v).representation := rfl

/-- Actual finite-slice, tensor and supplied spectral data for the full cuspidal twist. -/
def determinantTwist : CuspidalSpectralPresentation.{uF, uV} (S.determinantTwist χ hχ) where
  finiteSlice := P.finiteSlice.determinantTwist χ hχ
  localFactor := P.determinantTwistLocalFactor χ hχ
  tensorExceptional := FiniteTensorPresentation.determinantTwistExceptional
    (E := P.tensorExceptional) (n := r + 1) χ hχ
  reference := P.reference
  reference_fixed :=
    FiniteTensorPresentation.determinantTwistReference_fixed (he := P.reference_fixed) χ hχ
  presentation := P.presentation.determinantTwist χ hχ
  exceptional := P.exceptional ∪ χ.finiteDeterminantTail (r + 1) hχ
  unramified := P.unramified.determinantTwist χ hχ

@[simp]
theorem determinantTwist_finiteSlice :
    (P.determinantTwist χ hχ).finiteSlice = P.finiteSlice.determinantTwist χ hχ := rfl

@[simp]
theorem determinantTwist_tensorExceptional :
    (P.determinantTwist χ hχ).tensorExceptional =
      P.tensorExceptional ∪ χ.finiteDeterminantTail (r + 1) hχ := rfl

@[simp]
theorem determinantTwist_exceptional :
    (P.determinantTwist χ hχ).exceptional =
      P.exceptional ∪ χ.finiteDeterminantTail (r + 1) hχ := rfl

/-- The actual new numerical system is precisely the scaled, restricted old system. -/
@[simp]
theorem determinantTwist_spectralSystem :
    (P.determinantTwist χ hχ).spectralSystem =
      (SpectralSystem.scale χ.finiteUniformizerValue P.spectralSystem).restrict
        (P.exceptional ∪ χ.finiteDeterminantTail (r + 1) hχ)
        Finset.subset_union_left := rfl

/-- The new presentation's component and the actual multiplied old component
are genuinely equivalent; their auxiliary complementary vectors may differ. -/
def determinantTwistLocalComponentEquiv (v : FinitePlace F) :
    ((P.determinantTwist χ hχ).localComponent v).representation.Equiv
      ((P.localComponent v).determinantTwist χ hχ).representation :=
  ((P.determinantTwist χ hχ).presentation.localComponentEquiv
    (P.determinantTwist χ hχ).finiteSlice.nonzero v).symm.trans
      ((Langlands.twistEquiv (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom
        (P.presentation.localComponentEquiv P.finiteSlice.nonzero v)).trans
          ((P.localComponent v).determinantTwistRepresentationEquiv χ hχ))

theorem determinantTwist_localComponent_isoClass (v : FinitePlace F) :
    ((P.determinantTwist χ hχ).localComponent v).isoClass =
      ((P.localComponent v).determinantTwist χ hχ).isoClass :=
  (LocalRealization.isoClass_eq_iff _ _).mpr
    ⟨P.determinantTwistLocalComponentEquiv χ hχ v⟩

theorem determinantTwist_powerTrace (v : FinitePlace F)
    (hv : v ∉ P.exceptional ∪ χ.finiteDeterminantTail (r + 1) hχ) (k : ℕ) :
    (P.determinantTwist χ hχ).spectralSystem.powerTrace v hv k =
      (χ.finiteUniformizerValue v : ℂ) ^ k *
        P.spectralSystem.powerTrace v (fun h => hv (Finset.mem_union_left _ h)) k :=
  P.unramified.determinantTwist_powerTrace χ hχ v hv k

theorem determinantTwist_eulerPolynomial (v : FinitePlace F)
    (hv : v ∉ P.exceptional ∪ χ.finiteDeterminantTail (r + 1) hχ) :
    (P.determinantTwist χ hχ).spectralSystem.eulerPolynomial v hv =
      (P.spectralSystem.eulerPolynomial v
        (fun h => hv (Finset.mem_union_left _ h))).comp
          (Polynomial.C (χ.finiteUniformizerValue v : ℂ) * Polynomial.X) :=
  P.unramified.determinantTwist_eulerPolynomial χ hχ v hv

theorem samePowerTraces_determinantTwist :
    (SpectralSystem.scale χ.finiteUniformizerValue P.spectralSystem).SamePowerTraces
      (P.determinantTwist χ hχ).spectralSystem :=
  P.unramified.samePowerTraces_determinantTwist χ hχ

theorem sameEulerPolynomials_determinantTwist :
    (SpectralSystem.scale χ.finiteUniformizerValue P.spectralSystem).SameEulerPolynomials
      (P.determinantTwist χ hχ).spectralSystem :=
  P.unramified.sameEulerPolynomials_determinantTwist χ hχ

/-- Comparison with any supplied commonly scaled numerical system reflects to
the original presentation, even in a different rank. -/
theorem determinantTwist_samePowerTraces_scale_iff {m : ℕ}
    (t : SpectralSystem (FinitePlace F) m) :
    (P.determinantTwist χ hχ).spectralSystem.SamePowerTraces
        (SpectralSystem.scale χ.finiteUniformizerValue t) ↔
      P.spectralSystem.SamePowerTraces t :=
  P.unramified.determinantTwist_samePowerTraces_scale_iff χ hχ t

theorem determinantTwist_sameEulerPolynomials_scale_iff {m : ℕ}
    (t : SpectralSystem (FinitePlace F) m) :
    (P.determinantTwist χ hχ).spectralSystem.SameEulerPolynomials
        (SpectralSystem.scale χ.finiteUniformizerValue t) ↔
      P.spectralSystem.SameEulerPolynomials t :=
  P.unramified.determinantTwist_sameEulerPolynomials_scale_iff χ hχ t

/-- Two actual full presentation twists preserve and reflect the existing
comparison; each presentation retains its own finite exceptions and rank. -/
theorem determinantTwist_samePowerTraces_iff {q : ℕ}
    {T : CuspidalOperatorRealization F q}
    (Q : CuspidalSpectralPresentation.{uF, uW} T) :
    (P.determinantTwist χ hχ).spectralSystem.SamePowerTraces
        (Q.determinantTwist χ hχ).spectralSystem ↔
      P.spectralSystem.SamePowerTraces Q.spectralSystem := by
  have hQ := Q.samePowerTraces_determinantTwist χ hχ
  constructor
  · intro h
    exact (P.determinantTwist_samePowerTraces_scale_iff χ hχ Q.spectralSystem).mp
      (h.trans hQ.symm)
  · intro h
    exact ((P.determinantTwist_samePowerTraces_scale_iff χ hχ Q.spectralSystem).mpr h).trans hQ

theorem determinantTwist_sameEulerPolynomials_iff {q : ℕ}
    {T : CuspidalOperatorRealization F q}
    (Q : CuspidalSpectralPresentation.{uF, uW} T) :
    (P.determinantTwist χ hχ).spectralSystem.SameEulerPolynomials
        (Q.determinantTwist χ hχ).spectralSystem ↔
      P.spectralSystem.SameEulerPolynomials Q.spectralSystem := by
  have hQ := Q.sameEulerPolynomials_determinantTwist χ hχ
  constructor
  · intro h
    exact (P.determinantTwist_sameEulerPolynomials_scale_iff χ hχ Q.spectralSystem).mp
      (h.trans hQ.symm)
  · intro h
    exact ((P.determinantTwist_sameEulerPolynomials_scale_iff χ hχ Q.spectralSystem).mpr h).trans hQ

end CuspidalSpectralPresentation

namespace CuspidalOperatorRealization.IsoClass

variable {r : ℕ}

/-- An existing actual spectral attachment transports to the actual full class twist. -/
theorem HasSpectralSystem.determinantTwist
    {c : CuspidalOperatorRealization.IsoClass F r}
    {s : SpectralSystem (FinitePlace F) (r + 1)}
    (hs : HasSpectralSystem.{uF, uV} c s) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    HasSpectralSystem.{uF, uV} (c.determinantTwist χ hχ)
      ((SpectralSystem.scale χ.finiteUniformizerValue s).restrict
        (s.exceptional ∪ χ.finiteDeterminantTail (r + 1) hχ) Finset.subset_union_left) := by
  rcases hs with ⟨S, P, rfl, rfl⟩
  exact ⟨S.determinantTwist χ hχ, P.determinantTwist χ hχ, rfl, rfl⟩

end CuspidalOperatorRealization.IsoClass

namespace PositiveRankCuspidalClass

/-- Mixed positive ranks retain their rank and the genuine transported attachment. -/
theorem HasSpectralSystem.determinantTwist {c : PositiveRankCuspidalClass F}
    {s : SpectralSystem (FinitePlace F) c.rank}
    (hs : HasSpectralSystem.{uF, uV} c s) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    HasSpectralSystem.{uF, uV} (c.determinantTwist χ hχ)
      ((SpectralSystem.scale χ.finiteUniformizerValue s).restrict
        (s.exceptional ∪ χ.finiteDeterminantTail c.rank hχ) Finset.subset_union_left) :=
  CuspidalOperatorRealization.IsoClass.HasSpectralSystem.determinantTwist hs χ hχ

end PositiveRankCuspidalClass
end Langlands.Automorphic
