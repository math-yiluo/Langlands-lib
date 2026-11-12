import Langlands.Automorphic.CuspidalSpectralDeterminantTwist
import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.HeckeTwist.FiniteSlice
import Langlands.Automorphic.HeckeTwist.PresentedUnramifiedData
import Langlands.Representation.Category.Twist

/-! # Twists of cuspidal spectral presentations by any Hecke determinant character

A cuspidal spectral presentation of a cuspidal operator realization `S` yields one of the
twist `S.heckeDeterminantTwist χ` for an arbitrary Hecke character `χ`: the finite slice,
local factors, tensor presentation and unramified data are twisted, and the exceptional set
is enlarged by the full integral tail of `Langlands.Automorphic.HeckeTwist.FiniteTail`. This
is the finite-order-free version of the presentation part of
`Langlands.Automorphic.CuspidalSpectralDeterminantTwist`; the isomorphism-class statements
there are not ported.
-/

noncomputable section
open scoped Classical
universe uF uV uW

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance heckeSpectralTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeSpectralTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeSpectralTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeSpectralTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

namespace CuspidalSpectralPresentation

variable {r : ℕ} {S : CuspidalOperatorRealization F r}
variable (P : CuspidalSpectralPresentation.{uF, uV} S)
variable (χ : HeckeCharacter F)

/-- Bundle the genuine local character twist on the original factor carrier. -/
def heckeDeterminantTwistLocalFactor (v : FinitePlace F) :
    Langlands.SmoothRep.{0, uF, uV} ℂ (FiniteLocalGL F (r + 1) v) :=
  (P.localFactor v).twist (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom
    (χ.finiteLocalHeckeDeterminant_isOpen_ker (r + 1) v)

@[simp]
theorem heckeDeterminantTwistLocalFactor_representation (v : FinitePlace F) :
    (P.heckeDeterminantTwistLocalFactor χ v).representation =
      Langlands.twist (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom
        (P.localFactor v).representation := rfl

/-- Actual finite-slice, tensor and supplied spectral data for the full cuspidal twist. -/
def heckeDeterminantTwist : CuspidalSpectralPresentation.{uF, uV} (S.heckeDeterminantTwist χ) where
  finiteSlice := P.finiteSlice.heckeDeterminantTwist χ
  localFactor := P.heckeDeterminantTwistLocalFactor χ
  tensorExceptional := FiniteTensorPresentation.heckeDeterminantTwistExceptional
    (E := P.tensorExceptional) (n := r + 1) χ
  reference := P.reference
  reference_fixed :=
    FiniteTensorPresentation.heckeDeterminantTwistReference_fixed (he := P.reference_fixed) χ
  presentation := P.presentation.heckeDeterminantTwist χ
  exceptional := P.exceptional ∪ χ.finiteHeckeDeterminantTail (r + 1)
  unramified := P.unramified.heckeDeterminantTwist χ

@[simp]
theorem heckeDeterminantTwist_finiteSlice :
    (P.heckeDeterminantTwist χ).finiteSlice = P.finiteSlice.heckeDeterminantTwist χ := rfl

@[simp]
theorem heckeDeterminantTwist_tensorExceptional :
    (P.heckeDeterminantTwist χ).tensorExceptional =
      P.tensorExceptional ∪ χ.finiteHeckeDeterminantTail (r + 1) := rfl

@[simp]
theorem heckeDeterminantTwist_exceptional :
    (P.heckeDeterminantTwist χ).exceptional =
      P.exceptional ∪ χ.finiteHeckeDeterminantTail (r + 1) := rfl

/-- The actual new numerical system is precisely the scaled, restricted old system. -/
@[simp]
theorem heckeDeterminantTwist_spectralSystem :
    (P.heckeDeterminantTwist χ).spectralSystem =
      (SpectralSystem.scale χ.finiteUniformizerValue P.spectralSystem).restrict
        (P.exceptional ∪ χ.finiteHeckeDeterminantTail (r + 1))
        Finset.subset_union_left := rfl

/-- The new presentation's component and the actual multiplied old component
are genuinely equivalent; their auxiliary complementary vectors may differ. -/
def heckeDeterminantTwistLocalComponentEquiv (v : FinitePlace F) :
    ((P.heckeDeterminantTwist χ).localComponent v).representation.Equiv
      ((P.localComponent v).heckeDeterminantTwist χ).representation :=
  ((P.heckeDeterminantTwist χ).presentation.localComponentEquiv
    (P.heckeDeterminantTwist χ).finiteSlice.nonzero v).symm.trans
      ((Langlands.twistEquiv (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom
        (P.presentation.localComponentEquiv P.finiteSlice.nonzero v)).trans
          ((P.localComponent v).heckeDeterminantTwistRepresentationEquiv χ))

theorem heckeDeterminantTwist_localComponent_isoClass (v : FinitePlace F) :
    ((P.heckeDeterminantTwist χ).localComponent v).isoClass =
      ((P.localComponent v).heckeDeterminantTwist χ).isoClass :=
  (LocalRealization.isoClass_eq_iff _ _).mpr
    ⟨P.heckeDeterminantTwistLocalComponentEquiv χ v⟩

theorem heckeDeterminantTwist_powerTrace (v : FinitePlace F)
    (hv : v ∉ P.exceptional ∪ χ.finiteHeckeDeterminantTail (r + 1)) (k : ℕ) :
    (P.heckeDeterminantTwist χ).spectralSystem.powerTrace v hv k =
      (χ.finiteUniformizerValue v : ℂ) ^ k *
        P.spectralSystem.powerTrace v (fun h => hv (Finset.mem_union_left _ h)) k :=
  P.unramified.heckeDeterminantTwist_powerTrace χ v hv k

theorem heckeDeterminantTwist_eulerPolynomial (v : FinitePlace F)
    (hv : v ∉ P.exceptional ∪ χ.finiteHeckeDeterminantTail (r + 1)) :
    (P.heckeDeterminantTwist χ).spectralSystem.eulerPolynomial v hv =
      (P.spectralSystem.eulerPolynomial v
        (fun h => hv (Finset.mem_union_left _ h))).comp
          (Polynomial.C (χ.finiteUniformizerValue v : ℂ) * Polynomial.X) :=
  P.unramified.heckeDeterminantTwist_eulerPolynomial χ v hv

theorem samePowerTraces_heckeDeterminantTwist :
    (SpectralSystem.scale χ.finiteUniformizerValue P.spectralSystem).SamePowerTraces
      (P.heckeDeterminantTwist χ).spectralSystem :=
  P.unramified.samePowerTraces_heckeDeterminantTwist χ

theorem sameEulerPolynomials_heckeDeterminantTwist :
    (SpectralSystem.scale χ.finiteUniformizerValue P.spectralSystem).SameEulerPolynomials
      (P.heckeDeterminantTwist χ).spectralSystem :=
  P.unramified.sameEulerPolynomials_heckeDeterminantTwist χ

/-- Comparison with any supplied commonly scaled numerical system reflects to
the original presentation, even in a different rank. -/
theorem heckeDeterminantTwist_samePowerTraces_scale_iff {m : ℕ}
    (t : SpectralSystem (FinitePlace F) m) :
    (P.heckeDeterminantTwist χ).spectralSystem.SamePowerTraces
        (SpectralSystem.scale χ.finiteUniformizerValue t) ↔
      P.spectralSystem.SamePowerTraces t :=
  P.unramified.heckeDeterminantTwist_samePowerTraces_scale_iff χ t

theorem heckeDeterminantTwist_sameEulerPolynomials_scale_iff {m : ℕ}
    (t : SpectralSystem (FinitePlace F) m) :
    (P.heckeDeterminantTwist χ).spectralSystem.SameEulerPolynomials
        (SpectralSystem.scale χ.finiteUniformizerValue t) ↔
      P.spectralSystem.SameEulerPolynomials t :=
  P.unramified.heckeDeterminantTwist_sameEulerPolynomials_scale_iff χ t

/-- Two actual full presentation twists preserve and reflect the existing
comparison; each presentation retains its own finite exceptions and rank. -/
theorem heckeDeterminantTwist_samePowerTraces_iff {q : ℕ}
    {T : CuspidalOperatorRealization F q}
    (Q : CuspidalSpectralPresentation.{uF, uW} T) :
    (P.heckeDeterminantTwist χ).spectralSystem.SamePowerTraces
        (Q.heckeDeterminantTwist χ).spectralSystem ↔
      P.spectralSystem.SamePowerTraces Q.spectralSystem := by
  have hQ := Q.samePowerTraces_heckeDeterminantTwist χ
  constructor
  · intro h
    exact (P.heckeDeterminantTwist_samePowerTraces_scale_iff χ Q.spectralSystem).mp
      (h.trans hQ.symm)
  · intro h
    exact ((P.heckeDeterminantTwist_samePowerTraces_scale_iff χ Q.spectralSystem).mpr h).trans hQ

theorem heckeDeterminantTwist_sameEulerPolynomials_iff {q : ℕ}
    {T : CuspidalOperatorRealization F q}
    (Q : CuspidalSpectralPresentation.{uF, uW} T) :
    (P.heckeDeterminantTwist χ).spectralSystem.SameEulerPolynomials
        (Q.heckeDeterminantTwist χ).spectralSystem ↔
      P.spectralSystem.SameEulerPolynomials Q.spectralSystem := by
  have hQ := Q.sameEulerPolynomials_heckeDeterminantTwist χ
  constructor
  · intro h
    exact (P.heckeDeterminantTwist_sameEulerPolynomials_scale_iff χ Q.spectralSystem).mp
      (h.trans hQ.symm)
  · intro h
    exact ((P.heckeDeterminantTwist_sameEulerPolynomials_scale_iff χ Q.spectralSystem).mpr h).trans
      hQ

end CuspidalSpectralPresentation

end Langlands.Automorphic
