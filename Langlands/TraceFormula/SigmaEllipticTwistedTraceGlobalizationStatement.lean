import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.BaseChange.EllipticOrbitalIntegral
import Langlands.BaseChange.PseudoCoefficient
import Langlands.BaseChange.TwistedCharacter
import Langlands.Global.AdelicFunctoriality.Norm
import Langlands.Global.CompletionPadic
import Langlands.Group.GL.LocalFieldTopology
import Langlands.HarmonicAnalysis.Basic
import Langlands.TraceFormula.CyclicFieldGlobalizationStatement

/-!
# A σ-stable cusp with nonzero twisted trace at a σ-elliptic test function

Statement only (no proof). Let `E/F` be a cyclic extension of number fields of any degree `l`
with generator `σ`, split at every infinite place. Let `v` be a finite place of `F` with exactly
one place `w` of `E` above it, and let `v₁, v₂, v₃` be three distinct finite places of `F`,
different from `v`, that split completely in `E`. Give `F_v ⊗_F E` its module topology over
`F_v`, let `σv = id ⊗ σ`, and let `n = r + 1`.

Let `χ` be a unitary character of the centre of `GL_n(F_v ⊗_F E)`, `μ` a Haar measure on
`GL_n(F_v ⊗_F E)` and `φ` a Schwartz–Bruhat function on `GL_n(F_v ⊗_F E)` whose σv-orbital
integrals vanish at every σv-regular element that is not σv-elliptic. Suppose that some
irreducible admissible representation `τ` of `GL_n(F_v ⊗_F E)` with central character `χ` and
an isomorphism `A : τ ≅ τ^{σv}` have `tr (τ(φ) ∘ A) ≠ 0`. Then there are a cuspidal operator
realization `T` of `GL_n` over `E` and a spectral presentation `P` of `T` such that `T` has
unitary central character and `σ`-stable class, the local components of `P` above `v₁` and
`v₂` are supercuspidal, the local component `Π_w` at `w` is irreducible and admissible, and
`Π_w`, viewed on `GL_n(F_v ⊗_F E)` through the `w`-component of `finiteTensorMap v`, has central
character `χ` and a nonzero twisted trace `tr (Π_w(φ) ∘ A')` for some `A' : Π_w ≅ Π_w^{σv}`.

This is the global trace-formula step of the twisted globalization of Henniart–Lemaire 2011,
II.6.16, and Arthur–Clozel 1989, Chapter 1, §6.3(b), following the proof of Lemma 2.5 there.
It is derived content: the statement is formulated for this Library from the argument of these
sources. See the paired Markdown.
-/

noncomputable section

universe uF uE uR uW

open NumberField IsDedekindDomain MeasureTheory
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic Langlands.BaseChange Langlands.HarmonicAnalysis
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.TraceFormula

local instance sigmaEllipticGlobalizationRationalAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance sigmaEllipticGlobalizationContinuousAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance sigmaEllipticGlobalizationSmoothAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance sigmaEllipticGlobalizationFormsAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance sigmaEllipticGlobalizationLocalSpaceAddCommGroup {F : Type*} [Field F]
    [NumberField F] {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- **A σ-stable cusp with nonzero twisted trace at a σ-elliptic test function.** Let `E/F` be
a cyclic extension of number fields of degree `l` with generator `σ` (`IsCyclicAlgebra σ l`),
both adele quotients being compact, such that every infinite place `u` of `F` splits completely
in `E` with `σ` acting as the cyclic shift. Let `v` be a finite place of `F` with exactly one
place `w` of `E` above it, and `v₁, v₂, v₃` pairwise distinct finite places of `F`, all
different from `v`, with `IsCyclicShiftSplit F E (vᵢ.adicCompletion F) σ l`. Give
`F_v ⊗_F E` its module topology over `F_v` and let `σv = id ⊗ σ`.

Let `χ` be a character of the centre of `GL_{r+1}(F_v ⊗_F E)` of absolute value `1`, `μ` a Haar
measure on `GL_{r+1}(F_v ⊗_F E)` (Borel σ-algebra) and `φ` a Schwartz–Bruhat function whose
σv-orbital integrals vanish at every σv-regular element that is not σv-elliptic
(`SigmaOrbitalIntegralsVanishOffElliptic σv l μ ⇑φ`). Suppose that an irreducible admissible
representation `τ` of `GL_{r+1}(F_v ⊗_F E)` on a complex vector space in `Type uR`, with central
character `χ`, and an isomorphism `A` of `τ` onto `τ^{σv}` have `tr (τ(φ) ∘ A) ≠ 0`.

Then there are a cuspidal operator realization `T` of `GL_{r+1}` over `E` and a spectral
presentation `P` of `T` (local spaces in the free universe `uW`) such that

* `T` has unitary central character and its class is `σ`-stable,
* the local components of `P` at all places above `v₁` and above `v₂` are supercuspidal,
* the local component `Π_w` of `P` at `w` is irreducible and admissible,
* `Π_w`, viewed as a representation of `GL_{r+1}(F_v ⊗_F E)` through the `w`-component
  `F_v ⊗_F E → E_w` of `finiteTensorMap v`, has central character `χ`, and for some
  isomorphism `A'` of it onto its `σv`-conjugate, `tr (Π_w(φ) ∘ A') ≠ 0`. -/
def SigmaEllipticTwistedTraceGlobalizationStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    (∀ u : NumberField.InfinitePlace F, IsCyclicShiftSplit F E u.Completion σ l) →
    ∀ (v : Langlands.Global.FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w' : FinitePlacesAbove E v, w' = w) →
    ∀ (v₁ v₂ v₃ : Langlands.Global.FinitePlace F), v₁ ≠ v₂ → v₁ ≠ v₃ → v₂ ≠ v₃ →
      v₁ ≠ v → v₂ ≠ v → v₃ ≠ v →
      IsCyclicShiftSplit F E (v₁.adicCompletion F) σ l →
      IsCyclicShiftSplit F E (v₂.adicCompletion F) σ l →
      IsCyclicShiftSplit F E (v₃.adicCompletion F) σ l →
    ∀ (r : ℕ),
      letI : ValuativeRel (v.adicCompletion F) :=
        (CompletionPadic.topologicalData v).valuativeRel
      haveI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
        (CompletionPadic.topologicalData v).localField
      letI : TopologicalSpace (v.adicCompletion F ⊗[F] E) :=
        moduleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)
      haveI : IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := ⟨rfl⟩
      haveI : IsTopologicalRing (v.adicCompletion F ⊗[F] E) :=
        IsModuleTopology.isTopologicalRing (v.adicCompletion F) _
      haveI := generalLinear_t2Space_of_finite (v.adicCompletion F)
        (v.adicCompletion F ⊗[F] E) (r + 1)
      haveI := generalLinear_locallyCompactSpace_of_finite (v.adicCompletion F)
        (v.adicCompletion F ⊗[F] E) (r + 1)
      haveI := generalLinear_totallyDisconnectedSpace_of_finite (v.adicCompletion F)
        (v.adicCompletion F ⊗[F] E) (r + 1)
      letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) := borel _
      haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) := ⟨rfl⟩
      let σv : (v.adicCompletion F ⊗[F] E) ≃ₐ[v.adicCompletion F]
          (v.adicCompletion F ⊗[F] E) :=
        Algebra.TensorProduct.congr AlgEquiv.refl σ
    ∀ (χ : Subgroup.center (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) →* ℂˣ),
      (∀ z, ‖(χ z : ℂ)‖ = 1) →
    ∀ (μ : Measure (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E))) [μ.IsHaarMeasure]
      (φ : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E))),
      SigmaOrbitalIntegralsVanishOffElliptic σv l μ ⇑φ →
    ∀ (W : Type uR) [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) W)
      (hτ : IsAdmissible τ), τ.IsIrreducible → HasCentralCharacterRep τ χ →
      ∀ A : SigmaIntertwiner σv (r + 1) τ, twistedDistribution μ τ hτ A.toLinearMap φ ≠ 0 →
    ∃ (T : CuspidalOperatorRealization E r) (P : CuspidalSpectralPresentation.{uE, uW} T),
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T ∧
      T.isoClass.IsGaloisStable σ ∧
      (∀ w₁ : FinitePlacesAbove E v₁, (P.localComponent w₁.1).IsSupercuspidal) ∧
      (∀ w₂ : FinitePlacesAbove E v₂, (P.localComponent w₂.1).IsSupercuspidal) ∧
      (P.localComponent w.1).IsIrreducible ∧ (P.localComponent w.1).IsAdmissible ∧
      let PiV : Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E))
          (P.localComponent w.1).Space :=
        (P.localComponent w.1).representation.comp
          (Matrix.GeneralLinearGroup.map
            ((Pi.evalRingHom (fun q : FinitePlacesAbove E v => q.1.adicCompletion E) w).comp
              (finiteTensorMap v).toRingHom))
      HasCentralCharacterRep PiV χ ∧
      ∃ (hP : IsAdmissible PiV) (A' : SigmaIntertwiner σv (r + 1) PiV),
        twistedDistribution μ PiV hP A'.toLinearMap φ ≠ 0

end Langlands.TraceFormula
