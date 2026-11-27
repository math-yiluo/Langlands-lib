import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.Unramified.WeakTransfer
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.BaseChange.TwistedCharacter
import Langlands.BaseChange.OrbitalIntegral
import Langlands.Global.AdelicFunctoriality.Norm
import Langlands.Global.CompletionPadic
import Langlands.Group.GL.LocalFieldTopology
import Langlands.TraceFormula.CyclicFieldGlobalizationStatement
import Mathlib.RingTheory.Norm.Basic

/-!
# Weak descent of a stable cusp with a trace identity at a place with one place above

Statement only (no proof). Let `E/F` be a cyclic extension of number fields of any degree `l`
with generator `σ`, split at every infinite place. Let `v` be a finite place of `F` with exactly
one place `w` of `E` above it, and let `v₁ ≠ v₂` be finite places of `F` that split completely
in `E`. Let `T` be a cuspidal operator realization of `GL_{r+1}` over `E` with unitary central
character whose class is `σ`-stable, and `P` a spectral presentation of `T` whose local
components above `v₁` and above `v₂` are supercuspidal and whose local component `Π_w` at `w`
is irreducible and admissible. Then there are a cuspidal operator realization `S` of
`GL_{r+1}` over `F` with unitary central character, whose class has the class of `T` as weak
base change, and a spectral presentation `D` of `S` whose local component `π_v` at `v` is
irreducible and admissible, together with a σ-intertwiner `A` of `Π_w` (viewed on
`GL_{r+1}(F_v ⊗_F E)`) and `c ≠ 0`, such that `tr (Π_w(φ) ∘ A) = c · tr π_v(f)` for all
concordant test functions `φ` supported in the σ-regular set and `f` supported in the regular
semisimple set with determinants in the norm group `N((F_v ⊗_F E)ˣ)`.

This is the comparison step of the global proof of descent for σ-discrete series
(Henniart–Lemaire 2011, II.6.16–II.6.17; Arthur–Clozel 1989, Chapter 1, §6.3), the descent
stated in the Library as `Langlands.BaseChange.SigmaDiscreteRegularDescentStatement`. The
identity at `v` is written out; it is the body of `Langlands.BaseChange.IsRegularSigmaLift`
for `π_v`, `Π_w`, `A` and `c`, and this module does not import that definition.

Sources: Arthur–Clozel 1989, Chapter 1, Lemmas 2.4–2.5 (printed pp. 13–15) and §6.3 (printed
pp. 54–57; "on the image of the norm" on p. 57); Henniart–Lemaire 2011, II.6.12–II.6.17
(printed pp. 128–132). See the paired Markdown.
-/

noncomputable section

universe uF uE uV uW

open NumberField IsDedekindDomain MeasureTheory
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic Langlands.BaseChange Langlands.HarmonicAnalysis
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.TraceFormula

local instance stableDescentTraceRationalAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance stableDescentTraceContinuousAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance stableDescentTraceSmoothAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance stableDescentTraceFormsAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance stableDescentTraceLocalSpaceAddCommGroup {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- **Weak descent of a stable cusp with a trace identity at `v`.** Let `E/F` be a cyclic
extension of number fields of degree `l` with generator `σ` (`IsCyclicAlgebra σ l`; `l` need
not be prime), both adele quotients being compact, such that every infinite place `u` of `F`
splits completely in `E` with `σ` acting as the cyclic shift
(`IsCyclicShiftSplit F E u.Completion σ l`). Let `v` be a finite place of `F` with exactly one
place `w` of `E` above it, and `v₁ ≠ v₂` finite places of `F` with
`IsCyclicShiftSplit F E (vᵢ.adicCompletion F) σ l`. Let `T` be a cuspidal operator realization
of `GL_{r+1}` over `E` with unitary central character and `σ`-stable class, and `P` a spectral
presentation of `T` whose local components at all places above `v₁` and above `v₂` are
supercuspidal and whose local component at `w` is irreducible and admissible.

Then there are a cuspidal operator realization `S` of `GL_{r+1}` over `F` with unitary central
character, such that the class of `T` is a weak base change of the class of `S`, and a
spectral presentation `D` of `S` whose local component `π_v` at `v` is irreducible and
admissible, with the following property. Give `F_v ⊗_F E` its module topology over `F_v`, both
`GL_{r+1}(F_v)` and `GL_{r+1}(F_v ⊗_F E)` their Borel σ-algebras, let `σv = id ⊗ σ`, and let
`Π_w` be the local component of `P` at `w` viewed as a representation of
`GL_{r+1}(F_v ⊗_F E)` through the `w`-component `F_v ⊗_F E → E_w` of the Library's
`finiteTensorMap v`. Then `π_v` and `Π_w` are admissible, and there are a σv-intertwiner `A`
of `Π_w` and `c ≠ 0` such that for all Haar measures `μF` on `GL_{r+1}(F_v)` and `μE` on
`GL_{r+1}(F_v ⊗_F E)` and all Schwartz–Bruhat functions `φ` on `GL_{r+1}(F_v ⊗_F E)` and `f` on
`GL_{r+1}(F_v)` with

* `φ` and `f` concordant for `μF` and `μE`,
* `φ` supported in the σv-regular set,
* `f` supported in the regular semisimple set,
* `det g` a norm from `(F_v ⊗_F E)ˣ` whenever `f g ≠ 0`,

the twisted trace `tr (Π_w(φ) ∘ A)` for `μE` equals `c` times the trace `tr π_v(f)` for `μF`. -/
def CyclicStableCuspidalDescentTraceIdentityStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    (∀ u : NumberField.InfinitePlace F, IsCyclicShiftSplit F E u.Completion σ l) →
    ∀ (v : Langlands.Global.FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w' : FinitePlacesAbove E v, w' = w) →
    ∀ (v₁ v₂ : Langlands.Global.FinitePlace F), v₁ ≠ v₂ →
      IsCyclicShiftSplit F E (v₁.adicCompletion F) σ l →
      IsCyclicShiftSplit F E (v₂.adicCompletion F) σ l →
    ∀ (r : ℕ) (T : CuspidalOperatorRealization E r)
      (P : CuspidalSpectralPresentation.{uE, uW} T),
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      T.isoClass.IsGaloisStable σ →
      (∀ w₁ : FinitePlacesAbove E v₁, (P.localComponent w₁.1).IsSupercuspidal) →
      (∀ w₂ : FinitePlacesAbove E v₂, (P.localComponent w₂.1).IsSupercuspidal) →
      (P.localComponent w.1).IsIrreducible → (P.localComponent w.1).IsAdmissible →
    ∃ (S : CuspidalOperatorRealization F r) (D : CuspidalSpectralPresentation.{uF, uV} S),
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S ∧
      CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW}
        T.isoClass S.isoClass ∧
      (D.localComponent v).IsIrreducible ∧ (D.localComponent v).IsAdmissible ∧
      letI : ValuativeRel (v.adicCompletion F) :=
        (CompletionPadic.topologicalData v).valuativeRel
      haveI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
        (CompletionPadic.topologicalData v).localField
      letI : TopologicalSpace (v.adicCompletion F ⊗[F] E) :=
        moduleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)
      haveI : IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := ⟨rfl⟩
      haveI : IsTopologicalRing (v.adicCompletion F ⊗[F] E) :=
        IsModuleTopology.isTopologicalRing (v.adicCompletion F) _
      haveI := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion F) (r + 1)
      haveI := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion F) (r + 1)
      haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace
        (v.adicCompletion F) (r + 1)
      haveI := generalLinear_t2Space_of_finite (v.adicCompletion F)
        (v.adicCompletion F ⊗[F] E) (r + 1)
      haveI := generalLinear_locallyCompactSpace_of_finite (v.adicCompletion F)
        (v.adicCompletion F ⊗[F] E) (r + 1)
      haveI := generalLinear_totallyDisconnectedSpace_of_finite (v.adicCompletion F)
        (v.adicCompletion F ⊗[F] E) (r + 1)
      let σv : (v.adicCompletion F ⊗[F] E) ≃ₐ[v.adicCompletion F]
          (v.adicCompletion F ⊗[F] E) :=
        Algebra.TensorProduct.congr AlgEquiv.refl σ
      let PiV : Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E))
          (P.localComponent w.1).Space :=
        (P.localComponent w.1).representation.comp
          (Matrix.GeneralLinearGroup.map
            ((Pi.evalRingHom (fun q : FinitePlacesAbove E v => q.1.adicCompletion E) w).comp
              (finiteTensorMap v).toRingHom))
      ∃ (hπ : Langlands.IsAdmissible (D.localComponent v).representation)
        (hP : Langlands.IsAdmissible PiV) (A : SigmaIntertwiner σv (r + 1) PiV) (c : ℂ),
        c ≠ 0 ∧
          letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion F)) := borel _
          haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion F)) := ⟨rfl⟩
          letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) :=
            borel _
          haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) := ⟨rfl⟩
          ∀ (μF : Measure (GeneralLinear (r + 1) (v.adicCompletion F))) [μF.IsHaarMeasure]
            (μE : Measure (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)))
            [μE.IsHaarMeasure]
            (φ : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)))
            (f : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion F))),
            AreConcordant σv l μF μE φ f →
            IsSigmaRegularSupported σv l
              (φ : GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E) → ℂ) →
            IsRegularSupported (f : GeneralLinear (r + 1) (v.adicCompletion F) → ℂ) →
            (∀ g : GeneralLinear (r + 1) (v.adicCompletion F), f g ≠ 0 →
              GeneralLinear.determinant g ∈
                (Units.map (Algebra.norm (v.adicCompletion F) :
                  (v.adicCompletion F ⊗[F] E) →* v.adicCompletion F)).range) →
              twistedDistribution μE PiV hP A.toLinearMap φ =
                c * Character.distribution μF (D.localComponent v).representation hπ f

end Langlands.TraceFormula
