import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.Unramified.WeakTransfer
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.BaseChange.TwistedCharacter
import Langlands.BaseChange.EllipticSupport
import Langlands.BaseChange.OrbitalIntegral
import Langlands.Global.AdelicFunctoriality.Norm
import Langlands.Global.CompletionPadic
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.Norm.Basic

/-!
# The elliptic twisted trace identity at a non-split place for a cuspidal weak base change

Statement only (no proof). Let `E/F` be a cyclic extension of number fields of prime degree `l`
with generator `σ`, unramified at the infinite places. Let `S` be a cuspidal operator realization
of `GL_{r+1}` over `F` with unitary central character and `T` one over `E` whose class is a weak
base change of the class of `S`. Let `v ≠ v'` be finite places of `F` with exactly one place `w`,
respectively `w'`, of `E` above them, and let `P` be a spectral presentation of `T` whose local
components at `w` and `w'` are supercuspidal. Then, for every spectral presentation `D` of `S`
whose local component `π_v` at `v` is irreducible and admissible, the local component `Π_w` of `P`,
viewed as a representation of `GL_{r+1}(F_v ⊗_F E)`, has a σ-intertwiner `A` and there is a
constant `c ≠ 0` with `tr (Π_w(φ) ∘ A) = c · tr π_v(f)` for all concordant test functions `φ`
supported in the σ-elliptic set and `f` supported in the regular elliptic set with determinants
in the norm group `N((F_v ⊗_F E)ˣ)`. The constant `c` does not depend on the Haar measures or on
the test functions.

Identities of this form at a non-split place come from the comparison of the trace formula of
`GL_n` over `F` with the twisted trace formula over `E`. With local results the identity shows
that supercuspidality descends along a cuspidal weak base change
(`Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeSupercuspidalStatement`).

Sources: Arthur–Clozel 1989, Chapter 3, Theorem 5.1 and its proof (printed p. 212: the local
identity at every place for a cuspidal weak base change); Chapter 1, §6.3 (printed pp. 54–57;
the identity at `v₃` on printed p. 57); Henniart–Lemaire 2011, II.6.3–II.6.13 (printed
pp. 119–130; the identity at `v₀` in II.6.13). See the paired Markdown.
-/

noncomputable section

universe uF uE uV uW

open NumberField IsDedekindDomain MeasureTheory
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic Langlands.BaseChange Langlands.HarmonicAnalysis
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.TraceFormula

local instance ellipticTraceIdentityRationalAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance ellipticTraceIdentityContinuousAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance ellipticTraceIdentitySmoothAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance ellipticTraceIdentityFormsAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance ellipticTraceIdentityLocalSpaceAddCommGroup {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- **The elliptic twisted trace identity at a non-split place.** Let `E/F` be a cyclic
extension of number fields of prime degree `l` with generator `σ` (`IsCyclicAlgebra σ l`),
unramified at the infinite places, both adele quotients being compact. Let `v ≠ v'` be finite
places of `F` with exactly one place `w`, respectively `w'`, of `E` above them. Let `S` be a
cuspidal operator realization of `GL_{r+1}` over `F` with unitary central character, `T` one over
`E` whose class is a weak base change of that of `S`, and `P` a spectral presentation of `T`
whose local components at `w` and `w'` are supercuspidal. Let `D` be a spectral presentation of
`S` whose local component `π_v` at `v` is irreducible and admissible.

Give `F_v ⊗_F E` its module topology over `F_v`, both `GL_{r+1}(F_v)` and
`GL_{r+1}(F_v ⊗_F E)` their Borel σ-algebras, let `σv = id ⊗ σ`, and let `Π_w` be the local
component of `P` at `w` viewed as a representation of `GL_{r+1}(F_v ⊗_F E)` through the
`w`-component `F_v ⊗_F E → E_w` of the Library's `finiteTensorMap v`. Then `π_v` and `Π_w` are
admissible, and there are a σv-intertwiner `A` of `Π_w` and `c ≠ 0` such that for all Haar
measures `μF` on `GL_{r+1}(F_v)` and `μE` on `GL_{r+1}(F_v ⊗_F E)` and all Schwartz–Bruhat
functions `φ` on `GL_{r+1}(F_v ⊗_F E)` and `f` on `GL_{r+1}(F_v)` with

* `φ` supported in the σv-elliptic set,
* `f` supported in the regular elliptic set,
* `det g` a norm from `(F_v ⊗_F E)ˣ` whenever `f g ≠ 0`,
* `φ` and `f` concordant for `μF` and `μE`,

the twisted trace `tr (Π_w(φ) ∘ A)` for `μE` equals `c` times the trace `tr π_v(f)` for `μF`. -/
def CyclicBaseChangeEllipticTraceIdentityStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsUnramifiedAtInfinitePlaces F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E) (l : ℕ), l.Prime → IsCyclicAlgebra σ l →
    ∀ (v : Langlands.Global.FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w'' : FinitePlacesAbove E v, w'' = w) →
    ∀ (v' : Langlands.Global.FinitePlace F) (w' : FinitePlacesAbove E v'),
      v' ≠ v → (∀ w'' : FinitePlacesAbove E v', w'' = w') →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r) (T : CuspidalOperatorRealization E r)
      (P : CuspidalSpectralPresentation.{uE, uW} T),
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      (P.localComponent w.1).IsSupercuspidal →
      (P.localComponent w'.1).IsSupercuspidal →
      CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW}
        T.isoClass S.isoClass →
    ∀ D : CuspidalSpectralPresentation.{uF, uV} S,
      (D.localComponent v).IsIrreducible → (D.localComponent v).IsAdmissible →
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
    let σv : (v.adicCompletion F ⊗[F] E) ≃ₐ[v.adicCompletion F] (v.adicCompletion F ⊗[F] E) :=
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
        letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) := borel _
        haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) := ⟨rfl⟩
        ∀ (μF : Measure (GeneralLinear (r + 1) (v.adicCompletion F))) [μF.IsHaarMeasure]
          (μE : Measure (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E))) [μE.IsHaarMeasure]
          (φ : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)))
          (f : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion F))),
          IsSigmaEllipticSupported σv l
            (φ : GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E) → ℂ) →
          IsEllipticSupported (f : GeneralLinear (r + 1) (v.adicCompletion F) → ℂ) →
          (∀ g : GeneralLinear (r + 1) (v.adicCompletion F), f g ≠ 0 →
            GeneralLinear.determinant g ∈
              (Units.map (Algebra.norm (v.adicCompletion F) :
                (v.adicCompletion F ⊗[F] E) →* v.adicCompletion F)).range) →
          AreConcordant σv l μF μE φ f →
            twistedDistribution μE PiV hP A.toLinearMap φ =
              c * Character.distribution μF (D.localComponent v).representation hπ f

end Langlands.TraceFormula
