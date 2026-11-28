import Langlands.TraceFormula.CuspidalCyclicBaseChangeLiftStatement
import Langlands.BaseChange.SigmaDiscreteRegularDescentStatement

/-!
# The spectral comparison for the cuspidal cyclic lift

Statement only (no proof). Keep the hypotheses of
`Langlands.TraceFormula.CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement`: a cyclic
extension `L/K` of number fields of degree `l` with generator `σ`, split at every infinite
place with cyclic shift action and with compact adele quotients, a cuspidal operator
realization `S` of `GL_{r+1}` over `K` with unitary central character, a spectral presentation
`D` of `S` with irreducible admissible finite components, supercuspidal at two distinct split
finite places `v₁`, `v₂`.

The conclusion is what the comparison of the simple trace formula for `GL_{r+1}` over `K`
with its twisted form for `Res_{L/K} GL_{r+1}` gives after separation by the spherical Hecke
algebras, after the collapse of the cuspidal fibre of `S` (the determinant twists of `S` by
characters trivial on the idele norm have the traces of `S` on the test functions used) and
after strong multiplicity one (at the two auxiliary places, where the simple trace formula
restricts the test functions, through the isomorphism of components that a supercuspidal
coefficient forces): a list of at most one cuspidal realization `T` over `L` with the
global properties of the lift and the local trace identities

* at a split place `v` and `w | v`: `b · tr Π_w(f) = a · tr π_v(f)` for every `f`;
* at a place `v` with a single place `w` above it:
  `b · tr (Π_w(φ) ∘ A) = a · tr π_v(f)` for concordant pairs `(φ, f)` with σ-regular and
  regular support and norm determinants,

with `a ≠ 0` (a sum over the list, which is empty or has one term). This is
Arthur–Clozel (1989), Chapter 1, §6.3, the identities (6.2)–(6.3), printed pp. 54–57, and
Chapter III, Theorem 3.1, printed p. 201; Henniart–Lemaire (2011), II.6.1–II.6.13, printed
pp. 118–130. See the paired Markdown.
-/

noncomputable section

universe u uV uW

open NumberField IsDedekindDomain MeasureTheory
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic Langlands.BaseChange Langlands.HarmonicAnalysis
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.TraceFormula

local instance liftComparisonRationalAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance liftComparisonContinuousAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance liftComparisonSmoothAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance liftComparisonFormsAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance liftComparisonLocalSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- **The spectral comparison for the cuspidal cyclic lift.** Assume the hypotheses of
`CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement`. Then there are `k ≤ 1`, cuspidal
operator realizations `T j` (`j : Fin k`) of `GL_{r+1}` over `L` and spectral presentations
`P j` of `T j` with the following properties.

1. Each `T j` has unitary central character, the spectral system of `P j` is an arithmetic
   weak base change of that of `D`, the residue-degree Satake comparison of clause 3 of the
   lift statement holds for `P j`, and every finite local component of `P j` is irreducible
   and admissible.
2. At a finite place `v` that splits with cyclic shift action and at every `w` above `v`, the
   components `Π_{j,w}` of the `P j` at `w` pulled back along `K_v → L_w` are irreducible and
   admissible, and there are `b : Fin k → ℂ` and `a ≠ 0` such that for every Haar measure `μ`
   on `GL_{r+1}(K_v)` (Borel σ-algebra) and every Schwartz–Bruhat `f`,
   `Σ_j b j · tr Π_{j,w}(f) = a · tr π_v(f)`, where `π_v` is the component of `D` at `v`.
3. At a finite place `v` with a single place `w` above it, let `Π_{j,w}` be the component of
   `P j` at `w` viewed on `GL_{r+1}(K_v ⊗_K L)` (module topology) and `σv = id ⊗ σ`. Then
   `π_v` and the `Π_{j,w}` are admissible, and there are σv-intertwiners `A j` of `Π_{j,w}`,
   `b : Fin k → ℂ` and `a ≠ 0` such that for all Haar measures `μF` on `GL_{r+1}(K_v)` and
   `μE` on `GL_{r+1}(K_v ⊗_K L)` and all concordant `φ`, `f` with `φ` supported in the
   σv-regular set, `f` supported in the regular semisimple set and `det g` a norm from
   `(K_v ⊗_K L)ˣ` whenever `f g ≠ 0`,
   `Σ_j b j · tr (Π_{j,w}(φ) ∘ A j) = a · tr π_v(f)`. -/
def CuspidalCyclicLiftSpectralComparisonStatement : Prop :=
  ∀ (K : Type u) (L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
    (∀ u : NumberField.InfinitePlace K, IsCyclicShiftSplit K L u.Completion σ l) →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization K r)
      (D : CuspidalSpectralPresentation.{u, uV} S),
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      (∀ v, (D.localComponent v).IsIrreducible ∧ (D.localComponent v).IsAdmissible) →
    ∀ v₁ v₂ : Langlands.Global.FinitePlace K, v₁ ≠ v₂ →
      IsCyclicShiftSplit K L (v₁.adicCompletion K) σ l →
      IsCyclicShiftSplit K L (v₂.adicCompletion K) σ l →
      (D.localComponent v₁).IsSupercuspidal → (D.localComponent v₂).IsSupercuspidal →
    ∃ (k : ℕ), k ≤ 1 ∧ ∃ (T : Fin k → CuspidalOperatorRealization L r)
      (P : ∀ j, CuspidalSpectralPresentation.{u, uW} (T j)),
      (∀ j, ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter (T j) ∧
        (P j).spectralSystem.IsArithmeticWeakBaseChangeOf D.spectralSystem ∧
        (∀ (v : Langlands.Global.FinitePlace K) (hv : v ∉ D.spectralSystem.exceptional),
          (∀ w : FinitePlacesAbove L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1) →
          ∃ hw : ∀ w : FinitePlacesAbove L v, w.1 ∉ (P j).spectralSystem.exceptional,
            ∀ w : FinitePlacesAbove L v,
              (P j).spectralSystem.eigenvalues w.1 (hw w) =
                (D.spectralSystem.eigenvalues v hv).power (w.1.asIdeal.inertiaDeg (𝓞 K))) ∧
        (∀ w : Langlands.Global.FinitePlace L,
          ((P j).localComponent w).IsIrreducible ∧ ((P j).localComponent w).IsAdmissible)) ∧
      (∀ v : Langlands.Global.FinitePlace K, IsCyclicShiftSplit K L (v.adicCompletion K) σ l →
        ∀ w : FinitePlacesAbove L v,
          letI : ValuativeRel (v.adicCompletion K) :=
            (CompletionPadic.topologicalData v).valuativeRel
          haveI : IsNonarchimedeanLocalField (v.adicCompletion K) :=
            (CompletionPadic.topologicalData v).localField
          haveI := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion K) (r + 1)
          haveI := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion K) (r + 1)
          haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace
            (v.adicCompletion K) (r + 1)
          letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := borel _
          haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := ⟨rfl⟩
          ∃ (hπ : Langlands.IsAdmissible (D.localComponent v).representation)
            (hT : ∀ j, Langlands.IsAdmissible (completionPlaceAboveRepresentation v w
              ((P j).localComponent w.1).representation)),
            (∀ j, (completionPlaceAboveRepresentation v w
              ((P j).localComponent w.1).representation).IsIrreducible) ∧
            ∃ (b : Fin k → ℂ) (a : ℂ), a ≠ 0 ∧
              ∀ (μ : Measure (GeneralLinear (r + 1) (v.adicCompletion K))) [μ.IsHaarMeasure]
                (f : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion K))),
                ∑ j, b j * Character.distribution μ (completionPlaceAboveRepresentation v w
                    ((P j).localComponent w.1).representation) (hT j) f =
                  a * Character.distribution μ (D.localComponent v).representation hπ f) ∧
      (∀ (v : Langlands.Global.FinitePlace K) (w : FinitePlacesAbove L v),
        (∀ w' : FinitePlacesAbove L v, w' = w) →
        letI : ValuativeRel (v.adicCompletion K) :=
          (CompletionPadic.topologicalData v).valuativeRel
        haveI : IsNonarchimedeanLocalField (v.adicCompletion K) :=
          (CompletionPadic.topologicalData v).localField
        letI : TopologicalSpace (v.adicCompletion K ⊗[K] L) :=
          moduleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        haveI : IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) := ⟨rfl⟩
        haveI : IsTopologicalRing (v.adicCompletion K ⊗[K] L) :=
          IsModuleTopology.isTopologicalRing (v.adicCompletion K) _
        haveI := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion K) (r + 1)
        haveI := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion K) (r + 1)
        haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace
          (v.adicCompletion K) (r + 1)
        haveI := generalLinear_t2Space_of_finite (v.adicCompletion K)
          (v.adicCompletion K ⊗[K] L) (r + 1)
        haveI := generalLinear_locallyCompactSpace_of_finite (v.adicCompletion K)
          (v.adicCompletion K ⊗[K] L) (r + 1)
        haveI := generalLinear_totallyDisconnectedSpace_of_finite (v.adicCompletion K)
          (v.adicCompletion K ⊗[K] L) (r + 1)
        let σv : (v.adicCompletion K ⊗[K] L) ≃ₐ[v.adicCompletion K]
            (v.adicCompletion K ⊗[K] L) :=
          Algebra.TensorProduct.congr AlgEquiv.refl σ
        ∃ (hπ : Langlands.IsAdmissible (D.localComponent v).representation)
          (hP : ∀ j, Langlands.IsAdmissible
            (tensorPlaceAboveRepresentation v w ((P j).localComponent w.1).representation))
          (A : ∀ j, SigmaIntertwiner σv (r + 1)
            (tensorPlaceAboveRepresentation v w ((P j).localComponent w.1).representation))
          (b : Fin k → ℂ) (a : ℂ), a ≠ 0 ∧
          letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := borel _
          haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := ⟨rfl⟩
          letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L)) :=
            borel _
          haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L)) := ⟨rfl⟩
          ∀ (μF : Measure (GeneralLinear (r + 1) (v.adicCompletion K))) [μF.IsHaarMeasure]
            (μE : Measure (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L)))
            [μE.IsHaarMeasure]
            (φ : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L)))
            (f : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion K))),
            AreConcordant σv l μF μE φ f →
            IsSigmaRegularSupported σv l
              (φ : GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L) → ℂ) →
            IsRegularSupported (f : GeneralLinear (r + 1) (v.adicCompletion K) → ℂ) →
            (∀ g : GeneralLinear (r + 1) (v.adicCompletion K), f g ≠ 0 →
              GeneralLinear.determinant g ∈
                (Units.map (Algebra.norm (v.adicCompletion K) :
                  (v.adicCompletion K ⊗[K] L) →* v.adicCompletion K)).range) →
              ∑ j, b j * twistedDistribution μE
                  (tensorPlaceAboveRepresentation v w ((P j).localComponent w.1).representation)
                  (hP j) (A j).toLinearMap φ =
                a * Character.distribution μF (D.localComponent v).representation hπ f)

end Langlands.TraceFormula
