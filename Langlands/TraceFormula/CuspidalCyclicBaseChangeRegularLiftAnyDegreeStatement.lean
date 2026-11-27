import Langlands.TraceFormula.CuspidalCyclicBaseChangeLiftStatement
import Langlands.BaseChange.SigmaDiscreteRegularDescentStatement

/-!
# Cuspidal cyclic lift with the regular σ-lift identity

The proposition has the hypotheses of `CuspidalCyclicBaseChangeLiftAnyDegreeStatement`. Its
conclusion keeps clauses 1–4 and 6 of that proposition and replaces the σ-lift of clause 5,
at a finite place with one place above it, by the regular σ-lift identity
`IsRegularSigmaLift`: the trace identity on concordant pairs with σ-regular and regular
support and with the determinants of the ordinary support in the norm group.

This is the output of the global trace comparison of Arthur–Clozel (1989), Chapter 1, §6.3,
printed pp. 54–57, in which the determinant twists of the cuspidal fibre (Chapter III,
Theorem 3.1, printed p. 201) have equal traces on the image of the norm (printed p. 57).
Henniart–Lemaire (2011) set up the global comparison in any cyclic degree in §II.6.1, printed
p. 118, and in §II.6.13, printed pp. 129–130, obtain from it the local trace identity on
regularly supported concordant pairs. This file states the proposition and does not prove it.
The paired Markdown explains the formulation.
-/

noncomputable section

universe u uV uW

open NumberField IsDedekindDomain
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic Langlands.BaseChange
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.TraceFormula

local instance regularLiftRationalAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance regularLiftContinuousAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance regularLiftSmoothAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance regularLiftFormsAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance regularLiftLocalSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- **Cuspidal cyclic lift with the regular σ-lift identity at places with one place above.**
Let `L/K` be cyclic of degree `l` with generator `σ`. Assume every infinite place of `K` splits
with cyclic shift action. Let `S` be a cuspidal operator realization of `GL_{r+1}` over `K` with
unitary central character and `D` a spectral presentation of `S` with irreducible admissible
local components at every finite place. Suppose two distinct finite places split with cyclic
shift action and have supercuspidal components in `D`.

There exist a cuspidal operator realization `T` over `L` and a spectral presentation `P` of `T`
with the following properties.

1. `T` has unitary central character.
2. The spectral system of `P` is an arithmetic weak base change of that of `D`.
3. At every finite `v` outside the exceptional set of `D` with all places `w` above `v`
   unramified, every such `w` is outside the exceptional set of `P` and the Satake parameters
   at `w` are the parameters of `D` at `v` raised to the residue degree.
4. At a split finite `v` and every `w` above it, the component of `P` at `w` pulled back
   along `K_v → L_w` is isomorphic to the component of `D` at `v`.
5. At a finite `v` with a single `w` above it, the component of `P` at `w` pulled back
   along `K_v ⊗_K L → L_w` and the component of `D` at `v` are admissible and satisfy
   `IsRegularSigmaLift` for the automorphism `id ⊗ σ`, the module topology on the tensor
   product, some σ-intertwiner and some constant: the σ-lift identity holds for concordant
   pairs with σ-regular and regular support whose ordinary function is supported on matrices
   with determinant in the norm group.
6. Every finite local component of `P` is irreducible and admissible.

The hypotheses and clauses 1–4 and 6 are those of `CuspidalCyclicBaseChangeLiftAnyDegreeStatement`;
clause 5 has the same data and `IsRegularSigmaLift` in place of `IsSigmaLift`. -/
def CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement : Prop :=
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
    ∃ (T : CuspidalOperatorRealization L r) (P : CuspidalSpectralPresentation.{u, uW} T),
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T ∧
      P.spectralSystem.IsArithmeticWeakBaseChangeOf D.spectralSystem ∧
      (∀ (v : Langlands.Global.FinitePlace K) (hv : v ∉ D.spectralSystem.exceptional),
        (∀ w : FinitePlacesAbove L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1) →
        ∃ hw : ∀ w : FinitePlacesAbove L v, w.1 ∉ P.spectralSystem.exceptional,
          ∀ w : FinitePlacesAbove L v,
            P.spectralSystem.eigenvalues w.1 (hw w) =
              (D.spectralSystem.eigenvalues v hv).power (w.1.asIdeal.inertiaDeg (𝓞 K))) ∧
      (∀ v : Langlands.Global.FinitePlace K, IsCyclicShiftSplit K L (v.adicCompletion K) σ l →
        ∀ w : FinitePlacesAbove L v,
          Nonempty ((completionPlaceAboveRepresentation v w
            (P.localComponent w.1).representation).Equiv (D.localComponent v).representation)) ∧
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
        let PiV := tensorPlaceAboveRepresentation v w (P.localComponent w.1).representation
        ∃ (hπ : IsAdmissible (D.localComponent v).representation) (hP : IsAdmissible PiV)
          (A : SigmaIntertwiner σv (r + 1) PiV) (c : ℂ),
          IsRegularSigmaLift σv l (D.localComponent v).representation hπ PiV hP A c) ∧
      (∀ w : Langlands.Global.FinitePlace L,
        (P.localComponent w).IsIrreducible ∧ (P.localComponent w).IsAdmissible)

end Langlands.TraceFormula
