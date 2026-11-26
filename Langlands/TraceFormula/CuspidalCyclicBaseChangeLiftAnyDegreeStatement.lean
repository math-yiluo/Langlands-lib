import Langlands.TraceFormula.CuspidalCyclicBaseChangeLiftStatement

/-!
# Cuspidal base change for cyclic extensions of arbitrary degree

The proposition has the hypotheses of `CuspidalCyclicBaseChangeLiftStatement` with the
prime-degree condition removed. At a finite place with an intermediate number of places
above it, the applicable local conclusions are the conditional Satake comparison and
irreducibility and admissibility of the upper components.

This formulation uses the trace comparison of Arthur–Clozel (1989), Chapter 1, §6.3,
printed pp. 54–57, and the fibre theorem in Chapter III, Theorem 3.1, printed p. 201.
Henniart–Lemaire (2011), §§II.6.1 and II.6.18–II.6.20, printed p. 118 and pp. 132–135,
provide the arbitrary-degree comparison over function fields. The paired Markdown
explains the number-field formulation and the σ-lift identity.
-/

noncomputable section

universe u uV uW

open NumberField IsDedekindDomain
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic Langlands.BaseChange
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.TraceFormula

local instance anyDegreeLiftRationalAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance anyDegreeLiftContinuousAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance anyDegreeLiftSmoothAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance anyDegreeLiftFormsAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance anyDegreeLiftLocalSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- **Cyclic base change of a cuspidal representation with two split supercuspidal places.**
Let `L/K` be cyclic of degree `l` with generator `σ`. Assume every infinite place of
`K` splits with cyclic shift action. Let `S` be a cuspidal operator realization of `GL_{r+1}`
over `K` with unitary central character and `D` a spectral presentation of `S` with
irreducible admissible local components at every finite place. Suppose two distinct finite
places split with cyclic shift action and have supercuspidal components in `D`.

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
   along `K_v ⊗_K L → L_w` is a σ-lift of the component of `D` at `v`, with admissibility
   of both representations, the module topology on the tensor product and automorphism
   `id ⊗ σ`.
6. Every finite local component of `P` is irreducible and admissible. -/
def CuspidalCyclicBaseChangeLiftAnyDegreeStatement : Prop :=
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
          IsSigmaLift σv l (D.localComponent v).representation hπ PiV hP A c) ∧
      (∀ w : Langlands.Global.FinitePlace L,
        (P.localComponent w).IsIrreducible ∧ (P.localComponent w).IsAdmissible)

end Langlands.TraceFormula
