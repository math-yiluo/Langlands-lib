import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.Unramified.WeakTransfer
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.BaseChange.TwistedCharacter
import Langlands.TraceFormula.CyclicFieldGlobalizationStatement
import Langlands.Global.AdelicFunctoriality.Norm
import Langlands.Global.CompletionPadic
import Langlands.Group.GL.LocalFieldTopology

/-!
# Cyclic base change of a cuspidal representation of `GL_n` with two split supercuspidal places

This module states the cuspidal lift for a cyclic extension of prime degree with split
infinite places and two split supercuspidal finite places. It uses the local components of
spectral presentations with irreducible admissible finite factors.

The formulation is derived from Arthur–Clozel (1989), Chapter 1, §6.3, (6.2)–(6.5),
printed pp. 54–57, and Chapter III, Theorem 3.1, printed p. 201, with the σ-lift formulation
of Henniart–Lemaire (2011), §§II.2.7 and II.6, printed pp. 67 and 119–129. The paired
Markdown gives the source details and the trace comparison.
-/

noncomputable section

universe u uV uW

open NumberField IsDedekindDomain
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic Langlands.BaseChange
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.TraceFormula

local instance cyclicLiftRationalAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance cyclicLiftContinuousAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cyclicLiftSmoothAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cyclicLiftFormsAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance cyclicLiftLocalSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- For a finite place `w` of `L` above a finite place `v` of `K`, the ring homomorphism
`K_v ⊗_K L → L_w` is the `w`-component of `finiteTensorMap v`. -/
def tensorPlaceAboveHom {K : Type u} {L : Type u} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] (v : Langlands.Global.FinitePlace K)
    (w : FinitePlacesAbove L v) :
    v.adicCompletion K ⊗[K] L →+* w.1.adicCompletion L :=
  (Pi.evalRingHom (fun q : FinitePlacesAbove L v => q.1.adicCompletion L) w).comp
    (finiteTensorMap v).toRingHom

/-- A representation of `GL_n(L_w)`, for a finite place `w` of `L` above `v`, viewed as a
representation of `GL_n(K_v ⊗_K L)` through `tensorPlaceAboveHom v w`. -/
def tensorPlaceAboveRepresentation {K : Type u} {L : Type u} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] {n : ℕ} (v : Langlands.Global.FinitePlace K)
    (w : FinitePlacesAbove L v) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n (w.1.adicCompletion L)) V) :
    Representation ℂ (GeneralLinear n (v.adicCompletion K ⊗[K] L)) V :=
  ρ.comp (Matrix.GeneralLinearGroup.map (tensorPlaceAboveHom v w))

/-- A representation of `GL_n(L_w)`, for a finite place `w` of `L` above `v`, viewed as a
representation of `GL_n(K_v)` through the completed embedding `K_v → L_w`. -/
def completionPlaceAboveRepresentation {K : Type u} {L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] {n : ℕ} (v : Langlands.Global.FinitePlace K)
    (w : FinitePlacesAbove L v) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n (w.1.adicCompletion L)) V) :
    Representation ℂ (GeneralLinear n (v.adicCompletion K)) V :=
  haveI := w.2
  ρ.comp (Matrix.GeneralLinearGroup.map (FiniteExtension.completionMap v w.1))

/-- **Cyclic base change of a cuspidal representation with two split supercuspidal places.**
Let `L/K` be cyclic of prime degree `l` with generator `σ`. Assume every infinite place of
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
def CuspidalCyclicBaseChangeLiftStatement : Prop :=
  ∀ (K : Type u) (L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (σ : L ≃ₐ[K] L) (l : ℕ), l.Prime → IsCyclicAlgebra σ l →
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
