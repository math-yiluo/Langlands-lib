import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.TraceFormula.GroupSchemeCuspidalLocalTraceFactorizationStatement
import Langlands.TraceFormula.GeneralLinearBaseChangeLocal
import Langlands.TraceFormula.WeilGeneralLinearCuspidalSummandRealizationStatement
import Langlands.BaseChange.TwistedCharacter
import Langlands.Global.AdelicFunctoriality.Norm
import Langlands.Global.CompletionPadic
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# The local (twisted) trace factor of a cuspidal summand of `Res_{L/K} GL_n` at any finite place

Let `L/K` be a finite extension of number fields, `σ ∈ Aut(L/K)`, and `W = Res_{L/K} GL_{r+1}`.
Let `v` be any finite place of `K`. The local points are `W(K_v) = GL_{r+1}(K_v ⊗_K L)` (the
Library's `localPointsEquiv`), and `K_v ⊗_K L ≅ ∏_{w | v} L_w` (the Library's
`finiteTensorMap`). This module defines the tensor product `tensorPullbackRepresentation` of a
finite family of representations pulled back along ring maps, and states that, on an irreducible
cuspidal summand `P` of `L²([W])` attached to a cuspidal operator realization `R` over `L` as in
`WeilGeneralLinearCuspidalSummandRealizationStatement`, the local factor at `v` in the trace
factorization of `GroupSchemeCuspidalLocalTraceFactorizationStatement` (Task 7701) can be taken
to be `⊗_{w | v} Π_w`, the tensor product of the local components at the places `w` above `v`
of a spectral presentation of `R`, viewed as a representation of `GL_{r+1}(K_v ⊗_K L)`. For the
twist `I_θ` attached to `σ`, the local factor is a twisted trace `tr (ρ_v(f_v) ∘ A)` of this
tensor product, for an isomorphism `A` of `ρ_v` onto `ρ_v^σ`, where `σ` acts on `K_v ⊗_K L` by
`id ⊗ σ`.

The statement contains no proof. The paired Markdown gives the sources and the argument.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj TensorProduct
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis Langlands.BaseChange
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

/-- The tensor product of a family of representations pulled back along ring maps. For a
commutative ring `A`, ring maps `h i : A →+* B i` and representations `ρ i` of `GL_n(B i)` on
`V i`, this is the representation `g ↦ ⨂ᵢ ρ i (h i g)` of `GL_n(A)` on `⨂[ℂ] i, V i`
(Mathlib's `PiTensorProduct.mapMonoidHom` composed with the product of the pullbacks). -/
def tensorPullbackRepresentation {A : Type*} [CommRing A] {J : Type*} {B : J → Type*}
    [∀ i, CommRing (B i)] (n : ℕ) (h : ∀ i, A →+* B i) {V : J → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (GeneralLinear n (B i)) (V i)) :
    Representation ℂ (GeneralLinear n A) (⨂[ℂ] i, V i) :=
  (PiTensorProduct.mapMonoidHom (R := ℂ) (s := V)).comp
    (MonoidHom.pi fun i => (ρ i).comp (Matrix.GeneralLinearGroup.map (h i)))

local instance weilLocalTensorTraceIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance weilLocalTensorTraceSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

local instance weilLocalTensorTraceRationalAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance weilLocalTensorTraceContinuousAddCommGroup (F : Type u) [Field F]
    [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance weilLocalTensorTraceSmoothAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance weilLocalTensorTraceFormsAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance weilLocalTensorTraceLocalSpaceAddCommGroup {F : Type u} [Field F]
    [NumberField F] {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

set_option hygiene false in
/-- The `GL_{r+1}` group scheme over `K`, for the bound variables `K` and `r`. -/
local notation "GLᵣ" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)

set_option hygiene false in
/-- The Weil restriction `Res_{L/K} GL_{r+1}`, for the bound variables `K`, `L` and `r`. -/
local notation "Wᵣ" => weilGroup K L GLᵣ

set_option maxHeartbeats 1000000 in
/-- **The local (twisted) trace factor of a cuspidal summand of `Res_{L/K} GL_{r+1}` at a finite
place.** Let `L/K` be a finite extension of number fields, the adele quotient of `L` being
compact, `σ ∈ Aut(L/K)`, `W = Res_{L/K} GL_{r+1}` with a proof `hG` that it is connected
reductive, `T → W` central data as in `WeilGeneralLinearCuspidalSummandRealizationStatement`,
and `ν` a Haar measure on `W(𝔸_K)`. Let `v` be a finite place of `K`. Give `K_v ⊗_K L` its
module topology over `K_v`, `GL_{r+1}(K_v ⊗_K L)` the Borel σ-algebra, and let `μv` be a Haar
measure on it; let `σv = id ⊗ σ`. Let `P` be a nonzero complete subspace of the cuspidal space
`S` invariant under the right action `πc` and with no closed invariant subspaces other than `⊥`
and `P`. Let `R` be a cuspidal operator realization of `GL_{r+1}` over `L` and `Ψ` a linear map
from its space to `S` sending every form to its `L²` class (`IsWeilFormClass`), with the closure
of the image of `Ψ` equal to `P`. Let `D` be a spectral presentation of `R` whose local
components at all places `w` above `v` are irreducible and admissible, and let `ρv` be their
tensor product, a representation of `GL_{r+1}(K_v ⊗_K L)` through the components
`K_v ⊗_K L → L_w` of `finiteTensorMap v`. For `fv` a Schwartz–Bruhat function on
`GL_{r+1}(K_v ⊗_K L)` and `fw` a function on `W(𝔸_K)` invariant under right translation by
`W(K_v)`, let `f g = fv (g_v) * fw g`, where `g_v ∈ W(K_v)` is read in `GL_{r+1}(K_v ⊗_K L)`
through `localPointsEquiv`. Then `ρv` is admissible, and:

1. there is `C` such that, whenever `f` is `ν`-integrable and the compression to `P` of its
   integrated action on `S` is trace class, that trace equals
   `Character.distribution μv ρv hP fv * C fw`;
2. for the automorphism `Θ` of `W(𝔸_K)` induced by `σ`, preserving the positive rational
   subgroup and the quotient measure (`hΘ`, `hΘμ`), if the twisting operator `I_Θ` maps `P`
   into `P`, there are an isomorphism `A` of `ρv` onto `ρv^{σv}` (`SigmaIntertwiner`) and `C`
   such that, whenever `f` is `ν`-integrable and the compression to `P` of the compression to
   `S` of `R(f) ∘ I_Θ` is trace class, its trace equals
   `twistedDistribution μv ρv hP A fv * C fw`.

Each part supplies one functional `C` for all test-function pairs `fv`, `fw` in that part. -/
def WeilGeneralLinearCuspidalLocalTensorTraceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [CompactSpace (AdeleQuotient L)]
    (σ : L ≃ₐ[K] L) (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive Wᵣ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ Wᵣ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup K Wᵣ)).IsMulRightInvariant]
    (ν : Measure (AdelicGroupPoints K Wᵣ)) [ν.IsHaarMeasure],
    let S := fullAEL2CuspidalSubmodule K Wᵣ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction K Wᵣ hPD hG T i hi I e hc
    ∀ (P : Submodule ℂ S) [CompleteSpace P], P ≠ ⊥ →
      (∀ a, ∀ x ∈ P, πc a x ∈ P) →
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ a, ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) →
    ∀ (R : CuspidalOperatorRealization L r) (Ψ : R.Space →ₗ[ℂ] S),
      (∀ f : R.Space,
        IsWeilFormClass K L r T i
          ((Ψ f : S) : Lp ℂ 2 (positiveRationalQuotientHaarMeasure K Wᵣ T i))
          (R.realization.toContinuous f)) →
      (LinearMap.range Ψ).topologicalClosure = P →
    ∀ (v : Langlands.Global.FinitePlace K),
    letI : ValuativeRel (v.adicCompletion K) :=
      (CompletionPadic.topologicalData v).valuativeRel
    haveI : IsNonarchimedeanLocalField (v.adicCompletion K) :=
      (CompletionPadic.topologicalData v).localField
    letI : TopologicalSpace (v.adicCompletion K ⊗[K] L) :=
      moduleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
    haveI : IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) := ⟨rfl⟩
    haveI : IsTopologicalRing (v.adicCompletion K ⊗[K] L) :=
      IsModuleTopology.isTopologicalRing (v.adicCompletion K) _
    haveI := generalLinear_t2Space_of_finite (v.adicCompletion K)
      (v.adicCompletion K ⊗[K] L) (r + 1)
    haveI := generalLinear_locallyCompactSpace_of_finite (v.adicCompletion K)
      (v.adicCompletion K ⊗[K] L) (r + 1)
    haveI := generalLinear_totallyDisconnectedSpace_of_finite (v.adicCompletion K)
      (v.adicCompletion K ⊗[K] L) (r + 1)
    letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L)) := borel _
    haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L)) := ⟨rfl⟩
    ∀ (μv : Measure (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L))) [μv.IsHaarMeasure],
    let σv : (v.adicCompletion K ⊗[K] L) ≃ₐ[v.adicCompletion K] (v.adicCompletion K ⊗[K] L) :=
      Algebra.TensorProduct.congr AlgEquiv.refl σ
    let Θ : AdelicGroupPoints K Wᵣ ≃ₜ* AdelicGroupPoints K Wᵣ :=
      adelicAut K (unitGaloisAut K L GLᵣ σ)
    let gv : AdelicGroupPoints K Wᵣ → GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L) :=
      fun g => localPointsEquiv K L (r + 1) (.inr v) (atPlace K Wᵣ (.inr v) g)
    ∀ D : CuspidalSpectralPresentation.{u, uV} R,
      (∀ w : FinitePlacesAbove L v,
        (D.localComponent w.1).IsIrreducible ∧ (D.localComponent w.1).IsAdmissible) →
      let ρv : Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L))
          (⨂[ℂ] w : FinitePlacesAbove L v, (D.localComponent w.1).Space) :=
        tensorPullbackRepresentation (r + 1)
          (fun w : FinitePlacesAbove L v =>
            (Pi.evalRingHom (fun q : FinitePlacesAbove L v => q.1.adicCompletion L) w).comp
              (finiteTensorMap v).toRingHom)
          (fun w : FinitePlacesAbove L v => (D.localComponent w.1).representation)
      ∃ hP : Langlands.IsAdmissible ρv,
        (∃ C : (AdelicGroupPoints K Wᵣ → ℂ) → ℂ,
          ∀ (fv : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L)))
            (fw : AdelicGroupPoints K Wᵣ → ℂ),
            (∀ g x, fw (g * ofPlace K Wᵣ (.inr v) x) = fw g) →
            ∀ hf : Integrable (fun g => fv (gv g) * fw g) ν,
              let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                fullAEL2CuspidalIntegratedAction K Wᵣ hPD hG T i hi I e hc ν _ hf ∘L
                  P.subtypeL
              IsTraceClass (E := (P : Submodule ℂ S)) RPf →
                operatorTrace (E := (P : Submodule ℂ S)) RPf =
                  Character.distribution μv ρv hP fv * C fw) ∧
        ∀ (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup K Wᵣ T i ↔
            x ∈ positiveRationalSubgroup K Wᵣ T i)
          (hΘμ : MeasurePreserving
            (quotientAutomorphism (positiveRationalSubgroup K Wᵣ T i) Θ hΘ).symm
            (positiveRationalQuotientHaarMeasure K Wᵣ T i)
            (positiveRationalQuotientHaarMeasure K Wᵣ T i)),
          let IΘ := twistOperator (positiveRationalSubgroup K Wᵣ T i) Θ hΘ
            (positiveRationalQuotientHaarMeasure K Wᵣ T i) hΘμ
          (∀ x ∈ P, ∃ y ∈ P, (y : Lp ℂ 2 (positiveRationalQuotientHaarMeasure K Wᵣ T i)) =
            IΘ (x : Lp ℂ 2 (positiveRationalQuotientHaarMeasure K Wᵣ T i))) →
          ∃ (A : SigmaIntertwiner σv (r + 1) ρv) (C : (AdelicGroupPoints K Wᵣ → ℂ) → ℂ),
            ∀ (fv : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L)))
              (fw : AdelicGroupPoints K Wᵣ → ℂ),
              (∀ g x, fw (g * ofPlace K Wᵣ (.inr v) x) = fw g) →
              ∀ hf : Integrable (fun g => fv (gv g) * fw g) ν,
                let Rf := haarQuotientL2IntegratedAction K Wᵣ T i hi I e hc ν _ hf
                let BP : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                  (S.orthogonalProjectionOnto ∘L (Rf ∘L IΘ) ∘L S.subtypeL) ∘L P.subtypeL
                IsTraceClass (E := (P : Submodule ℂ S)) BP →
                  operatorTrace (E := (P : Submodule ℂ S)) BP =
                    twistedDistribution μv ρv hP A.toLinearMap fv * C fw

end Langlands.TraceFormula
