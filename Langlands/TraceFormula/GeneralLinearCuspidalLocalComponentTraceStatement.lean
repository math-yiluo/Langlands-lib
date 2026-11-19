import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationStatement
import Langlands.Automorphic.PresentedLocalCategory
import Langlands.TraceFormula.GroupSchemeCuspidalLocalTraceFactorizationStatement
import Langlands.TraceFormula.GeneralLinearBaseChangeLocal

/-!
# The local trace factor of a cuspidal summand of `GL_n` is the Library's local component

For `GL_{r+1}` over a number field `F`, this module states that the local factor at a finite
place `v` in the trace factorization of `GroupSchemeCuspidalLocalTraceFactorizationStatement`
(Task 7701) can be taken to be the Library's local component at `v` of a cuspidal operator
realization `R` attached to the summand. The summand `P` and the realization `R` are linked as
in `GeneralLinearCuspidalSummandRealizationStatement`: a linear map `Φ` sends each form of `R`
to its `L²` class, and the closure of its image is `P`. The local component is that of any
spectral presentation of `R` whose component at `v` is irreducible and admissible. It is
transported from `GL_{r+1}(F_v)` in the matrix model to the points of the group scheme over the
completion by the Library's `localGLHomeomorph`.

The statement contains no proof. The paired Markdown gives the sources and the argument.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula

local instance localComponentTraceGeneralLinearIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance localComponentTraceGeneralLinearSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

local instance localComponentTraceRationalAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance localComponentTraceContinuousAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance localComponentTraceSmoothAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance localComponentTraceFormsAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance localComponentTraceLocalSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- The representation of the points of `GL_{r+1}` over the completion `F_v` obtained from a
local realization of `GL_{r+1}(F_v)` (matrix model) through the Library's homeomorphism
`localGLHomeomorph F (r + 1) (.inr v)` between the two models of `GL_{r+1}(F_v)`. -/
def localRealizationPlaceRepresentation {F : Type u} [Field F] [NumberField F] {r : ℕ}
    {v : Langlands.Global.FinitePlace F} (A : LocalRealization F (r + 1) v) :
    Representation ℂ
      (PlaceGroupPoints F (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
        (.inr v)) A.Space :=
  A.representation.comp
    (localGLHomeomorph F (r + 1) (.inr v)).toMulEquiv.toMonoidHom

/-- **The local trace factor of a cuspidal summand of `GL_{r+1}` is the local component of its
realization.** Let `F` be a number field whose adele quotient is compact, `T → GL_{r+1}` central
data as in `GeneralLinearCuspidalSummandRealizationStatement`, `v` a finite place (with the
measurable and topological structure on `GL_{r+1}(F_v)` given as instance binders), `μv` a Haar
measure on `GL_{r+1}(F_v)` and `ν` a Haar measure on `GL_{r+1}(𝔸_F)`. Let `P` be a nonzero
complete subspace of the cuspidal space `S` invariant under the right action `πc` and with no
closed invariant subspaces other than `⊥` and `P`. Let `R` be a cuspidal operator realization
and `Φ` a linear map from its space to `S` sending every form to its `L²` class, with the
closure of the image of `Φ` equal to `P`. Let `D` be a spectral presentation of `R` whose local
component at `v` is irreducible and admissible, and let `ρ` be that local component, as a
representation of the points of the group scheme over `F_v`. Then `ρ` is admissible, and there
is `C : (GL_{r+1}(𝔸_F) → ℂ) → ℂ` such that, for every Schwartz–Bruhat function `fv` on
`GL_{r+1}(F_v)` and every `fw : GL_{r+1}(𝔸_F) → ℂ` invariant under right translation by
`GL_{r+1}(F_v)`, if `f g = fv (g_v) * fw g` is `ν`-integrable and the compression to `P` of
its integrated action on `S` is trace class, then that trace equals
`Character.distribution μv ρ hρ fv * C fw`. -/
def GeneralLinearCuspidalLocalComponentTraceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
    (v : Langlands.Global.FinitePlace F)
    [MeasurableSpace (PlaceGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) (.inr v))]
    [BorelSpace (PlaceGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) (.inr v))]
    [LocallyCompactSpace (PlaceGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) (.inr v))]
    [TotallyDisconnectedSpace (PlaceGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) (.inr v))]
    (μv : Measure (PlaceGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) (.inr v)))
    [μv.IsHaarMeasure]
    (ν : Measure (AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))))
    [ν.IsHaarMeasure],
    let hG := GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
    let S := fullAEL2CuspidalSubmodule F _ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F _ hPD hG T i hi I e hc
    ∀ (P : Submodule ℂ S) [CompleteSpace P], P ≠ ⊥ →
      (∀ a, ∀ x ∈ P, πc a x ∈ P) →
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ a, ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) →
      ∀ (R : CuspidalOperatorRealization F r) (Φ : R.Space →ₗ[ℂ] S),
        (∀ f : R.Space,
          IsGeneralLinearFormClass F r T i (Φ f : Lp ℂ 2 _) (R.realization.toContinuous f)) →
        (LinearMap.range Φ).topologicalClosure = P →
        ∀ D : CuspidalSpectralPresentation.{u, uV} R,
          (D.localComponent v).IsIrreducible → (D.localComponent v).IsAdmissible →
          ∃ hρ : Langlands.IsAdmissible
              (localRealizationPlaceRepresentation (D.localComponent v)),
            ∃ C : (AdelicGroupPoints F
                (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) → ℂ) → ℂ,
              ∀ (fv : SchwartzBruhat (PlaceGroupPoints F
                  (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) (.inr v)))
                (fw : AdelicGroupPoints F
                  (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) → ℂ),
                (∀ g x, fw (g * ofPlace F _ (.inr v) x) = fw g) →
                ∀ hf : Integrable (fun g => fv (atPlace F _ (.inr v) g) * fw g) ν,
                  let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                    fullAEL2CuspidalIntegratedAction F _ hPD hG T i hi I e hc ν _ hf ∘L
                      P.subtypeL
                  IsTraceClass (E := (P : Submodule ℂ S)) RPf →
                    operatorTrace (E := (P : Submodule ℂ S)) RPf =
                      Character.distribution μv
                        (localRealizationPlaceRepresentation (D.localComponent v)) hρ fv * C fw

end Langlands.TraceFormula
