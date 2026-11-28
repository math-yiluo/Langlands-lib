import Langlands.TraceFormula.CyclicBaseChangeEllipticTraceIdentityUniverse
import Langlands.BaseChange.EllipticTraceIdentityUntwist
import Langlands.BaseChange.CyclicAlgebraBaseChange
import Langlands.Automorphic.Unramified.WeakBaseChangeSplitCentre
import Langlands.Automorphic.HeckeDeterminantTwistSupercuspidalProof
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Global.AdelicFunctoriality.NormReduction
import Langlands.Representation.Twist.PullbackProof

/-! # Reduction of the elliptic trace identity to split-centre trivial realizations -/

noncomputable section

universe u uV uW

set_option autoImplicit false

namespace Langlands.TraceFormula

open NumberField
open Langlands.Automorphic Langlands.BaseChange Langlands.Global
open Langlands.Global.AdelicFunctoriality Langlands.Global.CuspidalPairPoles
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance splitCentreRationalGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance splitCentreContinuousGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance splitCentreSmoothGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance splitCentreFormsGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance splitCentreLocalGroup {K : Type u} [Field K] [NumberField K]
    {n : ℕ} {v : Langlands.Global.FinitePlace K} (L : LocalRealization K n v) :
    AddCommGroup L.Space :=
  Submodule.addCommGroup _

/-- The norm on the completed tensor algebra is the single local field norm when exactly
one place lies above the base place. -/
private theorem tensorComponentMap_norm_det {n : ℕ} {v : Langlands.Global.FinitePlace F}
    (w : FinitePlacesAbove E v)
    (hw : ∀ q : FinitePlacesAbove E v, q = w) (g : GeneralLinear n (v.adicCompletion F ⊗[F] E)) :
    FiniteExtension.localUnitNorm v w.1 (GeneralLinear.determinant (tensorComponentMap n v w g)) =
      Units.map (Algebra.norm (v.adicCompletion F) :
        (v.adicCompletion F ⊗[F] E) →* v.adicCompletion F) (GeneralLinear.determinant g) := by
  classical
  apply Units.ext
  unfold tensorComponentMap
  rw [Matrix.GeneralLinearGroup.map_det]
  let x : v.adicCompletion F ⊗[F] E := GeneralLinear.determinant g
  let e := AlgEquiv.ofBijective (finiteTensorMap (L := E) v) ((completedTensorComparison F E).1 v)
  change Algebra.norm (v.adicCompletion F) (e x w) = Algebra.norm (v.adicCompletion F) x
  rw [← Algebra.norm_eq_of_algEquiv e x, norm_pi]
  rw [Finset.prod_eq_single_of_mem w (Finset.mem_univ w)
    (fun q _ hq => (hq (hw q)).elim)]

private theorem continuous_tensorComponentMap (n : ℕ) {v : Langlands.Global.FinitePlace F}
    (w : FinitePlacesAbove E v) [TopologicalSpace (v.adicCompletion F ⊗[F] E)]
    [IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)] :
    Continuous (tensorComponentMap n v w) := by
  let e := (Pi.evalAlgHom (v.adicCompletion F)
    (fun q : FinitePlacesAbove E v => q.1.adicCompletion E) w).comp (finiteTensorMap v)
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  exact he.generalLinearGroup_map

section Twists

variable [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
  {r : ℕ} {S : CuspidalOperatorRealization F r} {T : CuspidalOperatorRealization E r}

/-- Compare the twisted presentation with the algebraic twist of the original
local representation, on its original carrier. -/
private def localTwistEquiv {K : Type u} [Field K] [NumberField K]
    [CompactSpace (AdeleQuotient K)] {A : CuspidalOperatorRealization K r}
    (D : CuspidalSpectralPresentation.{u, uV} A) (χ : HeckeCharacter K)
    (v : Langlands.Global.FinitePlace K) :
    ((D.heckeDeterminantTwist χ).localComponent v).representation.Equiv
      (twist (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom (D.localComponent v).representation) :=
  (D.heckeDeterminantTwistLocalComponentEquiv χ v).trans
    ((D.localComponent v).heckeDeterminantTwistRepresentationEquiv χ).symm

set_option maxHeartbeats 3000000 in
/-- A conclusion for the two compatible global twists gives the local elliptic trace
identity for the original presentations. -/
theorem CyclicBaseChangeEllipticConclusion.of_heckeDeterminantTwist
    {σ : E ≃ₐ[F] E} {l : ℕ} (hcyc : IsCyclicAlgebra σ l) {v : Langlands.Global.FinitePlace F}
    (w : FinitePlacesAbove E v) (hw : ∀ q : FinitePlacesAbove E v, q = w)
    (P : CuspidalSpectralPresentation.{u, uW} T) (D : CuspidalSpectralPresentation.{u, uV} S)
    (χ : HeckeCharacter F) (hπ : (D.localComponent v).IsAdmissible)
    (h : CyclicBaseChangeEllipticConclusion σ l v w
      (P.heckeDeterminantTwist (χ.normComp (L := E))) (D.heckeDeterminantTwist χ)) :
    CyclicBaseChangeEllipticConclusion σ l v w P D := by
  let : ValuativeRel (v.adicCompletion F) := (CompletionPadic.topologicalData v).valuativeRel
  have : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    (CompletionPadic.topologicalData v).localField
  let : TopologicalSpace (v.adicCompletion F ⊗[F] E) :=
    moduleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)
  have : IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (v.adicCompletion F ⊗[F] E) :=
    IsModuleTopology.isTopologicalRing (v.adicCompletion F) _
  have := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion F) (r + 1)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion F) (r + 1)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace (v.adicCompletion F) (r + 1)
  have := generalLinear_t2Space_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  have := generalLinear_locallyCompactSpace_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  have := generalLinear_totallyDisconnectedSpace_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  let χ' := χ.normComp (L := E)
  let ψ := tensorComponentMap (r + 1) v w
  let ω := (χ.finiteComponent v).toMonoidHom
  let χF := ω.comp (GeneralLinear.determinant (n := r + 1))
  let χE := (ω.comp (Units.map (Algebra.norm (v.adicCompletion F) :
    (v.adicCompletion F ⊗[F] E) →* v.adicCompletion F))).comp
      (GeneralLinear.determinant (n := r + 1))
  have hF_eq : (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom = χF :=
    MonoidHom.ext (χ.finiteLocalDeterminant_eq_finiteComponent_det (r + 1) v)
  have hE_eq : (χ'.finiteLocalDeterminant (r + 1) w.1).toMonoidHom.comp ψ = χE := by
    apply MonoidHom.ext
    intro g
    change (χ.normComp (L := E)).finiteLocalDeterminant (r + 1) w.1 (ψ g) =
      χ.finiteComponent v (Units.map (Algebra.norm (v.adicCompletion F))
        (GeneralLinear.determinant g))
    rw [HeckeCharacter.finiteLocalDeterminant_eq_finiteComponent_det,
      HeckeCharacter.normComp_finiteComponent χ v w,
      tensorComponentMap_norm_det w hw g]
  have hF : IsOpen (χF.ker : Set (GeneralLinear (r + 1) (v.adicCompletion F))) := by
    rw [← hF_eq]
    exact χ.finiteLocalHeckeDeterminant_isOpen_ker (r + 1) v
  have hE : IsOpen (χE.ker : Set (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E))) := by
    rw [← hE_eq]
    exact (χ'.finiteLocalHeckeDeterminant_isOpen_ker (r + 1) w.1).preimage
      (continuous_tensorComponentMap (r + 1) w)
  let π := (D.localComponent v).representation
  let τ₀ := (P.localComponent w.1).representation
  let τ := τ₀.comp ψ
  let eF : ((D.heckeDeterminantTwist χ).localComponent v).representation.Equiv (twist χF π) := by
    rw [← hF_eq]
    exact localTwistEquiv D χ v
  let eE₀ := localTwistEquiv P χ' w.1
  let eE : Representation.Equiv
      (((P.heckeDeterminantTwist χ').localComponent w.1).representation.comp ψ)
      (twist χE τ) := by
    rw [← hE_eq, ← twist_comp _ τ₀ ψ]
    exact Representation.Equiv.mk eE₀.toLinearEquiv
      (fun g => eE₀.toIntertwiningMap.isIntertwining' (ψ g))
  have hπχ := (isAdmissible_twist_iff χF π hF).mpr hπ
  have hcyc' := cyclicAlgebraBaseChange F E (v.adicCompletion F) σ l hcyc
  unfold CyclicBaseChangeEllipticConclusion at h ⊢
  obtain ⟨_, hid⟩ := h
  refine ⟨hπ, ?_⟩
  have htwist := hid.of_equiv (hπ' := hπχ) eF eE
  have key := htwist.of_determinantNormTwist (hπ := hπ) hcyc' ω hF hE hπχ
  dsimp only [tensorFactorAut, τ, ψ] at key
  with_reducible_and_instances exact key

end Twists

/-- The same-universe elliptic trace identity for realizations trivial on their
positive split centres. -/
def CyclicBaseChangeEllipticTraceIdentityOnSplitCentre : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsUnramifiedAtInfinitePlaces F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E) (l : ℕ), l.Prime → IsCyclicAlgebra σ l →
    ∀ (v : Langlands.Global.FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ q : FinitePlacesAbove E v, q = w) →
    ∀ (v' : Langlands.Global.FinitePlace F) (w' : FinitePlacesAbove E v'), v' ≠ v →
      (∀ q : FinitePlacesAbove E v', q = w') →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r) (T : CuspidalOperatorRealization E r)
      (P : CuspidalSpectralPresentation.{u, uW} T),
      IsTrivialOnSplitCentre S → IsTrivialOnSplitCentre T →
      (P.localComponent w.1).IsSupercuspidal → (P.localComponent w'.1).IsSupercuspidal →
      CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{u, u, uV, uW}
        T.isoClass S.isoClass →
    ∀ D : CuspidalSpectralPresentation.{u, uV} S,
      (D.localComponent v).IsIrreducible → (D.localComponent v).IsAdmissible →
      CyclicBaseChangeEllipticConclusion σ l v w P D

/-- The identity on the split-centre quotients implies the full identity for number
fields in a common universe. -/
def CyclicBaseChangeEllipticTraceIdentitySplitCentreReductionStatement : Prop :=
  CyclicBaseChangeEllipticTraceIdentityOnSplitCentre.{u, uV, uW} →
    CyclicBaseChangeEllipticTraceIdentityStatement.{u, u, uV, uW}

set_option maxHeartbeats 4000000 in
theorem cyclicBaseChangeEllipticTraceIdentity_of_splitCentre :
    CyclicBaseChangeEllipticTraceIdentitySplitCentreReductionStatement.{u, uV, uW} := by
  intro H
  apply cyclicBaseChangeEllipticTraceIdentity_iff_withConclusion.mpr
  intro F E _ _ _ _ _ _ _ _ σ l hl hcyc v w hw v' w' hv' hw' r S T P _ hsc hsc' hbc D hir hAd
  obtain ⟨s, hs, ht, hbc'⟩ := CuspidalOperatorRealization.weakBaseChangeSplitCentre F E r S T hbc
  let χ := HeckeCharacter.normPower F s
  let χ' := χ.normComp (L := E)
  let P' := P.heckeDeterminantTwist χ'
  let D' := D.heckeDeterminantTwist χ
  have hsc₁ := heckeDeterminantTwistSupercuspidal E T P χ' w.1 hsc
  have hsc₂ := heckeDeterminantTwistSupercuspidal E T P χ' w'.1 hsc'
  have hir' := (D.heckeDeterminantTwist_localComponent_isIrreducible_iff χ v).mpr hir
  have hAd' := (D.heckeDeterminantTwist_localComponent_isAdmissible_iff χ v).mpr hAd
  have hid := H F E σ l hl hcyc v w hw v' w' hv' hw' r
    (S.heckeDeterminantTwist χ) (T.heckeDeterminantTwist χ') P' hs ht hsc₁ hsc₂ hbc' D' hir' hAd'
  have key := CyclicBaseChangeEllipticConclusion.of_heckeDeterminantTwist hcyc w hw P D χ hAd hid
  with_reducible exact key

end Langlands.TraceFormula
