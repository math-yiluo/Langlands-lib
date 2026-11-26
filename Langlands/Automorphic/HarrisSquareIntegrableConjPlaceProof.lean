import Langlands.Automorphic.HarrisSquareIntegrableConjPlaceStatement
import Langlands.Global.Arithmetic.HarrisConjugateSelfDualSupercuspidalConjPlaceProof
import Langlands.BaseChange.PadicSquareIntegrableNotInduced
import Langlands.Representation.Classification.InverseTransposeAnalyticProof

/-!
# Square-integrability at the conjugate place of a conjugate self-dual cuspidal realization

Let `B` be a conjugate contragredient pairing of an irreducible cuspidal realization over a CM
field with CM involution `c`. For a spectral presentation of the realization, `B` gives a nonzero
pairing between the local component at `w` and the local component at `c(w)`, invariant when
`GL_n(E_{c(w)})` acts on the component at `w` through the completion isomorphism
`E_{c(w)} ≅ E_w`. When the component at `w` is irreducible and the component at `c(w)` is
square-integrable, the pulled-back component at `w` is the smooth dual of the component at
`c(w)`. Smooth duals of square-integrable representations are square-integrable, and
square-integrability modulo the center is invariant under pullback along an isomorphism of
topological fields.
-/

noncomputable section

universe u uV uF uF' uW

set_option autoImplicit false

namespace Langlands.PadicField.TopologicalData

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {F : PadicField.{uF} p}
  {F' : PadicField.{uF'} q} (T : F.TopologicalData) (T' : F'.TopologicalData) (n : ℕ)
  {V : Type uW} [AddCommGroup V] [Module ℂ V]

/-- Square-integrability modulo the center pulls back along the entrywise transport by an
isomorphism of the topological fields. -/
theorem isSquareIntegrable_comp_fieldEquiv (σ : F'.Carrier ≃+* F.Carrier)
    (hσ : @Continuous F'.Carrier F.Carrier T'.topology T.topology σ)
    (hσs : @Continuous F.Carrier F'.Carrier T.topology T'.topology σ.symm)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : T.IsSquareIntegrable ρ) :
    T'.IsSquareIntegrable (ρ.comp
      (@GeneralLinear.fieldEquiv F'.Carrier F.Carrier _ _ T'.topology T.topology n σ hσ
        hσs).toMonoidHom) := by
  let := T.topology
  let := T'.topology
  have := T.generalLinearTopologicalGroup n
  have := T'.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  let := T'.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  have := T'.centralQuotientBorelSpace n
  intro μ hμ
  exact isSquareIntegrableModCenter_comp_continuousMulEquiv ρ
    (GeneralLinear.fieldEquiv n σ hσ hσs) μ (hρ _)

/-- Square-integrability modulo the center is preserved and reflected by pullback along the
entrywise transport by an isomorphism of the topological fields. -/
theorem isSquareIntegrable_comp_fieldEquiv_iff (σ : F'.Carrier ≃+* F.Carrier)
    (hσ : @Continuous F'.Carrier F.Carrier T'.topology T.topology σ)
    (hσs : @Continuous F.Carrier F'.Carrier T.topology T'.topology σ.symm)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    T'.IsSquareIntegrable (ρ.comp
      (@GeneralLinear.fieldEquiv F'.Carrier F.Carrier _ _ T'.topology T.topology n σ hσ
        hσs).toMonoidHom) ↔ T.IsSquareIntegrable ρ := by
  refine ⟨fun h => ?_, isSquareIntegrable_comp_fieldEquiv T T' n σ hσ hσs ρ⟩
  have h' := isSquareIntegrable_comp_fieldEquiv T' T n σ.symm hσs hσ _ h
  let := T.topology
  let := T'.topology
  have heq : (ρ.comp (GeneralLinear.fieldEquiv n σ hσ hσs).toMonoidHom).comp
      (GeneralLinear.fieldEquiv n σ.symm hσs hσ).toMonoidHom = ρ := by
    apply MonoidHom.ext
    intro g
    exact congrArg ρ ((GeneralLinear.fieldEquiv n σ hσ hσs).apply_symm_apply g)
  rwa [heq] at h'

end Langlands.PadicField.TopologicalData

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic Langlands.Global.CMConjugation
open Langlands.Global.AdelicFunctoriality (finitePlaceEquiv finiteCompletionEquiv)
open Langlands.Global.CompletionPadic

variable {E : Type u} [Field E] [NumberField E] [IsCMField E]

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions E n) :=
  Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions E n) :=
  Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions E n) :=
  Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms E n) :=
  Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions E n) :=
  Submodule.addCommGroup _
private local instance {n : ℕ} (S : OperatorRealization E n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _
private local instance {n : ℕ} {v : FinitePlace E} (S : LocalRealization E n v) :
    AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- A local component at `w` is square-integrable when it is irreducible and pairs
nondegenerately with a square-integrable local component at `c(w)`, the group at `c(w)` acting
on it through the completion isomorphism `E_{c(w)} ≅ E_w`. -/
theorem isSquareIntegrable_of_conjPlace_pairing {r : ℕ} {w : FinitePlace E}
    (W : LocalRealization E (r + 1) w)
    (W' : LocalRealization E (r + 1) (finitePlaceEquiv (fieldConj E) w))
    (hI : W.IsIrreducible) (hW' : W'.IsSquareIntegrable)
    (b : W.Space →ₗ[ℂ] W'.Space →ₗ[ℂ] ℂ)
    (hinv : ∀ (g : FiniteLocalGL E (r + 1) (finitePlaceEquiv (fieldConj E) w)) (y : W.Space)
      (x : W'.Space),
      b (W.representation (AdelicGLTransport.localEquiv (r + 1) (fieldConj E) w g) y)
        (W'.representation g x) = b y x)
    (hb : b ≠ 0) : W.IsSquareIntegrable := by
  obtain ⟨hI', hsq'⟩ := hW'
  let w' := finitePlaceEquiv (fieldConj E) w
  let α := AdelicGLTransport.localEquiv (r + 1) (fieldConj E) w
  let σ : Representation ℂ (FiniteLocalGL E (r + 1) w') W.Space :=
    W.representation.comp α.toMonoidHom
  have hσI : σ.IsIrreducible :=
    (Langlands.isIrreducible_comp_continuousMulEquiv_iff W.representation α).mpr hI
  have hleft := invariantPairing_left_nondegenerate hσI b hinv hb
  have hright := invariantPairing_right_nondegenerate (σ := σ) hI' b hinv hb
  have hσS : Langlands.IsSmooth σ :=
    Langlands.isSmooth_comp α.toMonoidHom α.continuous W.isSmooth
  have hσSc : @Langlands.IsSmooth ℂ (FiniteLocalGL E (r + 1) w') W.Space _ _ _ _
      ((padicField w').canonicalGeneralLinearTopology (r + 1)) σ := by
    rw [← FiniteAdelicGL.localGL_topology_eq E w' (r + 1)]
    exact hσS
  have hρA : @Langlands.IsAdmissible ℂ (FiniteLocalGL E (r + 1) w') W'.Space _ _ _ _
      ((padicField w').canonicalGeneralLinearTopology (r + 1)) W'.representation :=
    hsq'.isAdmissible
  have hσsq : (padicField w').canonicalTopologicalData.IsSquareIntegrable σ := by
    let T := (padicField w').canonicalTopologicalData
    let := T.topology
    let _ : TopologicalSpace (Langlands.GeneralLinear (r + 1) (padicField w').Carrier) :=
      (padicField w').canonicalGeneralLinearTopology (r + 1)
    let _ : IsTopologicalGroup (Langlands.GeneralLinear (r + 1) (padicField w').Carrier) :=
      (padicField w').canonicalGeneralLinearTopologicalGroup (r + 1)
    have hE := smoothInvariantPairingDuality
      (GeneralLinear.compactOpen_cofinal (padicField w') T (r + 1))
      W'.representation σ hρA hσSc b hinv hleft hright
    obtain ⟨Φ, -⟩ := hE
    have hcontra := T.isSquareIntegrable_smoothContragredient W'.representation hsq'
    exact (T.isSquareIntegrable_iff_of_equiv Φ).mpr hcontra
  have hc : @Continuous (FiniteCompletion E w') (FiniteCompletion E w)
      (padicField w').canonicalTopologicalData.topology
      (padicField w).canonicalTopologicalData.topology
      (finiteCompletionEquiv (fieldConj E) w) := by
    rw [← completion_topology_eq w', ← completion_topology_eq w]
    exact AdelicFunctoriality.continuous_finiteCompletionEquiv (fieldConj E) w
  have hcs : @Continuous (FiniteCompletion E w) (FiniteCompletion E w')
      (padicField w).canonicalTopologicalData.topology
      (padicField w').canonicalTopologicalData.topology
      (finiteCompletionEquiv (fieldConj E) w).symm := by
    rw [← completion_topology_eq w', ← completion_topology_eq w]
    exact AdelicFunctoriality.continuous_finiteCompletionEquiv_symm (fieldConj E) w
  exact ⟨hI, (PadicField.TopologicalData.isSquareIntegrable_comp_fieldEquiv_iff
    (padicField w).canonicalTopologicalData (padicField w').canonicalTopologicalData (r + 1)
    (finiteCompletionEquiv (fieldConj E) w) hc hcs W.representation).mp hσsq⟩

variable [CompactSpace (AdeleQuotient E)]

/-- For a spectral presentation of a conjugate self-dual cuspidal realization, an irreducible
local component at `w` is square-integrable when the local component of the same presentation
at `c(w)` is square-integrable. -/
theorem isSquareIntegrable_localComponent_of_conjPlace {r : ℕ}
    (S : CuspidalOperatorRealization E r) (P : CuspidalSpectralPresentation.{u, uV} S)
    (w : FinitePlace E) (hI : (P.localComponent w).IsIrreducible)
    (hS : S.isoClass.IsConjugateSelfDual)
    (h : (P.localComponent (finitePlaceEquiv (fieldConj E) w)).IsSquareIntegrable) :
    (P.localComponent w).IsSquareIntegrable := by
  obtain ⟨B, hBinv, -, hBinj, -⟩ := (S.isoClass_isConjugateSelfDual_iff).mp hS
  have hW : (P.localComponent w).toSubmodule ≤
      S.realization.toFiniteRealization.toSubmodule := fun f hf =>
    P.finiteSlice.le_image (P.presentation.localComponent_le P.finiteSlice.nonzero w hf)
  have hW' : (P.localComponent (finitePlaceEquiv (fieldConj E) w)).toSubmodule ≤
      S.realization.toFiniteRealization.toSubmodule := fun f hf =>
    P.finiteSlice.le_image (P.presentation.localComponent_le P.finiteSlice.nonzero _ hf)
  obtain ⟨b, hinv, hb⟩ := exists_conjPlace_localInvariantPairing S hBinv hBinj
    (P.localComponent w) (P.localComponent (finitePlaceEquiv (fieldConj E) w)) hW hW'
    (P.localComponent_ne_bot w) (P.localComponent_ne_bot _)
  exact isSquareIntegrable_of_conjPlace_pairing (P.localComponent w)
    (P.localComponent (finitePlaceEquiv (fieldConj E) w)) hI h b hinv hb

end Langlands.Global.Harris

namespace Langlands.Global.Harris

/-- Over a CM field, a square-integrable component at `v` of a spectral presentation, with
irreducible admissible components at every finite place, of a conjugate self-dual cuspidal
realization gives a square-integrable component of the same presentation at `conjPlace E v`. -/
theorem harrisSquareIntegrableConjPlace :
    HarrisSquareIntegrableConjPlaceStatement.{u, uV} := by
  intro E _ _ _ _ r S P v hP hc hv
  apply isSquareIntegrable_localComponent_of_conjPlace S P (conjPlace E v) (hP _).1 hc
  change (P.localComponent (conjPlace E (conjPlace E v))).IsSquareIntegrable
  rw [conjPlace_conjPlace]
  exact hv

end Langlands.Global.Harris
