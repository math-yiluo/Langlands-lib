import Langlands.Global.Arithmetic.HarrisAuxiliaryConjugatePairStatement
import Langlands.Automorphic.CuspidalContragredientLocalCompatibilityProof
import Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentationProof
import Langlands.Automorphic.CuspidalPresentationUniverse
import Langlands.Automorphic.FiniteLocalCMTransport
import Langlands.Automorphic.Unramified.CyclicInductionSupercuspidalReduction
import Langlands.Representation.Classification.SupercuspidalContragredientProof
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport

/-!
# Supercuspidality at the conjugate place of a conjugate self-dual cuspidal class

Let `B` be a conjugate contragredient pairing of an irreducible cuspidal realization over a CM
field, and let `c` be the CM involution. After twisting by an operator that commutes with the
local group at `w`, `B` restricts to a nonzero pairing between the local component at `w` and
the local component at `c(w)`. This pairing is invariant when `GL_n(E_{c(w)})` acts on the
component at `w` through the completion isomorphism `E_{c(w)} ≅ E_w`. Both components are
irreducible, so the pulled-back component at `w` is the smooth dual of the component at `c(w)`.
Smooth duals of supercuspidal representations are supercuspidal, and supercuspidality is
invariant under pullback along an isomorphism of topological fields.
-/

noncomputable section

universe u uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic Langlands.Global.CMConjugation
open Langlands.Global.AdelicFunctoriality (finitePlaceEquiv finiteCompletionEquiv)
open Langlands.Global.FiniteAdelicGL (localInclusion)
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

/-- Complex conjugation of finite places is an involution. -/
theorem conjPlace_conjPlace (v : FinitePlace E) : conjPlace E (conjPlace E v) = v :=
  Langlands.Global.CMConjugation.finitePlaceComplexConj_involutive v

/-- Entrywise CM conjugation carries the local matrix at `c(w)` to the corresponding local
matrix at `w`. -/
theorem finiteConj_localInclusion_conjPlace (n : ℕ) (w : FinitePlace E)
    (g : FiniteLocalGL E n (finitePlaceEquiv (fieldConj E) w)) :
    finiteConj E n (localInclusion E n (finitePlaceEquiv (fieldConj E) w) g) =
      localInclusion E n w (AdelicGLTransport.localEquiv n (fieldConj E) w g) := by
  rw [← AdelicGLTransport.finiteEquiv_complexConj]
  exact AdelicGLTransport.finiteEquiv_localInclusion n (fieldConj E) w g

/-- A local component at `w` is supercuspidal when it pairs nondegenerately with a supercuspidal
local component at `c(w)`, the group at `c(w)` acting on it through the completion isomorphism
`E_{c(w)} ≅ E_w`. -/
theorem isSupercuspidal_of_conjPlace_pairing {r : ℕ} {w : FinitePlace E}
    (W : LocalRealization E (r + 1) w)
    (W' : LocalRealization E (r + 1) (finitePlaceEquiv (fieldConj E) w))
    (hI : W.IsIrreducible) (hW' : W'.IsSupercuspidal)
    (b : W.Space →ₗ[ℂ] W'.Space →ₗ[ℂ] ℂ)
    (hinv : ∀ (g : FiniteLocalGL E (r + 1) (finitePlaceEquiv (fieldConj E) w)) (y : W.Space)
      (x : W'.Space),
      b (W.representation (AdelicGLTransport.localEquiv (r + 1) (fieldConj E) w g) y)
        (W'.representation g x) = b y x)
    (hb : b ≠ 0) : W.IsSupercuspidal := by
  obtain ⟨hI', hA', hsc'⟩ := hW'
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
      ((padicField w').canonicalGeneralLinearTopology (r + 1)) W'.representation := by
    rw [← FiniteAdelicGL.localGL_topology_eq E w' (r + 1)]
    exact hA'
  have hρsc₀ : GeneralLinear.IsSupercuspidal (F := FiniteCompletion E w') (n := r + 1)
      W'.representation :=
    ((LocalRealization.isSupercuspidal_iff_representation W').mp ⟨hI', hA', hsc'⟩).2
  have hρsc : @GeneralLinear.IsSupercuspidal (FiniteCompletion E w') _
      (padicField w').canonicalTopologicalData.topology (r + 1) _ _ _ W'.representation :=
    (iff_of_eq (congrArg (fun t : TopologicalSpace (FiniteCompletion E w') =>
      @GeneralLinear.IsSupercuspidal (FiniteCompletion E w') _ t (r + 1) _ _ _
        W'.representation) (completion_topology_eq w'))).mp hρsc₀
  have hσsc : @GeneralLinear.IsSupercuspidal (FiniteCompletion E w') _
      (padicField w').canonicalTopologicalData.topology (r + 1) _ _ _ σ := by
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
    have hcontra := GeneralLinear.isSupercuspidal_smoothContragredient (padicField w') T (r + 1)
      W'.Space W'.representation hρsc
    exact GeneralLinear.isSupercuspidal_of_equiv Φ.symm hcontra
  have hσsc₀ : GeneralLinear.IsSupercuspidal (F := FiniteCompletion E w') (n := r + 1) σ :=
    (iff_of_eq (congrArg (fun t : TopologicalSpace (FiniteCompletion E w') =>
      @GeneralLinear.IsSupercuspidal (FiniteCompletion E w') _ t (r + 1) _ _ _ σ)
        (completion_topology_eq w'))).mpr hσsc
  have hWsc : GeneralLinear.IsSupercuspidal (F := FiniteCompletion E w) (n := r + 1)
      W.representation :=
    (GeneralLinear.isSupercuspidal_comp_fieldEquiv_iff (r + 1)
      (finiteCompletionEquiv (fieldConj E) w)
      (AdelicFunctoriality.continuous_finiteCompletionEquiv (fieldConj E) w)
      (AdelicFunctoriality.continuous_finiteCompletionEquiv_symm (fieldConj E) w)
      W.representation).mp hσsc₀
  exact (LocalRealization.isSupercuspidal_iff_representation W).mpr ⟨hI, hWsc⟩

variable [CompactSpace (AdeleQuotient E)]

/-- A conjugate contragredient pairing gives, after twisting by an operator commuting with the
local group at `w`, a nonzero pairing between an embedded local subspace `W` at `w` and an
embedded local subspace `W'` at `c(w)`, invariant when `GL_n(E_{c(w)})` acts on `W` through the
completion isomorphism `E_{c(w)} ≅ E_w`. -/
theorem exists_conjPlace_localInvariantPairing {r : ℕ} (S : CuspidalOperatorRealization E r)
    {B : S.realization.Space →ₗ[ℂ] S.realization.Space →ₗ[ℂ] ℂ}
    (hB : S.realization.IsConjugateInvariantPairing B) (hinj : Function.Injective B.flip)
    {w : FinitePlace E} (W : LocalRealization E (r + 1) w)
    (W' : LocalRealization E (r + 1) (finitePlaceEquiv (fieldConj E) w))
    (hW : W.toSubmodule ≤ S.realization.toFiniteRealization.toSubmodule)
    (hW' : W'.toSubmodule ≤ S.realization.toFiniteRealization.toSubmodule)
    (hW0 : W ≠ ⊥) (hW'0 : W' ≠ ⊥) :
    ∃ b : W.Space →ₗ[ℂ] W'.Space →ₗ[ℂ] ℂ,
      (∀ (g : FiniteLocalGL E (r + 1) (finitePlaceEquiv (fieldConj E) w)) (y : W.Space)
        (x : W'.Space),
        b (W.representation (AdelicGLTransport.localEquiv (r + 1) (fieldConj E) w g) y)
          (W'.representation g x) = b y x) ∧ b ≠ 0 := by
  have hx'0 := LocalRealization.exists_ne_zero_of_ne_bot hW'0
  obtain ⟨x', hx'⟩ := hx'0
  have hl : B.flip (S.realization.localLift W' hW' x') ≠ 0 := by
    intro h
    apply hx'
    apply S.realization.localLift_injective W' hW'
    apply hinj
    exact h.trans ((LinearMap.map_zero B.flip).symm.trans
      (congrArg B.flip (LinearMap.map_zero (S.realization.localLift W' hW')).symm))
  have htw := S.realization.exists_twist_ne_zero W hW S.irreducible hW0 _ hl
  obtain ⟨a, ha, x, hax⟩ := htw
  let f : W.Space →ₗ[ℂ] S.realization.Space :=
    S.realization.representation a ∘ₗ S.realization.localLift W hW
  let b : W.Space →ₗ[ℂ] W'.Space →ₗ[ℂ] ℂ := B.compl₁₂ f (S.realization.localLift W' hW')
  have hb : ∀ y x', b y x' = B (S.realization.representation a
      (S.realization.localLift W hW y)) (S.realization.localLift W' hW' x') := fun _ _ => rfl
  refine ⟨b, ?_, ?_⟩
  · intro g y x''
    have h1 := (congrArg (S.realization.representation a)
      (S.realization.localLift_representation W hW
        (AdelicGLTransport.localEquiv (r + 1) (fieldConj E) w g) y)).trans
      (S.realization.representation_commute ha _ (S.realization.localLift W hW y))
    have h2 := S.realization.localLift_representation W' hW' g x''
    have h3 := congrArg (fun d => S.realization.representation (finiteOperator E (r + 1) d)
      (S.realization.representation a (S.realization.localLift W hW y)))
      (finiteConj_localInclusion_conjPlace (r + 1) w g).symm
    exact (hb _ _).trans ((congrArg₂ (fun p q => B p q) (h1.trans h3) h2).trans
      ((hB.1 _ _ _).trans (hb y x'').symm))
  · intro h
    apply hax
    exact (hb x x').symm.trans ((LinearMap.congr_fun (LinearMap.congr_fun h x) x').trans
      ((LinearMap.congr_fun (LinearMap.zero_apply x) x').trans (LinearMap.zero_apply x')))

/-- If a conjugate self-dual cuspidal class has a supercuspidal component at `c(w)`, it has one
at `w`. -/
theorem hasSupercuspidalComponent_of_conjPlace {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass E r) (w : FinitePlace E)
    (hc : c.IsConjugateSelfDual)
    (h : c.HasSupercuspidalComponent.{u, uV} (finitePlaceEquiv (fieldConj E) w)) :
    c.HasSupercuspidalComponent.{u, uV} w := by
  obtain ⟨S, P, hS, hP⟩ := h
  subst hS
  have hcsd := (S.isoClass_isConjugateSelfDual_iff).mp hc
  obtain ⟨B, hBinv, -, hBinj, -⟩ := hcsd
  have hQ₀ := cuspidalAllLocalIrreduciblePresentationExistence E r S P
  obtain ⟨Q₀, hQ₀⟩ := hQ₀
  have hQ : ∃ Q : CuspidalSpectralPresentation.{u, uV} S,
      ∀ v, (Q.localComponent v).IsIrreducible ∧ (Q.localComponent v).IsAdmissible :=
    Q₀.exists_small hQ₀
  obtain ⟨Q, hQ⟩ := hQ
  refine ⟨S, Q, rfl, ?_⟩
  have hW : (Q.localComponent w).toSubmodule ≤
      S.realization.toFiniteRealization.toSubmodule := fun f hf =>
    Q.finiteSlice.le_image (Q.presentation.localComponent_le Q.finiteSlice.nonzero w hf)
  have hW' : (P.localComponent (finitePlaceEquiv (fieldConj E) w)).toSubmodule ≤
      S.realization.toFiniteRealization.toSubmodule := fun f hf =>
    P.finiteSlice.le_image (P.presentation.localComponent_le P.finiteSlice.nonzero _ hf)
  have hpair := exists_conjPlace_localInvariantPairing S hBinv hBinj (Q.localComponent w)
    (P.localComponent (finitePlaceEquiv (fieldConj E) w)) hW hW'
    (Q.localComponent_ne_bot w) (P.localComponent_ne_bot _)
  obtain ⟨b, hinv, hb⟩ := hpair
  exact isSupercuspidal_of_conjPlace_pairing (Q.localComponent w)
    (P.localComponent (finitePlaceEquiv (fieldConj E) w)) (hQ w).1 hP b hinv hb

/-- A conjugate self-dual cuspidal class over a CM field with a supercuspidal component at a
finite place `v` has a supercuspidal component at the conjugate place `conjPlace E v`, in the
same factor universe. -/
theorem conjugateSelfDualSupercuspidalConjPlace :
    ConjugateSelfDualSupercuspidalConjPlaceStatement.{u, uV} := by
  intro E _ _ _ _ r c v hc h
  apply hasSupercuspidalComponent_of_conjPlace c (conjPlace E v) hc
  change c.HasSupercuspidalComponent.{u, uV} (conjPlace E (conjPlace E v))
  rw [conjPlace_conjPlace]
  exact h

end Langlands.Global.Harris
