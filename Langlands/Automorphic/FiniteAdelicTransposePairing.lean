import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
import Langlands.Representation.Smooth.Contragredient.TwistedPairing
import Langlands.Representation.RestrictedTensor.Pairing
import Langlands.Global.RankinSelberg.ContragredientDualSpherical
import Mathlib.LinearAlgebra.BilinearForm.Hom

/-! # Nonzero inverse-transpose forms for irreducible admissible finite adelic representations -/

noncomputable section
universe uF uV
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Langlands.Global.FiniteAdelicGL.TransposePairing

open Langlands Langlands.Global Langlands.RestrictedTensor NumberField IsDedekindDomain
open scoped TensorProduct

variable {F : Type uF} [Field F] [NumberField F]

/-- The published local GK equivalence uses the actual completion topology. -/
theorem localDualEquiv (v : FinitePlace F) (r : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteLocalGL F (r + 1) v) V)
    (hA : IsAdmissible ρ) (hI : ρ.IsIrreducible) :
    ∃ E : V ≃ₗ[ℂ] SmoothDual ρ, ∀ g x,
      E (ρ (GeneralLinear.inverseTranspose (r + 1) (FiniteCompletion F v) g) x) =
        smoothContragredient ρ g (E x) := by
  have key : ∀ (τ : TopologicalSpace (FiniteLocalGL F (r + 1) v))
      (hτg : @IsTopologicalGroup (FiniteLocalGL F (r + 1) v) τ _),
      τ = (CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1) →
      letI := τ
      letI := hτg
      ∀ (σ : Representation ℂ (FiniteLocalGL F (r + 1) v) V),
        IsAdmissible σ → σ.IsIrreducible →
        ∃ E : V ≃ₗ[ℂ] SmoothDual σ, ∀ g x,
          E (σ (GeneralLinear.inverseTranspose (r + 1) (FiniteCompletion F v) g) x) =
            smoothContragredient σ g (E x) := by
    intro τ hτg hτ
    subst τ
    intro σ hσA hσI
    exact gelfandKazhdanContragredient (CompletionPadic.residuePrime v) inferInstance
      (CompletionPadic.padicField v) r V σ hσA hσI
  exact key _ inferInstance (localGL_topology_eq F v (r + 1)) ρ hA hI

/-- Every actual finite-place irreducible admissible factor has a nonzero transpose form. -/
def localPairing (v : FinitePlace F) (r : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteLocalGL F (r + 1) v) V)
    (hA : IsAdmissible ρ) (hI : ρ.IsIrreducible) :
    {C : V →ₗ[ℂ] V →ₗ[ℂ] ℂ //
      (∀ g x y, C (ρ g x)
        (ρ (GeneralLinear.inverseTranspose (r + 1) (FiniteCompletion F v) g) y) = C x y) ∧
      C ≠ 0} := by
  let h := localDualEquiv v r V ρ hA hI
  let E := Classical.choose h
  have hE := Classical.choose_spec h
  letI := hI
  letI : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (FiniteLocalGL F (r + 1) v)) ρ.asModule
  exact ⟨SmoothTwistedPairing.form ρ E,
    SmoothTwistedPairing.form_invariant ρ _ E hE, SmoothTwistedPairing.form_ne_zero ρ E⟩

/-- At a spherical place the form can be normalized on the prescribed reference. -/
def normalizedLocalPairing (v : FinitePlace F) (r : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteLocalGL F (r + 1) v) V)
    (hA : IsAdmissible ρ) (hI : ρ.IsIrreducible)
    (e : fixedVectors ρ (localIntegral F (r + 1) v).toSubgroup) (he : e ≠ 0)
    (hdim : Module.finrank ℂ (fixedVectors ρ (localIntegral F (r + 1) v).toSubgroup) = 1) :
    {C : V →ₗ[ℂ] V →ₗ[ℂ] ℂ //
      (∀ g x y, C (ρ g x)
        (ρ (GeneralLinear.inverseTranspose (r + 1) (FiniteCompletion F v) g) y) = C x y) ∧
      C ≠ 0 ∧ C e.val e.val = 1} := by
  let h := localDualEquiv v r V ρ hA hI
  let E := Classical.choose h
  have hE := Classical.choose_spec h
  letI := hA.2 (localIntegral F (r + 1) v)
  have hspan : ∀ w : fixedVectors ρ (localIntegral F (r + 1) v).toSubgroup,
      ∃ c : ℂ, c • e = w :=
    (finrank_eq_one_iff_of_nonzero' e he).mp hdim
  exact SmoothTwistedPairing.normalizedPairing ρ _ E hE hA.1
    (localIntegral F (r + 1) v) (localGL_flathTopology (F := F) v r).2.2.2
    (fun g hg => RankinSelbergGlobal.ContragredientDual.inverseTranspose_mem_localIntegral
      F (r + 1) v hg) e he hspan

/-- Local GK and actual Flath factorization produce the finite adelic transpose form. -/
theorem exists_pairing (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteAdelicGL F (r + 1)) V)
    (hA : IsAdmissible ρ) (hI : ρ.IsIrreducible) :
    ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
      (∀ d x y, B (ρ d x)
        (ρ (GeneralLinear.inverseTranspose (r + 1) (FiniteAdeleRing (𝓞 F) F) d) y) = B x y) ∧
      B ≠ 0 := by
  classical
  have htop := fun v => localGL_flathTopology (F := F) v r
  let : ∀ v, T2Space (FiniteLocalGL F (r + 1) v) := fun v => (htop v).1
  let : ∀ v, LocallyCompactSpace (FiniteLocalGL F (r + 1) v) := fun v => (htop v).2.1
  let : ∀ v, TotallyDisconnectedSpace (FiniteLocalGL F (r + 1) v) :=
    fun v => (htop v).2.2.1
  let : ∀ v, MeasurableSpace (FiniteLocalGL F (r + 1) v) := fun v => borel _
  let : ∀ v, BorelSpace (FiniteLocalGL F (r + 1) v) := fun v => ⟨rfl⟩
  choose μ hμH hμR hμC using fun v => localGL_exists_sphericalHeckeCommutative (F := F) v r
  let : ∀ v, (μ v).IsHaarMeasure := hμH
  let : ∀ v, (μ v).Regular := hμR
  let H : ∀ v, Subgroup (FiniteLocalGL F (r + 1) v) :=
    fun v => (localIntegral F (r + 1) v).toSubgroup
  let π : Representation ℂ
      (RestrictedGroup (fun v => FiniteLocalGL F (r + 1) v) H) V :=
    ρ.comp (restrictedProductEquiv F (r + 1)).symm.toMonoidHom
  have hπA : IsAdmissible π :=
    isAdmissible_comp_continuousMulEquiv ρ (restrictedProductEquiv F (r + 1)).symm hA
  have hπI : π.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff ρ
      (restrictedProductEquiv F (r + 1)).symm).mpr hI
  obtain ⟨W, σ, hσ, E, refs, hfix, hdim, ⟨eq⟩⟩ :=
    flathRestrictedProductExistence (FinitePlace F)
      (fun v => FiniteLocalGL F (r + 1) v) μ H V π
      (fun v => ⟨(localIntegral F (r + 1) v).isOpen, (htop v).2.2.2⟩)
      (Filter.Eventually.of_forall hμC) hπA hπI
  have hlocal : ∀ v, ∃ C : W v →ₗ[ℂ] W v →ₗ[ℂ] ℂ,
      (∀ g x y, C (σ v g x)
        (σ v (GeneralLinear.inverseTranspose (r + 1) (FiniteCompletion F v) g) y) = C x y) ∧
      C ≠ 0 ∧ ∀ hv : v ∉ E, C (refs.vector v hv) (refs.vector v hv) = 1 := by
    intro v
    by_cases hv : v ∈ E
    · let C := localPairing v r (W v) (σ v) (hσ v).1 (hσ v).2
      exact ⟨C.val, C.property.1, C.property.2, fun h => False.elim (h hv)⟩
    · let e : fixedVectors (σ v) (localIntegral F (r + 1) v).toSubgroup :=
        ⟨refs.vector v hv, fun k => hfix v hv k.val k.property⟩
      have he : e ≠ 0 := fun h => refs.nonzero v hv (congrArg Subtype.val h)
      let C := normalizedLocalPairing v r (W v) (σ v) (hσ v).1 (hσ v).2 e he (hdim v hv)
      exact ⟨C.val, C.property.1, C.property.2.1, fun _ => C.property.2.2⟩
  choose C hCi hC0 hCref using hlocal
  have hnorm : ∀ v ∉ E, C v (refs.family v) (refs.family v) = 1 := by
    intro v hv
    simpa only [ReferenceVectors.family_of_not_mem refs hv] using hCref v hv
  have href : ∀ v ∉ E, ∀ g ∈ H v, σ v g (refs.family v) = refs.family v := by
    intro v hv g hg
    simpa only [ReferenceVectors.family_of_not_mem refs hv] using hfix v hv g hg
  let B := Pairing.form C E refs.family hnorm
  let e := eq.symm.toLinearEquiv
  refine ⟨LinearMap.BilinForm.congr e B, ?_, ?_⟩
  · intro d x y
    let g := restrictedProductEquiv F (r + 1) d
    let g' := restrictedProductEquiv F (r + 1)
      (GeneralLinear.inverseTranspose (r + 1) (FiniteAdeleRing (𝓞 F) F) d)
    have heq (d : FiniteAdelicGL F (r + 1)) (x : V) :
        eq (ρ d x) = productRepresentation H σ E refs hfix
          (restrictedProductEquiv F (r + 1) d) (eq x) := by
      have h := Representation.IntertwiningMap.isIntertwining _ _ eq.toIntertwiningMap
        (restrictedProductEquiv F (r + 1) d) x
      change eq (ρ ((restrictedProductEquiv F (r + 1)).symm
        (restrictedProductEquiv F (r + 1) d)) x) = _ at h
      rw [ContinuousMulEquiv.symm_apply_apply] at h
      exact h
    change B (eq (ρ d x))
      (eq (ρ (GeneralLinear.inverseTranspose (r + 1) (FiniteAdeleRing (𝓞 F) F) d) y)) =
      B (eq x) (eq y)
    rw [heq, heq]
    exact Pairing.form_map_invariant C E refs.family hnorm
      (fun v => σ v (g v)) (fun v => σ v (g' v))
      (action_preserves H σ E refs.family href g)
      (action_preserves H σ E refs.family href g')
      (fun v a b => by
        have hproj : g' v =
            GeneralLinear.inverseTranspose (r + 1) (FiniteCompletion F v) (g v) :=
          RankinSelbergGlobal.ContragredientDual.localProjection_inverseTranspose
            F (r + 1) v d
        rw [hproj]
        exact hCi v (g v) a b) (eq x) (eq y)
  · intro hzero
    apply Pairing.form_ne_zero C E refs.family hnorm hC0
    exact (LinearMap.BilinForm.congr e).injective (hzero.trans (map_zero _).symm)

/-- A chosen nonzero form for every irreducible admissible finite adelic representation. -/
def pairing (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteAdelicGL F (r + 1)) V)
    (hA : IsAdmissible ρ) (hI : ρ.IsIrreducible) :
    {B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ //
      (∀ d x y, B (ρ d x)
        (ρ (GeneralLinear.inverseTranspose (r + 1) (FiniteAdeleRing (𝓞 F) F) d) y) = B x y) ∧
      B ≠ 0} :=
  ⟨Classical.choose (exists_pairing r V ρ hA hI),
    Classical.choose_spec (exists_pairing r V ρ hA hI)⟩

end Langlands.Global.FiniteAdelicGL.TransposePairing
