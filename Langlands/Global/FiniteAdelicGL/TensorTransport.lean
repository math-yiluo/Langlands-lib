import Langlands.Global.FiniteAdelicGL.RestrictedTensor
import Langlands.Global.AdelicGLTransport
import Langlands.Representation.RestrictedTensor.ReindexAction

/-! # Arithmetic transport of actual finite adelic tensor representations -/

noncomputable section
open scoped Classical TensorProduct
universe uK uL uA uV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.FiniteAdelicGL

open AdelicFunctoriality AdelicGLTransport Langlands.RestrictedTensor

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]
variable {A : Type uA} [Field A] {n : ℕ}
variable {V : FinitePlace K → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module A (V v)]

/-- The new local model is the old model at the actual pulled-back finite place. -/
def transportFactors (a : K ≃+* L)
    (ρ : ∀ v, Representation A (FiniteLocalGL K n v) (V v)) :
    ∀ v, Representation A (FiniteLocalGL L n v) (V (finitePlaceEquiv a v)) :=
  fun v => (ρ (finitePlaceEquiv a v)).comp (localEquiv n a v).symm.toMonoidHom

/-- New exceptional places are exactly the images of the original ones. -/
def transportExceptional (a : K ≃+* L) (E : Finset (FinitePlace K)) :
    Finset (FinitePlace L) := E.map (finitePlaceEquiv a).symm.toEmbedding

omit [NumberField K] [NumberField L] in
@[simp]
theorem transportExceptional_map (a : K ≃+* L) (E : Finset (FinitePlace K)) :
    (transportExceptional a E).map (finitePlaceEquiv a).toEmbedding = E := by
  ext v
  simp [transportExceptional]

/-- Actual local completion transport preserves integral fixed reference vectors. -/
theorem transportReference_fixed (a : K ≃+* L)
    (ρ : ∀ v, Representation A (FiniteLocalGL K n v) (V v))
    (E : Finset (FinitePlace K)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral K n v, ρ v g (e v) = e v)
    (v : FinitePlace L) (hv : v ∉ transportExceptional a E)
    (g : FiniteLocalGL L n v) (hg : g ∈ localIntegral L n v) :
    transportFactors a ρ v g (e (finitePlaceEquiv a v)) = e (finitePlaceEquiv a v) := by
  apply he (finitePlaceEquiv a v)
  · simpa only [transportExceptional, Finset.mem_map_equiv, Equiv.symm_symm] using hv
  · exact (localEquiv_mem_localIntegral_iff n a v ((localEquiv n a v).symm g)).mp
      (by simpa only [ContinuousMulEquiv.apply_symm_apply] using hg)

private theorem mappedReference_fixed (a : K ≃+* L)
    (ρ : ∀ v, Representation A (FiniteLocalGL K n v) (V v))
    (E : Finset (FinitePlace L)) (e : ∀ v, V v)
    (he : ∀ v ∉ E.map (finitePlaceEquiv a).toEmbedding,
      ∀ g ∈ localIntegral K n v, ρ v g (e v) = e v)
    (v : FinitePlace L) (hv : v ∉ E)
    (g : FiniteLocalGL L n v) (hg : g ∈ localIntegral L n v) :
    transportFactors a ρ v g (e (finitePlaceEquiv a v)) = e (finitePlaceEquiv a v) := by
  apply he (finitePlaceEquiv a v)
  · simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hv
  · exact (localEquiv_mem_localIntegral_iff n a v ((localEquiv n a v).symm g)).mp
      (by simpa only [ContinuousMulEquiv.apply_symm_apply] using hg)

private def tensorTransportEquivMapped (a : K ≃+* L)
    (ρ : ∀ v, Representation A (FiniteLocalGL K n v) (V v))
    (E : Finset (FinitePlace L)) (e : ∀ v, V v)
    (he : ∀ v ∉ E.map (finitePlaceEquiv a).toEmbedding,
      ∀ g ∈ localIntegral K n v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E.map (finitePlaceEquiv a).toEmbedding, e v ≠ 0) :
    Representation.Equiv
      ((tensorRepresentation L n (transportFactors a ρ) E
        (fun v => e (finitePlaceEquiv a v)) (mappedReference_fixed a ρ E e he)).comp
          (finiteEquiv n a).toMonoidHom)
      (tensorRepresentation K n ρ (E.map (finitePlaceEquiv a).toEmbedding) e he) :=
  Representation.Equiv.mk (reindex (finitePlaceEquiv a) E e hne) (fun g => by
    have hlocal : (fun v => transportFactors a ρ v
        (localProjection L n v (finiteEquiv n a g))) =
        (fun v => ρ (finitePlaceEquiv a v) (localProjection K n (finitePlaceEquiv a v) g)) := by
      funext v
      change ρ (finitePlaceEquiv a v)
        ((localEquiv n a v).symm (localProjection L n v (finiteEquiv n a g))) = _
      rw [localProjection_finiteEquiv, ContinuousMulEquiv.symm_apply_apply]
    change (reindexMap (finitePlaceEquiv a) E e).comp
      (map E E (fun v => e (finitePlaceEquiv a v)) (fun v => e (finitePlaceEquiv a v))
        (fun v => transportFactors a ρ v (localProjection L n v (finiteEquiv n a g))) _) =
      (map (E.map (finitePlaceEquiv a).toEmbedding) (E.map (finitePlaceEquiv a).toEmbedding)
        e e (fun v => ρ v (localProjection K n v g)) _).comp
          (reindexMap (finitePlaceEquiv a) E e)
    simp only [hlocal]
    exact reindexMap_natural (finitePlaceEquiv a) E E e e
      (fun v => ρ v (localProjection K n v g))
      (action_preserves (fun v => (localIntegral K n v).toSubgroup) ρ
        (E.map (finitePlaceEquiv a).toEmbedding) e he (restrictedProductEquiv K n g)))

private def tensorTransportEquivOfMap (a : K ≃+* L)
    (ρ : ∀ v, Representation A (FiniteLocalGL K n v) (V v))
    (E : Finset (FinitePlace K)) (Enew : Finset (FinitePlace L)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral K n v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0)
    (henew : ∀ v ∉ Enew, ∀ g ∈ localIntegral L n v,
      transportFactors a ρ v g (e (finitePlaceEquiv a v)) = e (finitePlaceEquiv a v))
    (hE : Enew.map (finitePlaceEquiv a).toEmbedding = E) :
    Representation.Equiv
      ((tensorRepresentation L n (transportFactors a ρ) Enew
        (fun v => e (finitePlaceEquiv a v)) henew).comp (finiteEquiv n a).toMonoidHom)
      (tensorRepresentation K n ρ E e he) := by
  subst E
  exact tensorTransportEquivMapped a ρ Enew e he hne

/-- Reindexing gives a genuine equivalence of the actual finite adelic tensor
representations, after pulling the transported action back by arithmetic transport. -/
def tensorTransportEquiv (a : K ≃+* L)
    (ρ : ∀ v, Representation A (FiniteLocalGL K n v) (V v))
    (E : Finset (FinitePlace K)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral K n v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0) :
    Representation.Equiv
      ((tensorRepresentation L n (transportFactors a ρ) (transportExceptional a E)
        (fun v => e (finitePlaceEquiv a v)) (transportReference_fixed a ρ E e he)).comp
          (finiteEquiv n a).toMonoidHom)
      (tensorRepresentation K n ρ E e he) :=
  tensorTransportEquivOfMap a ρ E (transportExceptional a E) e he hne
    (transportReference_fixed a ρ E e he) (transportExceptional_map a E)

end Langlands.Global.FiniteAdelicGL
