import Langlands.Global.FiniteAdelicGL.TensorTransport

/-! # Finite-stage formulas for arithmetic tensor transport -/

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

/-- The actual image stage, now an index for the exact original exceptions. -/
def transportTensorIndex (a : K ≃+* L) (E : Finset (FinitePlace K))
    (T : Index (transportExceptional a E)) : Index E :=
  ⟨T.1.map (finitePlaceEquiv a).toEmbedding, by
    exact Eq.mp (congrArg (fun D => D ⊆ T.1.map (finitePlaceEquiv a).toEmbedding)
      (transportExceptional_map a E)) (Finset.map_subset_map.mpr T.2)⟩

omit [NumberField L] in
private theorem representation_cast_of (a : K ≃+* L)
    (ρ : ∀ v, Representation A (FiniteLocalGL K n v) (V v))
    (Enew : Finset (FinitePlace L)) (E : Finset (FinitePlace K))
    (hE : Enew.map (finitePlaceEquiv a).toEmbedding = E)
    (e : ∀ v, V v)
    (τ : Representation A (FiniteAdelicGL K n)
      (Space A (fun v => V (finitePlaceEquiv a v)) Enew
        (fun v => e (finitePlaceEquiv a v))))
    (f : ∀ (hf : ∀ v ∉ Enew.map (finitePlaceEquiv a).toEmbedding,
        ∀ g ∈ localIntegral K n v, ρ v g (e v) = e v)
      (_hn : ∀ v ∉ Enew.map (finitePlaceEquiv a).toEmbedding, e v ≠ 0),
      Representation.Equiv τ
        (tensorRepresentation K n ρ (Enew.map (finitePlaceEquiv a).toEmbedding) e hf))
    (hf : ∀ hfix hn (T : Index Enew)
      (x : Stage A (fun v => V (finitePlaceEquiv a v)) T.1),
      f hfix hn
        (of A (fun v => V (finitePlaceEquiv a v)) Enew
          (fun v => e (finitePlaceEquiv a v)) T x) =
        of A V (Enew.map (finitePlaceEquiv a).toEmbedding) e
          ⟨T.1.map (finitePlaceEquiv a).toEmbedding, Finset.map_subset_map.mpr T.2⟩
          (reindexStage (finitePlaceEquiv a) T.1 x))
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral K n v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0)
    (T : Index Enew)
    (x : Stage A (fun v => V (finitePlaceEquiv a v)) T.1) :
    (hE ▸ f) he hne
      (of A (fun v => V (finitePlaceEquiv a v)) Enew
        (fun v => e (finitePlaceEquiv a v)) T x) =
      of A V E e
        ⟨T.1.map (finitePlaceEquiv a).toEmbedding,
          hE ▸ Finset.map_subset_map.mpr T.2⟩
        (reindexStage (finitePlaceEquiv a) T.1 x) := by
  subst E
  exact hf he hne T x

/-- Arithmetic tensor transport sends each finite stage to its image stage. -/
theorem tensorTransportEquiv_of (a : K ≃+* L)
    (ρ : ∀ v, Representation A (FiniteLocalGL K n v) (V v))
    (E : Finset (FinitePlace K)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral K n v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0)
    (T : Index (transportExceptional a E))
    (x : Stage A (fun v => V (finitePlaceEquiv a v)) T.1) :
    tensorTransportEquiv a ρ E e he hne
      (of A (fun v => V (finitePlaceEquiv a v)) (transportExceptional a E)
        (fun v => e (finitePlaceEquiv a v)) T x) =
      of A V E e (transportTensorIndex a E T) (reindexStage (finitePlaceEquiv a) T.1 x) := by
  apply representation_cast_of a ρ (transportExceptional a E) E
    (transportExceptional_map a E) e _ _ _ he hne T x
  intro hfix hn U z
  rfl

/-- On elementary tensors arithmetic transport only reindexes the entries. The
tuple is indexed by the image stage, avoiding casts between dependent fibers. -/
theorem tensorTransportEquiv_pure (a : K ≃+* L)
    (ρ : ∀ v, Representation A (FiniteLocalGL K n v) (V v))
    (E : Finset (FinitePlace K)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral K n v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0)
    (T : Index (transportExceptional a E))
    (x : ∀ v : T.1.map (finitePlaceEquiv a).toEmbedding, V v) :
    tensorTransportEquiv a ρ E e he hne
      (pure (transportExceptional a E) (fun v => e (finitePlaceEquiv a v)) T
        (fun v => x (reindexFinite (finitePlaceEquiv a) T.1 v))) =
      pure E e (transportTensorIndex a E T) x := by
  simp only [transportTensorIndex, Langlands.RestrictedTensor.pure,
    tensorTransportEquiv_of, reindexStage_tprod]

end Langlands.Global.FiniteAdelicGL
