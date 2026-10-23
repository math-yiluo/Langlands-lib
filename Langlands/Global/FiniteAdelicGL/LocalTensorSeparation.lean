import Langlands.Global.FiniteAdelicGL.RestrictedTensor
import Langlands.Representation.RestrictedTensor.Separation

/-! # Local factors inside actual finite adelic tensor representations -/

noncomputable section
open scoped Classical TensorProduct

universe uF uK uV

namespace Langlands.Global.FiniteAdelicGL

open Langlands.RestrictedTensor

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable {K : Type uK} [Field K]
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module K (V v)]

/-- The complementary tensor space after exposing one completed-local factor.
The exceptional places outside that factor remain exceptional. -/
abbrev LocalTensorTail (E : Finset (FinitePlace F)) (v : FinitePlace F) (e : ∀ w, V w) :=
  Space K (fun w : Outside {v} => V w) (tailSet {v} E) (fun w => e w)

/-- The local group acts on its own factor and trivially on the complementary tensor. -/
def separatedLocalRepresentation
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (v : FinitePlace F) (e : ∀ w, V w) :
    Representation K (FiniteLocalGL F n v)
      (V v ⊗[K] LocalTensorTail (K := K) F E v e) :=
  (ρ v).tprod (Representation.trivial K (FiniteLocalGL F n v) (LocalTensorTail (K := K) F E v e))

@[simp]
theorem separatedLocalRepresentation_tmul
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (v : FinitePlace F) (e : ∀ w, V w)
    (g : FiniteLocalGL F n v) (x : V v) (y : LocalTensorTail (K := K) F E v e) :
    separatedLocalRepresentation F n ρ E v e g (x ⊗ₜ[K] y) =
      ρ v g x ⊗ₜ[K] y := rfl

/-- The type of local actions on the constructed restricted tensor space. -/
abbrev TensorLocalAction (E : Finset (FinitePlace F)) (v : FinitePlace F)
    (e : ∀ w, V w) :=
  Representation K (FiniteLocalGL F n v) (Space K V E e)

/-- Restrict the actual finite adelic tensor action to one local insertion. -/
def tensorLocalRepresentation
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (v : FinitePlace F) : TensorLocalAction (K := K) F n E v e :=
  (tensorRepresentation F n ρ E e he).comp (localInclusion F n v).toMonoidHom

/-- The existing algebraic local separation intertwines the actual local insertion
with action on the first tensor factor alone. -/
theorem localSeparation_intertwines
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0) (v : FinitePlace F) (g : FiniteLocalGL F n v) :
    (localSeparation E v e hne).toLinearMap.comp
        (tensorRepresentation F n ρ E e he (localInclusion F n v g)) =
      (separatedLocalRepresentation F n ρ E v e g).comp
        (localSeparation E v e hne).toLinearMap := by
  apply hom_ext_cofinal {v}
  intro S hS x
  have hv : v ∈ S.1 := hS (Finset.mem_singleton_self v)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [tensorRepresentation_localInclusion_pure F n ρ E e he v g S hv]
  rw [localSeparation_pure E v e hne S hv,
    localSeparation_pure E v e hne S hv,
    separatedLocalRepresentation_tmul, Function.update_self]
  congr 2
  funext w
  apply Function.update_of_ne
  intro h
  exact w.1.2 (Finset.mem_singleton.mpr (congrArg Subtype.val h))

/-- Genuine representation equivalence exposing the chosen local factor of the
constructed adelic tensor action. No automorphic factorization is assumed. -/
def localTensorSeparation
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0) (v : FinitePlace F) :
    (tensorLocalRepresentation F n ρ E e he v).Equiv
      (separatedLocalRepresentation F n ρ E v e) :=
  Representation.Equiv.mk (localSeparation E v e hne)
    (localSeparation_intertwines F n ρ E e he hne v)

@[simp]
theorem localTensorSeparation_pure
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0) (v : FinitePlace F)
    (S : Index E) (hv : v ∈ S.1) (x : ∀ w : S.1, V w) :
    localTensorSeparation F n ρ E e he hne v (pure E e S x) =
      x ⟨v, hv⟩ ⊗ₜ[K]
        pure (tailSet {v} E) (fun w : Outside {v} => e w)
          ⟨tailSet {v} S.1, tailSet_mono {v} S.2⟩
          (fun w => x ⟨w.1.1, Finset.mem_subtype.mp w.2⟩) :=
  localSeparation_pure E v e hne S hv x

/-- Local insertion after reassembly changes only the exposed local vector. -/
theorem tensorLocalRepresentation_reassemble
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0) (v : FinitePlace F) (g : FiniteLocalGL F n v)
    (x : V v) (y : LocalTensorTail (K := K) F E v e) :
    tensorLocalRepresentation F n ρ E e he v g
        ((localTensorSeparation F n ρ E e he hne v).symm (x ⊗ₜ[K] y)) =
      (localTensorSeparation F n ρ E e he hne v).symm (ρ v g x ⊗ₜ[K] y) := by
  let q := localTensorSeparation F n ρ E e he hne v
  have h := LinearMap.congr_fun (q.symm.isIntertwining' g) (x ⊗ₜ[K] y)
  exact h.symm

/-- The same genuine local separation for the usual nonzero-reference product. -/
def restrictedLocalTensorSeparation
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (r : ReferenceVectors V E)
    (hr : ∀ v (hv : v ∉ E), ∀ g ∈ localIntegral F n v,
      ρ v g (r.vector v hv) = r.vector v hv)
    (v : FinitePlace F) :
    Representation.Equiv
      ((restrictedTensorRepresentation F n ρ E r hr).comp
        (localInclusion F n v).toMonoidHom)
      (separatedLocalRepresentation F n ρ E v r.family) :=
  localTensorSeparation F n ρ E r.family
    (fun w hw g hg => by
      simpa only [ReferenceVectors.family_of_not_mem r hw] using hr w hw g hg)
    r.family_nonzero v

end Langlands.Global.FiniteAdelicGL
