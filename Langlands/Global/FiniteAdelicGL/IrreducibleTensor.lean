import Langlands.Global.FiniteAdelicGL.LocalTensorSeparation
import Langlands.Representation.Induction.OpenNormalRestrictionSemisimple
import Langlands.Representation.RestrictedTensor.Irreducibility
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.TensorProduct.MultiplicityCancellation

/-! # Irreducible finite-adelic tensors and their local embeddings -/

noncomputable section

set_option autoImplicit false

universe uF uV

namespace Langlands.Global.FiniteAdelicGL

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable (ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v))
variable (E : Finset (FinitePlace F)) (e : ∀ v, V v)
variable (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
variable (hne : ∀ v ∉ E, e v ≠ 0)

include hne in
/-- Admissible irreducible local factors give an irreducible representation
of the actual finite adelic group. -/
theorem tensorRepresentation_isIrreducible
    (hI : ∀ v, (ρ v).IsIrreducible) (hA : ∀ v, IsAdmissible (ρ v)) :
    (tensorRepresentation F n ρ E e he).IsIrreducible := by
  let := hI
  have h := RestrictedTensor.representation_isIrreducible
    (fun v => (localIntegral F n v).toSubgroup) ρ E e he hne
    (fun v f => (admissibleSchur_scalarEndomorphism (ρ v) (hA v) (hI v) f).exists)
  exact Induction.isIrreducible_comp_of_surjective _
    (restrictedProductEquiv F n).toMonoidHom (restrictedProductEquiv F n).surjective h

/-- Fixing a vector in the complementary tensor gives an intertwiner from
the prescribed local factor into the restriction of the adelic tensor. -/
def localTensorEmbedding (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e) :
    (ρ v).IntertwiningMap (tensorLocalRepresentation F n ρ E e he v) :=
  (localTensorSeparation F n ρ E e he hne v).symm.toIntertwiningMap.comp
    (TensorMultiplicity.slice (ρ v) y)

theorem localTensorEmbedding_injective (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (hy : y ≠ 0) :
    Function.Injective (localTensorEmbedding F n ρ E e he hne v y).toLinearMap := by
  have hs : Function.Injective (TensorMultiplicity.slice (ρ v) y).toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    by_contra h
    exact TensorMultiplicity.tmul_ne_zero h hy hx
  exact (localTensorSeparation F n ρ E e he hne v).symm.injective.comp hs

include hne in
/-- Nontrivial local factors allow a nonzero complementary tensor at every place. -/
theorem exists_injective_localTensorEmbedding [∀ v, Nontrivial (V v)] (v : FinitePlace F) :
    ∃ f : (ρ v).IntertwiningMap (tensorLocalRepresentation F n ρ E e he v),
      Function.Injective f.toLinearMap := by
  let : Nontrivial (LocalTensorTail (K := ℂ) F E v e) :=
    RestrictedTensor.localTensorTail_nontrivial E v e hne
  obtain ⟨y, hy⟩ := exists_ne (0 : LocalTensorTail (K := ℂ) F E v e)
  exact ⟨localTensorEmbedding F n ρ E e he hne v y,
    localTensorEmbedding_injective F n ρ E e he hne v y hy⟩

end Langlands.Global.FiniteAdelicGL
