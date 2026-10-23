import Langlands.Global.FiniteAdelicGL.RestrictedProduct
import Langlands.Representation.RestrictedTensor.Smooth
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Mathlib.RepresentationTheory.Intertwining

/-! # Restricted tensor representations of the actual finite adelic GL group -/

noncomputable section
open scoped Classical

universe uF uK uV uW

namespace Langlands.Global.FiniteAdelicGL

open Langlands.RestrictedTensor

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable {K : Type uK} [Field K]
variable {V : FinitePlace F → Type uV} {W : FinitePlace F → Type uW}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module K (V v)]
variable [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)]

/-- Pull the constructed restricted-product action back along the actual adelic
matrix equivalence. The carrier is the existing algebraic direct limit. -/
def tensorRepresentation (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v) :
    Representation K (FiniteAdelicGL F n) (Space K V E e) :=
  (representation (fun v => (localIntegral F n v).toSubgroup) ρ E e he).comp
    (restrictedProductEquiv F n).toMonoidHom

/-- A compact name for the representation on the usual nonzero-reference product. -/
def restrictedTensorRepresentation
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (r : ReferenceVectors V E)
    (hr : ∀ v (hv : v ∉ E), ∀ g ∈ localIntegral F n v,
      ρ v g (r.vector v hv) = r.vector v hv) :
    Representation K (FiniteAdelicGL F n) (Product K V E r) :=
  tensorRepresentation F n ρ E r.family (fun v hv g hg => by
    simpa only [ReferenceVectors.family_of_not_mem r hv] using hr v hv g hg)

/-- Every adelic element acts on a sufficiently large finite tensor stage by its
actual completed-local matrix projections. -/
theorem tensorRepresentation_pure_of_mem
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (g : FiniteAdelicGL F n) (S : Index E)
    (hg : ∀ v ∉ S.1, localProjection F n v g ∈ localIntegral F n v)
    (x : ∀ v : S.1, V v) :
    tensorRepresentation F n ρ E e he g (pure E e S x) =
      pure E e S (fun v => ρ v (localProjection F n v g) (x v)) :=
  representation_pure_of_mem (fun v => (localIntegral F n v).toSubgroup)
    ρ E e he (restrictedProductEquiv F n g) S hg x

/-- The actual identity-supported local inclusion induces exactly the generic
single-place restricted-product operator. -/
theorem tensorRepresentation_localInclusion
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (v : FinitePlace F) (g : FiniteLocalGL F n v) :
    tensorRepresentation F n ρ E e he (localInclusion F n v g) =
      representation (fun w => (localIntegral F n w).toSubgroup) ρ E e he
        (RestrictedProduct.mulSingle (fun w => (localIntegral F n w).toSubgroup) v g) := by
  change representation _ ρ E e he
    (restrictedProductEquiv F n (localInclusion F n v g)) = _
  rw [restrictedProductEquiv_localInclusion]
  congr 1

/-- On a stage containing the chosen place, local insertion acts componentwise
on that same stage; all other local projections are identities. -/
theorem tensorRepresentation_localInclusion_pure
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (v : FinitePlace F) (g : FiniteLocalGL F n v)
    (S : Index E) (hv : v ∈ S.1) (x : ∀ w : S.1, V w) :
    tensorRepresentation F n ρ E e he (localInclusion F n v g) (pure E e S x) =
      pure E e S (Function.update x ⟨v, hv⟩ (ρ v g (x ⟨v, hv⟩))) := by
  have hg : ∀ w ∉ S.1,
      localProjection F n w (localInclusion F n v g) ∈ localIntegral F n w := by
    intro w hw
    have hne : w ≠ v := fun h => hw (h ▸ hv)
    rw [localProjection_localInclusion_of_ne F n v w hne]
    exact (localIntegral F n w).one_mem
  rw [tensorRepresentation_pure_of_mem F n ρ E e he _ S hg]
  congr 1
  funext w
  by_cases hw : w.1 = v
  · have hw' : w = ⟨v, hv⟩ := Subtype.ext hw
    subst w
    simp only [localProjection_localInclusion, Function.update_self]
  · have hne : w ≠ ⟨v, hv⟩ := fun h => hw (congrArg Subtype.val h)
    simp only [localProjection_localInclusion_of_ne F n v w hw,
      map_one, Module.End.one_apply, Function.update_of_ne hne]

/-- Local smoothness implies smoothness for the existing adelic topology. -/
theorem isSmooth_tensorRepresentation
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (hρ : ∀ v, Langlands.IsSmooth (ρ v))
    (E : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v) :
    Langlands.IsSmooth (tensorRepresentation F n ρ E e he) :=
  Langlands.isSmooth_comp (restrictedProductEquiv F n).toMonoidHom
    (restrictedProductEquiv F n).continuous
    (isSmooth_representation (fun v => (localIntegral F n v).toSubgroup)
      (fun v => (localIntegral F n v).isOpen) ρ hρ E e he)

theorem isSmooth_restrictedTensorRepresentation
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (hρ : ∀ v, Langlands.IsSmooth (ρ v))
    (E : Finset (FinitePlace F)) (r : ReferenceVectors V E)
    (hr : ∀ v (hv : v ∉ E), ∀ g ∈ localIntegral F n v,
      ρ v g (r.vector v hv) = r.vector v hv) :
    Langlands.IsSmooth (restrictedTensorRepresentation F n ρ E r hr) :=
  isSmooth_tensorRepresentation F n ρ hρ E r.family _

/-- Component intertwiners preserving references almost everywhere give an
actual intertwiner of finite adelic representations, with differing exceptional sets. -/
def tensorIntertwiner
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (σ : ∀ v, Representation K (FiniteLocalGL F n v) (W v))
    (E E' : Finset (FinitePlace F)) (e : ∀ v, V v) (e' : ∀ v, W v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (he' : ∀ v ∉ E', ∀ g ∈ localIntegral F n v, σ v g (e' v) = e' v)
    (f : ∀ v, (ρ v).IntertwiningMap (σ v))
    (hf : ∀ᶠ v in Filter.cofinite, f v (e v) = e' v) :
    (tensorRepresentation F n ρ E e he).IntertwiningMap
      (tensorRepresentation F n σ E' e' he') where
  toLinearMap := Langlands.RestrictedTensor.map E E' e e' (fun v => (f v).toLinearMap) hf
  isIntertwining' g :=
    map_intertwines (fun v => (localIntegral F n v).toSubgroup) ρ σ E E' e e' he he'
      (fun v => (f v).toLinearMap) hf (fun v h => (f v).isIntertwining' h)
      (restrictedProductEquiv F n g)

end Langlands.Global.FiniteAdelicGL
