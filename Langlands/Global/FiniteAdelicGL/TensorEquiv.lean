import Langlands.Global.FiniteAdelicGL.RestrictedTensor

/-! # Equivalences of finite adelic tensor representations -/

noncomputable section
open scoped Classical

universe uF uK uV uW

namespace Langlands.Global.FiniteAdelicGL

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable {K : Type uK} [Field K]
variable {V : FinitePlace F → Type uV} {W : FinitePlace F → Type uW}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module K (V v)]
variable [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)]

/-- Component equivalences preserving references outside a finite set give an
equivalence of representations of the actual finite adelic group. -/
def tensorEquivOver
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (σ : ∀ v, Representation K (FiniteLocalGL F n v) (W v))
    (E E' : Finset (FinitePlace F)) (e : ∀ v, V v) (e' : ∀ v, W v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (he' : ∀ v ∉ E', ∀ g ∈ localIntegral F n v, σ v g (e' v) = e' v)
    (f : ∀ v, (ρ v).Equiv (σ v))
    (hf : ∀ᶠ v in Filter.cofinite, f v (e v) = e' v) :
    (tensorRepresentation F n ρ E e he).Equiv
      (tensorRepresentation F n σ E' e' he') :=
  Representation.Equiv.mk
    (RestrictedTensor.congr E E' e e' (fun v => (f v).toLinearEquiv) hf)
    (tensorIntertwiner F n ρ σ E E' e e' he he' (fun v => (f v).toIntertwiningMap)
      hf).isIntertwining'

/-- Changing the integral-fixed references by a unit at almost every place gives
an equivalence of finite adelic tensor representations. -/
def tensorEquiv_of_eventually_unit_smul
    (ρ : ∀ v, Representation K (FiniteLocalGL F n v) (V v))
    (E E' : Finset (FinitePlace F)) (e e' : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (he' : ∀ v ∉ E', ∀ g ∈ localIntegral F n v, ρ v g (e' v) = e' v)
    (h : ∀ᶠ v in Filter.cofinite, ∃ c : Kˣ, (c : K) • e v = e' v) :
    (tensorRepresentation F n ρ E e he).Equiv
      (tensorRepresentation F n ρ E' e' he') := by
  let c (v : FinitePlace F) : Kˣ :=
    if hv : ∃ a : Kˣ, (a : K) • e v = e' v then Classical.choose hv else 1
  let f (v : FinitePlace F) : (ρ v).Equiv (ρ v) :=
    Representation.Equiv.mk (LinearEquiv.smulOfUnit (c v))
      (fun g => LinearMap.ext fun x => by
        change (c v : K) • ρ v g x = ρ v g ((c v : K) • x)
        rw [map_smul])
  refine tensorEquivOver F n ρ ρ E E' e e' he he' f (h.mono fun v hv => ?_)
  change (c v : K) • e v = e' v
  rw [show c v = Classical.choose hv from dite_eq_left hv]
  exact Classical.choose_spec hv

end Langlands.Global.FiniteAdelicGL
