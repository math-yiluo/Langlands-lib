import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.RingTheory.Localization.Module

/-! # Transfer of an integral root base to a rational root system -/

noncomputable section

namespace Langlands.LinearAlgebra.IntegralRationalRootBase

variable {J K X Y V W U : Type*}
  [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  [AddCommGroup U] [Module ℚ U]
  (P : RootPairing J ℤ X Y) (Q : RootPairing K ℚ V W)
  (f : X →+ U) (g : V →ₗ[ℚ] U) (e : J ≃ K)
  (hf : Function.Injective f) (hg : Function.Injective g)
  (hroot : ∀ j, f (P.root j) = g (Q.root (e j)))

include hf hroot

/-- Integral independence transfers through an injective additive realization
of the roots in a common rational ambient space. -/
theorem linearIndependent_transport {L : Type*} (a : L → J)
    (h : LinearIndependent ℤ (P.root ∘ a)) :
    LinearIndependent ℚ (Q.root ∘ e ∘ a) := by
  have hm := h.map_injOn f.toIntLinearMap hf.injOn
  have hq := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hm
  apply LinearIndependent.of_comp g
  convert hq using 1
  funext l
  exact (hroot (a l)).symm

include hg

/-- Reducedness transfers to a rational pairing with the same full roots. -/
theorem isReduced [P.IsReduced] : Q.IsReduced := by
  refine ⟨fun a b hdep => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective a
  obtain ⟨j, rfl⟩ := e.surjective b
  have hdep' : ¬ LinearIndependent ℤ ![P.root i, P.root j] := by
    intro h
    apply hdep
    have h' : LinearIndependent ℤ (P.root ∘ ![i, j]) := by
      convert h using 1
      funext k
      fin_cases k <;> rfl
    convert linearIndependent_transport P Q f g e hf hroot ![i, j] h' using 1
    funext k
    fin_cases k <;> rfl
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) i j hdep' with h | h
  · left
    apply hg
    rw [← hroot, ← hroot, h]
  · right
    apply hg
    rw [map_neg, ← hroot, ← hroot, h, map_neg]

omit hf in
/-- Additive positive-root generation is reflected from the common ambient
space along the injective target realization. -/
theorem closure_transport (s : Set J) {x : X} {y : V}
    (hxy : f x = g y)
    (hx : x ∈ AddSubmonoid.closure (P.root '' s)) :
    y ∈ AddSubmonoid.closure (Q.root '' (e '' s)) := by
  have heq : (AddSubmonoid.closure (P.root '' s)).map f =
      (AddSubmonoid.closure (Q.root '' (e '' s))).map g.toAddMonoidHom := by
    rw [AddMonoidHom.map_mclosure, AddMonoidHom.map_mclosure]
    simp only [Set.image_image]
    exact congrArg AddSubmonoid.closure (Set.image_congr' hroot)
  have hm := AddSubmonoid.mem_map_of_mem f hx
  rw [heq, hxy] at hm
  obtain ⟨z, hz, hez⟩ := hm
  exact hg hez ▸ hz

variable [Finite K] [Q.IsRootSystem] [Q.IsCrystallographic] [P.IsReduced]

/-- The rational base supported on the image of a supplied integral base.
The ambient realization allows central character directions outside the
rational root span. -/
def base (b : P.Base) : Q.Base := by
  letI : Q.IsReduced := isReduced P Q f g e hf hg hroot
  refine RootPairing.Base.mk' Q (e '' (b.support : Set J)) ?_ ?_
  · apply (linearIndepOn_equiv e).mp
    exact linearIndependent_transport P Q f g e hf hroot
      (fun j : b.support => j.val) b.linearIndepOn_root
  · intro a
    obtain ⟨j, rfl⟩ := e.surjective a
    rcases b.root_mem_or_neg_mem j with h | h
    · exact Or.inl (closure_transport P Q f g e hg hroot _ (hroot j) h)
    · exact Or.inr (closure_transport P Q f g e hg hroot _
        (by rw [map_neg, map_neg, hroot]) h)

/-- The transferred simple support is the image of the original support. -/
theorem support_base (b : P.Base) :
    ((base P Q f g e hf hg hroot b).support : Set K) =
      e '' (b.support : Set J) := by
  simp [base, RootPairing.Base.mk']

/-- Restricting the root-index equivalence identifies the two simple supports. -/
def supportEquiv (b : P.Base) :
    b.support ≃ (base P Q f g e hf hg hroot b).support :=
  Equiv.subtypeEquiv e (fun j => by
    change j ∈ (b.support : Set J) ↔
      e j ∈ ((base P Q f g e hf hg hroot b).support : Set K)
    rw [support_base]
    exact (e.injective.mem_set_image).symm)

/-- Equality of the rational root-coroot pairings yields exact equality of
the original integer Cartan entries. -/
theorem cartanMatrix_supportEquiv (b : P.Base)
    (hpair : ∀ i j, Q.pairing (e i) (e j) = (P.pairing i j : ℚ))
    (i j : b.support) :
    (base P Q f g e hf hg hroot b).cartanMatrix
      (supportEquiv P Q f g e hf hg hroot b i)
      (supportEquiv P Q f g e hf hg hroot b j) = b.cartanMatrix i j := by
  apply FaithfulSMul.algebraMap_injective ℤ ℚ
  simp only [RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def,
    RootPairing.algebraMap_pairingIn]
  change Q.pairing (e i.val) (e j.val) =
    algebraMap ℤ ℚ (P.pairingIn ℤ i.val j.val)
  have hp : P.pairingIn ℤ i.val j.val = P.pairing i.val j.val := by
    simpa using P.algebraMap_pairingIn ℤ i.val j.val
  rw [hp]
  exact hpair i.val j.val

end Langlands.LinearAlgebra.IntegralRationalRootBase
