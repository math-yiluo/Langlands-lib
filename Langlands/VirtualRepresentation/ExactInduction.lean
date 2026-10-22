import Langlands.VirtualRepresentation.Exact
import Langlands.Weil.Representation.Induction

/-!
# Finite-index induction on exact virtual representations

Induction is the existing equivariant-function construction. Exactness is proved
using its actual coset coordinates, so it descends to the exact-relation quotient.
-/

noncomputable section

universe uK uG uV

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]
variable (S : Subgroup G) [S.FiniteIndex]

/-- In coset coordinates the existing induced intertwiner acts pointwise. -/
theorem coordinates_induceMap
    {A B : FiniteRepresentation.{uK, uG, uV} K S}
    (f : A.representation.IntertwiningMap B.representation)
    (x : induce S A) (q : Induction.Cosets S) :
    Induction.coordinates S B (induceMap S f x) q =
      f (Induction.coordinates S A x q) := rfl

/-- Finite-index induction preserves actual short exact sequences.
The proof chooses preimages only in the original vector spaces, in coset
coordinates. It does not choose an equivariant splitting. -/
theorem isShortExact_induce
    {A B C : FiniteRepresentation.{uK, uG, uV} K S}
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation}
    (h : IsShortExact f g) :
    IsShortExact (induceMap S f) (induceMap S g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply (Induction.coordinates S A).injective
    funext q
    apply h.1
    exact congrArg (fun z : induce S B => Induction.coordinates S B z q) hxy
  · intro y
    let v : Induction.Cosets S → B :=
      fun q => Classical.choose (h.2.1 (Induction.coordinates S C y q))
    refine ⟨(Induction.coordinates S B).symm v, ?_⟩
    apply (Induction.coordinates S C).injective
    funext q
    change g (Induction.coordinates S B ((Induction.coordinates S B).symm v) q) = _
    rw [LinearEquiv.apply_symm_apply]
    exact Classical.choose_spec (h.2.1 (Induction.coordinates S C y q))
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      change induceMap S g (induceMap S f y) = 0
      apply (Induction.coordinates S C).injective
      funext q
      change g (f (Induction.coordinates S A y q)) = 0
      have hy : f (Induction.coordinates S A y q) ∈ LinearMap.range f.toLinearMap :=
        ⟨_, rfl⟩
      rw [h.2.2] at hy
      exact hy
    · intro hx
      change induceMap S g x = 0 at hx
      have hc : ∀ q : Induction.Cosets S,
          ∃ a : A, f a = Induction.coordinates S B x q := by
        intro q
        have hz : g (Induction.coordinates S B x q) = 0 := by
          exact congrArg (fun z : induce S C => Induction.coordinates S C z q) hx
        have hm : Induction.coordinates S B x q ∈ LinearMap.ker g.toLinearMap := hz
        rw [← h.2.2] at hm
        exact hm
      let v : Induction.Cosets S → A := fun q => Classical.choose (hc q)
      refine ⟨(Induction.coordinates S A).symm v, ?_⟩
      apply (Induction.coordinates S B).injective
      funext q
      change f (Induction.coordinates S A ((Induction.coordinates S A).symm v) q) = _
      rw [LinearEquiv.apply_symm_apply]
      exact Classical.choose_spec (hc q)

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]
variable (S : Subgroup G) [S.FiniteIndex]
variable (P : FiniteRepresentation.{uK, uG, uV} K S → Prop)
variable (Q : FiniteRepresentation.{uK, uG, max uG uV} K G → Prop)

/-- Actual induction on property-restricted genuine isomorphism classes.
The supplied implication is only the property-closure requirement for these
particular families; algebraic exactness is proved independently above. -/
def induceClassWith
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A)) :
    IsomorphismClassesWith P → IsomorphismClassesWith Q :=
  Quotient.map
    (fun A => ⟨FiniteRepresentation.induce S A.val, hPQ A.val A.property⟩)
    (fun _ _ ⟨e⟩ => ⟨FiniteRepresentation.induceEquiv S e⟩)

/-- The induced class function respects all exact relations. -/
theorem induceClassWith_isExactAdditive
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A)) :
    IsExactAdditive P (fun c => ofClass Q (induceClassWith S P Q hPQ c)) := by
  intro A B C f g h
  exact ofRepresentation_shortExact Q (isShortExact_induce S h)

/-- Finite-index induction on the actual exact-relation virtual group. -/
def induce (hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A)) :
    ExactGrothendieckGroup P →ₗ[ℤ] ExactGrothendieckGroup Q :=
  lift P (fun c => ofClass Q (induceClassWith S P Q hPQ c))
    (induceClassWith_isExactAdditive S P Q hPQ)

@[simp]
theorem induce_ofClass
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A))
    (c : IsomorphismClassesWith P) :
    induce S P Q hPQ (ofClass P c) = ofClass Q (induceClassWith S P Q hPQ c) :=
  lift_ofClass P _ _ c

@[simp]
theorem induce_ofRepresentation
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A))
    (A : {A : FiniteRepresentation.{uK, uG, uV} K S // P A}) :
    induce S P Q hPQ (ofRepresentation P A) =
      ofRepresentation Q ⟨FiniteRepresentation.induce S A.val, hPQ A.val A.property⟩ :=
  induce_ofClass S P Q hPQ _

/-- Induction multiplies virtual degree by the actual subgroup index. -/
theorem degree_comp_induce
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A)) :
    (degree Q).comp (induce S P Q hPQ) = (S.index : ℤ) • degree P := by
  apply hom_ext P
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change degree Q (induce S P Q hPQ (ofRepresentation P A)) =
      (S.index : ℤ) * degree P (ofRepresentation P A)
    rw [induce_ofRepresentation, degree_ofRepresentation, degree_ofRepresentation,
      FiniteRepresentation.rank_induce, Nat.cast_mul]

theorem degree_induce
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A))
    (x : ExactGrothendieckGroup P) :
    degree Q (induce S P Q hPQ x) = (S.index : ℤ) * degree P x :=
  LinearMap.congr_fun (degree_comp_induce S P Q hPQ) x

/-- Induction therefore acts on the genuine virtual dimension-zero subgroups. -/
def induceDegreeZero
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A)) :
    degreeZero P →ₗ[ℤ] degreeZero Q :=
  (induce S P Q hPQ).restrict fun x hx => by
    change degree Q (induce S P Q hPQ x) = 0
    rw [degree_induce, (mem_degreeZero P x).mp hx, mul_zero]

/-- Unconditional algebraic induction, with no extra object-property assumption. -/
def induceAll :
    ExactGrothendieckGroup
        (fun _ : FiniteRepresentation.{uK, uG, uV} K S => True) →ₗ[ℤ]
      ExactGrothendieckGroup
        (fun _ : FiniteRepresentation.{uK, uG, max uG uV} K G => True) :=
  induce S _ _ (fun _ _ => trivial)

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
