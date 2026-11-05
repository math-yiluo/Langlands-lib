import Langlands.Group.TitsSystem
import Mathlib.Logic.Relation

/-! # Saturation, parabolic subgroups and the restricted building of a Tits system

For subgroups `B` and `N` of a group `G` with Weyl-group datum `π : N →* W` and a set `S ⊆ W`
(the data of `Langlands.Group.IsTitsSystem`), this module defines

* saturation, axiom TS 5 of Kaletha–Prasad Definition 1.4.1;
* parabolic subgroups, the subgroups containing a conjugate of `B` (KP Definition 1.4.4(2));
* the conjugates `g G_X g⁻¹` of the standard parabolic subsets `G_X = B W_X B`
  (KP Definitions 1.4.4(1) and 1.4.6);
* the irreducible components of `S` and the admissible types and parabolic subgroups of
  KP Definition 1.5.17;
* the apartments of the restricted building of KP Proposition 1.5.18 and Definition 1.5.20,
  in the parabolic-subgroup description of KP Remark 1.5.7.

These are definitions only. No property of Tits systems is assumed or proved.
-/

namespace Langlands.Group.TitsSystem

universe u v

variable {G : Type u} [Group G] {W : Type v} [Group W]

/-- Axiom TS 5 of KP Definition 1.4.1: `⋂_{n ∈ N} n B n⁻¹ = B ∩ N`. A Tits system is
saturated when it satisfies this axiom. -/
def IsSaturated (B N : Subgroup G) : Prop :=
  ⨅ n : N, B.map (MulAut.conj (n : G)).toMonoidHom = B ⊓ N

theorem isSaturated_iff (B N : Subgroup G) :
    IsSaturated B N ↔ ⨅ n : N, B.map (MulAut.conj (n : G)).toMonoidHom = B ⊓ N :=
  Iff.rfl

/-- A parabolic subgroup (KP Definition 1.4.4(2)): a subgroup of `G` containing a conjugate
`g B g⁻¹` of `B`. -/
def IsParabolic (B P : Subgroup G) : Prop :=
  ∃ g : G, B.map (MulAut.conj g).toMonoidHom ≤ P

variable {N : Subgroup G}

/-- The conjugate `g G_X g⁻¹` of the standard parabolic subset `G_X = B W_X B`
(KP Definition 1.4.4(1)). A parabolic subgroup is of type `X` when it is such a conjugate
(KP Definition 1.4.6). -/
def conjStandardParabolic (B : Subgroup G) (π : N →* W) (g : G) (X : Set W) : Set G :=
  (fun x => g * x * g⁻¹) '' standardParabolic B π X

/-- Two elements of `S` lie in the same irreducible component of `S`: they are joined by a
chain of elements of `S` in which consecutive elements do not commute. The components are
the parts of the smallest decomposition `S = S₁ ∪ ⋯ ∪ Sₙ` such that the elements of
different parts commute (KP §1.4, after Definition 1.4.6). -/
def SameComponent (S : Set W) : W → W → Prop :=
  Relation.ReflTransGen fun s t => s ∈ S ∧ t ∈ S ∧ s * t ≠ t * s

/-- An admissible type (KP Definition 1.5.17(1)): a subset `X ⊆ S` such that `X ∩ Sᵢ` is a
proper subset of every irreducible component `Sᵢ` of `S`. For each `s ∈ S` some element of
the component of `s` lies outside `X`. -/
def IsAdmissibleType (S X : Set W) : Prop :=
  X ⊆ S ∧ ∀ s ∈ S, ∃ t ∈ S, SameComponent S s t ∧ t ∉ X

/-- An admissible parabolic subgroup (KP Definition 1.5.17(2)): a conjugate `g G_X g⁻¹` of a
standard parabolic subgroup of admissible type. -/
def IsAdmissibleParabolic (B : Subgroup G) (π : N →* W) (S : Set W) (P : Subgroup G) : Prop :=
  ∃ (g : G) (X : Set W), IsAdmissibleType S X ∧
    (P : Set G) = conjStandardParabolic B π g X

/-- The apartment `g A'` of the restricted building (KP Propositions 1.5.6(6) and 1.5.18(1)),
in the parabolic description of KP Remark 1.5.7: the facets of the standard apartment `A`
are the parabolic subgroups `n G_X n⁻¹` with `n ∈ N`, and those of `A' = B' ∩ A` are the ones
of admissible type. The apartments are the `G`-translates. -/
def restrictedApartment (B : Subgroup G) (π : N →* W) (S : Set W) (g : G) :
    Set (Subgroup G) :=
  {P | ∃ (n : N) (X : Set W), IsAdmissibleType S X ∧
    (P : Set G) = conjStandardParabolic B π (g * n) X}

/-- The set of apartments of the restricted building, each given as its set of admissible
parabolic subgroups. -/
def restrictedApartments (B : Subgroup G) (π : N →* W) (S : Set W) : Set (Set (Subgroup G)) :=
  Set.range (restrictedApartment B π S)

theorem mem_restrictedApartment {B : Subgroup G} {π : N →* W} {S : Set W} {g : G}
    {P : Subgroup G} :
    P ∈ restrictedApartment B π S g ↔ ∃ (n : N) (X : Set W), IsAdmissibleType S X ∧
      (P : Set G) = conjStandardParabolic B π (g * n) X :=
  Iff.rfl

/-- Every parabolic subgroup of a restricted apartment is admissible. -/
theorem isAdmissibleParabolic_of_mem_restrictedApartment {B : Subgroup G} {π : N →* W}
    {S : Set W} {g : G} {P : Subgroup G} (hP : P ∈ restrictedApartment B π S g) :
    IsAdmissibleParabolic B π S P := by
  obtain ⟨n, X, hX, hP⟩ := hP
  exact ⟨g * n, X, hX, hP⟩

end Langlands.Group.TitsSystem
