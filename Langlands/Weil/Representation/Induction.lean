import Langlands.Weil.Representation.Basic
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite-index induction on actual equivariant function spaces

The function model is Mathlib's coinduction. For a finite-index subgroup it
agrees with Mathlib's induction; its finite dimension is proved using coset
coordinates. No topology is required for this algebraic construction.
-/

noncomputable section

universe uK uG uV

open CategoryTheory

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

namespace Induction

/-- Right cosets, the quotient appropriate to left-equivariant functions. -/
abbrev Cosets (S : Subgroup G) := Quotient (QuotientGroup.rightRel S)

/-- The right coset of a group element. -/
def coset (S : Subgroup G) (g : G) : Cosets S := Quotient.mk _ g

/-- The subgroup factor of an element relative to the chosen coset representative. -/
def factor (S : Subgroup G) (g : G) : S :=
  ⟨g * (coset S g).out⁻¹,
    QuotientGroup.rightRel_apply.mp (Quotient.exact (coset S g).out_eq)⟩

theorem factor_mul_out (S : Subgroup G) (g : G) :
    (factor S g : G) * (coset S g).out = g := by
  simp [factor]

theorem coset_mul (S : Subgroup G) (s : S) (g : G) :
    coset S ((s : G) * g) = coset S g := by
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr (by simp)

theorem factor_mul (S : Subgroup G) (s : S) (g : G) :
    factor S ((s : G) * g) = s * factor S g := by
  apply Subtype.ext
  simp [factor, coset_mul, mul_assoc]

theorem coset_out (S : Subgroup G) (q : Cosets S) : coset S q.out = q :=
  q.out_eq

theorem factor_out (S : Subgroup G) (q : Cosets S) : factor S q.out = 1 := by
  apply Subtype.ext
  simp [factor, coset_out]

/-- Evaluating an equivariant function on chosen right-coset representatives is a
linear equivalence. Its inverse restores the values by the subgroup action. -/
def coordinates (S : Subgroup G) (A : FiniteRepresentation.{uK, uG, uV} K S) :
    Representation.coindV S.subtype A.representation ≃ₗ[K] (Cosets S → A) where
  toFun f q := f.val q.out
  invFun v :=
    ⟨fun g => A.representation (factor S g) (v (coset S g)), by
      intro s g
      simp only [Subgroup.coe_subtype, coset_mul, factor_mul, map_mul]
      rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    exact (f.property (factor S g) (coset S g).out).symm.trans
      (congrArg f.val (factor_mul_out S g))
  right_inv v := by
    funext q
    simp only [coset_out, factor_out, map_one, Module.End.one_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Induction

variable (S : Subgroup G) [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Finite-index induction has finite dimension, with no finite-dimensionality
certificate required from the caller beyond that of the original representation. -/
instance finite_coindV (A : FiniteRepresentation.{uK, uG, uV} K S) :
    Module.Finite K (Representation.coindV S.subtype A.representation) :=
  (Module.Finite.equiv_iff (Induction.coordinates S A)).mpr inferInstance

/-- Algebraic finite-index induction, on the actual space of equivariant functions.
The group acts by right translation. -/
def induce (A : FiniteRepresentation.{uK, uG, uV} K S) :
    FiniteRepresentation.{uK, uG, max uG uV} K G :=
  of (Representation.coind S.subtype A.representation)

/-- Induction of a linear intertwiner is pointwise application. -/
def induceMap {A B : FiniteRepresentation.{uK, uG, uV} K S}
    (f : A.representation.IntertwiningMap B.representation) :
    (induce S A).representation.IntertwiningMap (induce S B).representation :=
  Representation.coindMap S.subtype f

/-- Finite-index induction is a functor. -/
def induceFunctor :
    FiniteRepresentation.{uK, uG, uV} K S ⥤
      FiniteRepresentation.{uK, uG, max uG uV} K G where
  obj := induce S
  map f := (homEquiv _ _).symm (induceMap S (homEquiv _ _ f))
  map_id _ := by apply (homEquiv _ _).injective; rfl
  map_comp _ _ := by apply (homEquiv _ _).injective; rfl

/-- Induction of genuine representation equivalences. -/
def induceEquiv {A B : FiniteRepresentation.{uK, uG, uV} K S}
    (e : Equiv A B) : Equiv (induce S A) (induce S B) :=
  equivOfIso ((induceFunctor S).mapIso (isoOfEquiv e))

/-- Finite-index induction descends to genuine isomorphism classes. -/
def induceClass :
    IsomorphismClasses.{uK, uG, uV} K S →
      IsomorphismClasses.{uK, uG, max uG uV} K G :=
  Quotient.map (induce S) (fun _ _ ⟨e⟩ => ⟨induceEquiv S e⟩)

/-- The dimension is the index times the original dimension. -/
theorem rank_induce (A : FiniteRepresentation.{uK, uG, uV} K S) :
    (induce S A).rank = S.index * A.rank := by
  change Module.finrank K (Representation.coindV S.subtype A.representation) = _
  rw [(Induction.coordinates S A).finrank_eq, Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [QuotientGroup.card_quotient_rightRel, ← Nat.card_eq_fintype_card]
  rfl

/-- Comparison with Mathlib's tensor-and-coinvariant definition of induction.
The coefficient-universe restriction is inherited only by this comparison from
Mathlib's `Rep.indCoindIso`, not by the constructor above. -/
def induceIsoMathlib (A : FiniteRepresentation.{uK, uG, max uV uK} K S) :
    (induce S A).obj ≅ Rep.ind S.subtype A.obj := by
  classical
  exact (Rep.indCoindIso A.obj).symm

end Langlands.FiniteRepresentation
