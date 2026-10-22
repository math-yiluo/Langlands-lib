import Langlands.Representation.Finite.Classes
import Mathlib.RepresentationTheory.FiniteIndex

noncomputable section

open CategoryTheory

namespace Langlands.FiniteRep

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- Evaluation on chosen right-coset representatives. -/
def coindEvaluation (S : Subgroup G) (V : FDRep k S) :
    Representation.coindV S.subtype V.ρ →ₗ[k]
      (Quotient (QuotientGroup.rightRel S) → V) where
  toFun f q := f.1 q.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Equivariance determines a coinduced function from its values on coset representatives. -/
theorem coindEvaluation_injective (S : Subgroup G) (V : FDRep k S) :
    Function.Injective (coindEvaluation S V) := by
  intro f h he
  apply Subtype.ext
  funext g
  let q : Quotient (QuotientGroup.rightRel S) := Quotient.mk _ g
  obtain ⟨s, hs⟩ := Quotient.exact (Quotient.out_eq q).symm
  have heq : f.1 q.out = h.1 q.out := congrFun he q
  calc
    f.1 g = V.ρ s (f.1 q.out) := by
      rw [← hs]
      exact f.2 s q.out
    _ = V.ρ s (h.1 q.out) := congrArg _ heq
    _ = h.1 g := by
      rw [← hs]
      exact (h.2 s q.out).symm

/-- Coinduction from a finite-index subgroup of a finite-dimensional representation is finite. -/
instance finiteCoind (S : Subgroup G) [S.FiniteIndex] (V : FDRep k S) :
    Module.Finite k (Representation.coindV S.subtype V.ρ) := by
  let := Subgroup.fintypeQuotientOfFiniteIndex (H := S)
  exact Module.Finite.of_injective (coindEvaluation S V) (coindEvaluation_injective S V)

/-- The existing Mathlib equivalence between quotient induction and equivariant-function
coinduction, applied to an actual finite-dimensional representation. -/
def indCoindEquiv (S : Subgroup G) [S.FiniteIndex] (V : FDRep k S) :
    Representation.Equiv (Representation.ind S.subtype V.ρ)
      (Representation.coind S.subtype V.ρ) := by
  classical
  exact Representation.equivOfIso (Rep.indCoindIso (Rep.of V.ρ))

/-- The actual quotient induced representation has finite-dimensional carrier. -/
instance finiteInd (S : Subgroup G) [S.FiniteIndex] (V : FDRep k S) :
    Module.Finite k (Representation.IndV S.subtype V.ρ) :=
  Module.Finite.equiv (indCoindEquiv S V).toLinearEquiv.symm

/-- Finite-index induction as an actual `FDRep`, using a proved finite coordinate model. -/
def induceRep (S : Subgroup G) [S.FiniteIndex] (V : FDRep k S) : FDRep k G :=
  ofRepresentation (Representation.ind S.subtype V.ρ)

/-- The coordinate model represents Mathlib's genuine quotient induction. -/
def induceRepEquiv (S : Subgroup G) [S.FiniteIndex] (V : FDRep k S) :
    Representation.Equiv (Representation.ind S.subtype V.ρ) (induceRep S V).ρ :=
  modelEquiv _

/-- Induction carries actual representation isomorphisms to isomorphisms. -/
def induceIso (S : Subgroup G) [S.FiniteIndex] {V W : FDRep k S} (e : V ≅ W) :
    induceRep S V ≅ induceRep S W :=
  isoOfEquiv <|
    ((induceRepEquiv S V).symm.trans
      (Representation.equivOfIso
        ((Rep.indFunctor k S.subtype).mapIso (Rep.mkIso (equivOfIso e))))).trans
      (induceRepEquiv S W)

/-- Finite-index induction on genuine representation isomorphism classes. -/
def induce (S : Subgroup G) [S.FiniteIndex] : RepClass k S → RepClass k G :=
  Quotient.map (induceRep S) (fun _ _ ⟨e⟩ => ⟨induceIso S e⟩)

/-- Coinduction preserves the componentwise direct sum by evaluation in each component. -/
def coindSumEquiv (S : Subgroup G) (V W : FDRep k S) :
    Representation.Equiv (Representation.coind S.subtype (sumRep V W).ρ)
      (Representation.prod (Representation.coind S.subtype V.ρ)
        (Representation.coind S.subtype W.ρ)) :=
  Representation.Equiv.mk
    { toFun f :=
        (⟨fun g => (f.1 g).1, fun s g => congrArg Prod.fst (f.2 s g)⟩,
         ⟨fun g => (f.1 g).2, fun s g => congrArg Prod.snd (f.2 s g)⟩)
      invFun f := ⟨fun g => (f.1.1 g, f.2.1 g), fun s g =>
        Prod.ext (f.1.2 s g) (f.2.2 s g)⟩
      left_inv f := by
        apply Subtype.ext
        rfl
      right_inv f := by
        apply Prod.ext <;> apply Subtype.ext <;> rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (by
      intro g
      apply LinearMap.ext
      intro f
      apply Prod.ext <;> apply Subtype.ext <;> rfl)

/-- Additivity of genuine quotient induction, via the existing induction–coinduction
equivalence and the explicit componentwise coinduction equivalence. -/
def indSumEquiv (S : Subgroup G) [S.FiniteIndex] (V W : FDRep k S) :
    Representation.Equiv (Representation.ind S.subtype (sumRep V W).ρ)
      (Representation.prod (Representation.ind S.subtype V.ρ)
        (Representation.ind S.subtype W.ρ)) :=
  (indCoindEquiv S (sumRep V W)).trans <|
    (coindSumEquiv S V W).trans <|
      prodEquiv (indCoindEquiv S V).symm (indCoindEquiv S W).symm

/-- Induction of the zero-dimensional representation is zero-dimensional. -/
def indZeroEquiv (S : Subgroup G) [S.FiniteIndex] :
    Representation.Equiv (Representation.ind S.subtype (zeroRep (k := k) (G := S)).ρ)
      (zeroRep (k := k) (G := G)).ρ :=
  (indCoindEquiv S zeroRep).trans <|
    Representation.Equiv.mk (LinearEquiv.ofSubsingleton _ _) (by
      intro g
      exact Subsingleton.elim _ _)

/-- Finite-index induction as an additive map on genuine representation classes. -/
def induceHom (S : Subgroup G) [S.FiniteIndex] : RepClass k S →+ RepClass k G where
  toFun := induce S
  map_zero' := (classOfRepresentation_congr (indZeroEquiv S)).trans
    (classOfRepresentation_rho zeroRep)
  map_add' := by
    intro a b
    induction a using Quotient.inductionOn with | h V =>
      induction b using Quotient.inductionOn with | h W =>
        exact (classOfRepresentation_congr (indSumEquiv S V W)).trans
          (classOfRepresentation_prod _ _)

/-- The character of induced classes is the trace of the actual induced action. -/
@[simp]
theorem character_induce_classOf (S : Subgroup G) [S.FiniteIndex] (V : FDRep k S) :
    character (induce S (classOf V)) = (Representation.ind S.subtype V.ρ).character :=
  character_classOfRepresentation _

end Langlands.FiniteRep
