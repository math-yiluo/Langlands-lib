import Langlands.GroupScheme.Adjoint.RelativeQuotientEquivariance
import Langlands.GroupScheme.FppfLocalGroupIso
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Étale inner forms and comparison descent over arbitrary schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H K A B : GroupScheme S} {U V : Over S}

namespace LocalGroupIso

/-- An actual group-scheme isomorphism gives a constant local family on any parameter. -/
def ofIso (e : G ≅ H) (U : Over S) : LocalGroupIso G H U where
  toFun _ :=
    { toFun := fun g => g ≫ e.hom.hom.hom
      invFun := fun h => h ≫ e.inv.hom.hom
      left_inv := fun g => by
        change g ≫ (e.hom ≫ e.inv).hom.hom = g
        rw [e.hom_inv_id]
        exact Category.comp_id g
      right_inv := fun h => by
        change h ≫ (e.inv ≫ e.hom).hom.hom = h
        rw [e.inv_hom_id]
        exact Category.comp_id h
      map_mul' := fun g g' => MonObj.mul_comp g g' e.hom.hom.hom }
  naturality t _ g := Category.assoc t g e.hom.hom.hom

/-- A constant local family has identity discrepancy for every action. -/
theorem ofIso_hasInnerDiscrepancy (e : G ≅ H) (a : AutomorphicAction A G) (U : Over S) :
    (ofIso e U).HasInnerDiscrepancy a := by
  intro T b c
  refine ⟨1, ?_⟩
  intro W t g
  simp only [MonObj.comp_one, a.act_one_left]
  rfl

variable {q : G ⟶ A} {p : H ⟶ B}
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (hp : RelativeRoot.IsFppfQuotient (center H) p)
    (a : AutomorphicAction A G) (b : AutomorphicAction B H)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G))
    (hb : b.restrict p = AutomorphicAction.conjugation (𝟙 H))
    (e : LocalGroupIso G H U) (f : LocalGroupIso G K V)
    (he : e.HasInnerDiscrepancy a) (hf : f.HasInnerDiscrepancy a)

/-- The natural central-quotient cocycle of the comparison of two inner local families. -/
def comparisonInnerCocycle : Cocycle B (U ⊗ V) :=
  (e.compareOnProduct f).innerCocycleOfCentralQuotient p hp b hb
    (hq.hasInnerDiscrepancy_compareOnProduct hp a b ha hb e f he hf)

/-- The constructed comparison cocycle records the comparison family's discrepancy. -/
theorem comparisonInnerCocycle_hasDiscrepancy :
    (e.compareOnProduct f).HasDiscrepancy b
      (comparisonInnerCocycle hq hp a b ha hb e f he hf) :=
  (e.compareOnProduct f).innerCocycleOfCentralQuotient_hasDiscrepancy p hp b hb
    (hq.hasInnerDiscrepancy_compareOnProduct hp a b ha hb e f he hf)

variable [Etale U.hom] [Surjective U.hom] [Etale V.hom] [Surjective V.hom]

/-- Triviality of the actual comparison cocycle produces an isomorphism of the forms. -/
def comparisonIsoOfTrivialInnerCocycle
    (hξ : (comparisonInnerCocycle hq hp a b ha hb e f he hf).IsTrivial) : H ≅ K := by
  let : Etale (U ⊗ V).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  let : Surjective (U ⊗ V).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  exact (e.compareOnProduct f).descendOfTrivialFppf b
    (comparisonInnerCocycle hq hp a b ha hb e f he hf)
    (comparisonInnerCocycle_hasDiscrepancy hq hp a b ha hb e f he hf) hξ

end LocalGroupIso

namespace AutomorphicAction

/-- The étale inner-form predicate used in the semi-local quasi-split target, over any
scheme. Its discrepancy is required after every restriction of the test scheme. -/
def IsEtaleInnerForm (a : AutomorphicAction A G) (H : GroupScheme S) : Prop :=
  ∃ U : Over S, Etale U.hom ∧ Surjective U.hom ∧
    ∃ e : LocalGroupIso G H U, e.HasInnerDiscrepancy a

namespace IsEtaleInnerForm

variable (a : AutomorphicAction A G)

/-- An isomorphic group is an inner form for every specified action. -/
theorem of_iso (e : G ≅ H) : a.IsEtaleInnerForm H :=
  ⟨Over.mk (𝟙 S), (by change Etale (𝟙 S); infer_instance),
    (by change Surjective (𝟙 S); infer_instance), LocalGroupIso.ofIso e _,
    LocalGroupIso.ofIso_hasInnerDiscrepancy e a _⟩

/-- Every group is an inner form of itself. -/
theorem refl : a.IsEtaleInnerForm G := of_iso a (Iso.refl G)

variable {q : G ⟶ A} {p : H ⟶ B}
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (hp : RelativeRoot.IsFppfQuotient (center H) p)
    (b : AutomorphicAction B H)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G))
    (hb : b.restrict p = AutomorphicAction.conjugation (𝟙 H))

include hq hp ha hb

/-- Innerness is symmetric for the specified actions of full-centre fppf quotients. -/
theorem symm (he : a.IsEtaleInnerForm H) : b.IsEtaleInnerForm G := by
  obtain ⟨U, hUe, hUs, e, he⟩ := he
  exact ⟨U, hUe, hUs, e.symm,
    hq.hasInnerDiscrepancy_symm hp a b ha hb e he⟩

/-- Innerness composes, with the two étale covers refined to their fibre product. -/
theorem trans (he : a.IsEtaleInnerForm H) (hf : b.IsEtaleInnerForm K) :
    a.IsEtaleInnerForm K := by
  obtain ⟨U, hUe, hUs, e, he⟩ := he
  obtain ⟨V, hVe, hVs, f, hf⟩ := hf
  let : Etale U.hom := hUe
  let : Surjective U.hom := hUs
  let : Etale V.hom := hVe
  let : Surjective V.hom := hVs
  have hWe : Etale (U ⊗ V).hom := by rw [Over.tensorObj_hom]; infer_instance
  have hWs : Surjective (U ⊗ V).hom := by rw [Over.tensorObj_hom]; infer_instance
  exact ⟨U ⊗ V, hWe, hWs, e.transOnProduct f,
    hq.hasInnerDiscrepancy_transOnProduct hp a b ha hb e f he hf⟩

/-- Two inner forms of one source are inner forms of one another. -/
theorem compare (he : a.IsEtaleInnerForm H) (hf : a.IsEtaleInnerForm K) :
    b.IsEtaleInnerForm K := by
  exact trans b hp hq a hb ha (symm a hq hp b ha hb he) hf

/-- Inner-form comparison reduces isomorphism to triviality of its natural cocycle.
Only local families between the specified forms are covered by the vanishing premise. -/
theorem nonempty_iso_of_innerCocycle_trivial
    (he : a.IsEtaleInnerForm H) (hf : a.IsEtaleInnerForm K)
    (htriv : ∀ (W : Over S), Etale W.hom → Surjective W.hom →
      ∀ (d : LocalGroupIso H K W) (hd : d.HasInnerDiscrepancy b),
        (d.innerCocycleOfCentralQuotient p hp b hb hd).IsTrivial) :
    Nonempty (H ≅ K) := by
  obtain ⟨W, hWe, hWs, d, hd⟩ := compare a hq hp b ha hb he hf
  let : Etale W.hom := hWe
  let : Surjective W.hom := hWs
  exact ⟨d.descendOfTrivialFppf b
    (d.innerCocycleOfCentralQuotient p hp b hb hd)
    (d.innerCocycleOfCentralQuotient_hasDiscrepancy p hp b hb hd)
    (htriv W hWe hWs d hd)⟩

end IsEtaleInnerForm
end AutomorphicAction

end Langlands.GroupScheme
