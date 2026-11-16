import Langlands.AlgebraicGeometry.Picard.LocalRepresenterRelation

/-! # The étale equivalence relation of a local presheaf representer -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.LocalRepresenter

variable {S U : Scheme.{u}} (p : U ⟶ S)
    {F : (Over S)ᵒᵖ ⥤ Type v} {M : Over U}
    (e : ((Over.map p).op ⋙ F).RepresentableBy M)

@[simp]
theorem first_base : first p ≫ (chart p (M := M)).hom =
    (overlapOverS p (M := M)).hom := pullback.condition

@[simp]
theorem second_base : second p e ≫ (chart p (M := M)).hom =
    (overlapOverS p (M := M)).hom := by
  change (secondOver p e).left ≫ (M.hom ≫ p) = _
  rw [← Category.assoc, (secondOver p e).w]
  rfl

/-- Uniqueness of an overlap point as a morphism of schemes. -/
theorem hom_ext {T : Scheme.{u}} {r r' : T ⟶ overlap p (M := M)}
    (ht : r ≫ first p = r' ≫ first p)
    (hs : r ≫ second p e = r' ≫ second p e) : r = r' := by
  apply pullback.hom_ext
  · exact ht
  · have h := congrArg (· ≫ M.hom) hs
    simpa only [second, Category.assoc, (secondOver p e).w,
      overlapOver, Over.mk_hom] using h

@[simp]
theorem exchangeIso_first : (exchangeIso p e).hom ≫ first p = second p e :=
  congrArg Over.Hom.left (exchange_first p e)

@[simp]
theorem exchangeIso_second : (exchangeIso p e).hom ≫ second p e = first p :=
  congrArg Over.Hom.left (exchange_second p e)

/-- Reflexivity of the overlap relation on arbitrary scheme-valued points. -/
theorem exists_refl (T : Scheme.{u}) (a : T ⟶ M.left) :
    ∃ r : T ⟶ overlap p (M := M), r ≫ first p = a ∧ r ≫ second p e = a := by
  let T' : Over S := Over.mk (a ≫ M.hom ≫ p)
  let a' : T' ⟶ chart p (M := M) := Over.homMk a rfl
  refine ⟨(kernelLift p e a' a' rfl).left, ?_, ?_⟩
  · exact congrArg Over.Hom.left (kernelLift_first p e a' a' rfl)
  · exact congrArg Over.Hom.left (kernelLift_second p e a' a' rfl)

/-- Transitivity of the overlap relation on arbitrary scheme-valued points. -/
theorem exists_trans (T : Scheme.{u}) (r r' : T ⟶ overlap p (M := M))
    (h : r ≫ second p e = r' ≫ first p) :
    ∃ r'' : T ⟶ overlap p (M := M),
      r'' ≫ first p = r ≫ first p ∧ r'' ≫ second p e = r' ≫ second p e := by
  have hb : r' ≫ (overlapOverS p (M := M)).hom =
      r ≫ (overlapOverS p (M := M)).hom := by
    calc
      r' ≫ (overlapOverS p (M := M)).hom =
          (r' ≫ first p) ≫ (chart p (M := M)).hom := by
        rw [Category.assoc, first_base]
      _ = (r ≫ second p e) ≫ (chart p (M := M)).hom := by rw [h]
      _ = r ≫ (overlapOverS p (M := M)).hom := by
        rw [Category.assoc, second_base]
  let T' : Over S := Over.mk (r ≫ (overlapOverS p (M := M)).hom)
  let a : T' ⟶ overlapOverS p (M := M) := Over.homMk r rfl
  let b : T' ⟶ overlapOverS p (M := M) := Over.homMk r' hb
  have hm : a ≫ secondOverS p e = b ≫ firstOver p := by
    apply Over.OverMorphism.ext
    exact h
  have hw : F.map (a ≫ firstOver p).op (family p e) =
      F.map (b ≫ secondOverS p e).op (family p e) := by
    rw [kernel_w p e a, hm, kernel_w p e b]
  refine ⟨(kernelLift p e (a ≫ firstOver p) (b ≫ secondOverS p e) hw).left, ?_, ?_⟩
  · exact congrArg Over.Hom.left (kernelLift_first p e _ _ hw)
  · exact congrArg Over.Hom.left (kernelLift_second p e _ _ hw)

/-- The overlap of a representer after an étale base map is an actual étale
 equivalence relation, without a sheaf hypothesis. -/
def etaleRelation [Etale p] : EtaleEquivalenceRelation.{u} where
  U := M.left
  R := overlap p (M := M)
  t := first p
  s := second p e
  mono_lift := by
    constructor
    intro T x y h
    apply hom_ext p e
    · simpa using congrArg (· ≫ prod.fst) h
    · simpa using congrArg (· ≫ prod.snd) h
  refl := exists_refl p e
  symm T r := ⟨r ≫ (exchangeIso p e).hom, by simp, by simp⟩
  trans := exists_trans p e
  etale_t := inferInstance
  etale_s := by
    rw [← exchangeIso_first p e]
    infer_instance

end Langlands.AlgebraicGeometry.Picard.LocalRepresenter
