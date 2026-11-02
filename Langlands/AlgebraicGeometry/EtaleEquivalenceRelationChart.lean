import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationGeometry

/-! # Restricting an étale equivalence relation to an étale chart

The induced relation on `V → U` is `V ×_{U,t} R ×_{s,U} V`.
These internal constructions use only the scheme-valued equivalence relation
axioms and pullback properties.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

namespace Chart

variable (E : EtaleEquivalenceRelation.{u}) {V : Scheme.{u}} (f : V ⟶ E.U)

/-- The scheme of arrows of the induced relation on a chart. -/
noncomputable abbrev arrows : Scheme.{u} :=
  pullback (pullback.snd f E.t ≫ E.s) f

/-- First endpoint of an induced arrow. -/
noncomputable def t : arrows E f ⟶ V :=
  pullback.fst (pullback.snd f E.t ≫ E.s) f ≫ pullback.fst f E.t

/-- Second endpoint of an induced arrow. -/
noncomputable def s : arrows E f ⟶ V :=
  pullback.snd (pullback.snd f E.t ≫ E.s) f

/-- Forget the chart lifts of both endpoints. -/
noncomputable def map : arrows E f ⟶ E.R :=
  pullback.fst (pullback.snd f E.t ≫ E.s) f ≫ pullback.snd f E.t

@[reassoc]
lemma map_t : map E f ≫ E.t = t E f ≫ f := by
  simp only [map, t, Category.assoc]
  rw [← pullback.condition]

@[reassoc]
lemma map_s : map E f ≫ E.s = s E f ≫ f := by
  simpa only [map, s, Category.assoc] using
    (pullback.condition (f := pullback.snd f E.t ≫ E.s) (g := f))

/-- Lift an original arrow whose endpoints lift to the chart. -/
noncomputable def lift {T : Scheme.{u}} (a b : T ⟶ V) (r : T ⟶ E.R)
    (ht : r ≫ E.t = a ≫ f) (hs : r ≫ E.s = b ≫ f) : T ⟶ arrows E f :=
  pullback.lift (pullback.lift a r ht.symm) b (by
    rw [← Category.assoc, pullback.lift_snd, hs])

@[reassoc (attr := simp)]
lemma lift_t {T : Scheme.{u}} (a b : T ⟶ V) (r : T ⟶ E.R)
    (ht : r ≫ E.t = a ≫ f) (hs : r ≫ E.s = b ≫ f) :
    lift E f a b r ht hs ≫ t E f = a := by
  dsimp only [lift, t]
  rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma lift_s {T : Scheme.{u}} (a b : T ⟶ V) (r : T ⟶ E.R)
    (ht : r ≫ E.t = a ≫ f) (hs : r ≫ E.s = b ≫ f) :
    lift E f a b r ht hs ≫ s E f = b := by
  exact pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma lift_map {T : Scheme.{u}} (a b : T ⟶ V) (r : T ⟶ E.R)
    (ht : r ≫ E.t = a ≫ f) (hs : r ≫ E.s = b ≫ f) :
    lift E f a b r ht hs ≫ map E f = r := by
  dsimp only [lift, map]
  rw [← Category.assoc, pullback.lift_fst, pullback.lift_snd]

/-- Chart arrows are determined by their endpoints and original arrow. -/
lemma hom_ext' {T : Scheme.{u}} {a b : T ⟶ arrows E f}
    (ht : a ≫ t E f = b ≫ t E f) (hs : a ≫ s E f = b ≫ s E f)
    (hr : a ≫ map E f = b ≫ map E f) : a = b := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [t, Category.assoc] using ht
    · simpa only [map, Category.assoc] using hr
  · exact hs

/-- Both chart endpoints determine the original arrow as well. -/
lemma hom_ext {T : Scheme.{u}} {a b : T ⟶ arrows E f}
    (ht : a ≫ t E f = b ≫ t E f) (hs : a ≫ s E f = b ≫ s E f) : a = b := by
  apply hom_ext' E f ht hs
  apply E.hom_ext
  · rw [Category.assoc, Category.assoc, map_t, ← Category.assoc, ht, Category.assoc]
  · rw [Category.assoc, Category.assoc, map_s, ← Category.assoc, hs, Category.assoc]

/-- The induced relation is the base change of the original closed relation
along the map of absolute squares. -/
lemma isPullback_pair :
    IsPullback (map E f) (prod.lift (t E f) (s E f))
      (prod.lift E.t E.s) (prod.map f f) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · ext
    · simpa using map_t E f
    · simpa using map_s E f
  · intro T a b ha hab
    apply hom_ext E f
    · simpa using congrArg (· ≫ prod.fst) hab
    · simpa using congrArg (· ≫ prod.snd) hab
  · intro T a b hab
    have ht : a ≫ E.t = (b ≫ prod.fst) ≫ f := by
      simpa using congrArg (· ≫ prod.fst) hab
    have hs : a ≫ E.s = (b ≫ prod.snd) ≫ f := by
      simpa using congrArg (· ≫ prod.snd) hab
    refine ⟨lift E f (b ≫ prod.fst) (b ≫ prod.snd) a ht hs, by simp, ?_⟩
    ext <;> simp

lemma isClosedImmersion_pair [IsClosedImmersion (prod.lift E.t E.s)] :
    IsClosedImmersion (prod.lift (t E f) (s E f)) :=
  MorphismProperty.of_isPullback (isPullback_pair E f) inferInstance

lemma isAffine_arrows [IsAffine E.U] [IsAffine E.R] [IsAffine V] :
    IsAffine (arrows E f) := by
  dsimp only [arrows]
  infer_instance

lemma etale_t [Etale f] : Etale (t E f) := by
  let := E.etale_t
  dsimp only [t]
  infer_instance

lemma etale_s [Etale f] : Etale (s E f) := by
  let := E.etale_s
  dsimp only [s]
  infer_instance

end Chart

variable (E : EtaleEquivalenceRelation.{u})

/-- The equivalence relation induced on an étale chart. -/
noncomputable def chart {V : Scheme.{u}} (f : V ⟶ E.U) [Etale f] :
    EtaleEquivalenceRelation.{u} where
  U := V
  R := Chart.arrows E f
  t := Chart.t E f
  s := Chart.s E f
  mono_lift := by
    constructor
    intro T a b hab
    apply Chart.hom_ext E f
    · simpa using congrArg (· ≫ prod.fst) hab
    · simpa using congrArg (· ≫ prod.snd) hab
  refl := by
    intro T a
    exact ⟨Chart.lift E f a a (a ≫ f ≫ E.unit) (by simp) (by simp), by simp, by simp⟩
  symm := by
    intro T r
    have ht : (r ≫ Chart.map E f ≫ E.inverse) ≫ E.t = (r ≫ Chart.s E f) ≫ f := by
      simpa only [Category.assoc, inverse_t] using
        congrArg (fun k => r ≫ k) (Chart.map_s E f)
    have hs : (r ≫ Chart.map E f ≫ E.inverse) ≫ E.s = (r ≫ Chart.t E f) ≫ f := by
      simpa only [Category.assoc, inverse_s] using
        congrArg (fun k => r ≫ k) (Chart.map_t E f)
    exact ⟨Chart.lift E f (r ≫ Chart.s E f) (r ≫ Chart.t E f)
      (r ≫ Chart.map E f ≫ E.inverse) ht hs, by simp, by simp⟩
  trans := by
    intro T a b hab
    have hw : (a ≫ Chart.map E f) ≫ E.s = (b ≫ Chart.map E f) ≫ E.t := by
      rw [Category.assoc, Category.assoc, Chart.map_s, Chart.map_t,
        ← Category.assoc, hab, Category.assoc]
    have ht : E.compose (a ≫ Chart.map E f) (b ≫ Chart.map E f) hw ≫ E.t =
        (a ≫ Chart.t E f) ≫ f := by
      rw [compose_t, Category.assoc, Chart.map_t, ← Category.assoc]
    have hs : E.compose (a ≫ Chart.map E f) (b ≫ Chart.map E f) hw ≫ E.s =
        (b ≫ Chart.s E f) ≫ f := by
      rw [compose_s, Category.assoc, Chart.map_s, ← Category.assoc]
    exact ⟨Chart.lift E f (a ≫ Chart.t E f) (b ≫ Chart.s E f)
      (E.compose (a ≫ Chart.map E f) (b ≫ Chart.map E f) hw) ht hs, by simp, by simp⟩
  etale_t := Chart.etale_t E f
  etale_s := Chart.etale_s E f

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
