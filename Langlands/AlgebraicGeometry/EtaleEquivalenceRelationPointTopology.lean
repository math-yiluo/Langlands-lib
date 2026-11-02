import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationOrbitTopology
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Topology.LocalAtTarget

/-! # Finite closed orbits of actual étale scheme relations -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Set TopologicalSpace

namespace Langlands.AlgebraicGeometry

namespace FiniteOrbitTopology

variable {X : Type u} [TopologicalSpace X]
  {R : Type v} [TopologicalSpace R]

/-- A finite T₀ space with one orbit for a continuous source and open target
with discrete source fibers is discrete. -/
lemma discreteTopology_of_transitive_open_relation [T0Space X] [Finite X]
    (s t : R → X) (hs : Continuous s) (hto : IsOpenMap t)
    (hfib : ∀ x : X, IsDiscrete (s ⁻¹' {x}))
    (htrans : ∀ x y : X, ∃ r : R, s r = x ∧ t r = y) :
    DiscreteTopology X := by
  cases isEmpty_or_nonempty X with
  | inl h => exact inferInstance
  | inr h =>
    obtain ⟨x, hx⟩ := exists_open_singleton_of_finite (X := X)
    have himage : t '' (s ⁻¹' {x}) = univ := by
      apply eq_univ_of_forall
      intro y
      obtain ⟨r, hr, hrt⟩ := htrans x y
      exact ⟨r, hr, hrt⟩
    have hd := (hfib x).image_of_isOpenMap_of_isOpen hto (hx.preimage hs)
    rw [himage] at hd
    exact isDiscrete_univ_iff.mp hd

/-- A finite invariant class is discrete under the topological hypotheses of
an étale relation; no scheme restriction is required for this step. -/
lemma isDiscrete_of_finite_class [T0Space X]
    (s t : R → X) (hs : Continuous s) (hto : IsOpenMap t)
    (hfib : ∀ x : X, IsDiscrete (s ⁻¹' {x}))
    (T : Set X) (hfinite : T.Finite)
    (hinv : s ⁻¹' T = t ⁻¹' T)
    (htrans : ∀ x ∈ T, ∀ y ∈ T, ∃ r : R, s r = x ∧ t r = y) :
    IsDiscrete T := by
  let : Finite T := hfinite.to_subtype
  let s' : (s ⁻¹' T) → T := T.restrictPreimage s
  let t' : (s ⁻¹' T) → T :=
    fun r => ⟨t r, by
      change r.val ∈ t ⁻¹' T
      rw [← hinv]
      exact r.property⟩
  have hs' : Continuous s' := by
    exact (hs.comp continuous_subtype_val).subtype_mk _
  have ht' : IsOpenMap t' := by
    have heq : t' = (T.restrictPreimage t) ∘ (Homeomorph.setCongr hinv) := rfl
    rw [heq]
    exact (hto.restrictPreimage T).comp (Homeomorph.setCongr hinv).isOpenMap
  have hfib' : ∀ x : T, IsDiscrete (s' ⁻¹' {x}) := by
    intro x
    have hd := (hfib x.val).preimage
      (continuous_subtype_val (p := fun r => r ∈ s ⁻¹' T)).continuousOn
      Subtype.val_injective
    convert hd using 1
    ext r
    exact Subtype.ext_iff
  have htrans' : ∀ x y : T, ∃ r : (s ⁻¹' T), s' r = x ∧ t' r = y := by
    intro x y
    obtain ⟨r, hr, hrt⟩ := htrans x x.property y y.property
    refine ⟨⟨r, ?_⟩, Subtype.ext hr, Subtype.ext hrt⟩
    change s r ∈ T
    rw [hr]
    exact x.property
  exact ⟨discreteTopology_of_transitive_open_relation s' t' hs' ht' hfib' htrans'⟩

end FiniteOrbitTopology

namespace EtaleEquivalenceRelation

/-- The relation on underlying scheme points represented by an actual point
of the relation scheme, with source first. -/
def PointRel (E : EtaleEquivalenceRelation.{u}) (x y : E.U) : Prop :=
  ∃ r : E.R, E.s r = x ∧ E.t r = y

lemma pointRel_refl (E : EtaleEquivalenceRelation.{u}) (x : E.U) : E.PointRel x x := by
  obtain ⟨e, het, hes⟩ := E.refl E.U (𝟙 E.U)
  exact ⟨e x, congrArg (fun f : E.U ⟶ E.U => f x) hes,
    congrArg (fun f : E.U ⟶ E.U => f x) het⟩

lemma pointRel_symm (E : EtaleEquivalenceRelation.{u}) {x y : E.U}
    (h : E.PointRel x y) : E.PointRel y x := by
  obtain ⟨r, hr, hrt⟩ := h
  obtain ⟨i, hit, his⟩ := E.symm E.R (𝟙 E.R)
  refine ⟨i r, ?_, ?_⟩
  · exact (congrArg (fun f : E.R ⟶ E.U => f r) his).trans hrt
  · exact (congrArg (fun f : E.R ⟶ E.U => f r) hit).trans hr

lemma pointRel_trans (E : EtaleEquivalenceRelation.{u}) {x y z : E.U}
    (hxy : E.PointRel x y) (hyz : E.PointRel y z) : E.PointRel x z := by
  obtain ⟨r, hrs, hrt⟩ := hxy
  obtain ⟨r', hr's, hr't⟩ := hyz
  obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := E.t) (g := E.s) r r' (hrt.trans hr's.symm)
  obtain ⟨c, hct, hcs⟩ := E.trans (pullback E.t E.s)
    (pullback.snd E.t E.s) (pullback.fst E.t E.s) pullback.condition.symm
  refine ⟨c p, ?_, ?_⟩
  · exact (congrArg (fun f : pullback E.t E.s ⟶ E.U => f p) hcs).trans
      ((congrArg E.s hp₁).trans hrs)
  · exact (congrArg (fun f : pullback E.t E.s ⟶ E.U => f p) hct).trans
      ((congrArg E.t hp₂).trans hr't)

/-- The actual equivalence relation induced on underlying scheme points. -/
def pointSetoid (E : EtaleEquivalenceRelation.{u}) : Setoid E.U where
  r := E.PointRel
  iseqv := ⟨E.pointRel_refl, E.pointRel_symm, E.pointRel_trans⟩

/-- A set of scheme points is invariant under the actual relation. -/
def PointInvariant (E : EtaleEquivalenceRelation.{u}) (T : Set E.U) : Prop :=
  ∀ ⦃x y : E.U⦄, E.PointRel x y → x ∈ T → y ∈ T

lemma pointInvariant_preimage_eq (E : EtaleEquivalenceRelation.{u})
    {T : Set E.U} (hT : E.PointInvariant T) :
    E.s ⁻¹' T = E.t ⁻¹' T := by
  ext r
  exact ⟨hT ⟨r, rfl, rfl⟩, hT (E.pointRel_symm ⟨r, rfl, rfl⟩)⟩

private lemma locallyQuasiFinite_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h := f.etale_appLE U.property V.property e
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
  let := h.toAlgebra
  exact inferInstanceAs (@Algebra.QuasiFinite _ _ _ _ (f.appLE U V e).hom.toAlgebra)

lemma pointInvariant_closure (E : EtaleEquivalenceRelation.{u})
    {T : Set E.U} (hT : E.PointInvariant T) : E.PointInvariant (closure T) := by
  let := E.etale_s
  let := E.etale_t
  let := E.pointSetoid
  exact FiniteOrbitTopology.invariant_closure_of_open_maps E.s E.t
    E.s.continuous E.t.continuous E.s.isOpenMap E.t.isOpenMap (fun _ _ => Iff.rfl) hT

lemma pointRel_finite (E : EtaleEquivalenceRelation.{u}) [IsAffine E.U] [IsAffine E.R]
    (x : E.U) : {y : E.U | E.PointRel x y}.Finite := by
  let := E.etale_s
  let := locallyQuasiFinite_of_etale E.s
  have heq : {y : E.U | E.PointRel x y} = E.t '' (E.s ⁻¹' {x}) := by
    ext y
    exact Iff.rfl
  rw [heq]
  exact (E.s.finite_preimage_singleton x).image E.t

/-- The minimal nonempty closed invariant subset inside a supplied invariant
closed subset of a Noetherian object scheme. -/
noncomputable def minimalClosedPointInvariant (E : EtaleEquivalenceRelation.{u})
    [IsNoetherian E.U] (T : Closeds E.U)
    (hT : (T : Set E.U).Nonempty ∧ E.PointInvariant T) : Closeds E.U := by
  let := E.pointSetoid
  exact FiniteOrbitTopology.minimalClosedInvariant T hT

lemma minimalClosedPointInvariant_spec (E : EtaleEquivalenceRelation.{u})
    [IsNoetherian E.U] (T : Closeds E.U)
    (hT : (T : Set E.U).Nonempty ∧ E.PointInvariant T) :
    E.minimalClosedPointInvariant T hT ≤ T ∧
      Minimal (fun S : Closeds E.U => (S : Set E.U).Nonempty ∧ E.PointInvariant S)
        (E.minimalClosedPointInvariant T hT) := by
  let := E.pointSetoid
  exact FiniteOrbitTopology.minimalClosedInvariant_spec T hT

lemma eq_pointRel_of_minimal (E : EtaleEquivalenceRelation.{u})
    [IsAffine E.U] [IsAffine E.R] (T : Closeds E.U)
    (hT : Minimal (fun S : Closeds E.U => (S : Set E.U).Nonempty ∧ E.PointInvariant S) T)
    {x : E.U} (hx : x ∈ T) :
    (T : Set E.U) = {y : E.U | E.PointRel x y} := by
  let := E.pointSetoid
  exact FiniteOrbitTopology.eq_class_of_minimal_closed_invariant
    (fun _ h => E.pointInvariant_closure h) E.pointRel_finite T hT hx

/-- A minimal nonempty closed invariant subset of the actual affine étale
relation is finite, discrete, and consists of closed points of the object scheme. -/
lemma finite_discrete_closedPoints_of_minimal (E : EtaleEquivalenceRelation.{u})
    [IsAffine E.U] [IsAffine E.R] (T : Closeds E.U)
    (hT : Minimal (fun S : Closeds E.U => (S : Set E.U).Nonempty ∧ E.PointInvariant S) T) :
    (T : Set E.U).Finite ∧ _root_.IsDiscrete (T : Set E.U) ∧
      ∀ x ∈ T, IsClosed ({x} : Set E.U) := by
  let := E.etale_s
  let := E.etale_t
  let := locallyQuasiFinite_of_etale E.s
  obtain ⟨x, hx⟩ := hT.1.1
  have hfinite : (T : Set E.U).Finite := by
    rw [E.eq_pointRel_of_minimal T hT hx]
    exact E.pointRel_finite x
  have hd : _root_.IsDiscrete (T : Set E.U) :=
    FiniteOrbitTopology.isDiscrete_of_finite_class E.s E.t E.s.continuous E.t.isOpenMap
      E.s.isDiscrete_preimage_singleton T hfinite (E.pointInvariant_preimage_eq hT.1.2)
      (fun a ha b hb => by
        change E.PointRel a b
        rw [E.eq_pointRel_of_minimal T hT ha] at hb
        exact hb)
  refine ⟨hfinite, hd, fun y hy => ?_⟩
  exact isClosed_of_subset_discrete_closed (singleton_subset_iff.mpr hy) hd T.isClosed

end EtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
