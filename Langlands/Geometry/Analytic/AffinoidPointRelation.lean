import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredRingPointProof
import Langlands.Geometry.Analytic.AffinoidSectionEqualizer
import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedQuotient
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof
import Mathlib.RingTheory.RingHom.Finite

/-! # The finite affinoid relation of a ring-valued point over an affinoid base -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open PresentedAffinoidAlgebra AffinoidPushout

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))} {A B : PresentedAffinoidAlgebra K}

/-- The actual coefficient algebra and two finite maps for the relation
which imposes equality in `X` over `A`. -/
structure AffinoidPointRelation (f : BoundedAlgHom K A B) (x : RingPoints K X B) where
  algebra : PresentedAffinoidAlgebra K
  first : BoundedAlgHom K B algebra
  second : BoundedAlgHom K B algebra
  first_finite : first.toAlgHom.toRingHom.Finite
  second_finite : second.toAlgHom.toRingHom.Finite
  generates : first.toAlgHom.toRingHom.range ⊔ second.toAlgHom.toRingHom.range = ⊤
  factors_iff {T : Type u} [CommRing T] [Algebra K T] (α β : B →ₐ[K] T) :
    (∃ δ : algebra →ₐ[K] T, δ.comp first.toAlgHom = α ∧ δ.comp second.toAlgHom = β) ↔
      α.comp f.toAlgHom = β.comp f.toAlgHom ∧
        RingPoints.changeRing α x = RingPoints.changeRing β x

private theorem affinoidPushout_ring_isPushout (f : BoundedAlgHom K A B)
    (hf : f.IsFiniteBanach) :
    IsPushout (CommRingCat.ofHom f.toAlgHom.toRingHom) (CommRingCat.ofHom f.toAlgHom.toRingHom)
      (CommRingCat.ofHom (leftMap f f).toAlgHom.toRingHom)
      (CommRingCat.ofHom (rightMap f f).toAlgHom.toRingHom) := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let e := RingEquiv.ofBijective (tensorComparison f f) (finiteTensorComparison A B B f f hf)
  exact (CommRingCat.isPushout_tensorProduct A B B).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso
    rfl rfl
    (CommRingCat.hom_ext (RingHom.ext fun b => tensorComparison_tensorRight f f b))
    (CommRingCat.hom_ext (RingHom.ext fun b => tensorComparison_tensorLeft f f b))

private theorem range_sup_of_quotient_pushout (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    {C : PresentedAffinoidAlgebra K} (q : BoundedAlgHom K (algebra f f) C)
    (hq : Function.Surjective q) :
    ((q.comp (leftMap f f)).toAlgHom.toRingHom.range ⊔
      (q.comp (rightMap f f)).toAlgHom.toRingHom.range) = ⊤ := by
  let s := (q.comp (leftMap f f)).toAlgHom.toRingHom.range
  let t := (q.comp (rightMap f f)).toAlgHom.toRingHom.range
  apply top_unique
  intro c hc
  clear hc
  obtain ⟨r, rfl⟩ := hq c
  obtain ⟨m, rfl⟩ := (finiteTensorComparison A B B f f hf).2 r
  change q (tensorComparison f f m) ∈ s ⊔ t
  induction m using algebraicBaseChange_induction f f with
  | mul a b =>
    rw [tensorComparison_mul, map_mul]
    exact (s ⊔ t).mul_mem
      ((show t ≤ s ⊔ t from le_sup_right) ⟨a, rfl⟩)
      ((show s ≤ s ⊔ t from le_sup_left) ⟨b, rfl⟩)
  | add a b ha hb =>
    rw [map_add, map_add]
    exact (s ⊔ t).add_mem ha hb

set_option backward.isDefEq.respectTransparency false in
/-- Restrict the ordinary finite tensor square by the closed diagonal of
`X`, using the presented affinoid pushout and the actual closed quotient. -/
def affinoidPointRelation (hX : IsSeparated X) (f : BoundedAlgHom K A B)
    (hf : f.IsFiniteBanach) (x : RingPoints K X B) : AffinoidPointRelation f x := by
  let E := algebra f f
  let l := leftMap f f
  let r := rightMap f f
  let Q := affinoidSectionEqualizer hX
    (RingPoints.changeRing l.toAlgHom x) (RingPoints.changeRing r.toAlgHom x)
  let C := @ClosedQuotient.algebra K _ _ E Q.ideal Q.isClosed
  let q := @ClosedQuotient.map K _ _ E Q.ideal Q.isClosed
  let s := q.comp l
  let t := q.comp r
  have hq : Function.Surjective q := @ClosedQuotient.map_surjective K _ _ E Q.ideal Q.isClosed
  have hqFin := RingHom.Finite.of_surjective q.toAlgHom.toRingHom hq
  have hPush := affinoidPushout_ring_isPushout f hf
  let F : MorphismProperty CommRingCat.{u} := RingHom.toMorphismProperty (@RingHom.Finite)
  letI : F.IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
      RingHom.finite_isStableUnderBaseChange
  have hlFin : l.toAlgHom.toRingHom.Finite := F.of_isPushout hPush hf.finite
  have hrFin : r.toAlgHom.toRingHom.Finite := F.of_isPushout hPush.flip hf.finite
  refine ⟨C, s, t, hqFin.comp hlFin, hqFin.comp hrFin, range_sup_of_quotient_pushout f hf q hq, ?_⟩
  intro T _ _ α β
  constructor
  · rintro ⟨δ, hδα, hδβ⟩
    let δq := δ.comp q.toAlgHom
    have hδql : δq.comp l.toAlgHom = α := hδα
    have hδqr : δq.comp r.toAlgHom = β := hδβ
    refine ⟨?_, ?_⟩
    · have h := congrArg (fun z : BoundedAlgHom K A E => δq.comp z.toAlgHom) (condition f f)
      change (δq.comp l.toAlgHom).comp f.toAlgHom =
        (δq.comp r.toAlgHom).comp f.toAlgHom at h
      simpa only [hδql, hδqr] using h
    · rw [← hδql, ← hδqr,
        SpaceFilteredRingPoints.changeRing_comp l.toAlgHom δq x,
        SpaceFilteredRingPoints.changeRing_comp r.toAlgHom δq x]
      exact (Q.annihilates_iff δq).mp fun a ha => by
        change δ (q a) = 0
        rw [(@ClosedQuotient.map_eq_zero_iff K _ _ E Q.ideal Q.isClosed a).2 ha, map_zero]
  · rintro ⟨hαβ, hEq⟩
    have hw : CommRingCat.ofHom f.toAlgHom.toRingHom ≫ CommRingCat.ofHom α.toRingHom =
        CommRingCat.ofHom f.toAlgHom.toRingHom ≫ CommRingCat.ofHom β.toRingHom :=
      CommRingCat.hom_ext (congrArg AlgHom.toRingHom hαβ)
    let θ := hPush.desc (CommRingCat.ofHom α.toRingHom) (CommRingCat.ofHom β.toRingHom) hw
    have hl : θ.hom.comp l.toAlgHom.toRingHom = α.toRingHom :=
      congrArg CommRingCat.Hom.hom (hPush.inl_desc _ _ hw)
    have hr : θ.hom.comp r.toAlgHom.toRingHom = β.toRingHom :=
      congrArg CommRingCat.Hom.hom (hPush.inr_desc _ _ hw)
    let δ : E →ₐ[K] T := { θ.hom with
      commutes' := fun k => by
        have h := RingHom.congr_fun hl (algebraMap K B k)
        change θ.hom (l (algebraMap K B k)) = α (algebraMap K B k) at h
        rwa [l.toAlgHom.commutes, α.commutes] at h }
    have hδl : δ.comp l.toAlgHom = α := AlgHom.coe_ringHom_injective hl
    have hδr : δ.comp r.toAlgHom = β := AlgHom.coe_ringHom_injective hr
    have hδ0 : ∀ a ∈ Q.ideal, δ a = 0 := (Q.annihilates_iff δ).mpr (by
      rw [← SpaceFilteredRingPoints.changeRing_comp, ← SpaceFilteredRingPoints.changeRing_comp,
        hδl, hδr]
      exact hEq)
    have hKer : RingHom.ker q.toAlgHom.toRingHom ≤ RingHom.ker δ.toRingHom :=
      fun a ha => hδ0 a ((@ClosedQuotient.map_eq_zero_iff K _ _ E Q.ideal Q.isClosed a).mp ha)
    let δ' : C →ₐ[K] T := q.toAlgHom.liftOfSurjective hq δ hKer
    refine ⟨δ', ?_, ?_⟩
    · ext b
      change δ' (q (l b)) = α b
      exact (AlgHom.liftOfSurjective_apply _ _ _ _ _).trans (AlgHom.congr_fun hδl b)
    · ext b
      change δ' (q (r b)) = β b
      exact (AlgHom.liftOfSurjective_apply _ _ _ _ _).trans (AlgHom.congr_fun hδr b)

namespace AffinoidPointRelation

variable {f : BoundedAlgHom K A B} {x : RingPoints K X B} (V : AffinoidPointRelation f x)

omit [CompleteSpace K] in
theorem condition :
    V.first.comp f = V.second.comp f ∧
      RingPoints.changeRing V.first.toAlgHom x = RingPoints.changeRing V.second.toAlgHom x := by
  obtain ⟨h, hx⟩ := (V.factors_iff V.first.toAlgHom V.second.toAlgHom).mp
    ⟨AlgHom.id K V.algebra, by rw [AlgHom.id_comp], by rw [AlgHom.id_comp]⟩
  exact ⟨BoundedAlgHom.ext fun a => AlgHom.congr_fun h a, hx⟩

omit [CompleteSpace K] in
/-- For the ordinary ring tests, a relation witness also identifies the
two induced scalar structures on the test ring. -/
theorem ringEquivalence (T : Type u) [CommRing T] :
    _root_.Equivalence fun α β : B →+* T => ∃ δ : V.algebra →+* T,
      δ.comp V.first.toAlgHom.toRingHom = α ∧ δ.comp V.second.toAlgHom.toRingHom = β := by
  let Rel (α β : B →+* T) := ∃ δ : V.algebra →+* T,
    δ.comp V.first.toAlgHom.toRingHom = α ∧ δ.comp V.second.toAlgHom.toRingHom = β
  have hScalar {α β : B →+* T} (h : Rel α β) :
      α.comp (algebraMap K B) = β.comp (algebraMap K B) := by
    obtain ⟨δ, rfl, rfl⟩ := h
    apply RingHom.ext
    intro k
    change δ (V.first (algebraMap K B k)) = δ (V.second (algebraMap K B k))
    rw [V.first.toAlgHom.commutes, V.second.toAlgHom.commutes]
  have hCriterion [Algebra K T] (α β : B →ₐ[K] T) :
      Rel α.toRingHom β.toRingHom ↔
        α.comp f.toAlgHom = β.comp f.toAlgHom ∧
          RingPoints.changeRing α x = RingPoints.changeRing β x := by
    rw [← V.factors_iff α β]
    constructor
    · rintro ⟨δ, hdα, hdβ⟩
      let d : V.algebra →ₐ[K] T := { δ with
        commutes' := fun k => by
          have h := RingHom.congr_fun hdα (algebraMap K B k)
          change δ (V.first (algebraMap K B k)) = α (algebraMap K B k) at h
          rwa [V.first.toAlgHom.commutes, α.commutes] at h }
      exact ⟨d, AlgHom.coe_ringHom_injective hdα, AlgHom.coe_ringHom_injective hdβ⟩
    · rintro ⟨d, hdα, hdβ⟩
      exact ⟨d.toRingHom, congrArg AlgHom.toRingHom hdα, congrArg AlgHom.toRingHom hdβ⟩
  constructor
  · intro α
    let : Algebra K T := (α.comp (algebraMap K B)).toAlgebra
    let a : B →ₐ[K] T := { α with commutes' := fun _ => rfl }
    exact (hCriterion a a).mpr ⟨rfl, rfl⟩
  · intro α β h
    let : Algebra K T := (α.comp (algebraMap K B)).toAlgebra
    let a : B →ₐ[K] T := { α with commutes' := fun _ => rfl }
    let b : B →ₐ[K] T := { β with
      commutes' := fun k => (RingHom.congr_fun (hScalar h) k).symm }
    obtain ⟨h₁, h₂⟩ := (hCriterion a b).mp h
    exact (hCriterion b a).mpr ⟨h₁.symm, h₂.symm⟩
  · intro α β γ h₁ h₂
    let : Algebra K T := (α.comp (algebraMap K B)).toAlgebra
    let a : B →ₐ[K] T := { α with commutes' := fun _ => rfl }
    let b : B →ₐ[K] T := { β with
      commutes' := fun k => (RingHom.congr_fun (hScalar h₁) k).symm }
    let c : B →ₐ[K] T := { γ with
      commutes' := fun k => (RingHom.congr_fun ((hScalar h₁).trans (hScalar h₂)) k).symm }
    obtain ⟨h₁base, h₁point⟩ := (hCriterion a b).mp h₁
    obtain ⟨h₂base, h₂point⟩ := (hCriterion b c).mp h₂
    exact (hCriterion a c).mpr ⟨h₁base.trans h₂base, h₁point.trans h₂point⟩

end AffinoidPointRelation

end Langlands.Analytic.SpaceAnalytification
