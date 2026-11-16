import Langlands.GroupScheme.RelativeLevi.ParabolicFiniteQuotientChart
import Langlands.GroupScheme.RelativeLevi.ParabolicFiniteTypesStatement

/-! # Uniform field types distinguish actual parabolic quotient components -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} {I : Type u}
    {P : I → GroupScheme S} (j : ∀ a, P a ⟶ G)

/-- The supplied relative subgroups represent exactly once every rational
parabolic conjugacy class over every field-valued point of the base. -/
def HasUniformParabolicFieldTypes : Prop :=
  ∀ (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (Q : GroupScheme (Spec (CommRingCat.of k)))
    (i : Q ⟶ (GroupScheme.baseChange x).obj G),
    IsParabolicSubgroup i →
    ∃! a : I, ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        ((GroupScheme.baseChange x).obj G).X,
      range (i ≫ (((GroupScheme.baseChange x).obj G).innerIso g).hom) =
        range ((GroupScheme.baseChange x).map (j a))

variable (hG : IsReductive G) (hj : ∀ a, IsRelativeParabolicSubgroup (j a))

set_option maxHeartbeats 800000 in
/-- Uniform field types distinguish two actual conjugate families on a field test. -/
theorem conjugateParabolic_index_eq_of_fieldTypes
    (htypes : HasUniformParabolicFieldTypes j)
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (a b : I) (g h : Over.mk x ⟶ G.X)
    (heq : conjugateParabolic hG (j a) (hj a) g =
      conjugateParabolic hG (j b) (hj b) h) : a = b := by
  let Gk := (GroupScheme.baseChange x).obj G
  let ia := (GroupScheme.baseChange x).map (j a)
  let ib := (GroupScheme.baseChange x).map (j b)
  let gk := (baseChangeBasePointsEquiv x G).symm g
  let hk := (baseChangeBasePointsEquiv x G).symm h
  have hr : range (ia ≫ (Gk.innerIso gk).hom) =
      range (ib ≫ (Gk.innerIso hk).hom) := congrArg Subtype.val heq
  have hc := (range_comp_iso_eq_iff _ _ (Gk.innerIso hk).symm).mpr hr
  have hab : range (ia ≫ (Gk.innerIso (hk⁻¹ * gk)).hom) = range ib := by
    simpa only [innerIso_mul_hom, innerIso_inv_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using hc
  obtain ⟨c, _, huniq⟩ := htypes k x _ ia
    ((hj a).isParabolicSubgroup_baseChange hG x)
  have ha : ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Gk.X,
      range (ia ≫ (Gk.innerIso z).hom) = range ia :=
    ⟨1, by rw [innerIso_one_hom, Category.comp_id]⟩
  exact (huniq a ha).trans (huniq b ⟨hk⁻¹ * gk, hab⟩).symm

section Affine

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) {I : Type u} {P : I → GroupScheme (Spec (CommRingCat.of R))}
    (j : ∀ a, P a ⟶ G) (hj : ∀ a, IsRelativeParabolicSubgroup (j a))

/-- The component family evaluates every lift to its actual conjugate parabolic. -/
theorem restrict_affineParabolicQuotientFamilies_comp
    {T : Over (Spec (CommRingCat.of R))} (a : I) (g : T ⟶ G.X) :
    restrict hG (g ≫ (affineParabolicQuotient hG (j a) (hj a)).quotient.projection)
      (affineParabolicQuotientFamilies hG j hj a) =
      conjugateParabolic hG (j a) (hj a) g := by
  let Q := (affineParabolicQuotient hG (j a) (hj a)).quotient
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  exact restrict_quotientParabolic_comp hG (j a) (hj a) Q.projection
    (fun U g h hgh => (range (j a)).le_normalizer U ((Q.fibers U g h).mp hgh)) g

/-- Under uniform field types, equal values from two quotient components force
equal indices whenever the test scheme is nonempty. -/
theorem affineParabolicQuotientFamilies_disjoint_of_fieldTypes
    (htypes : HasUniformParabolicFieldTypes j) (a b : I)
    (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ affineParabolicQuotientComponents hG j hj a)
    (y : T ⟶ affineParabolicQuotientComponents hG j hj b)
    (hxy : restrict hG x (affineParabolicQuotientFamilies hG j hj a) =
      restrict hG y (affineParabolicQuotientFamilies hG j hj b)) :
    a = b ∨ IsEmpty T.left := by
  classical
  by_cases hT : Nonempty T.left
  swap
  · exact Or.inr ⟨fun t => hT ⟨t⟩⟩
  apply Or.inl
  let Qa := (affineParabolicQuotient hG (j a) (hj a)).quotient
  let Qb := (affineParabolicQuotient hG (j b) (hj b)).quotient
  let A := pullback x Qa.projection
  let r₁ : A ⟶ T := pullback.fst x Qa.projection
  let g₁ : A ⟶ G.X := pullback.snd x Qa.projection
  let B := pullback (r₁ ≫ y) Qb.projection
  let r₂ : B ⟶ A := pullback.fst (r₁ ≫ y) Qb.projection
  let g₂ : B ⟶ G.X := pullback.snd (r₁ ≫ y) Qb.projection
  have hs₁ : Surjective r₁.left :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (((IsPullback.of_hasPullback x Qa.projection).map (Over.forget _)).flip)
      Qa.surjective_projection
  have hs₂ : Surjective r₂.left :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (((IsPullback.of_hasPullback (r₁ ≫ y) Qb.projection).map (Over.forget _)).flip)
      Qb.surjective_projection
  obtain ⟨t⟩ := hT
  obtain ⟨t₁, _⟩ := hs₁.surj t
  obtain ⟨t₂, _⟩ := hs₂.surj t₁
  let c : B ⟶ T := r₂ ≫ r₁
  have hc₁ : (r₂ ≫ g₁) ≫ Qa.projection = c ≫ x := by
    dsimp [c, g₁, r₁]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  have hc₂ : g₂ ≫ Qb.projection = c ≫ y := by
    dsimp [c, g₂, r₂]
    rw [← pullback.condition, Category.assoc]
  have heq : conjugateParabolic hG (j a) (hj a) (r₂ ≫ g₁) =
      conjugateParabolic hG (j b) (hj b) g₂ := by
    rw [← restrict_affineParabolicQuotientFamilies_comp,
      ← restrict_affineParabolicQuotientFamilies_comp, hc₁, hc₂]
    calc
      restrict hG (c ≫ x) (affineParabolicQuotientFamilies hG j hj a) =
          restrict hG c (restrict hG x
            (affineParabolicQuotientFamilies hG j hj a)) :=
        (restrict_comp hG x c _).symm
      _ = restrict hG c (restrict hG y
            (affineParabolicQuotientFamilies hG j hj b)) := congrArg _ hxy
      _ = restrict hG (c ≫ y) (affineParabolicQuotientFamilies hG j hj b) :=
        restrict_comp hG y c _
  let K : Over (Spec (CommRingCat.of R)) :=
    Over.mk (B.left.fromSpecResidueField t₂ ≫ B.hom)
  let r : K ⟶ B := Over.homMk (B.left.fromSpecResidueField t₂) rfl
  have hk := congrArg (restrict hG r) heq
  rw [restrict_conjugateParabolic, restrict_conjugateParabolic] at hk
  exact conjugateParabolic_index_eq_of_fieldTypes j hG hj htypes K.hom a b _ _ hk

/-- Uniform field types make the finite smooth proper affine quotient chart monic. -/
theorem finiteAffineParabolicChart_mono_of_fieldTypes [Finite I]
    (htypes : HasUniformParabolicFieldTypes j) :
    Mono (finiteAffineParabolicChart hG j hj) :=
  finiteAffineParabolicChart_mono_of_disjoint hG j hj
    (affineParabolicQuotientFamilies_disjoint_of_fieldTypes hG j hj htypes)

end Affine

end Langlands.GroupScheme.ParabolicSubgroupModuli
