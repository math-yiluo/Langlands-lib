import Langlands.GroupScheme.SubgroupFunctor.FpqcProductReconstruction
import Langlands.GroupScheme.Reductive.DerivedTorusParabolicCorrespondenceStatement

/-! # Injectivity in the derived-group correspondence -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace DerivedCorrespondence

variable {S : Scheme.{u}} {G D Z P P' : GroupScheme S}

private theorem range_comp_le_of_range_le
    {B B' : GroupScheme S} (b : B ⟶ D) (b' : B' ⟶ D) (d : D ⟶ G)
    (h : SubgroupFunctor.range b ≤ SubgroupFunctor.range b') :
    SubgroupFunctor.range (b ≫ d) ≤ SubgroupFunctor.range (b' ≫ d) := by
  intro U x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.mp
    (h U (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩))
  refine SubgroupFunctor.mem_range.mpr ⟨y', ?_⟩
  change y' ≫ b'.hom.hom ≫ d.hom.hom = y ≫ b.hom.hom ≫ d.hom.hom
  rw [← Category.assoc, hy', Category.assoc]

/-- Equal intersection ranges determine monic subgroup ranges when both
subgroups have the stated isogeny product factorizations. -/
theorem range_eq_of_intersection_isogenies
    (d : D ⟶ G) (z : Z ⟶ G) (hz : IsCentral z)
    (i : P ⟶ G) [Mono i.hom.hom]
    (i' : P' ⟶ G) [Mono i'.hom.hom]
    (e : Z ⊗ subgroupIntersection d i ⟶ P) (he : IsIsogeny e)
    (heq : e ≫ i = prodHom z (subgroupIntersectionHom d i) (hz.commute_values _))
    (e' : Z ⊗ subgroupIntersection d i' ⟶ P') (he' : IsIsogeny e')
    (heq' : e' ≫ i' = prodHom z (subgroupIntersectionHom d i') (hz.commute_values _))
    (h : SubgroupFunctor.range (subgroupIntersectionFst d i) =
      SubgroupFunctor.range (subgroupIntersectionFst d i')) :
    SubgroupFunctor.range i = SubgroupFunctor.range i' := by
  have : IsFinite e.hom.hom.left := he.1
  have : Flat e.hom.hom.left := he.2.1
  have : Surjective e.hom.hom.left := he.2.2
  have : IsFinite e'.hom.hom.left := he'.1
  have : Flat e'.hom.hom.left := he'.2.1
  have : Surjective e'.hom.hom.left := he'.2.2
  apply SubgroupFunctor.range_eq_of_fpqc_products z
    (subgroupIntersectionHom d i) (subgroupIntersectionHom d i')
    (hz.commute_values _) (hz.commute_values _) i e heq i' e' heq'
  exact le_antisymm
    (range_comp_le_of_range_le _ _ d h.le)
    (range_comp_le_of_range_le _ _ d h.ge)

/-- The maximal-torus predicate used locally in the published correspondence. -/
def IsMaxTorus {H : GroupScheme S} {T : CommGroupScheme S} (t : T.toGrp ⟶ H) : Prop :=
  RelativeTorus.IsTorus T.toGrp ∧ IsClosedSubgroup t ∧ IsFibrewiseMaximalTorus t

/-- Isogeny factorizations imply the maximal-torus injectivity clause. -/
theorem maximal_torus_injective_of_isogenies
    (d : D ⟶ G) (z : Z ⟶ G) (hz : IsCentral z)
    (hfactor : ∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G), IsMaxTorus t →
      ∃ e : Z ⊗ subgroupIntersection d t ⟶ T.toGrp, IsIsogeny e ∧
        e ≫ t = prodHom z (subgroupIntersectionHom d t) (hz.commute_values _))
    (T₁ T₂ : CommGroupScheme S) (t₁ : T₁.toGrp ⟶ G) (t₂ : T₂.toGrp ⟶ G)
    (ht₁ : IsMaxTorus t₁) (ht₂ : IsMaxTorus t₂)
    (h : SubgroupFunctor.range (subgroupIntersectionFst d t₁) =
      SubgroupFunctor.range (subgroupIntersectionFst d t₂)) :
    SubgroupFunctor.range t₁ = SubgroupFunctor.range t₂ := by
  have : IsClosedImmersion t₁.hom.hom.left := ht₁.2.1
  have : IsClosedImmersion t₂.hom.hom.left := ht₂.2.1
  have : Mono t₁.hom.hom := Over.mono_of_mono_left _
  have : Mono t₂.hom.hom := Over.mono_of_mono_left _
  obtain ⟨e, he, heq⟩ := hfactor T₁ t₁ ht₁
  obtain ⟨e', he', heq'⟩ := hfactor T₂ t₂ ht₂
  exact range_eq_of_intersection_isogenies d z hz t₁ t₂ e he heq e' he' heq' h

/-- Central-isogeny factorizations imply the parabolic injectivity clause. -/
theorem parabolic_injective_of_isogenies
    (d : D ⟶ G) (z : Z ⟶ G) (hz : IsCentral z)
    (hfactor : ∀ (P : GroupScheme S) (i : P ⟶ G), IsRelativeParabolicSubgroup i →
      ∃ e : Z ⊗ subgroupIntersection d i ⟶ P, IsCentralIsogeny e ∧
        e ≫ i = prodHom z (subgroupIntersectionHom d i) (hz.commute_values _))
    (P₁ P₂ : GroupScheme S) (i₁ : P₁ ⟶ G) (i₂ : P₂ ⟶ G)
    (hi₁ : IsRelativeParabolicSubgroup i₁) (hi₂ : IsRelativeParabolicSubgroup i₂)
    (h : SubgroupFunctor.range (subgroupIntersectionFst d i₁) =
      SubgroupFunctor.range (subgroupIntersectionFst d i₂)) :
    SubgroupFunctor.range i₁ = SubgroupFunctor.range i₂ := by
  have : Mono i₁.hom.hom := hi₁.mono
  have : Mono i₂.hom.hom := hi₂.mono
  obtain ⟨e, he, heq⟩ := hfactor P₁ i₁ hi₁
  obtain ⟨e', he', heq'⟩ := hfactor P₂ i₂ hi₂
  exact range_eq_of_intersection_isogenies d z hz i₁ i₂
    e he.isIsogeny heq e' he'.isIsogeny heq' h

/-- The four geometric clauses of the published target, for fixed data:
intersection, product and inverse constructions for tori and parabolics. -/
def GeometricClauses (d : D ⟶ G) (z : Z ⟶ G) (hz : IsCentral z) : Prop :=
  (∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G), IsMaxTorus t →
    (∃ (T' : CommGroupScheme S) (t' : T'.toGrp ⟶ D), IsMaxTorus t' ∧
      SubgroupFunctor.range t' = SubgroupFunctor.range (subgroupIntersectionFst d t)) ∧
    ∃ e : Z ⊗ subgroupIntersection d t ⟶ T.toGrp, IsIsogeny e ∧
      e ≫ t = prodHom z (subgroupIntersectionHom d t) (hz.commute_values _)) ∧
  (∀ (T' : CommGroupScheme S) (t' : T'.toGrp ⟶ D), IsMaxTorus t' →
    ∃ (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (e : Z ⊗ T'.toGrp ⟶ T.toGrp),
      IsMaxTorus t ∧ IsIsogeny e ∧ e ≫ t = prodHom z (t' ≫ d) (hz.commute_values _) ∧
      SubgroupFunctor.range (subgroupIntersectionFst d t) = SubgroupFunctor.range t') ∧
  (∀ (P : GroupScheme S) (i : P ⟶ G), IsRelativeParabolicSubgroup i →
    IsRelativeParabolicSubgroup (subgroupIntersectionFst d i) ∧
    ∃ e : Z ⊗ subgroupIntersection d i ⟶ P, IsCentralIsogeny e ∧
      e ≫ i = prodHom z (subgroupIntersectionHom d i) (hz.commute_values _)) ∧
  (∀ (P' : GroupScheme S) (i' : P' ⟶ D), IsRelativeParabolicSubgroup i' →
    ∃ (P : GroupScheme S) (i : P ⟶ G) (e : Z ⊗ P' ⟶ P),
      IsRelativeParabolicSubgroup i ∧ IsCentralIsogeny e ∧
      e ≫ i = prodHom z (i' ≫ d) (hz.commute_values _) ∧
      SubgroupFunctor.range (subgroupIntersectionFst d i) = SubgroupFunctor.range i')

/-- Proving the four geometric clauses under exactly the hypotheses of the
published target suffices for the full six-clause correspondence. -/
theorem correspondence_of_geometric_clauses
    (h : ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
      let IsMaximalCentralTorus : ∀ {Z : GroupScheme S}, (Z ⟶ G) → Prop :=
        fun {Z} z => IsClosedSubgroup z ∧ IsCentral z ∧ RelativeTorus.IsTorus Z ∧
          ∀ (Z' : GroupScheme S) (z' : Z' ⟶ G), IsClosedSubgroup z' → IsCentral z' →
            RelativeTorus.IsTorus Z' → SubgroupFunctor.range z' ≤ SubgroupFunctor.range z
      ∀ (D : GroupScheme S) (d : D ⟶ G), IsClosedSubgroup d →
        (SubgroupFunctor.range d).IsNormal → IsReductive D →
        (∀ s : S, IsSemisimple (geometricFiber D s)) →
        (∃ (Q : GroupScheme S) (q : G ⟶ Q), RelativeTorus.IsTorus Q ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q) →
        ∀ (Z : GroupScheme S) (z : Z ⟶ G) (hz : IsCentral z), IsMaximalCentralTorus z →
          GeometricClauses d z hz) :
    ReductiveDerivedTorusParabolicCorrespondenceStatement.{u} := by
  intro S G hG
  dsimp only
  intro D d hd hnormal hD hsemisimple hquotient Z z hz hZ
  obtain ⟨ht, ht', hp, hp'⟩ :=
    h S G hG D d hd hnormal hD hsemisimple hquotient Z z hz hZ
  refine ⟨ht, ht', ?_, hp, hp', ?_⟩
  · exact maximal_torus_injective_of_isogenies d z hz
      (fun T t htT => (ht T t htT).2)
  · exact parabolic_injective_of_isogenies d z hz
      (fun P i hi => (hp P i hi).2)

end DerivedCorrespondence

end Langlands.GroupScheme
