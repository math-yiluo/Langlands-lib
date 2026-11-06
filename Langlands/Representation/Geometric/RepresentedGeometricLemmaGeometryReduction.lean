import Langlands.Representation.Geometric.RepresentedGeometricLemmaGeometryStatement
import Langlands.GroupScheme.Rational.ParabolicDoubleCosetStatement
import Langlands.GroupScheme.Rational.ParabolicLeviIntersectionStatement
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.SplitComponentLeviPoints
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Reduction of the represented geometric prerequisites to two structural statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Finiteness of parabolic double cosets with torus-adapted representatives, together with
the Levi-intersection structure for parabolics whose Levis share a maximal split torus, implies
the unchanged geometric prerequisites of the represented geometric lemma. Both structural
statements are explicit inputs of this reduction. -/
def RepresentedGeometricLemmaGeometryReductionStatement : Prop :=
  RepresentedParabolicDoubleCosetStatement.{u} →
    RepresentedParabolicLeviIntersectionStatement.{u} →
      RepresentedGeometricLemmaGeometryStatement.{u}

section Helpers

variable {S : Scheme.{u}} {H H₁ H₂ G G' : GroupScheme S}

/-- The range of a composite with an ambient isomorphism is the transported range. -/
theorem range_comp_iso_eq_transport (i : H ⟶ G) (e : G ≅ G') :
    SubgroupFunctor.range (i ≫ e.hom) = SubgroupFunctor.transport e (SubgroupFunctor.range i) := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.mem_transport, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp only [Grp.comp_hom_hom, Category.assoc, ← Grp.comp_hom_hom e.hom e.inv,
      Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hy, Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- An equality of a range with an infimum of ranges is transported by an ambient
isomorphism. -/
theorem range_comp_iso_eq_inf {i : H ⟶ G} {j₁ : H₁ ⟶ G} {j₂ : H₂ ⟶ G} (e : G ≅ G')
    (h : SubgroupFunctor.range i = SubgroupFunctor.range j₁ ⊓ SubgroupFunctor.range j₂) :
    SubgroupFunctor.range (i ≫ e.hom) =
      SubgroupFunctor.range (j₁ ≫ e.hom) ⊓ SubgroupFunctor.range (j₂ ≫ e.hom) := by
  simp only [range_comp_iso_eq_transport, h]
  apply SubgroupFunctor.ext
  intro T
  ext x
  simp only [SubgroupFunctor.inf_carrier, Subgroup.mem_inf, SubgroupFunctor.mem_transport]

/-- Intersection of all-test subgroup functors is commutative. -/
theorem subgroupFunctor_inf_comm (F F' : SubgroupFunctor G) : F ⊓ F' = F' ⊓ F :=
  SubgroupFunctor.ext fun T => inf_comm (F.carrier T) (F'.carrier T)

/-- A subgroup functor below two others is below their intersection. -/
theorem subgroupFunctor_le_inf {F F₁ F₂ : SubgroupFunctor G} (h₁ : F ≤ F₁) (h₂ : F ≤ F₂) :
    F ≤ F₁ ⊓ F₂ :=
  SubgroupFunctor.le_def.2 fun T =>
    le_inf (SubgroupFunctor.le_def.1 h₁ T) (SubgroupFunctor.le_def.1 h₂ T)

/-- A closed subgroup is a monomorphism over the base. -/
theorem mono_hom_hom_of_isClosedSubgroup {i : H ⟶ G} (hi : IsClosedSubgroup i) :
    Mono i.hom.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  exact Over.mono_of_mono_left _

end Helpers

/-- The geometric prerequisites of the represented geometric lemma follow from finiteness of
parabolic double cosets with torus-adapted representatives and from the Levi-intersection
structure for parabolics whose Levis share a maximal split torus. -/
theorem representedGeometricLemmaGeometry_of_doubleCoset_of_leviIntersection
    (hD : RepresentedParabolicDoubleCosetStatement.{u})
    (hI : RepresentedParabolicLeviIntersectionStatement.{u}) :
    RepresentedGeometricLemmaGeometryStatement.{u} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  obtain ⟨hfin, hrep⟩ := hD k G hG P M Q L p l hp hl q lQ hq hlQ
  apply exists_enumerated_geometricLemmaIntersectionDatum p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ hfin
  intro a
  obtain ⟨z, hz, T, i, hi, ⟨ta, hta⟩, ⟨tb, htb⟩⟩ := hrep a.out
  refine ⟨z, hz.trans (DoubleCoset.out_eq' a), ?_⟩
  have hzz : (G.innerIso z).hom ≫ (G.innerIso z⁻¹).hom = 𝟙 G := by
    rw [innerIso_inv_hom, Iso.hom_inv_id]
  have hzz' : (G.innerIso z⁻¹).hom ≫ (G.innerIso z).hom = 𝟙 G := by
    rw [innerIso_inv_hom, Iso.inv_hom_id]
  -- `M ∩ zQz⁻¹`, with Levi `M ∩ zLz⁻¹` and radical `M ∩ zUz⁻¹`.
  obtain ⟨P', M', N', p', l', r', hp', hr', hl', hmul', hpar, hlevi, hrad⟩ :=
    hI k G hG P M Q L U p l hp hl (q ≫ (G.innerIso z).hom) lQ rQ (hq.comp_iso _) hlQ hrQ
      hmulQ T i hi ⟨ta, hta⟩ ⟨tb, htb⟩
  -- `L ∩ z⁻¹Pz`, with Levi `L ∩ z⁻¹Mz` and radical `L ∩ z⁻¹Nz`.
  obtain ⟨Q', L', U', q', lQ', rQ', hq', hrQ', hlQ', hmulQ', hpar', hlevi', hrad'⟩ :=
    hI k G hG Q L P M N q lQ hq hlQ (p ≫ (G.innerIso z⁻¹).hom) l r (hp.comp_iso _) hl hr
      hmul T (i ≫ (G.innerIso z⁻¹).hom) (hi.comp_iso _)
      ⟨tb, by rw [← htb]; simp only [Category.assoc, hzz, Category.comp_id]⟩
      ⟨ta, by rw [← hta]; simp only [Category.assoc]⟩
  -- Both Levi intersections are the same subgroup functor of `G`.
  have hL : SubgroupFunctor.range (lQ' ≫ q' ≫ lQ ≫ q ≫ (G.innerIso z).hom) =
      SubgroupFunctor.range (l' ≫ p' ≫ l ≫ p) := by
    have h := range_comp_iso_eq_inf (G.innerIso z) hlevi'
    simp only [Category.assoc, hzz', Category.comp_id] at h
    rw [h, hlevi, subgroupFunctor_inf_comm]
  have hcM : IsClosedSubgroup (l' ≫ p' ≫ l ≫ p) :=
    hl'.isClosedSubgroup.comp (hp'.isClosedSubgroup.comp
      (hl.isClosedSubgroup.comp hp.isClosedSubgroup))
  have hcL : IsClosedSubgroup (lQ' ≫ q' ≫ lQ ≫ q ≫ (G.innerIso z).hom) :=
    hlQ'.isClosedSubgroup.comp (hq'.isClosedSubgroup.comp
      (hlQ.isClosedSubgroup.comp (hq.isClosedSubgroup.comp_iso _)))
  have := mono_hom_hom_of_isClosedSubgroup hcM
  have := mono_hom_hom_of_isClosedSubgroup hcL
  have := mono_hom_hom_of_isClosedSubgroup hi.1.2
  have hrepM : (SubgroupFunctor.range (l' ≫ p' ≫ l ≫ p)).IsRepresentedBy
      (l' ≫ p' ≫ l ≫ p) := ⟨inferInstance, rfl⟩
  have hrepL : (SubgroupFunctor.range (l' ≫ p' ≫ l ≫ p)).IsRepresentedBy
      (lQ' ≫ q' ≫ lQ ≫ q ≫ (G.innerIso z).hom) := ⟨inferInstance, hL⟩
  let φ : L' ≅ M' := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hrepL hrepM
  have hφ : φ.hom ≫ l' ≫ p' ≫ l ≫ p = lQ' ≫ q' ≫ lQ ≫ q ≫ (G.innerIso z).hom :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hrepL hrepM
  -- The maximal split torus lies in `M' = M ∩ zLz⁻¹`.
  have hTM : SubgroupFunctor.range i ≤ SubgroupFunctor.range (l' ≫ p' ≫ l ≫ p) := by
    rw [hlevi]
    exact subgroupFunctor_le_inf (SubgroupFunctor.range_le_of_factor ta hta)
      (SubgroupFunctor.range_le_of_factor tb htb)
  obtain ⟨t, ht⟩ := SubgroupFunctor.exists_factor_of_range_le hTM
  -- Rational points of `φ`, with the canonical point topologies.
  have := hlQ'.isConnectedReductive.isAffineHom
  have := hl'.isConnectedReductive.isAffineHom
  have : IsAffine L'.X.left := isAffine_of_isAffineHom L'.X.hom
  have : IsAffine M'.X.left := isAffine_of_isAffineHom M'.X.hom
  let := leviPointTopology lQ' hlQ'
  let := leviPointTopology l' hl'
  let eφ : rationalPoints L' ≃* rationalPoints M' :=
    { toFun := rationalPoints.map φ.hom
      invFun := rationalPoints.map φ.inv
      left_inv := fun x => by
        simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
          Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
      right_inv := fun x => by
        simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
          Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
      map_mul' := map_mul (rationalPoints.map φ.hom) }
  exact ⟨
    { P' := P', M' := M', N' := N', p' := p', l' := l', r' := r'
      hp' := hp', hr' := hr', hl' := hl', hmul' := hmul'
      Q' := Q', L' := L', U' := U', q' := q', lQ' := lQ', rQ' := rQ'
      hq' := hq', hrQ' := hrQ', hlQ' := hlQ', hmulQ' := hmulQ'
      parabolic_eq := hpar, levi_eq := hlevi, radical_eq := hrad
      parabolic_eq' := hpar', levi_eq' := hlevi', radical_eq' := hrad'
      φ := φ, φ_comp := hφ
      e :=
        { toMulEquiv := eφ
          continuous_toFun := continuous_rationalPoints_map φ.hom
          continuous_invFun := continuous_rationalPoints_map φ.inv }
      e_apply := fun _ => rfl
      torus := T, t := t
      isMaximalSplitTorus := by rw [ht]; exact hi }⟩

/-- The reduction of the represented geometric prerequisites to the double-coset and
Levi-intersection statements. -/
theorem representedGeometricLemmaGeometryReduction :
    RepresentedGeometricLemmaGeometryReductionStatement.{u} :=
  fun hD hI => representedGeometricLemmaGeometry_of_doubleCoset_of_leviIntersection hD hI

end Langlands.Aubert.General.RepresentedParabolic
