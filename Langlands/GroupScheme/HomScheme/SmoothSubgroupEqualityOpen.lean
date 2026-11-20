import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality

/-! # The open locus of equality of nested smooth subgroup schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {H K G : GroupScheme S}

private theorem range_eq_comp_iff (i : H ⟶ G) (j : K ⟶ G)
    {U V : Scheme.{u}} (a : U ⟶ S) (b : V ⟶ U) :
    range ((GroupScheme.baseChange (b ≫ a)).map i) = range ((GroupScheme.baseChange (b ≫ a)).map j) ↔
      range ((GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map i)) =
        range ((GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map j)) := by
  let e := Descent.pullbackComparison a b (b ≫ a) rfl G
  rw [← range_comp_iso_eq_iff _ _ e]
  rw [Descent.pullbackComparison_naturality a b (b ≫ a) rfl i,
    Descent.pullbackComparison_naturality a b (b ≫ a) rfl j, range_iso_comp, range_iso_comp]

set_option maxHeartbeats 800000 in
/-- The equality open of nested smooth subgroup schemes represents equality
of their all-test ranges after arbitrary change of base. -/
theorem range_eq_iff_range_subset_rangeEqualityOpen
    [Smooth H.X.hom] [Smooth K.X.hom] [GeometricallyConnected K.X.hom]
    (i : H ⟶ G) (j : K ⟶ G) [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (h : range i ≤ range j) {T : Scheme.{u}} (t : T ⟶ S) :
    range ((GroupScheme.baseChange t).map i) = range ((GroupScheme.baseChange t).map j) ↔
      Set.range t ⊆ (rangeEqualityOpen i j h : Set S) := by
  constructor
  · intro ht _ hs
    obtain ⟨y, rfl⟩ := hs
    let F := T.residueField y
    let b := T.fromSpecResidueField y
    let a := b ≫ t
    let s := t y
    have ha : range ((GroupScheme.baseChange a).map i) = range ((GroupScheme.baseChange a).map j) := by
      apply (range_eq_comp_iff i j t b).mpr
      rw [range_baseChangeHom b ((GroupScheme.baseChange t).map i),
        range_baseChangeHom b ((GroupScheme.baseChange t).map j), ht]
    let k := S.residueField s
    let φ : k ⟶ F := t.residueFieldMap y
    let c := Spec.map φ
    let d := S.fromSpecResidueField s
    have hfac : c ≫ d = a := t.SpecMap_residueFieldMap_fromSpecResidueField y
    let : Algebra k F := φ.hom.toAlgebra
    have hf : Surjective c ∧ Flat c ∧ QuasiCompact c := fieldExtension_fpqc k F
    have : Surjective c := hf.1
    have : Flat c := hf.2.1
    have : QuasiCompact c := hf.2.2
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    have : Mono j.hom.hom := Over.mono_of_mono_left _
    have : Mono ((GroupScheme.baseChange d).map i).hom.hom := by
      change Mono ((Over.pullback d).map i.hom.hom)
      infer_instance
    have : Mono ((GroupScheme.baseChange d).map j).hom.hom := by
      change Mono ((Over.pullback d).map j.hom.hom)
      infer_instance
    have hc : range ((GroupScheme.baseChange c).map ((GroupScheme.baseChange d).map i)) =
        range ((GroupScheme.baseChange c).map ((GroupScheme.baseChange d).map j)) :=
      (range_eq_comp_iff i j d c).mp (hfac.symm ▸ ha)
    rw [range_baseChangeHom c ((GroupScheme.baseChange d).map i),
      range_baseChangeHom c ((GroupScheme.baseChange d).map j)] at hc
    have hd := range_eq_of_baseChange_eq c
      ((GroupScheme.baseChange d).map i) ((GroupScheme.baseChange d).map j) hc
    exact mem_rangeEqualityOpen_of_residue_range_eq i j h s hd
  · intro ht
    let V := rangeEqualityOpen i j h
    let a : T ⟶ V := IsOpenImmersion.lift V.ι t (by rwa [Scheme.Opens.range_ι])
    have ha : a ≫ V.ι = t := IsOpenImmersion.lift_fac _ _ _
    rw [← ha, range_eq_comp_iff i j V.ι a, range_baseChangeHom a ((GroupScheme.baseChange V.ι).map i),
      range_baseChangeHom a ((GroupScheme.baseChange V.ι).map j),
      range_eq_on_rangeEqualityOpen i j h]

/-- For nested smooth subgroup schemes with geometrically connected larger
subgroup, the equality functor is represented by the canonical open. -/
def SmoothSubgroupEqualityOpenStatement : Prop :=
  ∀ {S : Scheme.{u}} {H K G : GroupScheme S}
    [Smooth H.X.hom] [Smooth K.X.hom] [GeometricallyConnected K.X.hom]
    (i : H ⟶ G) (j : K ⟶ G) [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (h : range i ≤ range j) {T : Scheme.{u}} (t : T ⟶ S),
    range ((GroupScheme.baseChange t).map i) = range ((GroupScheme.baseChange t).map j) ↔
      Set.range t ⊆ (rangeEqualityOpen i j h : Set S)

theorem smoothSubgroupEqualityOpen : SmoothSubgroupEqualityOpenStatement.{u} := by
  intro S H K G _ _ _ i j _ _ h T t
  exact range_eq_iff_range_subset_rangeEqualityOpen i j h t

end Langlands.GroupScheme.SubgroupFunctor
