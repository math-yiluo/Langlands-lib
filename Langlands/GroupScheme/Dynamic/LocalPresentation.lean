import Langlands.GroupScheme.Dynamic.LocalContainment
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Reductive.GenericFiberGeometry
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Persistence of a prescribed dynamic parabolic presentation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S T U : Scheme.{u}} {G H K : GroupScheme S}

/-- Equality of ranges is compatible with the canonical pullback tower comparison. -/
theorem range_eq_baseChange_comp_iff (p : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S)
    (h : q ≫ p = r) (i : H ⟶ G) (j : K ⟶ G) :
    range ((GroupScheme.baseChange q).map ((GroupScheme.baseChange p).map i)) =
        range ((GroupScheme.baseChange q).map ((GroupScheme.baseChange p).map j)) ↔
      range ((GroupScheme.baseChange r).map i) = range ((GroupScheme.baseChange r).map j) := by
  let eG := Descent.pullbackComparison p q r h G
  let eH := Descent.pullbackComparison p q r h H
  let eK := Descent.pullbackComparison p q r h K
  have hi := Descent.pullbackComparison_naturality p q r h i
  have hj := Descent.pullbackComparison_naturality p q r h j
  have hh := range_comp_iso_eq_iff
    ((GroupScheme.baseChange q).map ((GroupScheme.baseChange p).map i))
    ((GroupScheme.baseChange q).map ((GroupScheme.baseChange p).map j)) eG
  rw [hi, hj, range_iso_comp, range_iso_comp] at hh
  exact hh.symm

/-- Equality on a supplied field-valued fibre reflects to its canonical residue fibre. -/
theorem range_eq_residue_of_fieldPoint
    (i : H ⟶ G) (j : K ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom]
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (heq : range ((GroupScheme.baseChange b).map i) =
      range ((GroupScheme.baseChange b).map j)) :
    range ((GroupScheme.baseChange
        (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).map i) =
      range ((GroupScheme.baseChange
        (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).map j) := by
  let s := b (IsLocalRing.closedPoint k)
  let a := S.fromSpecResidueField s
  let c := Spec.map (fieldPointResidueMap b)
  let : Algebra (S.residueField s) k := (fieldPointResidueMap b).hom.toAlgebra
  have hc : c = Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) k)) := rfl
  have hfpqc := fieldExtension_fpqc (S.residueField s) k
  have : Flat c := hc.symm ▸ hfpqc.2.1
  have : Surjective c := hc.symm ▸ hfpqc.1
  have : QuasiCompact c := hc.symm ▸ hfpqc.2.2
  have : Mono ((GroupScheme.baseChange a).map i).hom.hom := by
    change Mono ((Over.pullback a).map i.hom.hom)
    infer_instance
  have : Mono ((GroupScheme.baseChange a).map j).hom.hom := by
    change Mono ((Over.pullback a).map j.hom.hom)
    infer_instance
  apply range_eq_of_baseChange_eq c ((GroupScheme.baseChange a).map i)
    ((GroupScheme.baseChange a).map j)
  rw [← range_baseChangeHom, ← range_baseChangeHom]
  exact (range_eq_baseChange_comp_iff a c b (fieldPointResidueMap_factorization b) i j).mpr heq

/-- Containment and equality on a supplied field-valued fibre give equality near its image. -/
theorem exists_open_range_eq_of_fieldPoint_range_eq
    (i : H ⟶ G) (j : K ⟶ G)
    [Smooth H.X.hom] [Smooth K.X.hom]
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    [GeometricallyConnected K.X.hom] (hle : range i ≤ range j)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (heq : range ((GroupScheme.baseChange b).map i) =
      range ((GroupScheme.baseChange b).map j)) :
    ∃ V : S.Opens, b (IsLocalRing.closedPoint k) ∈ V ∧
      range ((GroupScheme.baseChange V.ι).map i) =
        range ((GroupScheme.baseChange V.ι).map j) := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact exists_open_range_eq_of_residue_range_eq i j hle _
    (range_eq_residue_of_fieldPoint i j b heq)

end Langlands.GroupScheme.SubgroupFunctor

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- A field point factors through any base open containing its image. -/
def fieldPointOpenLift {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (V : S.Opens) (hb : b (IsLocalRing.closedPoint k) ∈ V) :
    Spec (CommRingCat.of k) ⟶ V :=
  IsOpenImmersion.lift V.ι b (by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨b z, ?_⟩, rfl⟩
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint k)] using hb)

@[reassoc (attr := simp)]
theorem fieldPointOpenLift_comp {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) (V : S.Opens)
    (hb : b (IsLocalRing.closedPoint k) ∈ V) :
    fieldPointOpenLift b V hb ≫ V.ι = b :=
  IsOpenImmersion.lift_fac _ _ _

/-- A prescribed cocharacter in a smooth monic subgroup presents that subgroup
near a field point if it presents its field-valued fibre and the canonical
residue fibre of the subgroup is closed. -/
theorem exists_local_presentation_of_fieldPoint
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    (i : H ⟶ G) [Mono i.hom.hom.left] (χ : (Gm S).toGrp ⟶ H)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hi : IsClosedSubgroup ((baseChange
      (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).map i))
    (heq : SubgroupFunctor.range ((baseChange b).map i) =
      parabolic (baseChangeCocharacter b (χ ≫ i))) :
    ∃ (U : Scheme.{u}) (p : U ⟶ S), IsOpenImmersion p ∧
      ∃ bU : Spec (CommRingCat.of k) ⟶ U, bU ≫ p = b ∧
        SubgroupFunctor.range ((baseChange p).map i) =
          parabolic (baseChangeCocharacter p (χ ≫ i)) := by
  obtain ⟨K, j, hjc, hjL, hj⟩ := (dynamicBaseRepresentability S G (χ ≫ i)).1
  let : IsClosedImmersion j.hom.hom.left := hjc
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono j.hom.hom := hj.1
  let : Smooth K.X.hom := ((dynamicBaseSmoothConnected S G (χ ≫ i) K j).2.1 hj).1
  let : GeometricallyConnected K.X.hom :=
    ((dynamicBaseSmoothConnected S G (χ ≫ i) K j).2.1 hj).2 inferInstance
  have heqj : SubgroupFunctor.range ((baseChange b).map i) =
      SubgroupFunctor.range ((baseChange b).map j) := by
    rw [SubgroupFunctor.range_baseChangeHom b j, hj.2, ← parabolic_baseChange]
    exact heq
  let s := b (IsLocalRing.closedPoint k)
  let a := S.fromSpecResidueField s
  have hres : SubgroupFunctor.range ((baseChange a).map i) =
      parabolic (baseChangeCocharacter a (χ ≫ i)) := by
    rw [parabolic_baseChange, ← hj.2, ← SubgroupFunctor.range_baseChangeHom]
    exact SubgroupFunctor.range_eq_residue_of_fieldPoint i j b heqj
  obtain ⟨V, hsV, hV⟩ := exists_range_le_parabolic_near_of_residueFiber i χ s
    hi hres.le
  let bV := fieldPointOpenLift b V hsV
  have hbV : bV ≫ V.ι = b := fieldPointOpenLift_comp b V hsV
  let iV := (baseChange V.ι).map i
  let jV := (baseChange V.ι).map j
  have : Smooth ((baseChange V.ι).obj H).X.hom :=
    inferInstanceAs (Smooth (pullback.snd H.X.hom V.ι))
  have : Smooth ((baseChange V.ι).obj K).X.hom :=
    inferInstanceAs (Smooth (pullback.snd K.X.hom V.ι))
  have : GeometricallyConnected ((baseChange V.ι).obj K).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd K.X.hom V.ι))
  have : Mono iV.hom.hom.left := by
    have : Mono iV.hom.hom := by
      change Mono ((Over.pullback V.ι).map i.hom.hom)
      infer_instance
    exact Over.mono_left_of_mono _
  have : IsClosedImmersion jV.hom.hom.left := IsClosedSubgroup.baseChange V.ι hjc
  have hle : SubgroupFunctor.range iV ≤ SubgroupFunctor.range jV := by
    change SubgroupFunctor.range ((baseChange V.ι).map i) ≤
      SubgroupFunctor.range ((baseChange V.ι).map j)
    rw [SubgroupFunctor.range_baseChangeHom V.ι j, hj.2, ← parabolic_baseChange]
    exact hV
  have hfib : SubgroupFunctor.range ((baseChange bV).map iV) =
      SubgroupFunctor.range ((baseChange bV).map jV) :=
    (SubgroupFunctor.range_eq_baseChange_comp_iff V.ι bV b hbV i j).mpr heqj
  obtain ⟨W, hbW, hW⟩ :=
    SubgroupFunctor.exists_open_range_eq_of_fieldPoint_range_eq iV jV hle bV hfib
  let bW := fieldPointOpenLift bV W hbW
  refine ⟨W, W.ι ≫ V.ι, inferInstance, bW, ?_, ?_⟩
  · rw [← Category.assoc, fieldPointOpenLift_comp, hbV]
  · rw [parabolic_baseChange, ← hj.2, ← SubgroupFunctor.range_baseChangeHom]
    exact (SubgroupFunctor.range_eq_baseChange_comp_iff V.ι W.ι (W.ι ≫ V.ι) rfl i j).mp hW

/-- Actual neighbourhood data retaining the prescribed field-valued point and presentation. -/
structure ParabolicPresentationNeighbourhoodData
    (i : H ⟶ G) (χ : (Gm S).toGrp ⟶ H)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) where
  U : Scheme.{u}
  projection : U ⟶ S
  isOpenImmersion : IsOpenImmersion projection
  point : Spec (CommRingCat.of k) ⟶ U
  point_projection : point ≫ projection = b
  presents : SubgroupFunctor.range ((baseChange projection).map i) =
    parabolic (baseChangeCocharacter projection (χ ≫ i))

/-- Choose an open neighbourhood where the prescribed cocharacter presents the subgroup. -/
def parabolicPresentationNeighbourhood
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    (i : H ⟶ G) [Mono i.hom.hom.left] (χ : (Gm S).toGrp ⟶ H)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hi : IsClosedSubgroup ((baseChange
      (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).map i))
    (heq : SubgroupFunctor.range ((baseChange b).map i) =
      parabolic (baseChangeCocharacter b (χ ≫ i))) :
    ParabolicPresentationNeighbourhoodData i χ b := by
  classical
  exact Classical.choice (by
    obtain ⟨U, p, hp, bU, hbU, hpres⟩ :=
      exists_local_presentation_of_fieldPoint i χ b hi heq
    exact ⟨⟨U, p, hp, bU, hbU, hpres⟩⟩)

end Langlands.GroupScheme.Dynamic
