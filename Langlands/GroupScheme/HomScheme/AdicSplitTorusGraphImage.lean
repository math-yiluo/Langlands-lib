import Langlands.AlgebraicGeometry.ResidueFibreSectionImage
import Langlands.GroupScheme.HomScheme.AdicSplitTorusValuation
import Langlands.GroupScheme.HomScheme.GraphBaseChange
import Langlands.GroupScheme.HomScheme.AffineTest
import Langlands.GroupScheme.Torus.DiagonalizableGeometry

/-! # Finite graph images of residue-field torsion realizations -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme

section GraphMaps

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- The actual relative graph followed by its projection to the original ambient product. -/
def relativeGraphMap {V : Over S} (f : RelativeHom H G V) :
    ((baseChange V.hom).obj H).X.left ⟶ (H ⊗ G).X.left :=
  (relativeGraphHom f).hom.hom.left ≫ pullback.fst (H ⊗ G).X.hom V.hom

@[reassoc (attr := simp)]
theorem relativeGraphMap_fst {V : Over S} (f : RelativeHom H G V) :
    relativeGraphMap f ≫ (fst H G).hom.hom.left = pullback.fst H.X.hom V.hom := by
  rw [relativeGraphMap, Category.assoc, ← baseChange_map_left_fst, ← Category.assoc]
  change (relativeGraphHom f ≫ (baseChange V.hom).map (fst H G)).hom.hom.left ≫
    pullback.fst H.X.hom V.hom = _
  rw [relativeGraphHom_fst, Grp.id_hom_hom, Over.id_left, Category.id_comp]

@[reassoc (attr := simp)]
theorem relativeGraphMap_snd {V : Over S} (f : RelativeHom H G V) :
    relativeGraphMap f ≫ (snd H G).hom.hom.left =
      f.hom.hom.left ≫ pullback.fst G.X.hom V.hom := by
  rw [relativeGraphMap, Category.assoc, ← baseChange_map_left_fst, ← Category.assoc]
  change (relativeGraphHom f ≫ (baseChange V.hom).map (snd H G)).hom.hom.left ≫
    pullback.fst G.X.hom V.hom = _
  rw [relativeGraphHom_snd]

theorem relativeGraphMap_evaluate {U V : Over S} (a : U ⟶ V) (f : RelativeHom H G V) :
    relativeGraphMap (evaluate a f) = baseChangeProj H a ≫ relativeGraphMap f := by
  apply pullback.hom_ext
  · simp only [← show (fst H G).hom.hom.left = pullback.fst H.X.hom G.X.hom from rfl,
      relativeGraphMap_fst, Category.assoc, baseChangeProj_fst]
  · simp only [← show (snd H G).hom.hom.left = pullback.snd H.X.hom G.X.hom from rfl,
      relativeGraphMap_snd, Category.assoc, evaluate_fst]

/-- The relative graphs over the residue fields, as preimmersion sections into the
original product. -/
def residueGraphSections [IsSeparated G.X.hom]
    (f : ∀ y : S, RelativeHom H G (Over.mk (S.fromSpecResidueField y))) :
    Langlands.AlgebraicGeometry.ResidueFibreSections H.X.hom (fst H G).hom.hom.left where
  hom y := relativeGraphMap (f y)
  fac y := relativeGraphMap_fst (f y)
  isPreimmersion y := by
    let : IsClosedImmersion (relativeGraphHom (f y)).hom.hom.left :=
      isClosedSubgroup_relativeGraphHom (f y)
    change IsPreimmersion ((relativeGraphHom (f y)).hom.hom.left ≫ (H ⊗ G).X.hom.fiberι y)
    infer_instance

end GraphMaps

namespace Adic

open Diagonalizable

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A] {G : GroupScheme (Spec (CommRingCat.of A))}
  {L : Type u} [Fintype L]

local notation "S" => Spec (CommRingCat.of A)
local notation "H" => CommGroupScheme.toGrp (groupScheme (CommRingCat.of A) (L → ℤ))

namespace System

variable {s : System (maximalIdeal A) (groupScheme (CommRingCat.of A) (L → ℤ)).toGrp G}
  [IsSeparated G.X.hom]

variable
  {f : ∀ y : Spec (CommRingCat.of A),
    RelativeHom (groupScheme (CommRingCat.of A) (L → ℤ)).toGrp G
      (Over.mk ((Spec (CommRingCat.of A)).fromSpecResidueField y))}

/-- The graph of a torsion realization on any test scheme has range in the
union of the residue-field graphs. -/
theorem range_relativeGraphMap_subset_residueGraphSections
    (hf : ∀ y, s.RealizesSplitTorsion L (f y))
    {V : Over S} {g : RelativeHom H G V} (hg : s.RealizesSplitTorsion L g) :
    Set.range (relativeGraphMap g) ⊆ (residueGraphSections f).range := by
  rintro _ ⟨x, rfl⟩
  let T := (baseChange V.hom).obj H
  let b := T.X.hom ≫ V.hom
  let r := T.X.left.fromSpecResidueField x
  let U := Over.mk (r ≫ b)
  let y := b x
  let a : U ⟶ V := Over.homMk (r ≫ T.X.hom) (Category.assoc _ _ _)
  let c : U ⟶ Over.mk (Scheme.fromSpecResidueField S y) :=
    Over.homMk (Spec.map (b.residueFieldMap x)) (b.SpecMap_residueFieldMap_fromSpecResidueField x)
  have he : evaluate a g = evaluate c (f y) := (hg.evaluate a).hom_ext ((hf y).evaluate c)
  let l : U.left ⟶ ((baseChange U.hom).obj H).X.left :=
    pullback.lift (r ≫ pullback.fst (H).X.hom V.hom) (𝟙 U.left) (by
      change (r ≫ pullback.fst (H).X.hom V.hom) ≫ (H).X.hom = 𝟙 _ ≫ (r ≫ b)
      rw [Category.assoc, pullback.condition, Category.id_comp]
      rfl)
  have hl : l ≫ baseChangeProj H a = r := by
    apply pullback.hom_ext <;> simp [l, a, T]
  have hcomp : (l ≫ baseChangeProj H c) ≫ relativeGraphMap (f y) = r ≫ relativeGraphMap g := by
    rw [Category.assoc, ← relativeGraphMap_evaluate, ← he, relativeGraphMap_evaluate,
      ← Category.assoc, hl]
  refine Set.mem_iUnion.mpr ⟨y, ⟨(l ≫ baseChangeProj H c) (closedPoint (T.X.left.residueField x)), ?_⟩⟩
  change relativeGraphMap (f y)
    ((l ≫ baseChangeProj H c) (closedPoint (T.X.left.residueField x))) = relativeGraphMap g x
  rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]
  exact congrArg (fun z => relativeGraphMap g z) (Scheme.fromSpecResidueField_apply _ _)

/-- DVR-valued points extend in the union of the residue-field graphs. -/
theorem dvrExtension_residueGraphSections
    (hf : ∀ y, s.RealizesSplitTorsion L (f y)) (hD : s.HasSplitTorusHomOnDvrTests) :
    (residueGraphSections f).DvrExtension := by
  intro R _ _ _ b
  let V := Over.mk (b ≫ (H).X.hom)
  obtain ⟨g, hg⟩ := hD R V.hom
  let l : V.left ⟶ ((baseChange V.hom).obj H).X.left :=
    pullback.lift b (𝟙 _) (Category.id_comp _).symm
  refine ⟨l ≫ relativeGraphMap g, ?_, ?_⟩
  · rw [Category.assoc, relativeGraphMap_fst]
    exact pullback.lift_fst _ _ _
  · exact (Set.range_comp_subset_range l (relativeGraphMap g)).trans
      (range_relativeGraphMap_subset_residueGraphSections hf hg)

/-- Images of Noetherian schemes in the residue-field graph family are finite
over the split torus. -/
def HasFiniteSplitTorusGraphImages
    (s : System (maximalIdeal A) (groupScheme (CommRingCat.of A) (L → ℤ)).toGrp G) : Prop :=
  ∀ (f : ∀ y : S, RelativeHom H G (Over.mk (Scheme.fromSpecResidueField S y))),
    (∀ y, s.RealizesSplitTorsion L (f y)) →
    ∀ {W : Scheme.{u}} [NoetherianSpace W] (a : W ⟶ (H ⊗ G).X.left),
      Set.range a ⊆ (residueGraphSections f).range →
      IsFinite (a.imageι ≫ (fst H G).hom.hom.left)

/-- For a smooth, separated, quasi-compact target with affine residue fibres,
the residue-field graphs admit finite schematic images over the split torus. -/
theorem hasFiniteSplitTorusGraphImages [Smooth G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasAffineResidueFibers G) : s.HasFiniteSplitTorusGraphImages := by
  intro f hf W _ a ha
  let : AddGroup.FG (L → ℤ) := Module.Finite.iff_addGroup_fg.mp inferInstance
  let : IsNoetherianRing (AddMonoidAlgebra A (L → ℤ)) :=
    Algebra.FiniteType.isNoetherianRing A _
  let p := (fst H G).hom.hom.left
  let : IsSeparated p := by
    change IsSeparated (pullback.fst (H).X.hom G.X.hom)
    infer_instance
  let : LocallyOfFiniteType p := by
    change LocallyOfFiniteType (pullback.fst (H).X.hom G.X.hom)
    infer_instance
  let : QuasiCompact p := by
    change QuasiCompact (pullback.fst (H).X.hom G.X.hom)
    infer_instance
  let : IsLocallyNoetherian (H).X.left := by
    change IsLocallyNoetherian (Spec (CommRingCat.of (AddMonoidAlgebra A (L → ℤ))))
    infer_instance
  let : IsLocallyNoetherian (H ⊗ G).X.left := LocallyOfFiniteType.isLocallyNoetherian p
  have hD := exists_splitTorusHom_on_dvrTest hG (fun y => ⟨f y, hf y⟩)
  exact Langlands.AlgebraicGeometry.ResidueFibreSections.finiteImage_of_dvrExtension
    (A := AddMonoidAlgebra A (L → ℤ)) (q := (H).X.hom) (p := p)
    inferInstance inferInstance inferInstance inferInstance inferInstance _
    (dvrExtension_residueGraphSections hf hD) a ha

end System
end Adic
end Langlands.GroupScheme.HomScheme
