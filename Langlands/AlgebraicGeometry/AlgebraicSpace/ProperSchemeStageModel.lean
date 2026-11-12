import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.AlgebraicGeometry.SchemeFilteredProperProof

/-! # Actual proper scheme models at an affine limit stage -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- An actual proper finitely presented scheme model with its original limit square. -/
structure ProperSchemeStageModel
    {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {W : Scheme.{u}} (g : W ⟶ c.pt) where
  index : I
  source : Scheme.{u}
  structureMap : source ⟶ D.obj index
  comparison : W ⟶ source
  locallyOfFinitePresentation : LocallyOfFinitePresentation structureMap
  proper : _root_.AlgebraicGeometry.IsProper structureMap
  square : IsPullback comparison g structureMap (c.π.app index)

namespace ProperSchemeStageModel

variable {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} {c : Cone D}
    {W : Scheme.{u}} {g : W ⟶ c.pt} (m : ProperSchemeStageModel D c g)

/-- The chosen stage scheme as an object over its actual affine diagram stage. -/
def schemeOver : Over (D.obj m.index) := Over.mk m.structureMap

/-- The original scheme is the actual scheme base change of the chosen model. -/
def sourceIso : Over.mk g ≅ (Over.pullback (c.π.app m.index)).obj m.schemeOver :=
  Over.isoMk m.square.isoPullback (by
    change m.square.isoPullback.hom ≫ pullback.snd m.structureMap (c.π.app m.index) = g
    exact m.square.isoPullback_hom_snd)

/-- The scheme model comparison induces a whole-space base-change isomorphism. -/
def spaceIso : (schemeToSpace c.pt).obj (Over.mk g) ≅
    baseChange (c.π.app m.index) ((schemeToSpace (D.obj m.index)).obj m.schemeOver) :=
  (schemeToSpace c.pt).mapIso m.sourceIso ≪≫ baseChangeSchemeIso (c.π.app m.index) m.schemeOver

end ProperSchemeStageModel

/-- A proper finitely presented scheme over an arbitrary cofiltered affine limit
has an actual proper finitely presented model at one of the original stages. -/
theorem exists_properSchemeStageModel
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    (W : Scheme.{u}) (g : W ⟶ c.pt)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (hg : _root_.AlgebraicGeometry.IsProper g) : Nonempty (ProperSchemeStageModel D c g) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let A := D.op ⋙ Scheme.Γ
  let dA := Scheme.Γ.mapCocone c.op
  have hcA : IsColimit dA := (nonempty_isColimit_Γ_mapCocone D c hc).some
  let := hg
  obtain ⟨j, Xj, gj, π, hfp, hqc, hqs, hproper, hpb⟩ :=
    @SchemeLimitModel.schemeFilteredProperModelExistence.{u} Iᵒᵖ _ _ A dA hcA W
      (g ≫ c.pt.isoSpec.hom) inferInstance inferInstance inferInstance inferInstance
  let := hfp
  let := hqc
  let := hqs
  let := hproper
  refine ⟨⟨j.unop, Xj, gj ≫ (D.obj j.unop).isoSpec.inv, π,
    inferInstance, inferInstance, ?_⟩⟩
  refine hpb.of_iso (Iso.refl _) (Iso.refl _) c.pt.isoSpec.symm (D.obj j.unop).isoSpec.symm
    (by simp) (by simp) (by simp) ?_
  change Spec.map (c.π.app j.unop).appTop ≫ (D.obj j.unop).isoSpec.inv =
    c.pt.isoSpec.inv ≫ c.π.app j.unop
  exact Scheme.isoSpec_inv_naturality (X := c.pt) (Y := D.obj j.unop) (c.π.app j.unop)

end Langlands.AlgebraicGeometry.AlgebraicSpace
