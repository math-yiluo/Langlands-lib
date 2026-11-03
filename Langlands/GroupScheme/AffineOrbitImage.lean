import Langlands.GroupScheme.SchemeActionOrbit
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.GroupScheme.ImageGenerationAppend

/-! # The actual schematic image of an affine orbit -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

variable {S : Scheme.{u}} {G : GroupScheme S} {X : Over S}
  (a : SchemeAction G X) (x : 𝟙_ (Over S) ⟶ X)

/-- The actual schematic image of the orbit map, over the original base. -/
def orbitImage : Over S :=
  Over.mk ((a.orbitMap x).left.imageι ≫ X.hom)

/-- The closed inclusion of the schematic orbit image. -/
def orbitImageInclusion : a.orbitImage x ⟶ X :=
  Over.homMk (a.orbitMap x).left.imageι rfl

/-- The orbit morphism factored through its schematic image. -/
def orbitImageProjection : G.X ⟶ a.orbitImage x :=
  Over.homMk (a.orbitMap x).left.toImage (by
    change (a.orbitMap x).left.toImage ≫
      ((a.orbitMap x).left.imageι ≫ X.hom) = G.X.hom
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact Over.w _)

instance orbitImageInclusion_closed : IsClosedImmersion (a.orbitImageInclusion x).left :=
  inferInstanceAs (IsClosedImmersion (a.orbitMap x).left.imageι)

instance orbitImageInclusion_mono : Mono (a.orbitImageInclusion x) :=
  Over.mono_of_mono_left _

@[reassoc (attr := simp)]
theorem orbitImageProjection_comp :
    a.orbitImageProjection x ≫ a.orbitImageInclusion x = a.orbitMap x :=
  Over.OverMorphism.ext (Scheme.Hom.toImage_imageι _)

variable [IsAffine X.left] [QuasiCompact (a.orbitMap x).left]

instance orbitImage_affine : IsAffine (a.orbitImage x).left :=
  isAffine_of_isAffineHom (a.orbitImageInclusion x).left

instance orbitImageProjection_quasiCompact :
    QuasiCompact (a.orbitImageProjection x).left :=
  inferInstanceAs (QuasiCompact (a.orbitMap x).left.toImage)

instance orbitImageProjection_schematic :
    IsSchemeTheoreticallyDominant (a.orbitImageProjection x).left :=
  ImageGeneration.isSchemeTheoreticallyDominant_toImage _

theorem orbitImage_reduced [IsReduced G.X.left] : IsReduced (a.orbitImage x).left :=
  IsSchemeTheoreticallyDominant.isReduced (a.orbitImageProjection x).left

variable [Flat G.X.hom]

private theorem exists_orbitImageActionHom :
    ∃ h : G.X ⊗ a.orbitImage x ⟶ a.orbitImage x,
      h ≫ a.orbitImageInclusion x =
        a.act (fst G.X (a.orbitImage x))
          (snd G.X (a.orbitImage x) ≫ a.orbitImageInclusion x) := by
  let p := G.X ◁ a.orbitImageProjection x
  let : IsSchemeTheoreticallyDominant p.left :=
    ImageGeneration.isSchemeTheoreticallyDominant_whiskerLeft
      (a.orbitImageProjection x) G.X
  let g := a.act (fst G.X (a.orbitImage x))
    (snd G.X (a.orbitImage x) ≫ a.orbitImageInclusion x)
  let h := ((fst G.X G.X) * (snd G.X G.X)) ≫ a.orbitImageProjection x
  have he : p ≫ g = h ≫ a.orbitImageInclusion x := by
    dsimp only [p, g, h]
    rw [a.naturality, whiskerLeft_fst, whiskerLeft_snd_assoc,
      orbitImageProjection_comp, Category.assoc, orbitImageProjection_comp,
      a.comp_orbitMap, a.comp_orbitMap, a.act_mul]
  have hker : (a.orbitImageInclusion x).left.ker ≤ g.left.ker := by
    have he' : p.left ≫ g.left =
        h.left ≫ (a.orbitImageInclusion x).left := congrArg Over.Hom.left he
    have hh := h.left.le_ker_comp (a.orbitImageInclusion x).left
    rw [← he', Scheme.Hom.ker_comp,
      p.left.ker_eq_bot, Scheme.IdealSheafData.map_bot] at hh
    exact hh
  exact ImageGeneration.exists_over_factor_of_ker_le (a.orbitImageInclusion x) g hker

/-- The action morphism induced on the schematic orbit image. -/
def orbitImageActionHom : G.X ⊗ a.orbitImage x ⟶ a.orbitImage x :=
  (a.exists_orbitImageActionHom x).choose

@[reassoc]
theorem orbitImageActionHom_comp :
    a.orbitImageActionHom x ≫ a.orbitImageInclusion x =
      a.act (fst G.X (a.orbitImage x))
        (snd G.X (a.orbitImage x) ≫ a.orbitImageInclusion x) :=
  (a.exists_orbitImageActionHom x).choose_spec

private theorem lift_orbitImageActionHom_comp {T : Over S}
    (g : T ⟶ G.X) (y : T ⟶ a.orbitImage x) :
    (lift g y ≫ a.orbitImageActionHom x) ≫ a.orbitImageInclusion x =
      a.act g (y ≫ a.orbitImageInclusion x) := by
  rw [Category.assoc, orbitImageActionHom_comp, a.naturality,
    lift_fst, lift_snd_assoc]

/-- The original action restricts to its actual schematic orbit image. -/
@[instance_reducible]
def orbitImageAction : SchemeAction G (a.orbitImage x) :=
  schemeActionOfPointLaws (a.orbitImageActionHom x)
    (fun y => by
      apply (cancel_mono (a.orbitImageInclusion x)).mp
      rw [a.lift_orbitImageActionHom_comp, a.act_one])
    (fun g h y => by
      apply (cancel_mono (a.orbitImageInclusion x)).mp
      rw [a.lift_orbitImageActionHom_comp, a.lift_orbitImageActionHom_comp,
        a.lift_orbitImageActionHom_comp, a.act_mul])

/-- The inclusion intertwines both actions on every scheme test. -/
@[reassoc]
theorem orbitImageAction_act_comp {T : Over S}
    (g : T ⟶ G.X) (y : T ⟶ a.orbitImage x) :
    (a.orbitImageAction x).act g y ≫ a.orbitImageInclusion x =
      a.act g (y ≫ a.orbitImageInclusion x) :=
  a.lift_orbitImageActionHom_comp x g y

/-- The identity point of the orbit lifts to its schematic image. -/
def orbitImagePoint : 𝟙_ (Over S) ⟶ a.orbitImage x :=
  (1 : 𝟙_ (Over S) ⟶ G.X) ≫ a.orbitImageProjection x

omit [IsAffine X.left] [QuasiCompact (a.orbitMap x).left] [Flat G.X.hom] in
@[reassoc (attr := simp)]
theorem orbitImagePoint_comp :
    a.orbitImagePoint x ≫ a.orbitImageInclusion x = x := by
  rw [orbitImagePoint, Category.assoc, orbitImageProjection_comp,
    a.comp_orbitMap, a.act_one, toUnit_unit, Category.id_comp]

/-- The projected orbit map is the orbit map for the restricted action. -/
theorem orbitImageAction_orbitMap :
    (a.orbitImageAction x).orbitMap (a.orbitImagePoint x) =
      a.orbitImageProjection x := by
  apply (cancel_mono (a.orbitImageInclusion x)).mp
  rw [orbitImageProjection_comp, orbitMap, a.orbitImageAction_act_comp,
    Category.assoc, orbitImagePoint_comp]
  rfl

end Langlands.GroupScheme.SchemeAction
