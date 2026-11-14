import Langlands.GroupScheme.RelativeLevi.ModuliValue
import Langlands.GroupScheme.HomScheme.AdmissibleRestrictionPoints

/-! # Coherent restriction of actual subgroup images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeLevi

open TorusSubgroupModuli

variable {S : Scheme.{u}} {P : GroupScheme S} {M T N : Over S}

/-- Restrict the all-test subgroup condition through the actual direct/iterated
pullback comparison. This definition imposes no geometric admissibility condition. -/
def restrictImage (a : T ⟶ M)
    (F : SubgroupFunctor ((baseChange M.hom).obj P)) :
    SubgroupFunctor ((baseChange T.hom).obj P) :=
  (F.baseChange a.left).comap
    (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) P).inv

/-- Restricted membership uses the published family point adjunction. -/
theorem mem_restrictImage (a : T ⟶ M)
    (F : SubgroupFunctor ((baseChange M.hom).obj P))
    (V : Over T.left) (x : V ⟶ ((baseChange T.hom).obj P).X) :
    x ∈ (restrictImage a F).carrier V ↔
      familyPointsEquiv (G := P) a V x ∈
        F.carrier ((Over.map a.left).obj V) :=
  Iff.rfl

/-- Identity family restriction on points uses only the identity test comparison. -/
theorem familyPointsEquiv_id (V : Over M.left)
    (x : V ⟶ ((baseChange M.hom).obj P).X) :
    familyPointsEquiv (G := P) (𝟙 M) V x =
      (Over.mapId M.left).hom.app V ≫ x := by
  apply familyPointsEquiv_eq_of_original
  simp

/-- The family point adjunction respects composition, with the actual comparison
between the two relative test schemes. -/
theorem familyPointsEquiv_comp (a : T ⟶ M) (b : N ⟶ T)
    (V : Over N.left) (x : V ⟶ ((baseChange N.hom).obj P).X) :
    familyPointsEquiv (G := P) a ((Over.map b.left).obj V)
        (familyPointsEquiv (G := P) b V x) =
      (Over.mapComp b.left a.left).inv.app V ≫
        familyPointsEquiv (G := P) (b ≫ a) V x := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, familyPointsEquiv_original,
      Over.mapComp_inv_app_left]
    erw [Category.id_comp]
    exact (familyPointsEquiv_original (G := P) (b ≫ a) V x).symm
  · exact (Over.w _).trans (Over.w _).symm

/-- The identity restriction is literal equality of all-test subgroup functors. -/
@[simp]
theorem restrictImage_id
    (F : SubgroupFunctor ((baseChange M.hom).obj P)) :
    restrictImage (𝟙 M) F = F := by
  ext V x
  rw [mem_restrictImage, familyPointsEquiv_id]
  constructor
  · intro hx
    simpa only [Iso.inv_hom_id_app_assoc, Functor.id_obj] using
      F.comp_mem ((Over.mapId M.left).inv.app V) hx
  · exact F.comp_mem ((Over.mapId M.left).hom.app V)

/-- Successive restriction equals direct restriction on all relative tests. -/
theorem restrictImage_comp (a : T ⟶ M) (b : N ⟶ T)
    (F : SubgroupFunctor ((baseChange M.hom).obj P)) :
    restrictImage b (restrictImage a F) = restrictImage (b ≫ a) F := by
  ext V x
  rw [mem_restrictImage, mem_restrictImage, mem_restrictImage,
    familyPointsEquiv_comp]
  constructor
  · intro hx
    simpa only [Iso.hom_inv_id_app_assoc, Over.comp_left] using
      F.comp_mem ((Over.mapComp b.left a.left).hom.app V) hx
  · exact F.comp_mem ((Over.mapComp b.left a.left).inv.app V)

/-- The presheaf of all subgroup functors of the actual pullbacks of `P`.
Its relative Levi subfunctor additionally requires geometric stability. -/
def subgroupPresheaf (P : GroupScheme S) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := SubgroupFunctor ((baseChange T.unop.hom).obj P)
  map a := TypeCat.ofHom (restrictImage a.unop)
  map_id _ := by
    apply TypeCat.homEquiv.injective
    funext F
    exact restrictImage_id F
  map_comp a b := by
    apply TypeCat.homEquiv.injective
    funext F
    exact (restrictImage_comp a.unop b.unop F).symm

/-- Restriction of a represented image is the image of the actual pulled-back
inclusion, followed by the ambient comparison. -/
theorem restrictImage_range {K : GroupScheme M.left}
    (j : K ⟶ (baseChange M.hom).obj P) (a : T ⟶ M) :
    restrictImage a (SubgroupFunctor.range j) =
      SubgroupFunctor.range (familyHom j a) := by
  simp only [restrictImage, familyHom, SubgroupFunctor.range_comp_iso,
    SubgroupFunctor.range_baseChangeHom]

end Langlands.GroupScheme.RelativeLevi
