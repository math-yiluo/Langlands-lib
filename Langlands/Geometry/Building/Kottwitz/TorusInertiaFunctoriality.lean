import Langlands.Geometry.Building.Kottwitz.FundamentalGroupStatement
import Langlands.GroupScheme.AlgebraicFundamentalGroupFunctorStatement
import Langlands.GroupScheme.AlgebraicFundamentalGroupStatement

/-! # Induced maps between actual torus inertia targets -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)

/-- The map on geometric cocharacters induced by an actual torus morphism. -/
def geometricCocharacterMap :
    geometricCocharacters k E S →ₗ[ℤ] geometricCocharacters k E T :=
  (AddMonoidHom.mk'
    (fun ν => ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map f)
    (fun _ _ => Preadditive.add_comp _ _ _ _ _ _)).toIntLinearMap

/-- The actual geometric cocharacter map commutes with Galois transport. -/
theorem geometricCocharacterMap_galois (σ : E ≃ₐ[k] E)
    (ν : geometricCocharacters k E S) :
    cocharacterLattice.galoisRepresentation k E T σ
        (geometricCocharacterMap k E f ν) =
      geometricCocharacterMap k E f
        (cocharacterLattice.galoisRepresentation k E S σ ν) := by
  apply Additive.ofMul.injective
  change transportCocharacter (algebraBaseMap k E) (galoisBaseMap k E σ)
    (galoisBaseMap_over k E σ) T.toGrp
    (CommGroupScheme.groupHom ν ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map (CommGroupScheme.groupHom f)) = _
  exact transportCocharacter_naturality (algebraBaseMap k E) (galoisBaseMap k E σ)
    (galoisBaseMap_over k E σ) (CommGroupScheme.groupHom f) (CommGroupScheme.groupHom ν)

variable (K : Type u) [Field K] [Algebra k K] [Algebra K E]
  [IsScalarTower k K E] [Normal k K]

/-- The map on actual integral inertia coinvariants induced by a torus morphism. -/
def torusInertiaMap :
    torusInertiaCoinvariants k K E S →ₗ[ℤ] torusInertiaCoinvariants k K E T :=
  Representation.Coinvariants.map _ _
    { toLinearMap := geometricCocharacterMap k E f
      isIntertwining' σ := LinearMap.ext fun ν =>
        (geometricCocharacterMap_galois k E f σ.val ν).symm }

/-- The induced inertia map has the defining law on actual cocharacters. -/
@[simp]
theorem torusInertiaMap_projection (ν : geometricCocharacters k E S) :
    torusInertiaMap k E f K
        (inertiaProjection k K E (cocharacterLattice.galoisRepresentation k E S) ν) =
      inertiaProjection k K E (cocharacterLattice.galoisRepresentation k E T)
        (geometricCocharacterMap k E f ν) := rfl

omit K [Field K] [Algebra k K] [Algebra K E] [IsScalarTower k K E] [Normal k K] in
/-- Naturality of the selected torus fundamental comparison follows from its
representative law and the existing fundamental-group map statements. -/
theorem torusFundamentalComparison_natural_of_statements
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (htorus : TorusFundamentalComparisonStatement.{u})
    [IsSepClosure k E] (hS : IsTorus S.toGrp) (hT : IsTorus T.toGrp)
    (x : fundamentalGroup k S.toGrp E hS.isConnectedReductive_of_fieldSplitting) :
    torusFundamentalComparison k E T hT
        (fundamentalGroupMap k E S.toGrp T.toGrp
          hS.isConnectedReductive_of_fieldSplitting
          hT.isConnectedReductive_of_fieldSplitting (CommGroupScheme.groupHom f) x) =
      geometricCocharacterMap k E f (torusFundamentalComparison k E S hS x) := by
  let a := chosenChoice k S.toGrp hS.isConnectedReductive_of_fieldSplitting
  let c := chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting
  let : IsIso c.inclusion := c.isMaximal.isIso_of_torus hT
  let d : a.torus ⟶ c.torus :=
    Additive.ofMul (a.inclusion ≫ CommGroupScheme.groupHom f ≫ inv c.inclusion)
  have hd : d ≫ Additive.ofMul c.inclusion = Additive.ofMul a.inclusion ≫ f := by
    change (a.inclusion ≫ CommGroupScheme.groupHom f ≫ inv c.inclusion) ≫
      c.inclusion = a.inclusion ≫ CommGroupScheme.groupHom f
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hf : a.IsTorusFactorization E c (CommGroupScheme.groupHom f)
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map d) := by
    change (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map (CommGroupScheme.groupHom f) =
      (GroupScheme.baseChange (algebraBaseMap k E)).map
        (a.inclusion ≫ CommGroupScheme.groupHom f ≫ inv c.inclusion) ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map c.inclusion
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  have hm := (hfund k E S.toGrp T.toGrp
    hS.isConnectedReductive_of_fieldSplitting hT.isConnectedReductive_of_fieldSplitting
    a c (CommGroupScheme.groupHom f)).2.1.2 c _ hf ν
  rw [(hcmp k E T.toGrp hT.isConnectedReductive_of_fieldSplitting).2.1 c,
    LinearMap.id_apply] at hm
  change torusFundamentalComparison k E T hT (a.mapTo E c
      (CommGroupScheme.groupHom f) (a.projection E ν)) = _
  rw [hm, (htorus k E T hT).2.1, (htorus k E S hS).2.1]
  change (ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map d) ≫
      (CommGroupScheme.baseChange (algebraBaseMap k E)).map (Additive.ofMul c.inclusion) =
    (ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map
      (Additive.ofMul a.inclusion)) ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map f
  rw [Category.assoc, ← Functor.map_comp, hd]
  have hb := (CommGroupScheme.baseChange (algebraBaseMap k E)).map_comp
    (Additive.ofMul a.inclusion : a.torus ⟶ S) f
  exact (congrArg (fun y => ν ≫ y) hb).trans
    (Category.assoc ν
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map
        (Additive.ofMul a.inclusion : a.torus ⟶ S))
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map f)).symm

end Langlands.Geometry.Building.Kottwitz
