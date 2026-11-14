import Langlands.Geometry.Building.Kottwitz.TorusMapStatement
import Langlands.Geometry.Building.Kottwitz.TorusInertiaFunctoriality
import Langlands.Geometry.Building.Kottwitz.CentralSurjectionZeroSurjectivity
import Langlands.Geometry.Building.Kottwitz.CocenterSurjectivityReduction
import Langlands.GroupScheme.Torus.BaseChange

/-! # Torus Kottwitz naturality from the norm characterization -/

noncomputable section
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

section RelativeNorm

variable (k K L : Type u) [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional K L] [IsGalois K L]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffine S.X.left] [IsAffine T.X.left]

/-- Relative finite-Galois norms commute with every actual torus morphism. -/
theorem relativeNorm_natural (f : S ⟶ T)
    (x : affinePoints S.toGrp (CommAlgCat.of k L)) :
    affinePointsTarget S.toGrp (CommGroupScheme.groupHom f) (CommAlgCat.of k K)
        (GaloisPoint.relativeNorm k K L S x) =
      GaloisPoint.relativeNorm k K L T
        (affinePointsTarget S.toGrp (CommGroupScheme.groupHom f) (CommAlgCat.of k L) x) := by
  apply GaloisPoint.relativeExtend_injective k K L T.toGrp
  have hn := DFunLike.congr_fun
    (affinePointsTarget_naturality S.toGrp (CommGroupScheme.groupHom f)
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k K L)))
    (GaloisPoint.relativeNorm k K L S x)
  change GaloisPoint.relativeExtend k K L T.toGrp
    (affinePointsTarget S.toGrp (CommGroupScheme.groupHom f) _
      (GaloisPoint.relativeNorm k K L S x)) =
    affinePointsTarget S.toGrp (CommGroupScheme.groupHom f) _
      (GaloisPoint.relativeExtend k K L S.toGrp
        (GaloisPoint.relativeNorm k K L S x)) at hn
  rw [hn, GaloisPoint.relativeExtend_norm, map_prod, GaloisPoint.relativeExtend_norm]
  apply Finset.prod_congr rfl
  intro σ _
  exact (DFunLike.congr_fun
    (affinePointsTarget_naturality S.toGrp (CommGroupScheme.groupHom f)
      (CommAlgCat.ofHom (σ.restrictScalars k).toAlgHom)) x).symm

end RelativeNorm

section SplitValuation

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (v : Valuation k (WithZero (Multiplicative ℤ))) (f : S ⟶ T)

/-- Split valuations commute with homomorphisms, by the character-pairing law. -/
theorem splitValuation_natural (x : rationalPoints S.toGrp) :
    (splitValuation T hT v (rationalPoints.map (CommGroupScheme.groupHom f) x)).toAdd =
      (splitValuation S hS v x).toAdd ≫ f := by
  apply (cocharacterDualEquiv T hT).injective
  apply LinearMap.ext
  intro χ
  rw [cocharacterDualEquiv_apply, cocharacterDualEquiv_apply, splitValuation_pairing]
  have hp : latticePairing T χ ((splitValuation S hS v x).toAdd ≫ f) =
      latticePairing S (f ≫ χ) (splitValuation S hS v x).toAdd := by
    change gmEndEquiv k (((splitValuation S hS v x).toAdd ≫ f) ≫ χ) =
      gmEndEquiv k ((splitValuation S hS v x).toAdd ≫ f ≫ χ)
    rw [Category.assoc]
  rw [hp, splitValuation_pairing]
  exact congrArg (fun z => (IntegerValuation.orderUnits v z).toAdd)
    (rationalCharacterEval_characterRestrict (CommGroupScheme.groupHom f)
      ((rationalCharacters.equivCharacterLattice T).symm χ) x).symm

end SplitValuation

section Tower

variable (k L E : Type u) [Field k] [Field L] [Field E]
  [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]

/-- The canonical direct/iterated base-change comparison is natural in the group. -/
theorem towerBaseChangeIso_natural {S T : GroupScheme (Spec (CommRingCat.of k))}
    (f : S ⟶ T) :
    (GroupScheme.baseChange (baseMap L E)).map
        ((GroupScheme.baseChange (baseMap k L)).map f) ≫
        (towerBaseChangeIso k L E T).hom =
      (towerBaseChangeIso k L E S).hom ≫
        (GroupScheme.baseChange (baseMap k E)).map f := by
  have heq : ∀ {b c : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of k)}
      (h : b = c),
      (GroupScheme.baseChange b).map f ≫
          (eqToIso (congrArg (fun t => (GroupScheme.baseChange t).obj T) h)).hom =
        (eqToIso (congrArg (fun t => (GroupScheme.baseChange t).obj S) h)).hom ≫
          (GroupScheme.baseChange c).map f := by
    intro b c h
    subst c
    simp
  have hc :=
    (((Functor.mapGrpNatIso (Over.pullbackComp (baseMap L E) (baseMap k L))) ≪≫
      Functor.mapGrpCompIso).inv.naturality f)
  change (GroupScheme.baseChange (baseMap L E)).map
      ((GroupScheme.baseChange (baseMap k L)).map f) ≫
      (baseChangeCompIso (baseMap k L) (baseMap L E) T).inv =
    (baseChangeCompIso (baseMap k L) (baseMap L E) S).inv ≫
      (GroupScheme.baseChange (baseMap L E ≫ baseMap k L)).map f at hc
  change _ ≫ ((baseChangeCompIso (baseMap k L) (baseMap L E) T).inv ≫
      (eqToIso (congrArg (fun t => (GroupScheme.baseChange t).obj T)
        (baseMap_tower k L E))).hom) =
    ((baseChangeCompIso (baseMap k L) (baseMap L E) S).inv ≫
      (eqToIso (congrArg (fun t => (GroupScheme.baseChange t).obj S)
        (baseMap_tower k L E))).hom) ≫ _
  rw [← Category.assoc, hc, Category.assoc, heq (baseMap_tower k L E),
    ← Category.assoc]

/-- Extending cocharacters through a tower commutes with actual postcomposition. -/
theorem extendGeometricCocharacters_natural
    {S T : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)
    (nu : cocharacterLattice ((CommGroupScheme.baseChange (baseMap k L)).obj S)) :
    extendGeometricCocharacters k L E T
        (nu ≫ (CommGroupScheme.baseChange (baseMap k L)).map f) =
      geometricCocharacterMap k E f (extendGeometricCocharacters k L E S nu) := by
  let iS : (CommGroupScheme.baseChange (baseMap L E)).obj
      ((CommGroupScheme.baseChange (baseMap k L)).obj S) ≅
      (CommGroupScheme.baseChange (baseMap k E)).obj S :=
    CommGroupScheme.isoOfGroupIso (towerBaseChangeIso k L E S.toGrp)
  let iT : (CommGroupScheme.baseChange (baseMap L E)).obj
      ((CommGroupScheme.baseChange (baseMap k L)).obj T) ≅
      (CommGroupScheme.baseChange (baseMap k E)).obj T :=
    CommGroupScheme.isoOfGroupIso (towerBaseChangeIso k L E T.toGrp)
  change cocharacterLattice.baseChange (baseMap L E) _
      (nu ≫ (CommGroupScheme.baseChange (baseMap k L)).map f) ≫
        iT.hom =
    (cocharacterLattice.baseChange (baseMap L E) _ nu ≫ iS.hom) ≫
        (CommGroupScheme.baseChange (baseMap k E)).map f
  rw [cocharacterLattice.baseChange_comp, Category.assoc]
  have hn : (CommGroupScheme.baseChange (baseMap L E)).map
      ((CommGroupScheme.baseChange (baseMap k L)).map f) ≫ iT.hom =
    iS.hom ≫ (CommGroupScheme.baseChange (baseMap k E)).map f :=
    towerBaseChangeIso_natural k L E (CommGroupScheme.groupHom f)
  rw [hn, Category.assoc]

end Tower

section Kottwitz

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k]
  [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [Normal k (UnramifiedClosure F)]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hS : IsTorus S.toGrp) (hT : IsTorus T.toGrp) (f : S ⟶ T)

/-- Push the selected source torus homomorphism through the actual inertia map. -/
def torusKottwitzPushforward :
    torusKPoints F k S →* Multiplicative (TorusTarget F k T) :=
  ((torusInertiaMap k (SeparableClosure F) f (UnramifiedClosure F)).toAddMonoidHom.toMultiplicative).comp
    (torusKottwitz F k S hS)

/-- The norm characterization implies naturality of the selected torus maps. -/
theorem torusKottwitz_natural_of_existence
    (hexists : TorusKottwitzExistenceStatement.{u}) (x : torusKPoints F k S) :
    (torusKottwitz F k T hT
      (affinePointsTarget S.toGrp (CommGroupScheme.groupHom f)
        (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
      torusInertiaMap k (SeparableClosure F) f (UnramifiedClosure F)
        (torusKottwitz F k S hS x).toAdd := by
  let : IsAffine S.X.left := torusIsAffine k S hS
  let : IsAffine T.X.left := torusIsAffine k T hT
  obtain ⟨L, hfin, hgal, hSL, hTL⟩ :=
    exists_commonFiniteGaloisSplittingField_inside (SeparableClosure F)
      (baseChanged k (UnramifiedClosure F) S.toGrp)
      (baseChanged k (UnramifiedClosure F) T.toGrp)
      (IsTorus.baseChange hS) (IsTorus.baseChange hT)
  let : FiniteDimensional (UnramifiedClosure F) L := hfin
  let : IsGalois (UnramifiedClosure F) L := hgal
  have hSL' : IsSplitTorus ((CommGroupScheme.baseChange (baseMap k L)).obj S).toGrp :=
    (IsSplitTorus.baseChange_fieldTower_iff k (UnramifiedClosure F) L S.toGrp).2 hSL
  have hTL' : IsSplitTorus ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp :=
    (IsSplitTorus.baseChange_fieldTower_iff k (UnramifiedClosure F) L T.toGrp).2 hTL
  obtain ⟨y, rfl⟩ := ((hexists F k S hS).2.2.2 L hSL').1 x
  obtain ⟨t, rfl⟩ := (baseChangeCoeffEquiv k L S.toGrp).surjective y
  rw [relativeNorm_natural, ← baseChangeCoeffEquiv_map,
    (hexists F k T hT).2.1 L hTL', (hexists F k S hS).2.1 L hSL']
  change inertiaProjection k (UnramifiedClosure F) (SeparableClosure F)
      (cocharacterLattice.galoisRepresentation k (SeparableClosure F) T)
      (extendGeometricCocharacters k L (SeparableClosure F) T
        (splitValuation ((CommGroupScheme.baseChange (baseMap k L)).obj T) hTL'
          (normalizedIntermediateValuation F L)
          (rationalPoints.map
            (CommGroupScheme.groupHom ((CommGroupScheme.baseChange (baseMap k L)).map f))
            t)).toAdd) =
    torusInertiaMap k (SeparableClosure F) f (UnramifiedClosure F)
      (inertiaProjection k (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation k (SeparableClosure F) S)
        (extendGeometricCocharacters k L (SeparableClosure F) S
          (splitValuation ((CommGroupScheme.baseChange (baseMap k L)).obj S) hSL'
            (normalizedIntermediateValuation F L) t).toAdd))
  rw [torusInertiaMap_projection,
    splitValuation_natural hSL' hTL' (normalizedIntermediateValuation F L)
      ((CommGroupScheme.baseChange (baseMap k L)).map f),
    extendGeometricCocharacters_natural]

/-- Naturality identifies the actual target composite with source pushforward. -/
theorem torusKottwitzPushforward_eq
    (hexists : TorusKottwitzExistenceStatement.{u}) :
    torusKottwitzPushforward F k hS f =
      (torusKottwitz F k T hT).comp
        (affinePointsTarget S.toGrp (CommGroupScheme.groupHom f)
          (CommAlgCat.of k (UnramifiedClosure F))) := by
  ext x
  apply Multiplicative.toAdd.injective
  exact (torusKottwitz_natural_of_existence F k hS hT f hexists x).symm

end Kottwitz

/-- The cocenter construction needs only the five comparison statements and
torus existence; torus naturality follows from the norm characterization. -/
theorem simplyConnectedDerivedKottwitz_of_norm_inputs
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (htorus : TorusFundamentalComparisonStatement.{u})
    (hmap : FundamentalInertiaMapStatement.{u})
    (hinertia : TorusInertiaComparisonStatement.{u})
    (hexists : TorusKottwitzExistenceStatement.{u}) :
    SimplyConnectedDerivedKottwitzStatement.{u} := by
  apply simplyConnectedDerivedKottwitz_of_torus_inputs
    hcmp hfund htorus hmap hinertia hexists
  intro F _ _ _ _ k _ _ _ _ _ S T hS hT f x
  exact torusKottwitz_natural_of_existence F k hS hT f hexists x

end Langlands.Geometry.Building.Kottwitz
