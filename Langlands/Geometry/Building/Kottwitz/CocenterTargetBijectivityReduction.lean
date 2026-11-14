import Langlands.Geometry.Building.Kottwitz.CocenterCocharacterExactness
import Langlands.Geometry.Building.Kottwitz.SimplyConnectedDerivedNaturalityReduction
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Integral cocenter target bijectivity from the selected comparison laws -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

section ChosenEquivalence

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (a : Choice k G) (hsc : HasSimplyConnectedDerivedGroup G) (c : Cocenter k G)
  (E : Type u) [Field E] [Algebra k E]
  (hTE : IsSplitTorus (GaloisPointComparison.baseChanged k E a.torus.toGrp))

/-- The integral cocenter equivalence commutes with the actual Galois actions. -/
theorem cocenterCocharacterEquiv_galois (σ : E ≃ₐ[k] E) (x : a.atChoice E) :
    cocenterCocharacterEquiv a hsc c E hTE (a.galoisRepresentation E σ x) =
      cocharacterLattice.galoisRepresentation k E c.torus σ
        (cocenterCocharacterEquiv a hsc c E hTE x) := by
  obtain ⟨v, rfl⟩ := (a.corootImage E).mkQ_surjective x
  rw [Choice.galoisRepresentation_projection, cocenterCocharacterEquiv_projection,
    cocenterCocharacterEquiv_projection]
  exact (geometricCocharacterMap_galois k E
    (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus) σ v).symm

variable (K : Type u) [Field K] [Algebra k K] [Algebra K E]
  [IsScalarTower k K E] [Normal k K]

/-- The integral equivalence descends, with its inverse, to actual inertia
coinvariants. -/
def cocenterInertiaEquiv :
    inertiaCoinvariants k K E (a.galoisRepresentation E) ≃ₗ[ℤ]
      torusInertiaCoinvariants k K E c.torus := by
  let e := cocenterCocharacterEquiv a hsc c E hTE
  let f : Representation.IntertwiningMap
      ((a.galoisRepresentation E).comp (relativeInertia k K E).subtype)
      ((cocharacterLattice.galoisRepresentation k E c.torus).comp
        (relativeInertia k K E).subtype) :=
    { toLinearMap := e.toLinearMap
      isIntertwining' σ := LinearMap.ext fun x =>
        cocenterCocharacterEquiv_galois a hsc c E hTE σ.val x }
  let g : Representation.IntertwiningMap
      ((cocharacterLattice.galoisRepresentation k E c.torus).comp
        (relativeInertia k K E).subtype)
      ((a.galoisRepresentation E).comp (relativeInertia k K E).subtype) :=
    { toLinearMap := e.symm.toLinearMap
      isIntertwining' σ := LinearMap.ext fun x => by
        apply e.injective
        change e (e.symm
            (cocharacterLattice.galoisRepresentation k E c.torus σ.val x)) =
          e (a.galoisRepresentation E σ.val (e.symm x))
        rw [e.apply_symm_apply, cocenterCocharacterEquiv_galois,
          e.apply_symm_apply] }
  refine LinearEquiv.ofLinearMap (Representation.Coinvariants.map _ _ f)
    (Representation.Coinvariants.map _ _ g) ?_ ?_
  · apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    change inertiaProjection k K E (cocharacterLattice.galoisRepresentation k E c.torus)
      (e (e.symm v)) = inertiaProjection k K E
        (cocharacterLattice.galoisRepresentation k E c.torus) v
    rw [e.apply_symm_apply]
  · apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    change inertiaProjection k K E (a.galoisRepresentation E) (e.symm (e v)) =
      inertiaProjection k K E (a.galoisRepresentation E) v
    rw [e.symm_apply_apply]

/-- The descended equivalence retains the actual cocharacter law. -/
@[simp]
theorem cocenterInertiaEquiv_projection (x : a.atChoice E) :
    cocenterInertiaEquiv a hsc c E hTE K
        (inertiaProjection k K E (a.galoisRepresentation E) x) =
      inertiaProjection k K E (cocharacterLattice.galoisRepresentation k E c.torus)
        (cocenterCocharacterEquiv a hsc c E hTE x) := rfl

end ChosenEquivalence

section SelectedMaps

variable
  (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
  (hfund : AlgebraicFundamentalGroupMapStatement.{u})
  (htorus : TorusFundamentalComparisonStatement.{u})
  (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosure k E]
  (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
  (hsc : HasSimplyConnectedDerivedGroup G) (c : Cocenter k G)

include hcmp hfund htorus

/-- The actual lattice equivalence is the selected fundamental-group map
followed by the selected torus comparison. -/
theorem cocenterCocharacterEquiv_eq_selected
    (hTE : IsSplitTorus (GaloisPointComparison.baseChanged k E
      (chosenChoice k G hG).torus.toGrp))
    (x : fundamentalGroup k G E hG) :
    cocenterCocharacterEquiv (chosenChoice k G hG) hsc c E hTE x =
      torusFundamentalComparison k E c.torus c.isTorus
        (fundamentalGroupMap k E G c.torus.toGrp hG
          c.isTorus.isConnectedReductive_of_fieldSplitting c.quotient x) := by
  let a := chosenChoice k G hG
  let b := chosenChoice k c.torus.toGrp c.isTorus.isConnectedReductive_of_fieldSplitting
  let : IsIso b.inclusion := b.isMaximal.isIso_of_torus c.isTorus
  let d : a.torus ⟶ b.torus :=
    Additive.ofMul (a.inclusion ≫ c.quotient ≫ inv b.inclusion)
  have hd : d ≫ (Additive.ofMul b.inclusion : b.torus ⟶ c.torus) =
      Additive.ofMul (a.inclusion ≫ c.quotient) := by
    change (a.inclusion ≫ c.quotient ≫ inv b.inclusion) ≫ b.inclusion =
      a.inclusion ≫ c.quotient
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hf : a.IsTorusFactorization E b c.quotient
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map d) := by
    change (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map c.quotient =
      (GroupScheme.baseChange (algebraBaseMap k E)).map
        (a.inclusion ≫ c.quotient ≫ inv b.inclusion) ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨v, rfl⟩ := (a.corootImage E).mkQ_surjective x
  have hm := (hfund k E G c.torus.toGrp hG
    c.isTorus.isConnectedReductive_of_fieldSplitting a b c.quotient).2.1.2 b _ hf v
  rw [(hcmp k E c.torus.toGrp
    c.isTorus.isConnectedReductive_of_fieldSplitting).2.1 b, LinearMap.id_apply] at hm
  change cocenterCocharacterEquiv a hsc c E hTE (a.projection E v) =
    torusFundamentalComparison k E c.torus c.isTorus
      (a.mapTo E b c.quotient (a.projection E v))
  rw [cocenterCocharacterEquiv_projection, hm, (htorus k E c.torus c.isTorus).2.1]
  change v ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map
      (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus) =
    (v ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map d) ≫
      (CommGroupScheme.baseChange (algebraBaseMap k E)).map
        (Additive.ofMul b.inclusion : b.torus ⟶ c.torus)
  rw [Category.assoc, ← Functor.map_comp, hd]

variable (hmap : FundamentalInertiaMapStatement.{u})
  (hinertia : TorusInertiaComparisonStatement.{u})
  (K : Type u) [Field K] [Algebra k K] [Algebra K E]
  [IsScalarTower k K E] [Normal k K] [Normal k E]

include hmap hinertia hsc

/-- The selected cocenter comparison on integral inertia targets is bijective. -/
theorem cocenterInertiaMap_bijective_of_statements :
    Function.Bijective
      ((torusInertiaComparison k K E c.torus c.isTorus).comp
        (fundamentalInertiaMap k K E c.torus.toGrp
          c.isTorus.isConnectedReductive_of_fieldSplitting G hG c.quotient)) := by
  let a := chosenChoice k G hG
  let : IsSepClosed E := IsSepClosure.sep_closed k
  have hTE : IsSplitTorus (GaloisPointComparison.baseChanged k E a.torus.toGrp) :=
    SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
      Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning _
      (IsTorus.baseChange_of_isAlgebraic k E a.torus.toGrp a.isMaximal.1)
  let e := cocenterInertiaEquiv a hsc c E hTE K
  have he : (torusInertiaComparison k K E c.torus c.isTorus).comp
      (fundamentalInertiaMap k K E c.torus.toGrp
        c.isTorus.isConnectedReductive_of_fieldSplitting G hG c.quotient) =
      e.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective
      ((fundamentalGroupGalois k G E hG).comp (relativeInertia k K E).subtype) x
    change torusInertiaComparison k K E c.torus c.isTorus
        (fundamentalInertiaMap k K E c.torus.toGrp
          c.isTorus.isConnectedReductive_of_fieldSplitting G hG c.quotient
          (fundamentalInertiaProjection k K E G hG y)) =
      e (inertiaProjection k K E (a.galoisRepresentation E) y)
    rw [((hmap k K E).1 G c.torus.toGrp hG
      c.isTorus.isConnectedReductive_of_fieldSplitting c.quotient).2.1,
      (hinertia k K E c.torus c.isTorus).2.1,
      ← cocenterCocharacterEquiv_eq_selected hcmp hfund htorus k E G hG hsc c hTE]
    exact (cocenterInertiaEquiv_projection a hsc c E hTE K y).symm
  rw [he]
  exact e.bijective

end SelectedMaps

/-- The cocenter target in the Kottwitz construction is bijective under the
existing selected comparison and descent statements. -/
theorem cocenterTargetMap_bijective_of_statements
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (htorus : TorusFundamentalComparisonStatement.{u})
    (hmap : FundamentalInertiaMapStatement.{u})
    (hinertia : TorusInertiaComparisonStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k]
    [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
    [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (hsc : HasSimplyConnectedDerivedGroup G) (c : Cocenter k G) :
    Function.Bijective (cocenterTargetMap F k G hG c) :=
  cocenterInertiaMap_bijective_of_statements hcmp hfund htorus k
    (SeparableClosure F) G hG hsc c hmap hinertia (UnramifiedClosure F)

end Langlands.Geometry.Building.Kottwitz
