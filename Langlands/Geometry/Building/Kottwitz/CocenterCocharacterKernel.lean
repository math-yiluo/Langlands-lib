import Langlands.Geometry.Building.Kottwitz.CocenterTorusRestriction
import Langlands.Geometry.Building.Kottwitz.ReductiveMap
import Langlands.Geometry.Building.Kottwitz.TorusInertiaFunctoriality
import Langlands.GroupScheme.Derived.MaximalTorusIntersectionProof
import Langlands.GroupScheme.Derived.BaseChangeElementary
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Torus.PositiveMultipleLift
import Langlands.GroupScheme.Reductive.AbsoluteStarAction
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.FppfQuotientComparison

/-! # Cocharacters of a maximal torus mapped to the actual cocenter -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  (a : Choice k G)

/-- The full scheme-theoretic intersection `T ∩ G_der` is a torus. -/
theorem derivedTorus_isTorus :
    IsTorus (subgroupIntersection a.inclusion a.derivedInclusion) :=
  derivedMaximalTorusIntersection k G a.derived a.torus a.derivedInclusion a.inclusion
    a.isCover.isConnectedReductive a.isCover.isDerivedSubgroup a.isMaximal

/-- The intersection `T ∩ G_der`, with the commutativity of a torus. -/
def derivedTorus : CommGroupScheme (Spec (CommRingCat.of k)) :=
  { subgroupIntersection a.inclusion a.derivedInclusion with
    comm := a.derivedTorus_isTorus.isCommMonObj }

/-- The inclusion `T ∩ G_der → T`. -/
def derivedTorusInclusion : a.derivedTorus ⟶ a.torus :=
  Additive.ofMul (subgroupIntersectionFst a.inclusion a.derivedInclusion)

/-- The actual homomorphism `T_sc → T ∩ G_der` given by the pullback property. -/
def scToDerivedTorus : a.scTorus ⟶ a.derivedTorus :=
  Additive.ofMul ((IsPullback.of_hasPullback a.inclusion a.derivedInclusion).lift
    (subgroupIntersectionSnd (a.covering ≫ a.derivedInclusion) a.inclusion)
    (a.scInclusion ≫ a.covering) (by
      rw [Category.assoc]
      exact (subgroupIntersection_condition _ _).symm))

theorem scToDerivedTorus_comp_inclusion :
    a.scToDerivedTorus ≫ a.derivedTorusInclusion = a.scToTorus :=
  congrArg Additive.ofMul
    ((IsPullback.of_hasPullback a.inclusion a.derivedInclusion).lift_fst _ _ _)

theorem scToDerivedTorus_comp_snd :
    CommGroupScheme.groupHom a.scToDerivedTorus ≫
        subgroupIntersectionSnd a.inclusion a.derivedInclusion =
      a.scInclusion ≫ a.covering :=
  (IsPullback.of_hasPullback a.inclusion a.derivedInclusion).lift_snd _ _ _

/-- The map `T_sc → T ∩ G_der` is the pullback of the central cover `G_sc → G_der`. -/
theorem scToDerivedTorus_isPullback :
    IsPullback a.scInclusion (CommGroupScheme.groupHom a.scToDerivedTorus) a.covering
      (subgroupIntersectionSnd a.inclusion a.derivedInclusion) := by
  refine IsPullback.of_bot (v₂₁ := subgroupIntersectionFst a.inclusion a.derivedInclusion)
    (v₂₂ := a.derivedInclusion) (h₃₁ := a.inclusion) ?_
    (a.scToDerivedTorus_comp_snd).symm
    (IsPullback.of_hasPullback a.inclusion a.derivedInclusion).flip
  have h : CommGroupScheme.groupHom a.scToDerivedTorus ≫
      subgroupIntersectionFst a.inclusion a.derivedInclusion =
        subgroupIntersectionSnd (a.covering ≫ a.derivedInclusion) a.inclusion :=
    (IsPullback.of_hasPullback a.inclusion a.derivedInclusion).lift_fst _ _ _
  rw [h]
  exact IsPullback.of_hasPullback (a.covering ≫ a.derivedInclusion) a.inclusion

theorem flat_scToDerivedTorus :
    Flat (CommGroupScheme.groupHom a.scToDerivedTorus).hom.hom.left := by
  have hπ := a.isCover.isSimplyConnectedCover.isCentralIsogeny
  exact MorphismProperty.of_isPullback
    ((a.scToDerivedTorus_isPullback.map (Grp.forget _)).map (Over.forget _)) hπ.flat

theorem surjective_scToDerivedTorus :
    Surjective (CommGroupScheme.groupHom a.scToDerivedTorus).hom.hom.left := by
  have hπ := a.isCover.isSimplyConnectedCover.isCentralIsogeny
  exact MorphismProperty.of_isPullback
    ((a.scToDerivedTorus_isPullback.map (Grp.forget _)).map (Over.forget _)) hπ.surjective

end Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice

namespace Langlands.Geometry.Building.Kottwitz

open Langlands.GroupScheme.AlgebraicFundamentalGroup

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual homomorphism `T → D` from a chosen maximal torus to the cocenter. -/
def Cocenter.torusMap (c : Cocenter k G) (a : Choice k G) : a.torus ⟶ c.torus :=
  cocenterTorusRestriction a c

/-- The induced map `X_*(T) → X_*(D)` on geometric cocharacters. -/
def Cocenter.torusCocharacterMap (c : Cocenter k G) (a : Choice k G)
    (E : Type u) [Field E] [Algebra k E] :
    a.lattice E →ₗ[ℤ] geometricCocharacters k E c.torus :=
  geometricCocharacterMap k E (c.torusMap a)

theorem Cocenter.torusCocharacterMap_apply (c : Cocenter k G) (a : Choice k G)
    (E : Type u) [Field E] [Algebra k E] (ν : a.lattice E) :
    c.torusCocharacterMap a E ν =
      ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map (c.torusMap a) := rfl

/-- Over the separable closure, a geometric cocharacter of `T` killed by the cocenter map
has a positive multiple in the coroot image `X_*(T_sc) → X_*(T)`. -/
theorem Cocenter.exists_pos_smul_mem_corootImage (c : Cocenter k G) (a : Choice k G)
    (ν : a.lattice (SeparableClosure k))
    (hν : c.torusCocharacterMap a (SeparableClosure k) ν = 0) :
    ∃ n : ℤ, 0 < n ∧ n • ν ∈ a.corootImage (SeparableClosure k) := by
  let E := SeparableClosure k
  let b := algebraBaseMap k E
  let BG := GroupScheme.baseChange b
  let BC := CommGroupScheme.baseChange b
  have hG := a.isCover.isConnectedReductive
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have heq := derivedSubgroup_baseChange_eq_of_field b G
  have hqE : RelativeRoot.IsFppfQuotient (derivedSubgroup (BG.obj G))
      (BG.map c.quotient) := by
    rw [← heq]
    exact c.isQuotient.baseChange b
  have hdE := a.isCover.isDerivedSubgroup.baseChange_of_eq b heq
  let g := CommGroupScheme.groupHom ν ≫ BG.map a.inclusion
  have hle : SubgroupFunctor.range g ≤ derivedSubgroup (BG.obj G) := by
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    rw [← hqE.2.2.2]
    apply (mem_range_kernelι_iff _ _).2
    have h0 : y ≫ (CommGroupScheme.groupHom
        (c.torusCocharacterMap a (SeparableClosure k) ν)).hom.hom = 1 := by
      rw [hν]
      exact comp_groupHom_zero y
    rw [← h0]
    change (y ≫ (CommGroupScheme.groupHom ν ≫ BG.map a.inclusion).hom.hom) ≫
        (BG.map c.quotient).hom.hom =
      y ≫ (CommGroupScheme.groupHom ν ≫ BG.map (a.inclusion ≫ c.quotient)).hom.hom
    rw [Functor.map_comp]
    simp only [Grp.comp_hom_hom, Category.assoc]
  let y := hdE.isRepresentedBy.liftOfLE g hle
  have hy : y ≫ BG.map a.derivedInclusion = g := hdE.isRepresentedBy.liftOfLE_comp g hle
  have hpb := (IsPullback.of_hasPullback a.inclusion a.derivedInclusion).map BG
  let ν'' := hpb.lift (CommGroupScheme.groupHom ν) y hy.symm
  let ν' : cocharacterLattice (BC.obj a.derivedTorus) := Additive.ofMul ν''
  have hν' : ν' ≫ BC.map a.derivedTorusInclusion = ν :=
    congrArg Additive.ofMul (hpb.lift_fst _ _ _)
  have hsc := GaloisPinningData.isSplitTorus_separableClosure a.scTorus a.scPreimage_isTorus
  have hdt := GaloisPinningData.isSplitTorus_separableClosure a.derivedTorus
    a.derivedTorus_isTorus
  let pE := BC.map a.scToDerivedTorus
  have : Flat (CommGroupScheme.hom pE) :=
    MorphismProperty.of_isPullback (baseChange_map_isPullback b _).flip
      a.flat_scToDerivedTorus
  have : Surjective (CommGroupScheme.hom pE) :=
    MorphismProperty.of_isPullback (baseChange_map_isPullback b _).flip
      a.surjective_scToDerivedTorus
  obtain ⟨n, hn, ξ, hξ⟩ :=
    hsc.exists_positive_multiple_cocharacter_lift_of_flat_surjective hdt pE ν'
  refine ⟨n, hn, LinearMap.mem_range.2 ⟨ξ, ?_⟩⟩
  change ξ ≫ BC.map a.scToTorus = n • ν
  rw [← a.scToDerivedTorus_comp_inclusion, Functor.map_comp, ← Category.assoc]
  change (ξ ≫ pE) ≫ BC.map a.derivedTorusInclusion = n • ν
  rw [hξ, Preadditive.zsmul_comp, hν']

/-- Over the separable closure, every geometric cocharacter of the cocenter lifts to the
chosen maximal torus. -/
theorem Cocenter.torusCocharacterMap_surjective (c : Cocenter k G) (a : Choice k G) :
    Function.Surjective (c.torusCocharacterMap a (SeparableClosure k)) := by
  let E := SeparableClosure k
  let BC := CommGroupScheme.baseChange (algebraBaseMap k E)
  have hG := a.isCover.isConnectedReductive
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine c.torus.X.left := torusIsAffine k c.torus c.isTorus
  obtain ⟨Q₀, q₀, hQa, hq₀, _, hT⟩ := cocenterQuotientExistence k G a.derived
    a.derivedInclusion hG a.isCover.isDerivedSubgroup
  let : IsAffine Q₀.X.left := hQa
  have hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range a.derivedInclusion)
      c.quotient := by
    rw [a.isCover.isDerivedSubgroup.2]
    exact c.isQuotient
  let e : Q₀.toGrp ≅ c.torus.toGrp := FppfQuotientComparison.iso hq₀ hq'
  have he : q₀ ≫ e.hom = c.quotient := FppfQuotientComparison.iso_fac hq₀ hq'
  have hsplit := GaloisPinningData.isSplitTorus_separableClosure a.torus a.isMaximal.1
  obtain ⟨_, hsurj⟩ := hT a.torus a.inclusion a.isMaximal E hsplit
  let f₀ : a.torus ⟶ Q₀ := Additive.ofMul (a.inclusion ≫ q₀)
  let eh : Q₀ ⟶ c.torus := Additive.ofMul e.hom
  let ei : c.torus ⟶ Q₀ := Additive.ofMul e.inv
  have hfac : c.torusMap a = f₀ ≫ eh := by
    change Additive.ofMul (a.inclusion ≫ c.quotient) = Additive.ofMul ((a.inclusion ≫ q₀) ≫ e.hom)
    rw [Category.assoc, he]
  have hinv : ei ≫ eh = 𝟙 c.torus := congrArg Additive.ofMul e.inv_hom_id
  intro ν'
  obtain ⟨ν, hν⟩ := hsurj (ν' ≫ BC.map ei)
  change ν ≫ BC.map f₀ = ν' ≫ BC.map ei at hν
  refine ⟨ν, ?_⟩
  change ν ≫ BC.map (c.torusMap a) = ν'
  rw [hfac, Functor.map_comp, ← Category.assoc, hν, Category.assoc, ← Functor.map_comp,
    hinv, CategoryTheory.Functor.map_id, Category.comp_id]

end Langlands.Geometry.Building.Kottwitz
