import Langlands.Global.AdelicSiegelFactors
import Langlands.GroupScheme.Derived.KernelAnnihilation

/-! # Actual adelic norm-one maps from derived-subgroup containment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global

namespace AdelicGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (H G : GroupScheme (Spec (CommRingCat.of F)))

omit [NumberField F] in
/-- All-test containment in the derived subgroup makes every ambient rational
character trivial along the given actual morphism. -/
theorem charactersTrivialAlong_of_range_le_derived (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ derivedSubgroup G) :
    CharactersTrivialAlong F H G f := by
  intro χ
  have : IsSeparated (Gm (Spec (CommRingCat.of F))).X.hom := by
    have : IsSeparated Gm.overSpecZ.{u}.hom := by
      change IsSeparated (Spec.map _)
      infer_instance
    change IsSeparated (Limits.pullback.snd _ (Gm.toSpecZ _))
    infer_instance
  apply hom_ext_points
  intro U x
  have hx := hf U (show x ≫ f.hom.hom ∈ (SubgroupFunctor.range f).carrier U from ⟨x, rfl⟩)
  have h := (mem_range_kernelι_iff χ _).mp
    (derivedSubgroup_le_range_kernelι χ U hx)
  simpa only [Grp.comp_hom_hom, ← Category.assoc, Grp.Hom.hom_one, Mon.Hom.hom_one,
    MonObj.comp_one] using h

/-- The full adelic range of a morphism contained in the derived subgroup lies
in the genuine ambient norm-one subgroup. -/
theorem range_le_normOne_of_range_le_derived (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ derivedSubgroup G) :
    (map F H G f).toMonoidHom.range ≤ normOneSubgroup F G :=
  range_le_normOne_of_charactersTrivialAlong F H G f
    (charactersTrivialAlong_of_range_le_derived F H G f hf)

/-- In particular every adelic point of an actual derived subgroup maps into
ambient norm-one points. -/
theorem range_le_normOne_of_isDerivedSubgroup (f : H ⟶ G)
    (hf : IsDerivedSubgroup f) :
    (map F H G f).toMonoidHom.range ≤ normOneSubgroup F G :=
  range_le_normOne_of_range_le_derived F H G f hf.2.le

/-- The actual continuous adelic map, with codomain restricted to norm-one
points using derived-subgroup containment rather than a character premise. -/
def mapToNormOneOfDerived (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ derivedSubgroup G) :
    AdelicGroupPoints F H →ₜ* normOneSubgroup F G where
  toMonoidHom := (map F H G f).toMonoidHom.codRestrict (normOneSubgroup F G)
    (fun x => range_le_normOne_of_range_le_derived F H G f hf ⟨x, rfl⟩)
  continuous_toFun := (map F H G f).continuous.subtype_mk _

@[simp] theorem mapToNormOneOfDerived_val (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ derivedSubgroup G) (x : AdelicGroupPoints F H) :
    (mapToNormOneOfDerived F H G f hf x : AdelicGroupPoints F G) = map F H G f x := rfl

/-- The restricted map retains the actual principal-point naturality formula. -/
theorem mapToNormOneOfDerived_rational (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ derivedSubgroup G) (x : RationalGroupPoints F H) :
    mapToNormOneOfDerived F H G f hf (rational F H x) =
      rationalNormOne F G (H.affinePointsTarget f (CommAlgCat.of F F) x) := by
  apply Subtype.ext
  exact (DFunLike.congr_fun (rational_naturality F H f) x).symm

end AdelicGroupPoints

namespace AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ G)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- A positive point maps into ambient norm-one points whenever its actual
composite morphism has all-test range in the derived subgroup. -/
theorem positiveMap_mem_normOne_of_range_le_derived
    (hT : SubgroupFunctor.range (CommGroupScheme.groupHom j ≫ i) ≤ derivedSubgroup G)
    (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
    positiveMap F G T i T₀ j a ∈ normOneSubgroup F G :=
  range_le_normOne_of_range_le_derived F T₀.toGrp G (CommGroupScheme.groupHom j ≫ i)
    hT ⟨a, rfl⟩

/-- The existing actual positive-torus map, restricted to ambient norm-one points. -/
def positiveMapNormOneOfDerived
    (hT : SubgroupFunctor.range (CommGroupScheme.groupHom j ≫ i) ≤ derivedSubgroup G) :
    PositiveRealTorus.intrinsicSubgroup F T₀ →ₜ* normOneSubgroup F G where
  toMonoidHom := (positiveMap F G T i T₀ j).toMonoidHom.codRestrict
    (normOneSubgroup F G) (positiveMap_mem_normOne_of_range_le_derived F G T i T₀ j hT)
  continuous_toFun := (positiveMap F G T i T₀ j).continuous.subtype_mk _

@[simp] theorem positiveMapNormOneOfDerived_val
    (hT : SubgroupFunctor.range (CommGroupScheme.groupHom j ≫ i) ≤ derivedSubgroup G)
    (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
    (positiveMapNormOneOfDerived F G T i T₀ j hT a : AdelicGroupPoints F G) =
      positiveMap F G T i T₀ j a := rfl

variable [IsAffineHom G.X.hom] (ν : cocharacterLattice T)
  (D : StandardFactorData F G T i ν) (C : CompactFactors F G D.unipotent D.levi)

/-- The existing ordered factor product is in ambient norm-one points when
the unipotent and positive-torus morphisms have range in the actual derived functor. -/
theorem productSet_subset_normOne_of_derived
    (hN : SubgroupFunctor.range D.unipotentInclusion ≤ derivedSubgroup G)
    (hT : SubgroupFunctor.range (CommGroupScheme.groupHom j ≫ i) ≤ derivedSubgroup G)
    (A : Set (PositiveRealTorus.intrinsicSubgroup F T₀)) :
    productSet F G T i ν D C T₀ j A ⊆ normOneSubgroup F G :=
  productSet_subset_normOne F G T i ν D C T₀ j
    (charactersTrivialAlong_of_range_le_derived F D.unipotent G D.unipotentInclusion hN)
    (charactersTrivialAlong_of_range_le_derived F T₀.toGrp G
      (CommGroupScheme.groupHom j ≫ i) hT) A

end AdelicSiegelFactors

end Langlands.Global
