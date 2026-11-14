import Langlands.Geometry.Building.Kottwitz.FundamentalGroupStatement
import Langlands.GroupScheme.Derived.KernelAnnihilation

/-! # The canonical fundamental-group comparison for a torus -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)

include hT in
/-- The preimage-torus map of any presentation of a torus is trivial. -/
theorem torusChoice_scToTorus_eq_zero (a : Choice k T.toGrp) :
    a.scToTorus = 0 := by
  let : IsIso a.inclusion := a.isMaximal.isIso_of_torus hT
  let : IsAffineHom T.X.hom :=
    hT.isConnectedReductive_of_fieldSplitting.isAffineHom
  have hd : a.derivedInclusion = 1 := by
    simpa using a.isCover.isDerivedSubgroup.comp_eq_one (𝟙 T.toGrp)
  apply Additive.toMul.injective
  change subgroupIntersectionSnd (a.covering ≫ a.derivedInclusion) a.inclusion = 1
  apply (cancel_mono a.inclusion).mp
  rw [← subgroupIntersection_condition, hd]
  simp

include hT in
/-- Thus the coroot-image submodule in a torus presentation is zero. -/
theorem torusChoice_corootImage_eq_bot (a : Choice k T.toGrp) :
    a.corootImage E = ⊥ := by
  have hz : a.corootMap E = 0 := by
    ext ν
    change ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map a.scToTorus = 0
    rw [torusChoice_scToTorus_eq_zero k T hT a, Functor.map_zero, Limits.comp_zero]
  simp [Choice.corootImage, hz]

/-- Composition with the chosen maximal-torus inclusion is bijective on cocharacters. -/
theorem torusPresentationMap_bijective :
    Function.Bijective (torusPresentationMap k E T hT) := by
  let a := chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting
  let : IsIso a.inclusion := a.isMaximal.isIso_of_torus hT
  let e : a.torus ≅ T :=
    { hom := Additive.ofMul a.inclusion
      inv := Additive.ofMul (inv a.inclusion)
      hom_inv_id := congrArg Additive.ofMul (IsIso.hom_inv_id a.inclusion)
      inv_hom_id := congrArg Additive.ofMul (IsIso.inv_hom_id a.inclusion) }
  exact (cocharacterLattice.congr
    ((CommGroupScheme.baseChange (algebraBaseMap k E)).mapIso e)).bijective

/-- The comparison's representative law determines a unique linear map. -/
theorem existsUnique_torusFundamentalComparison :
    ∃! m, IsTorusFundamentalComparison k E T hT m := by
  let a := chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting
  have hz : a.corootImage E = ⊥ := torusChoice_corootImage_eq_bot k E T hT a
  let m := (a.corootImage E).liftQ (torusPresentationMap k E T hT) (by rw [hz]; exact bot_le)
  refine ⟨m, (fun _ => rfl), ?_⟩
  intro n hn
  apply LinearMap.ext
  intro x
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  exact hn ν

/-- The selected comparison satisfies its actual cocharacter law. -/
theorem torusFundamentalComparison_spec :
    IsTorusFundamentalComparison k E T hT (torusFundamentalComparison k E T hT) :=
  Classical.epsilon_spec (existsUnique_torusFundamentalComparison k E T hT).exists

/-- The selected comparison is bijective. -/
theorem torusFundamentalComparison_bijective :
    Function.Bijective (torusFundamentalComparison k E T hT) := by
  let a := chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting
  have hm := torusFundamentalComparison_spec k E T hT
  have hi := (torusPresentationMap_bijective k E T hT).1
  have hs := (torusPresentationMap_bijective k E T hT).2
  constructor
  · intro x y hxy
    obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
    obtain ⟨ν', rfl⟩ := (a.corootImage E).mkQ_surjective y
    rw [hm ν, hm ν'] at hxy
    exact congrArg (a.projection E) (hi hxy)
  · intro ν
    obtain ⟨ν', hν'⟩ := hs ν
    exact ⟨a.projection E ν', (hm ν').trans hν'⟩

/-- Naturality of actual cocharacter transport for the chosen inclusion. -/
theorem torusPresentationMap_galois (σ : E ≃ₐ[k] E) (ν :
    (chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting).lattice E) :
    cocharacterLattice.galoisRepresentation k E T σ (torusPresentationMap k E T hT ν) =
      torusPresentationMap k E T hT
        (cocharacterLattice.galoisRepresentation k E
          (chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting).torus σ ν) := by
  apply Additive.ofMul.injective
  change transportCocharacter (algebraBaseMap k E) (galoisBaseMap k E σ)
      (galoisBaseMap_over k E σ) T.toGrp
      (CommGroupScheme.groupHom ν ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map
          (chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting).inclusion) = _
  exact transportCocharacter_naturality (algebraBaseMap k E) (galoisBaseMap k E σ)
    (galoisBaseMap_over k E σ)
    (chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting).inclusion
    (CommGroupScheme.groupHom ν)

/-- The selected comparison respects the actual absolute Galois action. -/
theorem torusFundamentalComparison_galois (σ : E ≃ₐ[k] E)
    (x : fundamentalGroup k T.toGrp E hT.isConnectedReductive_of_fieldSplitting) :
    torusFundamentalComparison k E T hT
      (fundamentalGroupGalois k T.toGrp E hT.isConnectedReductive_of_fieldSplitting σ x) =
    cocharacterLattice.galoisRepresentation k E T σ
      (torusFundamentalComparison k E T hT x) := by
  let a := chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  rw [Choice.galoisRepresentation_projection, torusFundamentalComparison_spec k E T hT,
    torusFundamentalComparison_spec k E T hT]
  exact (torusPresentationMap_galois k E T hT σ ν).symm

/-- KP Fact 11.3.5 for the actual chosen presentation and actual torus lattices. -/
theorem torusFundamentalComparison_proof : TorusFundamentalComparisonStatement.{u} := by
  intro k E _ _ _ _ T hT
  exact ⟨existsUnique_torusFundamentalComparison k E T hT,
    torusFundamentalComparison_spec k E T hT,
    torusFundamentalComparison_bijective k E T hT,
    torusFundamentalComparison_galois k E T hT⟩

end Langlands.Geometry.Building.Kottwitz
