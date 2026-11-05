import Langlands.Geometry.Building.SimplyConnectedImageNormal
import Langlands.GroupScheme.SimplyConnected.CoverComparison
import Langlands.GroupScheme.RepresentedSubgroupTransport
import Langlands.GroupScheme.HomConjugacy
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! # Normality of the actual simply connected image and zero-subgroup products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {B : Scheme.{u}} {G : GroupScheme B} {F : SubgroupFunctor G}

/-- Inner automorphisms preserve an all-test normal subgroup functor. -/
theorem IsNormal.comap_innerIso (hF : F.IsNormal) (g : Over.mk (𝟙 B) ⟶ G.X) :
    F.comap (G.innerIso g).hom = F := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  change x ≫ (G.innerIso g).hom.hom.hom ∈ F.carrier T ↔ x ∈ F.carrier T
  rw [G.comp_innerIso_hom]
  constructor
  · intro hx
    have h := hF T (G.constantPoint g T)⁻¹ _ (Subgroup.mem_top _) hx
    simpa [mul_assoc] using h
  · exact fun hx => hF T (G.constantPoint g T) x (Subgroup.mem_top _) hx

end SubgroupFunctor

variable {k : Type u} [Field k]
  {G D C : GroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {π : C ⟶ D}

/-- Restrict an actual ambient inner automorphism to the actual derived subgroup. -/
def IsDerivedSubgroup.conjugationIso (hd : IsDerivedSubgroup d) (g : rationalPoints G) :
    D ≅ D :=
  hd.isRepresentedBy.isoOfComap hd.isRepresentedBy (G.innerIso g)
    ((derivedSubgroup_isNormal G).comap_innerIso g)

@[reassoc]
theorem IsDerivedSubgroup.conjugationIso_hom_comp
    (hd : IsDerivedSubgroup d) (g : rationalPoints G) :
    (hd.conjugationIso g).hom ≫ d = d ≫ (G.innerIso g).hom :=
  hd.isRepresentedBy.isoOfComap_hom_comp hd.isRepresentedBy (G.innerIso g)
    ((derivedSubgroup_isNormal G).comap_innerIso g)

/-- Lift ambient conjugation through the supplied simply connected derived cover. -/
def IsSimplyConnectedDerivedCover.conjugationLiftIso
    (h : IsSimplyConnectedDerivedCover d π) (g : rationalPoints G) : C ≅ C :=
  h.isSimplyConnectedCover.isoOver h.isSimplyConnectedCover
    (h.isDerivedSubgroup.conjugationIso g)

@[reassoc]
theorem IsSimplyConnectedDerivedCover.conjugationLiftIso_hom_comp
    (h : IsSimplyConnectedDerivedCover d π) (g : rationalPoints G) :
    (h.conjugationLiftIso g).hom ≫ π ≫ d = (π ≫ d) ≫ (G.innerIso g).hom := by
  calc
    (h.conjugationLiftIso g).hom ≫ π ≫ d =
        ((h.conjugationLiftIso g).hom ≫ π) ≫ d := (Category.assoc _ _ _).symm
    _ = (π ≫ (h.isDerivedSubgroup.conjugationIso g).hom) ≫ d := by
      rw [conjugationLiftIso, IsSimplyConnectedCover.isoOver_hom_comp]
    _ = π ≫ (d ≫ (G.innerIso g).hom) := by
      rw [Category.assoc, h.isDerivedSubgroup.conjugationIso_hom_comp]
    _ = (π ≫ d) ≫ (G.innerIso g).hom := (Category.assoc _ _ _).symm

/-- The lift realizes literal ambient conjugation on actual rational points. -/
theorem IsSimplyConnectedDerivedCover.map_conjugationLiftIso
    (h : IsSimplyConnectedDerivedCover d π) (g : rationalPoints G) (c : rationalPoints C) :
    rationalPoints.map (π ≫ d) (rationalPoints.map (h.conjugationLiftIso g).hom c) =
      g * rationalPoints.map (π ≫ d) c * g⁻¹ := by
  have hc := congrArg (fun f => rationalPoints.map f c) (h.conjugationLiftIso_hom_comp g)
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, ← Category.assoc] at hc ⊢
  rw [comp_innerIso_hom, constantPoint_self] at hc
  exact hc

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

open Langlands.GroupScheme

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

namespace UnramifiedZeroDatum

variable {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  (E : UnramifiedZeroDatum F H)

/-- The join defining the unramified zero subgroup is an actual product. -/
theorem mem_zeroPoints_iff {h : rationalPoints H} :
    h ∈ E.zeroPoints ↔
      ∃ c ∈ E.simplyConnectedImage, ∃ t ∈ E.torusIwahori,
        c * rationalPoints.map E.i t = h := by
  let : E.simplyConnectedImage.Normal :=
    Building.simplyConnectedImage_normal E.isSimplyConnectedDerivedCover
  change h ∈ E.simplyConnectedImage ⊔ E.torusIwahori.map (rationalPoints.map E.i) ↔ _
  rw [Subgroup.mem_sup_of_normal_left]
  constructor
  · rintro ⟨c, hc, _, ⟨t, ht, rfl⟩, heq⟩
    exact ⟨c, hc, t, ht, heq⟩
  · rintro ⟨c, hc, t, ht, heq⟩
    exact ⟨c, hc, _, ⟨t, ht, rfl⟩, heq⟩

end UnramifiedZeroDatum

namespace ZeroSubgroupDatum

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} (E : ZeroSubgroupDatum i j)

/-- The join defining the base-field zero subgroup is an actual product. -/
theorem mem_zeroSubgroup_iff {g : rationalPoints G} :
    g ∈ E.zeroSubgroup ↔
      ∃ c ∈ E.simplyConnectedImage, ∃ z ∈ E.centralizerZero,
        c * rationalPoints.map j z = g := by
  let : E.simplyConnectedImage.Normal :=
    Building.simplyConnectedImage_normal E.isSimplyConnectedDerivedCover
  change g ∈ E.simplyConnectedImage ⊔ E.centralizerZero.map (rationalPoints.map j) ↔ _
  rw [Subgroup.mem_sup_of_normal_left]
  constructor
  · rintro ⟨c, hc, _, ⟨z, hz, rfl⟩, heq⟩
    exact ⟨c, hc, z, hz, heq⟩
  · rintro ⟨c, hc, z, hz, heq⟩
    exact ⟨c, hc, _, ⟨z, hz, rfl⟩, heq⟩

/-- Multiplication of the actual cover-image and centralizer-zero factors. -/
def zeroSubgroupProductMap :
    E.simplyConnectedImage × E.centralizerZero → E.zeroSubgroup :=
  fun cz => ⟨cz.1 * rationalPoints.map j cz.2,
    E.zeroSubgroup.mul_mem
      (E.simplyConnectedImage_le_zeroSubgroup cz.1.property)
      (E.map_centralizerZero_le_zeroSubgroup ⟨cz.2, cz.2.property, rfl⟩)⟩

@[simp] theorem zeroSubgroupProductMap_coe (c : E.simplyConnectedImage) (z : E.centralizerZero) :
    (E.zeroSubgroupProductMap (c, z) : rationalPoints G) =
      c * rationalPoints.map j z := rfl

/-- The actual multiplication map onto the zero subgroup is surjective. -/
theorem zeroSubgroupProductMap_surjective : Function.Surjective E.zeroSubgroupProductMap := by
  intro g
  obtain ⟨c, hc, z, hz, heq⟩ := E.mem_zeroSubgroup_iff.mp g.property
  exact ⟨(⟨c, hc⟩, ⟨z, hz⟩), Subtype.ext heq⟩

end ZeroSubgroupDatum

end Local

end Langlands.Geometry.Building
