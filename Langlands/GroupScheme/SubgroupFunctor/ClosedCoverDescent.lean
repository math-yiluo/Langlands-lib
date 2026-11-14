import Langlands.GroupScheme.SubgroupFunctor.ClosedZariskiDescent
import Langlands.AlgebraicGeometry.Descent.FppfClosedLocusDescentProof
import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # Closed subgroup descent along covering families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Absolute membership in a subgroup, as a sieve on the ambient scheme. -/
def membershipSieve (F : SubgroupFunctor G) : Sieve G.X.left where
  arrows _ x := F.schemeCondition x
  downward_closed hx a := F.schemeCondition_comp _ a hx

/-- A closed representative of a sieve pulls back to a closed representative. -/
theorem exists_closedRepresentative_pullback {Y Z Y' : Scheme.{u}}
    (E : Sieve Y) (j : Z ⟶ Y) [IsClosedImmersion j]
    (hj : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y),
      (∃ a : T ⟶ Z, a ≫ j = g) ↔ E g) (f : Y' ⟶ Y) :
    ∃ (W : Scheme.{u}) (k : W ⟶ Y'), IsClosedImmersion k ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y'),
        (∃ a : T ⟶ W, a ≫ k = g) ↔ E (g ≫ f) := by
  refine ⟨pullback j f, pullback.snd j f, inferInstance, fun T g => ?_⟩
  rw [← hj (g ≫ f)]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a ≫ pullback.fst j f, by
      rw [Category.assoc, pullback.condition, ← Category.assoc]⟩
  · rintro ⟨a, ha⟩
    exact ⟨pullback.lift a g ha, pullback.lift_snd _ _ _⟩

/-- The published fppf closed-locus descent theorem in covering-family form. -/
theorem exists_closedRepresentative_of_cover {Y : Scheme.{u}}
    {K : Precoverage Scheme.{u}} (𝒱 : Scheme.Cover.{u} K Y)
    (E : Sieve Y) (hE : Scheme.fppfTopology.IsClosed E)
    (hcover : Sieve.generate 𝒱.presieve₀ ∈ Scheme.fppfTopology Y)
    (h : ∀ i, ∃ (Z : Scheme.{u}) (j : Z ⟶ 𝒱.X i), IsClosedImmersion j ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ 𝒱.X i),
        (∃ a : T ⟶ Z, a ≫ j = g) ↔ E (g ≫ 𝒱.f i)) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ Y), IsClosedImmersion j ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y),
        (∃ a : T ⟶ Z, a ≫ j = g) ↔ E g := by
  apply Langlands.AlgebraicGeometry.fppfClosedLocusDescent Y E hE
  refine ⟨Sieve.generate 𝒱.presieve₀, hcover, ?_⟩
  rintro Y' f ⟨_, m, _, ⟨i⟩, hm⟩
  obtain ⟨Z, j, hj, hfac⟩ := h i
  let : IsClosedImmersion j := hj
  obtain ⟨W, k, hk, hW⟩ := exists_closedRepresentative_pullback
    (E.pullback (𝒱.f i)) j hfac m
  refine ⟨W, k, hk, fun T g => ?_⟩
  rw [hW g]
  change E ((g ≫ m) ≫ 𝒱.f i) ↔ E (g ≫ f)
  rw [Category.assoc, hm]

namespace CoverDescent

variable {K : Precoverage Scheme.{u}} (𝒰 : Scheme.Cover.{u} K S)
    (F : ∀ i, SubgroupFunctor ((GroupScheme.baseChange (𝒰.f i)).obj G))

/-- All-test compatibility for subgroups over an arbitrary covering family. -/
def IsMatching : Prop :=
  ∀ (i j : 𝒰.I₀) (V : Over (𝒰.X i)) (W : Over (𝒰.X j))
    (a : (Over.map (𝒰.f i)).obj V ⟶ (Over.map (𝒰.f j)).obj W)
    (x : W ⟶ ((GroupScheme.baseChange (𝒰.f j)).obj G).X),
    x ∈ (F j).carrier W →
      (baseChangePointsEquiv (𝒰.f i) G V).symm
        (a ≫ baseChangePointsEquiv (𝒰.f j) G W x) ∈ (F i).carrier V

/-- The global subgroup consists of the points satisfying every local subgroup
condition after every relative restriction to a cover member. -/
def subgroup : SubgroupFunctor G where
  carrier T :=
    { carrier := {x | ∀ (i : 𝒰.I₀) (V : Over (𝒰.X i))
          (a : (Over.map (𝒰.f i)).obj V ⟶ T),
        (baseChangePointsEquiv (𝒰.f i) G V).symm (a ≫ x) ∈ (F i).carrier V}
      one_mem' := by
        intro i V a
        simpa only [MonObj.comp_one, map_one] using (F i).carrier V |>.one_mem
      mul_mem' := by
        intro x y hx hy i V a
        simpa only [MonObj.comp_mul, map_mul] using
          (F i).carrier V |>.mul_mem (hx i V a) (hy i V a)
      inv_mem' := by
        intro x hx i V a
        simpa only [GrpObj.comp_inv, map_inv] using
          (F i).carrier V |>.inv_mem (hx i V a) }
  comp_mem a x hx := by
    intro i V b
    simpa only [Category.assoc] using hx i V (b ≫ a)

/-- A matching family is recovered on every member of the cover. -/
theorem baseChange_subgroup (hF : IsMatching 𝒰 F) (i : 𝒰.I₀) :
    (subgroup 𝒰 F).baseChange (𝒰.f i) = F i := by
  ext V x
  change (∀ (j : 𝒰.I₀) (W : Over (𝒰.X j))
      (a : (Over.map (𝒰.f j)).obj W ⟶ (Over.map (𝒰.f i)).obj V),
    (baseChangePointsEquiv (𝒰.f j) G W).symm
      (a ≫ baseChangePointsEquiv (𝒰.f i) G V x) ∈ (F j).carrier W) ↔ _
  constructor
  · intro hx
    simpa only [Category.id_comp, MulEquiv.symm_apply_apply] using hx i V (𝟙 _)
  · intro hx j W a
    exact hF j i W V a x hx

/-- The absolute membership sieve of the global condition is fppf closed if
each local subgroup is represented by a closed subgroup scheme. -/
theorem isClosed_membershipSieve_subgroup
    (hc : ∀ i, (F i).IsClosedRepresentable) :
    Scheme.fppfTopology.IsClosed (subgroup 𝒰 F).membershipSieve := by
  intro Y x hx
  let T : Over S := Over.mk (x ≫ G.X.hom)
  let p : T ⟶ G.X := Over.homMk x rfl
  change p ∈ (subgroup 𝒰 F).carrier T
  intro i V a
  let y := (baseChangePointsEquiv (𝒰.f i) G V).symm (a ≫ p)
  obtain ⟨L, j, hj, hclosed⟩ := hc i
  let : IsClosedImmersion j.hom.hom.left := hclosed
  apply ((F i).schemeCondition_iff_mem y).mp
  apply ((F i).schemeCondition_iff_exists_of_isRepresentedBy hj y.left).mpr
  apply Langlands.AlgebraicGeometry.FppfClosedLocusDescent.exists_lift_of_covering
    Scheme.fppfTopology j.hom.hom.left y.left
    (((subgroup 𝒰 F).membershipSieve.pullback x).pullback a.left)
    (Scheme.fppfTopology.pullback_stable a.left hx)
  intro Z u hu
  let W : Over (𝒰.X i) := Over.mk (u ≫ V.hom)
  let v : W ⟶ V := Over.homMk u rfl
  let q : (Over.map (𝒰.f i)).obj W ⟶ G.X :=
    (Over.map (𝒰.f i)).map v ≫ a ≫ p
  have hq : q ∈ (subgroup 𝒰 F).carrier ((Over.map (𝒰.f i)).obj W) := by
    apply ((subgroup 𝒰 F).schemeCondition_iff_mem q).mp
    change (subgroup 𝒰 F).schemeCondition (u ≫ a.left ≫ x)
    exact hu
  have hlocal := hq i W (𝟙 _)
  have hy : (baseChangePointsEquiv (𝒰.f i) G W).symm q = v ≫ y := by
    apply (baseChangePointsEquiv (𝒰.f i) G W).injective
    simp only [MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality, y]
    rfl
  have hmem : v ≫ y ∈ (F i).carrier W := by
    simpa only [Category.id_comp, ← hy] using hlocal
  exact ((F i).schemeCondition_iff_exists_of_isRepresentedBy hj
    (v ≫ y).left).mp (((F i).schemeCondition_iff_mem (v ≫ y)).mpr hmem)

variable {𝒰 F}

/-- Matching closed subgroups over an fppf covering family have a global
closed representative on the original arbitrary base. -/
theorem isClosedRepresentable_subgroup_fppf
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (F : ∀ i, SubgroupFunctor ((GroupScheme.baseChange (𝒰.f i)).obj G))
    (hF : IsMatching 𝒰 F) (hc : ∀ i, (F i).IsClosedRepresentable) :
    (subgroup 𝒰 F).IsClosedRepresentable := by
  let 𝒱 := 𝒰.pullback₁ G.X.hom
  obtain ⟨Z, j, hj, hfac⟩ := exists_closedRepresentative_of_cover 𝒱
    (subgroup 𝒰 F).membershipSieve (isClosed_membershipSieve_subgroup 𝒰 F hc)
    (Precoverage.generate_mem_toGrothendieck 𝒱.mem₀) (fun i => by
      obtain ⟨L, k, hk, hclosed⟩ := hc i
      refine ⟨L.X.left, k.hom.hom.left, hclosed, fun T a => ?_⟩
      change _ ↔ (subgroup 𝒰 F).schemeCondition (a ≫ pullback.fst G.X.hom (𝒰.f i))
      rw [schemeCondition_baseChange_iff, baseChange_subgroup 𝒰 F hF i]
      exact ((F i).schemeCondition_iff_exists_of_isRepresentedBy hk a).symm)
  let : IsClosedImmersion j := hj
  exact (subgroup 𝒰 F).isClosedRepresentable_of_schemeCondition j
    (fun T g => (hfac g).symm)

/-- The actual global closed subgroup descended from an fppf matching family. -/
def closedRepresentativeFppf
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (F : ∀ i, SubgroupFunctor ((GroupScheme.baseChange (𝒰.f i)).obj G))
    (hF : IsMatching 𝒰 F) (hc : ∀ i, (F i).IsClosedRepresentable) :
    ClosedRepresentative (subgroup 𝒰 F) :=
  ClosedRepresentative.ofIsClosedRepresentable
    (isClosedRepresentable_subgroup_fppf 𝒰 F hF hc)

/-- Effective closed subgroup descent for an étale matching family. -/
theorem isClosedRepresentable_subgroup_etale
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (F : ∀ i, SubgroupFunctor ((GroupScheme.baseChange (𝒰.f i)).obj G))
    (hF : IsMatching 𝒰 F) (hc : ∀ i, (F i).IsClosedRepresentable) :
    (subgroup 𝒰 F).IsClosedRepresentable := by
  let 𝒰' : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun i => ⟨inferInstance, inferInstance⟩)
  exact isClosedRepresentable_subgroup_fppf 𝒰' F hF hc

/-- The actual global closed subgroup descended from an étale matching family. -/
def closedRepresentativeEtale
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (F : ∀ i, SubgroupFunctor ((GroupScheme.baseChange (𝒰.f i)).obj G))
    (hF : IsMatching 𝒰 F) (hc : ∀ i, (F i).IsClosedRepresentable) :
    ClosedRepresentative (subgroup 𝒰 F) :=
  ClosedRepresentative.ofIsClosedRepresentable
    (isClosedRepresentable_subgroup_etale 𝒰 F hF hc)

end CoverDescent

end Langlands.GroupScheme.SubgroupFunctor
