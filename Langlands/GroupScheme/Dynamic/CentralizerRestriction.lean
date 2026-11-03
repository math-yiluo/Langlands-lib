import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.SubgroupIntersection

/-! # Restriction of dynamic centralizers to closed subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H M : GroupScheme S}

namespace Dynamic

/-- Restrict a cocharacter to a monic subgroup containing its full functorial range. -/
def restrictCocharacter (b : H ⟶ G) [Mono b.hom.hom]
    (χ : (Gm S).toGrp ⟶ G) (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b) :
    (Gm S).toGrp ⟶ H :=
  (show (SubgroupFunctor.range b).IsRepresentedBy b from ⟨inferInstance, rfl⟩).factorHom χ hχ

theorem restrictCocharacter_comp (b : H ⟶ G) [Mono b.hom.hom]
    (χ : (Gm S).toGrp ⟶ G) (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b) :
    restrictCocharacter b χ hχ ≫ b = χ :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- A monomorphism preserves and reflects centralization of a cocharacter on every test. -/
theorem mem_centralizer_comp_iff (b : H ⟶ G) [Mono b.hom.hom]
    (χ : (Gm S).toGrp ⟶ H) {T : Over S} (g : T ⟶ H.X) :
    g ≫ b.hom.hom ∈ (centralizer (χ ≫ b)).carrier T ↔
      g ∈ (centralizer χ).carrier T := by
  rw [← torusCentralizer_gm_eq_dynamicCentralizer,
    ← torusCentralizer_gm_eq_dynamicCentralizer, mem_torusCentralizer,
    mem_torusCentralizer]
  constructor
  · intro hg V a t
    apply (commute_iff_eq _ _).mpr
    apply (cancel_mono b.hom.hom).mp
    simpa only [MonObj.mul_comp, Category.assoc, Grp.comp_hom_hom] using (hg V a t).eq
  · intro hg V a t
    apply (commute_iff_eq _ _).mpr
    simpa only [MonObj.mul_comp, Category.assoc, Grp.comp_hom_hom] using
      congrArg (fun x : V ⟶ H.X => x ≫ b.hom.hom) (hg V a t).eq

/-- The projection of an actual closed intersection to either factor is closed. -/
theorem isClosedSubgroup_intersectionSnd (j : M ⟶ G) (b : H ⟶ G)
    (hj : IsClosedSubgroup j) : IsClosedSubgroup (subgroupIntersectionSnd j b) := by
  have : IsClosedImmersion j.hom.hom.left := hj
  change IsClosedImmersion (subgroupIntersectionSnd j b).hom.hom.left
  exact MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme j b) hj

/-- Intersecting an ambient centralizer with a closed subgroup gives the internal centralizer
of the same cocharacter, as an equality on all test schemes. -/
theorem range_intersectionSnd_eq_centralizer (b : H ⟶ G) [Mono b.hom.hom]
    (χ : (Gm S).toGrp ⟶ H) (j : M ⟶ G)
    (hj : (centralizer (χ ≫ b)).IsRepresentedBy j) :
    SubgroupFunctor.range (subgroupIntersectionSnd j b) = centralizer χ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  change (∃ x : T ⟶ (subgroupIntersection j b).X,
      x ≫ (subgroupIntersectionSnd j b).hom.hom = g) ↔
    g ∈ (centralizer χ).carrier T
  constructor
  · rintro ⟨x, hx⟩
    apply (mem_centralizer_comp_iff b χ g).mp
    rw [← hj.2]
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨x ≫ (subgroupIntersectionFst j b).hom.hom, ?_⟩
    calc
      (x ≫ (subgroupIntersectionFst j b).hom.hom) ≫ j.hom.hom =
          (x ≫ (subgroupIntersectionSnd j b).hom.hom) ≫ b.hom.hom := by
        simp only [Category.assoc, (subgroupIntersection_isPullback j b).w]
      _ = g ≫ b.hom.hom := by rw [hx]
  · intro hg
    have hg' := (mem_centralizer_comp_iff b χ g).mpr hg
    rw [← hj.2] at hg'
    obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hg'
    let hpb := subgroupIntersection_isPullback j b
    exact ⟨hpb.lift m g hm, hpb.lift_snd m g hm⟩

/-- The actual closed intersection represents the internal dynamic centralizer. -/
theorem isRepresentedBy_intersectionSnd (b : H ⟶ G) (hb : IsClosedSubgroup b)
    (χ : (Gm S).toGrp ⟶ H) (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hrep : (centralizer (χ ≫ b)).IsRepresentedBy j) :
    (centralizer χ).IsRepresentedBy (subgroupIntersectionSnd j b) := by
  have : IsClosedImmersion b.hom.hom.left := hb
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion (subgroupIntersectionSnd j b).hom.hom.left :=
    isClosedSubgroup_intersectionSnd j b hj
  exact ⟨Over.mono_of_mono_left _, range_intersectionSnd_eq_centralizer b χ j hrep⟩

/-- Any chosen representative of the internal centralizer has the same ambient range as the
intersection of the given subgroup and the represented ambient centralizer. -/
theorem range_internalCentralizer_comp {C : GroupScheme S}
    (b : H ⟶ G) [Mono b.hom.hom] (χ : (Gm S).toGrp ⟶ H)
    (j : M ⟶ G) (hj : (centralizer (χ ≫ b)).IsRepresentedBy j)
    (c : C ⟶ H) (hc : (centralizer χ).IsRepresentedBy c) :
    SubgroupFunctor.range (c ≫ b) =
      SubgroupFunctor.range j ⊓ SubgroupFunctor.range b := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  change (∃ y : T ⟶ C.X, y ≫ (c ≫ b).hom.hom = x) ↔
    (∃ m : T ⟶ M.X, m ≫ j.hom.hom = x) ∧
      (∃ y : T ⟶ H.X, y ≫ b.hom.hom = x)
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ≫ c.hom.hom ∈ (centralizer χ).carrier T := by
      rw [← hc.2]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    constructor
    · apply SubgroupFunctor.mem_range.mp
      rw [hj.2]
      simpa only [Grp.comp_hom_hom, ← Category.assoc] using
        (mem_centralizer_comp_iff b χ (y ≫ c.hom.hom)).mpr hy
    · exact ⟨y ≫ c.hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  · rintro ⟨hx, y, hy⟩
    have hx' : x ∈ (centralizer (χ ≫ b)).carrier T := by
      rw [← hj.2]
      exact SubgroupFunctor.mem_range.mpr hx
    rw [← hy] at hx'
    have hy' := (mem_centralizer_comp_iff b χ y).mp hx'
    rw [← hc.2] at hy'
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hy'
    refine ⟨z, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hz, hy]

end Dynamic

end Langlands.GroupScheme
