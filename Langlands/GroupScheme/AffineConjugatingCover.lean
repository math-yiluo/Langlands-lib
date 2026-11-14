import Langlands.GroupScheme.LocalSubgroupConjugacy
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality
import Langlands.GroupScheme.RelativeLevi.BorelConjugacyProof
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # Affine conjugating covers from etale conjugating covers -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G B B' : GroupScheme S}

namespace SubgroupFunctor

/-- For monomorphically represented subgroups, conjugacy of a supplied point
can be checked on an arbitrary open cover of its test scheme. -/
theorem IsConjugatingPoint.of_openCover
    (i : B ⟶ G) (j : B' ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom]
    {U : Over S} {g : U ⟶ G.X} (𝒰 : Scheme.OpenCover.{u} U.left)
    (hg : ∀ k, IsConjugatingPoint (range i) (range j) (coverMap 𝒰 k ≫ g)) :
    IsConjugatingPoint (range i) (range j) g := by
  intro V a x
  let 𝒱 := 𝒰.pullback₁ a.left
  have hloc (k : 𝒱.I₀) :
      coverMap 𝒱 k ≫ x ∈ (range i).carrier _ ↔
      coverMap 𝒱 k ≫ ((a ≫ g) * x * (a ≫ g)⁻¹) ∈ (range j).carrier _ := by
    let Z := coverObj (T := V) 𝒱 k
    let r : Z ⟶ V := coverMap 𝒱 k
    let b : Z ⟶ coverObj (T := U) 𝒰 k :=
      Over.homMk (pullback.snd a.left (𝒰.f k)) (by
        change pullback.snd a.left (𝒰.f k) ≫ (𝒰.f k ≫ U.hom) =
          pullback.fst a.left (𝒰.f k) ≫ V.hom
        rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w a])
    have hr : r ≫ a = b ≫ coverMap 𝒰 k :=
      Over.OverMorphism.ext pullback.condition
    change r ≫ x ∈ (range i).carrier Z ↔
      r ≫ ((a ≫ g) * x * (a ≫ g)⁻¹) ∈ (range j).carrier Z
    simpa only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hr] using
      hg k Z b (r ≫ x)
  rw [mem_range_iff_openCover i 𝒱 x,
    mem_range_iff_openCover j 𝒱 ((a ≫ g) * x * (a ≫ g)⁻¹)]
  exact forall_congr' hloc

end SubgroupFunctor

/-- A pair of represented subgroups admits a conjugating point on a single
affine etale surjective test scheme. -/
def HasAffineEtaleConjugatingCover (i : B ⟶ G) (j : B' ⟶ G) : Prop :=
  ∃ U : Over S, IsAffine U.left ∧ Etale U.hom ∧ Surjective U.hom ∧
    ∃ g : U ⟶ G.X,
      SubgroupFunctor.IsConjugatingPoint (SubgroupFunctor.range i) (SubgroupFunctor.range j) g

namespace AffineConjugatingCover

open SubgroupFunctor

set_option maxHeartbeats 1000000 in
/-- On a quasi-compact base, an etale cover carrying conjugators refines to a
single affine etale surjective cover carrying a conjugator. -/
theorem hasAffineEtaleConjugatingCover_of_cover [CompactSpace S]
    (i : B ⟶ G) (j : B' ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom]
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hg : ∀ k, ∃ g : Over.mk (𝒰.f k) ⟶ G.X,
      IsConjugatingPoint (range i) (range j) g) :
    HasAffineEtaleConjugatingCover i j := by
  have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap fun k => (𝒰.f k).isOpenMap
  obtain ⟨𝒱, f, hfin, _⟩ := QuasiCompactCover.exists_hom.{u,u} 𝒰
  let : Finite 𝒱.cover.I₀ := hfin
  choose g hg using hg
  let r (k : 𝒱.cover.I₀) :
      Over.mk (𝒱.cover.f k) ⟶ Over.mk (𝒰.f (f.s₀ k)) :=
    Over.homMk (f.h₀ k) (f.w₀ k)
  let v (k : 𝒱.cover.I₀) : Over.mk (𝒱.cover.f k) ⟶ G.X :=
    r k ≫ g (f.s₀ k)
  have hv (k : 𝒱.cover.I₀) : IsConjugatingPoint (range i) (range j) (v k) :=
    (hg (f.s₀ k)).restrict (r k)
  let q : (∐ 𝒱.cover.X) ⟶ S := Sigma.desc 𝒱.cover.f
  let U : Over S := Over.mk q
  let z : U ⟶ G.X := Over.homMk (Sigma.desc fun k => (v k).left) (by
    apply Sigma.hom_ext
    intro k
    change Sigma.ι 𝒱.cover.X k ≫
      (Sigma.desc (fun k => (v k).left) ≫ G.X.hom) =
      Sigma.ι 𝒱.cover.X k ≫ Sigma.desc 𝒱.cover.f
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact Over.w (v k))
  let e (k : 𝒱.cover.I₀) :
      coverObj (T := U) (sigmaOpenCover 𝒱.cover.X) k ⟶
        Over.mk (𝒱.cover.f k) :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ 𝒱.cover.f k =
        Sigma.ι 𝒱.cover.X k ≫ Sigma.desc 𝒱.cover.f
      rw [Category.id_comp, Sigma.ι_comp_desc])
  have hc (k : 𝒱.cover.I₀) :
      coverMap (sigmaOpenCover 𝒱.cover.X) k ≫ z = e k ≫ v k := by
    apply Over.OverMorphism.ext
    change Sigma.ι 𝒱.cover.X k ≫ Sigma.desc (fun k => (v k).left) =
      𝟙 _ ≫ (v k).left
    rw [Sigma.ι_comp_desc, Category.id_comp]
  have hz : IsConjugatingPoint (range i) (range j) z :=
    IsConjugatingPoint.of_openCover i j (sigmaOpenCover 𝒱.cover.X) fun k => by
      rw [hc]
      exact (hv k).restrict (e k)
  have ha : IsAffine U.left := by
    change IsAffine (∐ 𝒱.cover.X)
    have (k : 𝒱.cover.I₀) : IsAffine (𝒱.cover.X k) :=
      inferInstanceAs (IsAffine (Spec (𝒱.X k)))
    infer_instance
  have he : Etale U.hom := by
    exact 𝒱.cover.sigma.map_prop default
  have hs : Surjective U.hom := by
    constructor
    intro s
    obtain ⟨k, x, hx⟩ := 𝒱.cover.exists_eq s
    refine ⟨Sigma.ι 𝒱.cover.X k x, ?_⟩
    change (Sigma.ι 𝒱.cover.X k ≫ Sigma.desc 𝒱.cover.f) x = s
    rw [Sigma.ι_comp_desc]
    exact hx
  exact ⟨U, ha, he, hs, z, hz⟩

set_option maxHeartbeats 800000 in
/-- The same refinement starting with the actual rational range equalities
on every member of the etale cover. -/
theorem hasAffineEtaleConjugatingCover_of_range_cover [CompactSpace S]
    (i : B ⟶ G) (j : B' ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom]
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hg : ∀ k, ∃ g : Over.mk (𝟙 (𝒰.X k)) ⟶
      ((GroupScheme.baseChange (𝒰.f k)).obj G).X,
      range ((GroupScheme.baseChange (𝒰.f k)).map i ≫
        (((GroupScheme.baseChange (𝒰.f k)).obj G).innerIso g).hom) =
      range ((GroupScheme.baseChange (𝒰.f k)).map j)) :
    HasAffineEtaleConjugatingCover i j := by
  apply hasAffineEtaleConjugatingCover_of_cover i j 𝒰
  intro k
  obtain ⟨g, hg⟩ := hg k
  refine ⟨baseChangeBasePointsEquiv (𝒰.f k) G g, ?_⟩
  apply (isConjugatingPoint_baseChangeBasePointsEquiv_iff (𝒰.f k) g).mp
  rw [← range_baseChangeHom, ← range_baseChangeHom]
  exact (isConjugatingPoint_iff_range_innerIso _ _ _).mpr hg

/-- The etale-local Borel conjugacy statement supplies a single affine
conjugating cover on any quasi-compact base. -/
theorem hasAffineEtaleConjugatingCover_of_borelStatement [CompactSpace S]
    (hconj : RelativeBorelEtaleLocalConjugacyStatement.{u})
    (i : B ⟶ G) (j : B' ⟶ G)
    (hG : IsReductive G) (hi : IsRelativeBorelSubgroup i) (hj : IsRelativeBorelSubgroup j) :
    HasAffineEtaleConjugatingCover i j := by
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  let : Mono j.hom.hom := hj.isRelativeParabolicSubgroup.mono
  obtain ⟨𝒰, hg⟩ := hconj S G B B' i j hG hi hj
  exact hasAffineEtaleConjugatingCover_of_range_cover i j 𝒰 hg

/-- Relative Borel subgroups of a reductive group on a quasi-compact base
admit a single affine etale surjective conjugating cover. -/
theorem hasAffineEtaleConjugatingCover_of_borels [CompactSpace S]
    (i : B ⟶ G) (j : B' ⟶ G)
    (hG : IsReductive G) (hi : IsRelativeBorelSubgroup i) (hj : IsRelativeBorelSubgroup j) :
    HasAffineEtaleConjugatingCover i j :=
  hasAffineEtaleConjugatingCover_of_borelStatement
    relativeBorelEtaleLocalConjugacyStatement i j hG hi hj

end AffineConjugatingCover

end Langlands.GroupScheme
