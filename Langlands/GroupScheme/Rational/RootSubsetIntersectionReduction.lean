import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Geometric points and the minimality inclusion for root-subset intersections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of k))}

/-- Intersection equality tested on every algebraically closed geometric point over the base. -/
def HasGeometricPointIntersection (h₁ : H₁ ⟶ G) (h₂ : H₂ ⟶ G) (h₃ : H₃ ⟶ G) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (g : Over.mk b ⟶ G.X),
    (g ∈ (SubgroupFunctor.range h₁).carrier (Over.mk b) ∧
      g ∈ (SubgroupFunctor.range h₂).carrier (Over.mk b) ↔
      g ∈ (SubgroupFunctor.range h₃).carrier (Over.mk b))

namespace SubgroupFunctor

/-- Membership in a closed subgroup from a reduced test scheme is detected by
all algebraically closed points of the test scheme. No finite-type hypothesis is needed. -/
theorem mem_range_iff_geometricPoints {j : H ⟶ G} (hj : IsClosedSubgroup j)
    {U : Over (Spec (CommRingCat.of k))} [IsReduced U.left] (g : U ⟶ G.X) :
    g ∈ (range j).carrier U ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
        (a : Over.mk b ⟶ U), a ≫ g ∈ (range j).carrier (Over.mk b) := by
  constructor
  · intro hg K _ _ b a
    exact (range j).comp_mem a hg
  · intro h
    let f := g.left
    let q := j.hom.hom.left
    have : IsClosedImmersion q := hj
    let p := pullback.fst f q
    have hp : Set.range p = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      rw [Scheme.Pullback.range_fst]
      let K := AlgebraicClosure (U.left.residueField x)
      let a := geometricPoint U.left x
      let V := Over.mk (a ≫ U.hom)
      let a' : V ⟶ U := Over.homMk a
      obtain ⟨y, hy⟩ := mem_range.mp (h K (a ≫ U.hom) a')
      refine ⟨y.left (IsLocalRing.closedPoint K), ?_⟩
      have he := congrArg (fun r : V ⟶ G.X => r.left (IsLocalRing.closedPoint K)) hy
      change q (y.left (IsLocalRing.closedPoint K)) = f (a (IsLocalRing.closedPoint K)) at he
      have ha : a (IsLocalRing.closedPoint K) = x := by
        change U.left.fromSpecResidueField x
          ((toAlgebraicClosure (U.left.residueField x)) (IsLocalRing.closedPoint K)) = x
        exact Scheme.fromSpecResidueField_apply _ _
      exact he.trans (congrArg f ha)
    have : Surjective p := ⟨Set.range_eq_univ.mp hp⟩
    have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
    let l := inv p ≫ pullback.snd f q
    have hl : l ≫ q = f := by
      dsimp only [l, p]
      rw [Category.assoc, ← pullback.condition, ← Category.assoc,
        IsIso.inv_hom_id, Category.id_comp]
    let l' : U ⟶ H.X := Over.homMk l (by
      rw [← Over.w j.hom.hom, ← Category.assoc, hl]
      exact Over.w g)
    exact mem_range.mpr ⟨l', by
      apply Over.OverMorphism.ext
      exact hl⟩

end SubgroupFunctor

/-- For three closed subgroups, equality on reduced test schemes is equivalent
to equality on algebraically closed geometric points. -/
theorem hasReducedPointIntersection_iff_geometricPoints
    {h₁ : H₁ ⟶ G} {h₂ : H₂ ⟶ G} {h₃ : H₃ ⟶ G}
    (hc₁ : IsClosedSubgroup h₁) (hc₂ : IsClosedSubgroup h₂)
    (hc₃ : IsClosedSubgroup h₃) :
    HasReducedPointIntersection h₁ h₂ h₃ ↔ HasGeometricPointIntersection h₁ h₂ h₃ := by
  constructor
  · intro h K _ _ b g
    exact h (Over.mk b)
      (inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))) g
  · intro h U hU g
    let _ := hU
    constructor
    · rintro ⟨h₁g, h₂g⟩
      apply (SubgroupFunctor.mem_range_iff_geometricPoints hc₃ g).mpr
      intro K _ _ b a
      exact (h K b (a ≫ g)).mp
        ⟨(SubgroupFunctor.range h₁).comp_mem a h₁g,
          (SubgroupFunctor.range h₂).comp_mem a h₂g⟩
    · intro h₃g
      constructor
      · apply (SubgroupFunctor.mem_range_iff_geometricPoints hc₁ g).mpr
        intro K _ _ b a
        exact ((h K b (a ≫ g)).mpr ((SubgroupFunctor.range h₃).comp_mem a h₃g)).1
      · apply (SubgroupFunctor.mem_range_iff_geometricPoints hc₂ g).mpr
        intro K _ _ b a
        exact ((h K b (a ≫ g)).mpr ((SubgroupFunctor.range h₃).comp_mem a h₃g)).2

variable {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
  {S X : Set (characterLattice T)}

/-- Minimal closed root-subset groups are monotone in their sets of generators. -/
theorem IsRootSubsetGroup.range_le_of_subset {h : H ⟶ G} {h' : H₁ ⟶ G}
    (hh : IsRootSubsetGroup i S h) (hh' : IsRootSubsetGroup i X h') (hSX : S ⊆ X) :
    SubgroupFunctor.range h ≤ SubgroupFunctor.range h' :=
  hh.2.2.2 H₁ h' hh'.1 hh'.2.1 (fun γ hγ => hh'.2.2.1 γ (hSX hγ))

/-- The generated group of the overlap lies in both generated groups on all test schemes. -/
theorem IsRootSubsetGroup.range_inter_le {h₁ : H₁ ⟶ G} {h₂ : H₂ ⟶ G} {h₃ : H₃ ⟶ G}
    (hh₁ : IsRootSubsetGroup i S h₁) (hh₂ : IsRootSubsetGroup i X h₂)
    (hh₃ : IsRootSubsetGroup i (S ∩ X) h₃) :
    SubgroupFunctor.range h₃ ≤ SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂ := by
  intro U g hg
  exact ⟨hh₃.range_le_of_subset hh₁ Set.inter_subset_left U hg,
    hh₃.range_le_of_subset hh₂ Set.inter_subset_right U hg⟩

end Langlands.GroupScheme
