import Langlands.GroupScheme.RelativeLevi.ConjugacyReduction
import Langlands.GroupScheme.SubgroupFunctor.EtaleLocality

/-! # Etale descent of uniquely determined radical conjugators -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {P L L' U : GroupScheme S}

/-- A point of a specified subgroup is a conjugator when its image conjugates
the two ranges after every further restriction. -/
def IsRadicalConjugator (l : L ⟶ P) (l' : L' ⟶ P) (r : U ⟶ P)
    {T : Over S} (n : T ⟶ U.X) : Prop :=
  IsRangeConjugator l l' (n ≫ r.hom.hom)

/-- Restriction preserves radical conjugators. -/
theorem IsRadicalConjugator.comp {l : L ⟶ P} {l' : L' ⟶ P} {r : U ⟶ P}
    {T V : Over S} {n : T ⟶ U.X} (hn : IsRadicalConjugator l l' r n)
    (a : V ⟶ T) : IsRadicalConjugator l l' r (a ≫ n) := by
  simpa only [IsRadicalConjugator, Category.assoc] using IsRangeConjugator.comp hn a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An all-test range conjugator can be checked on an arbitrary etale cover
of its domain. -/
theorem isRangeConjugator_iff_etaleCover (l : L ⟶ P) (l' : L' ⟶ P)
    [Mono l.hom.hom] [Mono l'.hom.hom] {T : Over S}
    (𝒰 : T.left.Cover.{v} (Scheme.precoverage @Etale)) (g : T ⟶ P.X) :
    IsRangeConjugator l l' g ↔ ∀ k,
      IsRangeConjugator l l' (SubgroupFunctor.etaleCoverMap 𝒰 k ≫ g) := by
  let : Scheme.IsJointlySurjectivePreserving (@Etale.{u}) :=
    Scheme.isJointlySurjectivePreserving _
  constructor
  · intro hg k
    exact hg.comp _
  · intro hg V a x
    let 𝒱 := 𝒰.pullback₁ a.left
    have hk (k : 𝒰.I₀) :
        SubgroupFunctor.etaleCoverMap 𝒱 k ≫ x ∈
          (SubgroupFunctor.range l').carrier (SubgroupFunctor.etaleCoverObj 𝒱 k) ↔
        SubgroupFunctor.etaleCoverMap 𝒱 k ≫ ((a ≫ g)⁻¹ * x * (a ≫ g)) ∈
          (SubgroupFunctor.range l).carrier (SubgroupFunctor.etaleCoverObj 𝒱 k) := by
      let q : SubgroupFunctor.etaleCoverObj 𝒱 k ⟶
          SubgroupFunctor.etaleCoverObj 𝒰 k :=
        Over.homMk (pullback.snd a.left (𝒰.f k)) (by
          change pullback.snd a.left (𝒰.f k) ≫ (𝒰.f k ≫ T.hom) =
            pullback.fst a.left (𝒰.f k) ≫ V.hom
          rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w a])
      have hq : q ≫ SubgroupFunctor.etaleCoverMap 𝒰 k =
          SubgroupFunctor.etaleCoverMap 𝒱 k ≫ a := by
        apply Over.OverMorphism.ext
        exact pullback.condition.symm
      have hc := hg k _ q (SubgroupFunctor.etaleCoverMap 𝒱 k ≫ x)
      have hm :
          SubgroupFunctor.etaleCoverMap 𝒱 k ≫ ((a ≫ g)⁻¹ * x * (a ≫ g)) =
            ((q ≫ SubgroupFunctor.etaleCoverMap 𝒰 k) ≫ g)⁻¹ *
              (SubgroupFunctor.etaleCoverMap 𝒱 k ≫ x) *
              ((q ≫ SubgroupFunctor.etaleCoverMap 𝒰 k) ≫ g) := by
        rw [hq]
        change ((P.points.map (SubgroupFunctor.etaleCoverMap 𝒱 k).op).hom) _ = _
        simp only [map_mul, map_inv, Category.assoc]
        rfl
      simpa only [Category.assoc, hm] using hc
    rw [SubgroupFunctor.mem_range_iff_etaleCover l' 𝒱 x,
      SubgroupFunctor.mem_range_iff_etaleCover l 𝒱 ((a ≫ g)⁻¹ * x * (a ≫ g))]
    exact forall_congr' hk

/-- The same locality statement for points of the specified subgroup. -/
theorem isRadicalConjugator_iff_etaleCover (l : L ⟶ P) (l' : L' ⟶ P) (r : U ⟶ P)
    [Mono l.hom.hom] [Mono l'.hom.hom] {T : Over S}
    (𝒰 : T.left.Cover.{v} (Scheme.precoverage @Etale)) (n : T ⟶ U.X) :
    IsRadicalConjugator l l' r n ↔ ∀ k,
      IsRadicalConjugator l l' r (SubgroupFunctor.etaleCoverMap 𝒰 k ≫ n) := by
  simpa only [IsRadicalConjugator, Category.assoc] using
    isRangeConjugator_iff_etaleCover l l' 𝒰 (n ≫ r.hom.hom)

/-- Locally existing conjugators glue to a unique point when uniqueness is
known after every test-scheme restriction. -/
theorem existsUnique_isRadicalConjugator_of_etaleCover
    (l : L ⟶ P) (l' : L' ⟶ P) (r : U ⟶ P)
    [Mono l.hom.hom] [Mono l'.hom.hom]
    (huniq : ∀ (V : Over S) (a b : V ⟶ U.X),
      IsRadicalConjugator l l' r a → IsRadicalConjugator l l' r b → a = b)
    {T : Over S} (𝒰 : T.left.Cover.{v} (Scheme.precoverage @Etale))
    (hex : ∀ k, ∃ n : SubgroupFunctor.etaleCoverObj 𝒰 k ⟶ U.X,
      IsRadicalConjugator l l' r n) :
    ∃! n : T ⟶ U.X, IsRadicalConjugator l l' r n := by
  let : EffectiveEpiFamily 𝒰.X 𝒰.f := SubgroupFunctor.effectiveEpiFamily_etaleCover 𝒰
  choose n hn using hex
  have hc {Z : Scheme.{u}} (k j : 𝒰.I₀) (a : Z ⟶ 𝒰.X k) (b : Z ⟶ 𝒰.X j)
      (hab : a ≫ 𝒰.f k = b ≫ 𝒰.f j) :
      a ≫ (n k).left = b ≫ (n j).left := by
    let V : Over S := Over.mk (a ≫ (𝒰.f k ≫ T.hom))
    let ak : V ⟶ SubgroupFunctor.etaleCoverObj 𝒰 k := Over.homMk a rfl
    let bj : V ⟶ SubgroupFunctor.etaleCoverObj 𝒰 j := Over.homMk b (by
      change b ≫ (𝒰.f j ≫ T.hom) = a ≫ (𝒰.f k ≫ T.hom)
      simpa only [← Category.assoc] using congrArg (fun f => f ≫ T.hom) hab.symm)
    exact congrArg (fun f => f.left)
      (huniq V (ak ≫ n k) (bj ≫ n j) ((hn k).comp ak) ((hn j).comp bj))
  let d := EffectiveEpiFamily.desc 𝒰.X 𝒰.f (fun k => (n k).left) hc
  have hd (k : 𝒰.I₀) : 𝒰.f k ≫ d = (n k).left :=
    EffectiveEpiFamily.fac 𝒰.X 𝒰.f _ hc k
  have hw : d ≫ U.X.hom = T.hom := by
    apply EffectiveEpiFamily.hom_ext 𝒰.X 𝒰.f
    intro k
    rw [← Category.assoc, hd]
    exact Over.w (n k)
  let z : T ⟶ U.X := Over.homMk d hw
  have hz (k : 𝒰.I₀) : SubgroupFunctor.etaleCoverMap 𝒰 k ≫ z = n k := by
    apply Over.OverMorphism.ext
    exact hd k
  have hconj : IsRadicalConjugator l l' r z := by
    apply (isRadicalConjugator_iff_etaleCover l l' r 𝒰 z).mpr
    intro k
    rw [hz]
    exact hn k
  exact ⟨z, hconj, fun m hm => huniq T m z hm hconj⟩

end Langlands.GroupScheme.RelativeLevi
