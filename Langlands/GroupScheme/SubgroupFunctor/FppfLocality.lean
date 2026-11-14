import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Fppf locality of represented subgroup membership -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- A member of an fppf cover of a relative test scheme, regarded over the
original base. -/
abbrev fppfCoverObj {U : Over S}
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage U.left) (k : 𝒰.I₀) : Over S :=
  Over.mk (𝒰.f k ≫ U.hom)

/-- The map from a member of an fppf cover into the relative test scheme. -/
def fppfCoverMap {U : Over S}
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage U.left) (k : 𝒰.I₀) :
    fppfCoverObj 𝒰 k ⟶ U :=
  Over.homMk (𝒰.f k) rfl

/-- Membership in the range of a monomorphic homomorphism is local on
arbitrary fppf covering families of test schemes. -/
theorem mem_range_iff_fppfCover (i : H ⟶ G) [Mono i.hom.hom]
    {U : Over S} (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage U.left)
    (x : U ⟶ G.X) :
    x ∈ (range i).carrier U ↔
      ∀ k : 𝒰.I₀, fppfCoverMap 𝒰 k ≫ x ∈ (range i).carrier (fppfCoverObj 𝒰 k) := by
  constructor
  · intro hx k
    exact (range i).comp_mem (fppfCoverMap 𝒰 k) hx
  · intro hx
    let : EffectiveEpiFamily 𝒰.X 𝒰.f := by
      rw [← Sieve.effectiveEpimorphic_family,
        Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
      intro Y
      exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := Scheme.fppfTopology) _).isSheafFor _
          (Precoverage.generate_mem_toGrothendieck 𝒰.mem₀)
    choose y hy using fun k => mem_range.mp (hx k)
    have hy' (k : 𝒰.I₀) :
        (y k).left ≫ i.hom.hom.left = 𝒰.f k ≫ x.left :=
      congrArg (fun f => f.left) (hy k)
    have hc : ∀ {W : Scheme.{u}} (k l : 𝒰.I₀)
        (a : W ⟶ 𝒰.X k) (b : W ⟶ 𝒰.X l),
        a ≫ 𝒰.f k = b ≫ 𝒰.f l → a ≫ (y k).left = b ≫ (y l).left := by
      intro W k l a b hab
      apply (cancel_mono i.hom.hom.left).mp
      simpa only [Category.assoc, hy'] using congrArg (fun f => f ≫ x.left) hab
    let d := EffectiveEpiFamily.desc 𝒰.X 𝒰.f (fun k => (y k).left) hc
    have hd (k : 𝒰.I₀) : 𝒰.f k ≫ d = (y k).left :=
      EffectiveEpiFamily.fac _ _ _ _ k
    have hw : d ≫ H.X.hom = U.hom := by
      apply EffectiveEpiFamily.hom_ext 𝒰.X 𝒰.f
      intro k
      rw [← Category.assoc, hd]
      exact Over.w (y k)
    refine mem_range.mpr ⟨Over.homMk d hw, ?_⟩
    apply Over.OverMorphism.ext
    apply EffectiveEpiFamily.hom_ext 𝒰.X 𝒰.f
    intro k
    change 𝒰.f k ≫ (d ≫ i.hom.hom.left) = 𝒰.f k ≫ x.left
    rw [← Category.assoc, hd, hy']

/-- Containment in a monomorphically represented subgroup is fppf local
on the base, without finiteness restrictions on the covering family. -/
theorem le_range_iff_baseChange_fppfCover
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
    {F : SubgroupFunctor G} (i : H ⟶ G) [Mono i.hom.hom] :
    F ≤ range i ↔
      ∀ k : 𝒰.I₀, F.baseChange (𝒰.f k) ≤ (range i).baseChange (𝒰.f k) := by
  constructor
  · intro h k U x hx
    exact h _ hx
  · intro h U x hx
    apply (mem_range_iff_fppfCover i (𝒰.pullback₁ U.hom) x).mpr
    intro k
    let V : Over (𝒰.X k) := Over.mk (pullback.snd U.hom (𝒰.f k))
    let q : (Over.map (𝒰.f k)).obj V ⟶ U :=
      Over.homMk (pullback.fst U.hom (𝒰.f k)) pullback.condition
    let x' := (baseChangePointsEquiv (𝒰.f k) G V).symm (q ≫ x)
    have hx' : x' ∈ (F.baseChange (𝒰.f k)).carrier V := by
      rw [mem_baseChange]
      change baseChangePointsEquiv (𝒰.f k) G V
        ((baseChangePointsEquiv (𝒰.f k) G V).symm (q ≫ x)) ∈ F.carrier _
      rw [MulEquiv.apply_symm_apply]
      exact F.comp_mem q hx
    have hi := h k V hx'
    rw [mem_baseChange] at hi
    have hi' : q ≫ x ∈ (range i).carrier ((Over.map (𝒰.f k)).obj V) := by
      simpa only [x', MulEquiv.apply_symm_apply] using hi
    let r : fppfCoverObj (𝒰.pullback₁ U.hom) k ⟶ (Over.map (𝒰.f k)).obj V :=
      Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ (pullback.snd U.hom (𝒰.f k) ≫ 𝒰.f k) =
          pullback.fst U.hom (𝒰.f k) ≫ U.hom
        simpa only [Category.id_comp] using
          (pullback.condition (f := U.hom) (g := 𝒰.f k)).symm)
    have hr : r ≫ q = fppfCoverMap (𝒰.pullback₁ U.hom) k := by
      apply Over.OverMorphism.ext
      exact Category.id_comp _
    simpa only [← Category.assoc, hr] using (range i).comp_mem r hi'

end Langlands.GroupScheme.SubgroupFunctor
