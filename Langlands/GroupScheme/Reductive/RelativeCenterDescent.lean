import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.RelativeCentralizerDescent

/-! # Descent of diagonalizable scheme-theoretic centres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Centrality on all test schemes is detected on an étale cover of the base. -/
theorem center_eq_coverDescent
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S) :
    center G = SubgroupFunctor.CoverDescent.subgroup 𝒰
      (fun k => (center G).baseChange (𝒰.f k)) := by
  apply le_antisymm (SubgroupFunctor.CoverDescent.le_subgroup_baseChange 𝒰 _) ?_
  intro U x hx V a g
  let 𝒱 := 𝒰.pullback₁ V.hom
  let : EffectiveEpiFamily 𝒱.X 𝒱.f :=
    SubgroupFunctor.effectiveEpiFamily_etaleCover 𝒱
  apply Over.OverMorphism.ext
  apply EffectiveEpiFamily.hom_ext 𝒱.X 𝒱.f
  intro k
  let W : Over (𝒰.X k) := Over.mk (pullback.snd V.hom (𝒰.f k))
  let q : (Over.map (𝒰.f k)).obj W ⟶ V :=
    Over.homMk (pullback.fst V.hom (𝒰.f k)) pullback.condition
  have hm := hx k W (q ≫ a)
  rw [SubgroupFunctor.mem_baseChange, MulEquiv.apply_symm_apply] at hm
  have hc := hm _ (𝟙 _) (q ≫ g)
  simp only [Category.id_comp, Category.assoc] at hc
  have he := congrArg (fun f => f.left) hc.eq
  change (q ≫ ((a ≫ x) * g)).left = (q ≫ (g * (a ≫ x))).left
  simpa only [MonObj.comp_mul, Category.assoc] using he

/-- Closed representability of the full centre descends along an arbitrary
étale covering family. -/
theorem center_isClosedRepresentable_of_etaleCover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (h : ∀ k, (center ((GroupScheme.baseChange (𝒰.f k)).obj G)).IsClosedRepresentable) :
    (center G).IsClosedRepresentable := by
  rw [center_eq_coverDescent 𝒰]
  apply SubgroupFunctor.CoverDescent.isClosedRepresentable_subgroup_etale 𝒰 _
    (SubgroupFunctor.CoverDescent.isMatching_baseChange 𝒰 (center G))
  intro k
  rw [← center_baseChange]
  exact h k

/-- Construct the actual closed centre over the original base from local closed
diagonalizable centres. The group need not be smooth or reductive. -/
def relativeCenterModelOfEtaleCover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (h : ∀ k, ∃ (Z : GroupScheme (𝒰.X k))
      (z : Z ⟶ (GroupScheme.baseChange (𝒰.f k)).obj G),
      IsSchemeTheoreticCenter z ∧ RelativeMultiplicativeType.IsDiagonalizable Z) :
    Σ Z : GroupScheme S, {z : Z ⟶ G //
      IsSchemeTheoreticCenter z ∧ RelativeMultiplicativeType.IsMultiplicativeType Z} := by
  have hclosed : (center G).IsClosedRepresentable := by
    apply center_isClosedRepresentable_of_etaleCover 𝒰
    intro k
    obtain ⟨Z, z, hz, _⟩ := h k
    exact ⟨Z, z, hz.isRepresentedBy, hz.1⟩
  let C := SubgroupFunctor.ClosedRepresentative.ofIsClosedRepresentable hclosed
  have hz : IsSchemeTheoreticCenter C.hom := ⟨C.closed, C.represents.2⟩
  refine ⟨C.group, C.hom, hz, ?_⟩
  let 𝒰' : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S :=
    𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun k => ⟨inferInstance, inferInstance⟩)
  refine ⟨𝒰', fun k => ?_⟩
  obtain ⟨Z, z, hZ, hdiag⟩ := h k
  exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
    ((hz.baseChange (𝒰.f k)).isRepresentedBy.isoOfIsRepresentedBy hZ.isRepresentedBy) hdiag

/-- The centre constructed by étale descent represents the full centre after
every base change. -/
theorem relativeCenterModelOfEtaleCover_baseChange
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (h : ∀ k, ∃ (Z : GroupScheme (𝒰.X k))
      (z : Z ⟶ (GroupScheme.baseChange (𝒰.f k)).obj G),
      IsSchemeTheoreticCenter z ∧ RelativeMultiplicativeType.IsDiagonalizable Z)
    {S' : Scheme.{u}} (b : S' ⟶ S) :
    IsSchemeTheoreticCenter
      ((GroupScheme.baseChange b).map (relativeCenterModelOfEtaleCover 𝒰 h).2.val) :=
  (relativeCenterModelOfEtaleCover 𝒰 h).2.property.1.baseChange b

/-- Local diagonalizable centres give the full relative-centre conclusion,
including its arbitrary-base-change clause. -/
theorem exists_multiplicativeTypeCenter_of_etaleCover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (h : ∀ k, ∃ (Z : GroupScheme (𝒰.X k))
      (z : Z ⟶ (GroupScheme.baseChange (𝒰.f k)).obj G),
      IsSchemeTheoreticCenter z ∧ RelativeMultiplicativeType.IsDiagonalizable Z) :
    ∃ (Z : GroupScheme S) (z : Z ⟶ G),
      IsSchemeTheoreticCenter z ∧ RelativeMultiplicativeType.IsMultiplicativeType Z ∧
      ∀ (S' : Scheme.{u}) (b : S' ⟶ S),
        IsSchemeTheoreticCenter ((GroupScheme.baseChange b).map z) := by
  let C := relativeCenterModelOfEtaleCover 𝒰 h
  exact ⟨C.1, C.2.val, C.2.property.1, C.2.property.2,
    fun _ b => C.2.property.1.baseChange b⟩

end Langlands.GroupScheme
