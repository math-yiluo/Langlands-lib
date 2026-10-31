import Langlands.AlgebraicGeometry.Picard.FieldPicardZeroComponentConstancyStatement
import Langlands.AlgebraicGeometry.Picard.UniversalMumfordClassifierProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalGroupObject
import Langlands.AlgebraicGeometry.Picard.PicardZeroGroup
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs
import Langlands.AlgebraicGeometry.Modules.ExplicitPullbackTensorAssociativityProofs
import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs
import Langlands.AlgebraicGeometry.Picard.FibreContractionOpenProof
import Langlands.AlgebraicGeometry.Picard.FieldGroupOpenSubgroupClosedProof

/-! # Constancy of the geometric Picard-zero condition on connected components -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.ComponentConstancy

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Let `e` be a section of a morphism `f : X ⟶ S` to a one-point scheme. A morphism from a
reduced scheme to `X` whose image lies in the image of `e` factors through `e`. -/
lemma eq_comp_of_range_subset_range {X S T : Scheme.{u}} [Subsingleton S] [IsReduced T]
    (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S) (g : T ⟶ X)
    (hg : Set.range g ⊆ Set.range e) : g = (g ≫ f) ≫ e := by
  have : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id f e he
  have : Surjective (pullback.snd e g) := ⟨fun t ↦ by
    obtain ⟨s, hs⟩ := hg ⟨t, rfl⟩
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback s t hs
    exact ⟨w, hw⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd e g)
  have h : g = inv (pullback.snd e g) ≫ pullback.fst e g ≫ e := by
    rw [pullback.condition, IsIso.inv_hom_id_assoc]
  have h2 : g ≫ f = inv (pullback.snd e g) ≫ pullback.fst e g := by
    conv_lhs => rw [h]
    simp only [Category.assoc, he, Category.comp_id]
  rw [h2, Category.assoc]
  exact h

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The geometric Picard-zero classes are closed under `a, b ↦ a * b⁻¹` in the group of
rigidified classes. -/
lemma isPicardZeroClass_mul_inv (T : Over S) (a b : RigidifiedClasses A T)
    (ha : IsPicardZeroClass A a) (hb : IsPicardZeroClass A b) :
    letI := RigidifiedLineBundle.classesCommGroup pullbackTensorComparisonIsIso
      pullbackTensorUnitCoherence explicitPullbackTensorAssociativity
      tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry
      locallyFreeRankOneIffTensorInvertible A.X.hom (unitSection A) (unitSection_comp A) T
    IsPicardZeroClass A (a * b⁻¹) := by
  let := RigidifiedLineBundle.classesCommGroup pullbackTensorComparisonIsIso
    pullbackTensorUnitCoherence explicitPullbackTensorAssociativity
    tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry
    locallyFreeRankOneIffTensorInvertible A.X.hom (unitSection A) (unitSection_comp A) T
  let := picardZeroClassesCommGroup pullbackTensorComparisonIsIso
    pullbackTensorUnitCoherence explicitPullbackTensorAssociativity
    tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry
    locallyFreeRankOneIffTensorInvertible A T
  let a' : PicardZeroClasses A T := ⟨a, ha⟩
  let b' : PicardZeroClasses A T := ⟨b, hb⟩
  have hinv : b⁻¹ = (b'⁻¹).1 := by
    apply inv_eq_of_mul_eq_one_right
    change (b' * b'⁻¹).1 = 1
    rw [mul_inv_cancel]
    rfl
  rw [hinv]
  exact (a' * b'⁻¹).2

variable {P : Over S} (L : RigidifiedFamily A P)
  (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L)

/-- For the commutative group structure of a universal parameter, the parameter morphisms with
geometric Picard-zero pullback are closed under `p, q ↦ p * q⁻¹`. -/
lemma isPicardZeroFamily_mul_inv (T : Over S) (p q : T ⟶ P) :
    letI := RigidifiedLineBundle.universalCommGrpObj pullbackTensorComparisonIsIso
      pullbackTensorUnitCoherence explicitPullbackTensorAssociativity
      tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry
      locallyFreeRankOneIffTensorInvertible A.X.hom (unitSection A) (unitSection_comp A)
      pullbackTensorComposition L hL
    IsPicardZeroFamily A
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          p).obj L) →
      IsPicardZeroFamily A
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          q).obj L) →
      IsPicardZeroFamily A
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          (p * q⁻¹)).obj L) := by
  let := RigidifiedLineBundle.universalCommGrpObj pullbackTensorComparisonIsIso
    pullbackTensorUnitCoherence explicitPullbackTensorAssociativity
    tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry
    locallyFreeRankOneIffTensorInvertible A.X.hom (unitSection A) (unitSection_comp A)
    pullbackTensorComposition L hL
  intro hp hq
  change IsPicardZeroClass A (RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
    (unitSection_comp A) L T (p * q⁻¹))
  rw [RigidifiedLineBundle.classifyingMap_mul, RigidifiedLineBundle.classifyingMap_inv]
  exact isPicardZeroClass_mul_inv A T _ _ hp hq

end Langlands.AbelianScheme.ComponentConstancy

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules ComponentConstancy

/-- Over a field, the geometric Picard-zero condition on pullbacks of a universal rigidified
family is constant along the geometric points of each connected component of the parameter. -/
theorem fieldPicardZeroComponentConstancy : FieldPicardZeroComponentConstancyStatement.{u} := by
  intro k _ A P L hLFT hL x K₀ _ _ s₀ K₁ _ _ s₁ h₀ h₁ hZ₀
  have : Subsingleton ↥(Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
    inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of k)))
  obtain ⟨Ψ, hΨS, hΨ0, hcrit⟩ := universalMumfordClassifier _ A P L hL
  let B := (baseChange P.hom).obj A
  let τ := RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A) (unitSection_comp A) L hL
  let e : Spec (CommRingCat.of k) ⟶ P.left := τ.left
  have he : e ≫ P.hom = 𝟙 _ := Over.w τ
  let e₀ : P.left := e (IsLocalRing.closedPoint k)
  have he₀ : ∀ z, e z = e₀ := fun z ↦ congrArg e (Subsingleton.elim _ _)
  have hrange : Set.range e = {e₀} := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩; exact he₀ z
    · rintro rfl; exact ⟨_, rfl⟩
  have hclosed : IsClosed ({e₀} : Set P.left) := by
    have : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id P.hom e he
    rw [← hrange]
    exact e.isClosedEmbedding.isClosed_range
  let U : Set P.left := {y | ∀ z, B.X.hom z = y → Ψ z = e₀}
  have hUo : IsOpen U := fibreContractionOpen _ _ B Ψ e₀ (fun y ↦ by
    rw [← Scheme.Hom.comp_apply, hΨ0, Scheme.Hom.comp_apply]
    exact he₀ _)
  have key : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) (p : Over.mk b ⟶ P),
      IsPicardZeroFamily A ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) p).obj L) ↔ Set.range p.left ⊆ U := by
    intro K _ _ b p
    rw [hcrit (Over.mk b) p]
    constructor
    · intro H
      rintro _ ⟨w, rfl⟩ z hz
      let F : Scheme.{u} := pullback B.X.hom p.left
      let sn : F ⟶ Spec (CommRingCat.of K) := pullback.snd B.X.hom p.left
      let fs : F ⟶ B.X.left := pullback.fst B.X.hom p.left
      have : JacobsonSpace F := LocallyOfFiniteType.jacobsonSpace sn
      have hC : IsClosed ((fs ≫ Ψ) ⁻¹' {e₀}) := hclosed.preimage (Scheme.Hom.continuous _)
      have hall : closedPoints F ⊆ (fs ≫ Ψ) ⁻¹' {e₀} := by
        intro c hc
        have hc' : IsClosed {c} := hc
        let σ := pointOfClosedPoint sn c hc'
        have hσ : σ ≫ sn = 𝟙 _ := pointOfClosedPoint_comp sn c hc'
        have hy := H K (𝟙 _) (σ ≫ fs) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc, hσ])
        change Ψ (fs c) = e₀
        rw [← pointOfClosedPoint_apply sn c hc' (IsLocalRing.closedPoint K)]
        change ((σ ≫ fs) ≫ Ψ) (IsLocalRing.closedPoint K) = e₀
        rw [hy, Category.id_comp]
        exact he₀ _
      have huniv : Set.univ ⊆ (fs ≫ Ψ) ⁻¹' {e₀} := by
        rw [← closure_closedPoints]
        exact hC.closure_subset_iff.mpr hall
      obtain ⟨v, hv1, -⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := B.X.hom) (g := p.left) z w hz
      have hv := huniv (Set.mem_univ v)
      simp only [Set.mem_preimage, Scheme.Hom.comp_apply, Set.mem_singleton_iff] at hv
      rwa [show fs v = z from hv1] at hv
    · intro hU K' _ _ t y hy
      refine (eq_comp_of_range_subset_range P.hom e he (y ≫ Ψ) ?_).trans ?_
      · rintro _ ⟨w, rfl⟩
        refine ⟨IsLocalRing.closedPoint k, ?_⟩
        change e₀ = Ψ (y w)
        symm
        apply hU ⟨t w, rfl⟩ (y w)
        rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
      · simp only [Category.assoc, reassoc_of% hΨS, reassoc_of% hy, Over.w_assoc]
        rfl
  have hUc : IsClosed U := by
    let := RigidifiedLineBundle.universalCommGrpObj pullbackTensorComparisonIsIso
      pullbackTensorUnitCoherence explicitPullbackTensorAssociativity
      tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry
      locallyFreeRankOneIffTensorInvertible A.X.hom (unitSection A) (unitSection_comp A)
      pullbackTensorComposition L hL
    have : LocallyOfFiniteType P.hom := hLFT
    refine GroupScheme.fieldGroupOpenSubgroupClosed k P U hUo ?_
    intro K _ _ b p q hp hq
    rw [← key K b] at hp hq ⊢
    exact isPicardZeroFamily_mul_inv A L hL _ p q hp hq
  have hy₀ : s₀ (IsLocalRing.closedPoint K₀) ∈ U :=
    (key K₀ _ (Over.homMk s₀ rfl)).mp hZ₀ ⟨_, rfl⟩
  have hcomp : connectedComponent x ⊆ U := by
    rw [connectedComponent_eq (h₀ ⟨IsLocalRing.closedPoint K₀, rfl⟩)]
    exact (IsClopen.connectedComponent_subset ⟨hUc, hUo⟩ hy₀)
  exact (key K₁ _ (Over.homMk s₁ rfl)).mpr (h₁.trans hcomp)

end Langlands.AbelianScheme
