import Langlands.AlgebraicGeometry.Picard.ArtinianPicardSourceMinimality
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerEvaluation
import Langlands.AlgebraicGeometry.Picard.FlatPicardSquareGluing
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.BaseLifting
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.ChartOpenness
import Langlands.AlgebraicGeometry.Deformation.ArtinianTestPullbacks
import Langlands.AlgebraicGeometry.Deformation.AugmentedAdicCompletion

/-! # Lifting maps into the effective Picard tower base along principal extensions -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardTowerRingLifting

open Langlands.AlgebraicGeometry.Deformation Langlands.CategoryTheory
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianPicardSourceStep ArtinianPicardSourceTower ArtinianPicardSourceMinimality
open ArtinianPicardTowerFormalSystem ArtinianPicardTowerAlgebraization
open ArtinianPicardTowerEvaluation PseudofunctorSquareGluing

section Algebra

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K] [CommRing R] [Algebra k R]
  {A B T : ArtinianTest k K} (q : A ⟶ B)
  (c : Kernel q ≃+ K)
  (hc : ∀ (a : A.algebra) (x : Kernel q), c (a • x) = A.augmentation a * c x)
  (g : T ⟶ B) (σ : R →ₐ[k] A.algebra) (π : R →ₐ[k] T.algebra)
  (hσπ : (toAlgHom q).comp σ = (toAlgHom g).comp π)

include hc in
/-- Let `q` have one-dimensional kernel. If `σ` does not kill the kernel of a surjection
`π`, then the pair `(σ, π)` maps onto the fibre product of `q` and `g`. -/
theorem liftAlgHom_surjective (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
    (hσ : A.augmentation.comp σ = ε) (hπ : Function.Surjective π)
    (hJ : ¬ RingHom.ker π.toRingHom ≤ RingHom.ker σ.toRingHom) :
    Function.Surjective (Pullback.liftAlgHom q g σ π hσπ) := by
  obtain ⟨r₀, hr₀, hσr₀⟩ := SetLike.not_le_iff_exists.mp hJ
  have hr₀' : π r₀ = 0 := hr₀
  have hσr₀' : σ r₀ ≠ 0 := hσr₀
  have hker₀ : σ r₀ ∈ Kernel q := by
    change toAlgHom q (σ r₀) = 0
    rw [show toAlgHom q (σ r₀) = toAlgHom g (π r₀) from DFunLike.congr_fun hσπ r₀, hr₀',
      map_zero]
  let x₀ : Kernel q := ⟨σ r₀, hker₀⟩
  have hx₀ : c x₀ ≠ 0 := by
    intro h
    apply hσr₀'
    have : x₀ = 0 := c.injective (h.trans (map_zero c).symm)
    exact congrArg Subtype.val this
  intro z
  obtain ⟨r₁, hr₁⟩ := hπ z.val.2
  have hd : z.val.1 - σ r₁ ∈ Kernel q := by
    change toAlgHom q (z.val.1 - σ r₁) = 0
    rw [map_sub, show toAlgHom q (σ r₁) = toAlgHom g (π r₁) from DFunLike.congr_fun hσπ r₁,
      hr₁]
    exact sub_eq_zero.mpr z.property
  let d : Kernel q := ⟨z.val.1 - σ r₁, hd⟩
  obtain ⟨r₂, hr₂⟩ := hε (c d / c x₀)
  have hsmul : σ r₂ • x₀ = d := by
    apply c.injective
    rw [hc, show A.augmentation (σ r₂) = ε r₂ from DFunLike.congr_fun hσ r₂, hr₂,
      div_mul_cancel₀ _ hx₀]
  refine ⟨r₁ + r₂ * r₀, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change σ (r₁ + r₂ * r₀) = z.val.1
    have h := congrArg Subtype.val hsmul
    change σ r₂ * σ r₀ = z.val.1 - σ r₁ at h
    rw [map_add, map_mul, h, add_sub_cancel]
  · change π (r₁ + r₂ * r₀) = z.val.2
    rw [map_add, map_mul, hr₀', mul_zero, add_zero, hr₁]

end Algebra

section Extension

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Flat f]
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))

/-- Over a flat base, a pointed family `ξ` on a test `T` extends to the fibre product
`A ×_B T` along an elementary surjection `q : A ⟶ B`, as soon as the pullback of `ξ` to
`B` is the pullback of some line bundle on `A`. -/
theorem exists_extension {A B T : ArtinianTest k K} (q : A ⟶ B)
    (hq : IsElementarySurjection q) (g : T ⟶ B)
    (ξ : ArtinianTestDeformations.Deformations f M T)
    (N : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)))
    (e : (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.baseMap g))).obj ξ.right.of ≅
      (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.baseMap q))).obj N) :
    ∃ Z : ArtinianTestDeformations.Deformations f M (Pullback.test q g hq.1),
      Nonempty ((ArtinianTestDeformations.restrict f M (Pullback.snd q g hq.1)).obj Z ≅ ξ) := by
  have hE := affine_isSquareEffective f (toAlgHom (Pullback.snd q g hq.1))
    (toAlgHom (Pullback.fst q g hq.1)) (toAlgHom g) (toAlgHom q)
    (Pullback.ring_isPullback q g).flip hq.1 ⟨2, hq.ker_sq.trans Ideal.zero_eq_bot.symm⟩
  obtain ⟨Z, e₁, -, -⟩ := hE ξ.right (Core.mk N) (Core.isoMk e)
  exact ⟨PseudofunctorPointedTransport.transport (relative f)
      (T₀ := ArtinianTest.residueBase k K) (Core.mk M) (pointedMap (Pullback.snd q g hq.1)) Z ξ e₁,
    ⟨PseudofunctorPointedTransport.transportIso (relative f)
      (T₀ := ArtinianTest.residueBase k K) (Core.mk M) (pointedMap (Pullback.snd q g hq.1)) Z ξ e₁⟩⟩

end Extension

section Lifting

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
  [Flat f] [IsProper f] (s₀ : Stage ε f M)
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- Ring-map lifting for the effective tower bundle: let `q : A ⟶ B` be an elementary
surjection with one-dimensional kernel. Every actual point of the effective bundle over
`baseMap q`, at the closed point, has a base map that extends along `baseMap q`. -/
theorem exists_ringLift
    (hlift : ∀ {A B : ArtinianTest k K} (q : A ⟶ B), Function.Surjective (toAlgHom q) →
      Function.Surjective (AugmentedAdicCompletion.postcomp ε q))
    {A B : ArtinianTest k K} (q : A ⟶ B) (hq : IsElementarySurjection q)
    (c : Kernel q ≃+ K)
    (hc : ∀ (a : A.algebra) (x : Kernel q), c (a • x) = A.augmentation a * c x)
    (N : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)))
    (y : ArtinianChartVersality.FiberPoints f (effectiveBundle ε hε f M s₀) N
      (Over.mk (ArtinianTest.baseMap q)))
    (hy : ArtinianTest.reduction B ≫ y.1 = residuePoint ε hε f M s₀) :
    ∃ u : ArtinianTest.base A ⟶ affineBase k (limitRing ε hε f M s₀),
      ArtinianTest.baseMap q ≫ u = y.1 := by
  obtain ⟨y₁, y₂⟩ := y
  obtain ⟨αB, rfl⟩ := OpennessOfVersality.exists_affineBaseMap_eq (R := k)
    (A := limitRing ε hε f M s₀) (B := B.algebra) y₁
  have hαB : B.augmentation.comp αB = limitAugmentation ε hε f M s₀ := by
    apply OpennessOfVersality.affineBaseMap_injective
    rw [← OpennessOfVersality.reduction_comp_affineBaseMap]
    exact hy
  obtain ⟨a, ha⟩ := ArtinianAdicEvaluation.exists_bound
    (IsLocalRing.maximalIdeal (limitRing ε hε f M s₀)) αB (limitAugmentation ε hε f M s₀)
    (maximalIdeal_le_augmentation ε hε f M s₀) hαB
  let n := index ε hε f M s₀ a
  let s := stage ε hε f M s₀ n
  let g : s.test ⟶ B := stageMap ε hε f M s₀ αB hαB a ha
  have hg : (toAlgHom g).comp (projection ε hε f M s₀ n) = αB :=
    stageMap_projection ε hε f M s₀ αB hαB a ha
  obtain ⟨⟨σ, hσ⟩, hσq⟩ := hlift q hq.1 ⟨(toAlgHom g).comp s.cover, by
    rw [← AlgHom.comp_assoc, augmentation_comp, s.augmentation_cover]⟩
  have hσq' : (toAlgHom q).comp σ = (toAlgHom g).comp s.cover := congrArg Subtype.val hσq
  have key : ∀ φ : limitRing ε hε f M s₀ →ₐ[k] A.algebra, (toAlgHom q).comp φ = αB →
      ∃ u : ArtinianTest.base A ⟶ affineBase k (limitRing ε hε f M s₀),
        ArtinianTest.baseMap q ≫ u = affineBaseMap αB := by
    intro φ hφ
    refine ⟨affineBaseMap φ, ?_⟩
    rw [← hφ, affineBaseMap_comp]
    rfl
  by_cases hJ : RingHom.ker s.cover.toRingHom ≤ RingHom.ker σ.toRingHom
  · apply key (Ideal.Quotient.liftₐ _ σ (fun r hr ↦ RingHom.mem_ker.mp
      (hJ (limitingEquations_le ε hε f M s₀ n hr))))
    rw [← hg]
    apply Ideal.Quotient.algHom_ext
    ext r
    exact DFunLike.congr_fun hσq' r
  · have hτ := liftAlgHom_surjective q c hc g σ s.cover hσq' ε hε hσ s.cover_surjective hJ
    have hsnd := Pullback.snd_isElementary q g hq
    let τ := ElementarySourceExtension.factor ε hε s.test s.cover s.augmentation_cover
      (Pullback.snd q g hq.1) (Pullback.liftAlgHom q g σ s.cover hσq') hsnd rfl
    have hτρ : τ ≫ Pullback.snd q g hq.1 = s.sourceReduction ε hε f M :=
      ElementarySourceExtension.factor_reduction ε hε s.test s.cover s.augmentation_cover
        (Pullback.snd q g hq.1) (Pullback.liftAlgHom q g σ s.cover hσq') hsnd rfl
    have hτproj : (toAlgHom τ).comp (s.sourceProjection ε hε f M) =
        Pullback.liftAlgHom q g σ s.cover hσq' :=
      ElementarySourceExtension.factor_projection ε hε s.test s.cover s.augmentation_cover
        (Pullback.snd q g hq.1) (Pullback.liftAlgHom q g σ s.cover hσq') hsnd rfl
    have hτs : Function.Surjective (toAlgHom τ) := by
      intro x
      obtain ⟨r, hr⟩ := hτ x
      exact ⟨s.sourceProjection ε hε f M r, (DFunLike.congr_fun hτproj r).trans hr⟩
    let eN : (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.baseMap g))).obj
        s.family.right.of ≅
        (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.baseMap q))).obj N :=
      (effectiveEvaluationIso ε hε f M s₀ αB hαB a ha).symm ≪≫ y₂.hom.iso
    obtain ⟨Z, ⟨eZ⟩⟩ := exists_extension f M q hq g s.family N eN
    obtain ⟨ψ, -, hψ⟩ := exists_next_factor_of_extension ε hε f M s τ
      (Pullback.snd q g hq.1) hτρ hτs Z eZ
    apply key ((toAlgHom (ψ ≫ Pullback.fst q g hq.1)).comp
      (projection ε hε f M s₀ (n + 1)))
    have h₁ : ψ ≫ Pullback.fst q g hq.1 ≫ q = s.reduction ε hε f M ≫ g := by
      rw [Pullback.condition, ← Category.assoc, hψ]
    rw [← hg, ← projection_step ε hε f M s₀ n]
    change (toAlgHom (ψ ≫ Pullback.fst q g hq.1 ≫ q)).comp (projection ε hε f M s₀ (n + 1)) =
      (toAlgHom (s.reduction ε hε f M ≫ g)).comp (projection ε hε f M s₀ (n + 1))
    rw [h₁]

end Lifting

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardTowerRingLifting
