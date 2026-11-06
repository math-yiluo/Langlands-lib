import Langlands.Algebra.CompleteLocalIdealCofinalityStatement
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardSourceCompletion
import Langlands.AlgebraicGeometry.Deformation.LocalAdicArtinianTests

/-! # Actual maps from Picard tower stages to ordinary adic tests -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardSourceAdic

open Langlands.AlgebraicGeometry.Deformation ArtinianPicardSourceStep
open ArtinianPicardSourceTower

private def augmentedDescent {k K C : Type u} [CommRing k] [Field K] [Algebra k K]
    [CommRing C] [Algebra k C] (ε : C →ₐ[k] K)
    {A B : ArtinianTest k K} (α : C →ₐ[k] A.algebra) (hα : Function.Surjective α)
    (hαε : A.augmentation.comp α = ε) (β : C →ₐ[k] B.algebra)
    (hβε : B.augmentation.comp β = ε)
    (hker : RingHom.ker α.toRingHom ≤ RingHom.ker β.toRingHom) : A ⟶ B :=
  ArtinianTest.homMk (AlgHom.liftOfSurjective α hα β hker) (by
    ext a
    obtain ⟨c, rfl⟩ := hα a
    simp only [AlgHom.comp_apply, AlgHom.liftOfSurjective_apply]
    exact (DFunLike.congr_fun hβε c).trans (DFunLike.congr_fun hαε c).symm)

private lemma augmentedDescent_comp {k K C : Type u} [CommRing k] [Field K] [Algebra k K]
    [CommRing C] [Algebra k C] (ε : C →ₐ[k] K)
    {A B : ArtinianTest k K} (α : C →ₐ[k] A.algebra) (hα : Function.Surjective α)
    (hαε : A.augmentation.comp α = ε) (β : C →ₐ[k] B.algebra)
    (hβε : B.augmentation.comp β = ε)
    (hker : RingHom.ker α.toRingHom ≤ RingHom.ker β.toRingHom) :
    (ArtinianTest.toAlgHom (augmentedDescent ε α hα hαε β hβε hker)).comp α = β :=
  AlgHom.liftOfSurjective_comp α hα β hker

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
  [Flat f] [IsProper f] (s₀ : Stage ε f M)

local notation "C" => limitRing ε hε f M s₀
local notation "εC" => limitAugmentation ε hε f M s₀
local notation "hεC" => limitAugmentation_surjective ε hε f M s₀

/-- The actual projection kernels form a decreasing ideal sequence in the unchanged source quotient. -/
abbrev projectionKernel (n : ℕ) : Ideal C :=
  RingHom.ker (projection ε hε f M s₀ n).toRingHom

lemma projectionKernel_antitone : Antitone (projectionKernel ε hε f M s₀) := by
  intro n m hnm
  simp only [projectionKernel, ker_projection]
  exact Ideal.map_mono (equations_antitone ε hε f M s₀ hnm)

lemma iInf_projectionKernel : (⨅ n, projectionKernel ε hε f M s₀ n) = ⊥ :=
  iInf_ker_projection ε hε f M s₀

/-- The ordinary positive maximal-ideal quotient with the original residue augmentation. -/
abbrev adicTest (a : ℕ) : ArtinianTest k K :=
  LocalAdicArtinianTests.test εC hεC a

/-- The original source quotient maps canonically to each ordinary adic test. -/
abbrev adicProjection (a : ℕ) : C →ₐ[k] (adicTest ε hε f M s₀ a).algebra :=
  LocalAdicArtinianTests.projection εC hεC a

lemma ker_adicProjection (a : ℕ) :
    RingHom.ker (adicProjection ε hε f M s₀ a).toRingHom =
      IsLocalRing.maximalIdeal C ^ (a + 1) := Ideal.mk_ker

/-- An actual kernel containment gives an actual augmentation-preserving map from a tower test. -/
def toAdic {n a : ℕ}
    (h : projectionKernel ε hε f M s₀ n ≤ IsLocalRing.maximalIdeal C ^ (a + 1)) :
    test ε hε f M s₀ n ⟶ adicTest ε hε f M s₀ a :=
  augmentedDescent εC (projection ε hε f M s₀ n)
    (projection_surjective ε hε f M s₀ n) (augmentation_projection ε hε f M s₀ n)
    (adicProjection ε hε f M s₀ a) (LocalAdicArtinianTests.augmentation_projection εC hεC a)
    (by rwa [ker_adicProjection])

lemma toAdic_projection {n a : ℕ}
    (h : projectionKernel ε hε f M s₀ n ≤ IsLocalRing.maximalIdeal C ^ (a + 1)) :
    (ArtinianTest.toAlgHom (toAdic ε hε f M s₀ h)).comp (projection ε hε f M s₀ n) =
      adicProjection ε hε f M s₀ a :=
  augmentedDescent_comp εC _ _ _ _ _ _

lemma toAdic_surjective {n a : ℕ}
    (h : projectionKernel ε hε f M s₀ n ≤ IsLocalRing.maximalIdeal C ^ (a + 1)) :
    Function.Surjective (ArtinianTest.toAlgHom (toAdic ε hε f M s₀ h)) :=
  AlgHom.liftOfSurjective_surjective _ _ _ _ (Ideal.Quotient.mkₐ_surjective k _)

/-- The exact source quotient equation uniquely determines the actual map to the adic test. -/
lemma toAdic_unique {n a : ℕ}
    (h : projectionKernel ε hε f M s₀ n ≤ IsLocalRing.maximalIdeal C ^ (a + 1))
    (q : test ε hε f M s₀ n ⟶ adicTest ε hε f M s₀ a)
    (hq : (ArtinianTest.toAlgHom q).comp (projection ε hε f M s₀ n) =
      adicProjection ε hε f M s₀ a) : q = toAdic ε hε f M s₀ h := by
  apply ArtinianTest.hom_ext
  ext b
  obtain ⟨c, rfl⟩ := projection_surjective ε hε f M s₀ n b
  exact (DFunLike.congr_fun hq c).trans
    (DFunLike.congr_fun (toAdic_projection ε hε f M s₀ h) c).symm

/-- Later tower stages retain every actual kernel containment into a given adic power. -/
lemma later_bound {n m a : ℕ} (hnm : n ≤ m)
    (h : projectionKernel ε hε f M s₀ n ≤ IsLocalRing.maximalIdeal C ^ (a + 1)) :
    projectionKernel ε hε f M s₀ m ≤ IsLocalRing.maximalIdeal C ^ (a + 1) :=
  (projectionKernel_antitone ε hε f M s₀ hnm).trans h

/-- Descending one tower step gives the same actual map to the fixed adic test. -/
lemma toAdic_step {n a : ℕ}
    (h : projectionKernel ε hε f M s₀ n ≤ IsLocalRing.maximalIdeal C ^ (a + 1)) :
    step ε hε f M s₀ n ≫ toAdic ε hε f M s₀ h =
      toAdic ε hε f M s₀ (later_bound ε hε f M s₀ (Nat.le_succ n) h) := by
  apply toAdic_unique ε hε f M s₀
  rw [ArtinianTest.toAlgHom_comp, AlgHom.comp_assoc, projection_step, toAdic_projection]

/-- Reducing an ordinary adic test retains the exact map induced from the source quotient. -/
lemma toAdic_adicTransition {n a b : ℕ} (hab : a ≤ b)
    (h : projectionKernel ε hε f M s₀ n ≤ IsLocalRing.maximalIdeal C ^ (b + 1)) :
    toAdic ε hε f M s₀ h ≫ LocalAdicArtinianTests.transition εC hεC hab =
      toAdic ε hε f M s₀
        (h.trans (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1))) := by
  apply toAdic_unique ε hε f M s₀
  rw [ArtinianTest.toAlgHom_comp, AlgHom.comp_assoc, toAdic_projection,
    LocalAdicArtinianTests.projection_transition]

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- The isolated general cofinality proposition supplies the exact actual containment needed at each adic level. -/
lemma exists_adic_bound (hc : Langlands.Algebra.CompleteLocalIdealCofinalityStatement.{u}) (a : ℕ) :
    ∃ n, projectionKernel ε hε f M s₀ n ≤ IsLocalRing.maximalIdeal C ^ (a + 1) :=
  hc C (projectionKernel ε hε f M s₀) (projectionKernel_antitone ε hε f M s₀)
    (iInf_projectionKernel ε hε f M s₀) (a + 1)

/-- With that general cofinality input, every ordinary adic test is an actual quotient of a tower test. -/
lemma exists_toAdic (hc : Langlands.Algebra.CompleteLocalIdealCofinalityStatement.{u}) (a : ℕ) :
    ∃ n, ∃ q : test ε hε f M s₀ n ⟶ adicTest ε hε f M s₀ a,
      Function.Surjective (ArtinianTest.toAlgHom q) ∧
      (ArtinianTest.toAlgHom q).comp (projection ε hε f M s₀ n) =
        adicProjection ε hε f M s₀ a := by
  obtain ⟨n, hn⟩ := exists_adic_bound ε hε f M s₀ hc a
  exact ⟨n, toAdic ε hε f M s₀ hn, toAdic_surjective ε hε f M s₀ hn,
    toAdic_projection ε hε f M s₀ hn⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardSourceAdic
