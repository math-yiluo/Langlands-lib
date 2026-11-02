import Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingStatement
import Langlands.AlgebraicGeometry.Modules.CoherentEulerFiltration
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Uniform two-bundle vanishing and exact sequences -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

variable {X : Scheme.{u}} {K : Type u} [Field K]

instance tensorBy_preservesZeroMorphisms (N : X.Modules) :
    (tensorBy N).PreservesZeroMorphisms where
  map_zero M M' := by
    have : (Scheme.Modules.toPresheafOfModules X).Additive :=
      inferInstanceAs (SheafOfModules.forget X.ringCatSheaf).Additive
    have : (sheafify X).Additive := (sheafifyAdjunction X).left_adjoint_additive
    have hz : (0 : M ⟶ M').val ⊗ₘ (𝟙 N : N ⟶ N).val = 0 := by
      apply PresheafOfModules.hom_ext
      intro U
      change (0 : M.val.obj U ⟶ M'.val.obj U) ⊗ₘ (𝟙 N : N ⟶ N).val.app U = 0
      exact MonoidalPreadditive.zero_tensor _
    change (sheafify X).map ((0 : M ⟶ M').val ⊗ₘ (𝟙 N : N ⟶ N).val) = 0
    rw [hz, Functor.map_zero]

/-- The actual tensor functor with the two prescribed powers. -/
def pairTwist (N₁ N₂ : X.Modules) (a b : ℕ) : X.Modules ⥤ X.Modules :=
  tensorBy (tensorPow N₁ a) ⋙ tensorBy (tensorPow N₂ b)

instance (N₁ N₂ : X.Modules) (a b : ℕ) :
    (pairTwist N₁ N₂ a b).PreservesZeroMorphisms :=
  inferInstanceAs (tensorBy (tensorPow N₁ a) ⋙ tensorBy (tensorPow N₂ b)).PreservesZeroMorphisms

/-- One threshold makes every positive degree vanish in the whole quadrant. -/
def Good (f : X ⟶ Spec (CommRingCat.of K)) (N₁ N₂ M : X.Modules) : Prop :=
  ∃ m : ℕ, ∀ a b : ℕ, m ≤ a → m ≤ b → ∀ i : ℕ, 0 < i →
    IsZero ((DerivedSections.relativeCohomology f i).obj ((pairTwist N₁ N₂ a b).obj M))

lemma rankOne_pow (N : X.Modules) (hN : IsLocallyFreeRankOne N) (a : ℕ) :
    IsLocallyFreeRankOne (tensorPow N a) :=
  tensorPow_isLocallyFreeRankOne X ⟨N, hN⟩ a

lemma shortExact_pairTwist (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (N₁ N₂ : X.Modules) (h₁ : IsLocallyFreeRankOne N₁)
    (h₂ : IsLocallyFreeRankOne N₂) (a b : ℕ) :
    (S.map (pairTwist N₁ N₂ a b)).ShortExact :=
  shortExact_tensorBy (S.map (tensorBy (tensorPow N₁ a)))
    (shortExact_tensorBy S hS _ (rankOne_pow N₁ h₁ a)) _
    (rankOne_pow N₂ h₂ b)

lemma Good.of_iso {f : X ⟶ Spec (CommRingCat.of K)} {N₁ N₂ M M' : X.Modules}
    (h : Good f N₁ N₂ M) (e : M ≅ M') : Good f N₁ N₂ M' := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, fun a b ha hb i hi =>
    (hm a b ha hb i hi).of_iso
      ((DerivedSections.relativeCohomology f i).mapIso
        ((pairTwist N₁ N₂ a b).mapIso e.symm))⟩

lemma Good.of_isZero (f : X ⟶ Spec (CommRingCat.of K))
    (N₁ N₂ : X.Modules) (h₁ : IsLocallyFreeRankOne N₁)
    (h₂ : IsLocallyFreeRankOne N₂) {M : X.Modules} (hM : IsZero M) :
    Good f N₁ N₂ M := by
  refine ⟨0, fun a b _ _ i _ => ?_⟩
  apply NoetherianVanishing.isZero_relativeCohomology_of_isZero f
  exact (((HasSupportDimensionLT.of_isZero hM 0).tensor_lineBundle
    (rankOne_pow N₁ h₁ a)).tensor_lineBundle (rankOne_pow N₂ h₂ b)).isZero

/-- Vanishing in one degree is closed under an extension. -/
lemma isZero_cohomology_middle {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (i : ℕ)
    (h₁ : IsZero ((DerivedSections.relativeCohomology f i).obj S.X₁))
    (h₃ : IsZero ((DerivedSections.relativeCohomology f i).obj S.X₃)) :
    IsZero ((DerivedSections.relativeCohomology f i).obj S.X₂) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  exact (Langlands.Cohomology.DerivedPlus.rightDerived_exact₂
    (DerivedSections.relativeGlobalSections f) hS i).isZero_X₂_iff.2
      ⟨h₁.eq_of_src _ _, h₃.eq_of_tgt _ _⟩

lemma Good.extension (f : X ⟶ Spec (CommRingCat.of K))
    (N₁ N₂ : X.Modules) (h₁ : IsLocallyFreeRankOne N₁)
    (h₂ : IsLocallyFreeRankOne N₂)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hleft : Good f N₁ N₂ S.X₁) (hright : Good f N₁ N₂ S.X₃) :
    Good f N₁ N₂ S.X₂ := by
  obtain ⟨m, hm⟩ := hleft
  obtain ⟨n, hn⟩ := hright
  refine ⟨max m n, fun a b ha hb i hi => ?_⟩
  exact isZero_cohomology_middle f (S.map (pairTwist N₁ N₂ a b))
    (shortExact_pairTwist S hS N₁ N₂ h₁ h₂ a b) i
    (hm a b ((le_max_left _ _).trans ha) ((le_max_left _ _).trans hb) i hi)
    (hn a b ((le_max_right _ _).trans ha) ((le_max_right _ _).trans hb) i hi)

/-- Good graded factors give a good last filtration term. -/
lemma Good.filtration (f : X ⟶ Spec (CommRingCat.of K))
    (N₁ N₂ : X.Modules) (h₁ : IsLocallyFreeRankOne N₁)
    (h₂ : IsLocallyFreeRankOne N₂) {n : ℕ} (F : CoherentFiltration X n)
    (hF : ∀ j, Good f N₁ N₂ (F.factor j)) :
    Good f N₁ N₂ (F.term (Fin.last n)) := by
  have hterm : ∀ k : Fin (n + 1), Good f N₁ N₂ (F.term k) := by
    intro k
    induction k using Fin.induction with
    | zero => exact Good.of_isZero f N₁ N₂ h₁ h₂ F.zero
    | succ j ih =>
        exact Good.extension f N₁ N₂ h₁ h₂ (F.complex j)
          (F.complex_shortExact j) ih (hF j)
  exact hterm _

/-- After any exact functor, vanishing of the source, kernel in the next
degree and cokernel in the current degree forces vanishing of the target. -/
lemma isZero_cohomology_target {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    (T : X.Modules ⥤ X.Modules) [T.PreservesZeroMorphisms]
    (hT : ∀ (S : ShortComplex X.Modules), S.ShortExact → (S.map T).ShortExact)
    {M M' : X.Modules} (φ : M ⟶ M') (i : ℕ)
    (hK : IsZero ((DerivedSections.relativeCohomology f (i + 1)).obj
      (T.obj (kernel φ))))
    (hC : IsZero ((DerivedSections.relativeCohomology f i).obj
      (T.obj (cokernel φ))))
    (hM : IsZero ((DerivedSections.relativeCohomology f i).obj (T.obj M))) :
    IsZero ((DerivedSections.relativeCohomology f i).obj (T.obj M')) := by
  let p := Abelian.factorThruImage φ
  let j := Abelian.image.ι φ
  have eK : kernel φ ≅ kernel p :=
    (kernelIsoOfEq (Abelian.image.fac φ)).symm ≪≫ kernelCompMono p j
  have eC : cokernel φ ≅ cokernel j :=
    (cokernelIsoOfEq (Abelian.image.fac φ)).symm ≪≫ cokernelEpiComp p j
  let S₁ := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  let S₂ := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
  have hS₂ : S₂.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel j) }
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  have hI : IsZero ((DerivedSections.relativeCohomology f i).obj
      (T.obj (Abelian.image φ))) := by
    exact (Langlands.Cohomology.DerivedPlus.rightDerived_exact₃
      (DerivedSections.relativeGlobalSections f) (hT S₁ hS₁) i (i + 1) rfl).isZero_X₂_iff.2
      ⟨hM.eq_of_src _ _, (hK.of_iso
        ((DerivedSections.relativeCohomology f (i + 1)).mapIso (T.mapIso eK.symm))).eq_of_tgt _ _⟩
  exact isZero_cohomology_middle f (S₂.map T) (hT S₂ hS₂) i hI
    (hC.of_iso ((DerivedSections.relativeCohomology f i).mapIso (T.mapIso eC.symm)))

end Langlands.AlgebraicGeometry.Modules.SerreVanishing
