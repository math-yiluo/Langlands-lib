import Langlands.AlgebraicGeometry.Modules.TwistCechBridge
import Langlands.AlgebraicGeometry.Modules.RelativeSerreVanishingFLT
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj_monoidalV2
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow_monoidalV2
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent

/-! # Relative Serre vanishing for invertible modules twisted by a very ample module -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Langlands.AlgebraicGeometry.Modules.CechBridge

section

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)}
  {L : X.Modules} {N : ℕ} (𝔓 : L.ProjPresentation f N)

lemma inter_le_pullbackChart [IsAffineHom 𝔓.toProj] {i : ℕ}
    (s : (ProjSpace.stdCoverPullback 𝔓.toProj).Idx i) :
    (ProjSpace.stdCoverPullback 𝔓.toProj).inter s ≤ ProjSpace.pullbackChart 𝔓.toProj (s.1 0).down :=
  (ProjSpace.stdCoverPullback 𝔓.toProj).inter_le s 0

/-- Step 1: the twisted presheaf and the presheaf tensor with sections of `L^{⊗ d}`. -/
lemma nonempty_hsucc_twist_equiv_tensor [IsSeparated f] [IsAffineHom 𝔓.toProj] (F : X.Modules)
    (d : ℕ) (e : ∀ U : X.Opens, Γ(L.tensorPow d, U) →ₗ[Γ(X, U)] ProjSpace.twistObj f 𝔓.toProj d U)
    (he : ∀ (U U' : X.Opens) (h : U ≤ U') (x : Γ(L.tensorPow d, U')),
      e U ((L.tensorPow d).presheaf.map (homOfLE h).op x) = ProjSpace.twistRes f 𝔓.toProj d h (e U' x))
    (hbij : ∀ (U : X.Opens) (i : Fin (N + 1)), U ≤ ProjSpace.pullbackChart 𝔓.toProj i →
      Function.Bijective (e U)) (j : ℕ) :
    Nonempty (((OModulePresheaf.ofModules f F).tensor
        (OModulePresheaf.ofModules f (L.tensorPow d))).HSucc
        (ProjSpace.stdCoverPullback 𝔓.toProj) j ≃ₗ[A]
      ((OModulePresheaf.ofModules f F).tensor (ProjSpace.twist f 𝔓.toProj d)).HSucc
        (ProjSpace.stdCoverPullback 𝔓.toProj) j) :=
  ⟨hsuccEquivOfBijective (ProjSpace.stdCoverPullback 𝔓.toProj)
    (tensorRightAffHom (OModulePresheaf.ofModules f F)
      (OModulePresheaf.ofModules f (L.tensorPow d)) (ProjSpace.twist f 𝔓.toProj d) e
      (fun h x => he _ _ h x))
    (fun _ s => tensorRightAffHom_bijective (OModulePresheaf.ofModules f F)
      (OModulePresheaf.ofModules f (L.tensorPow d)) (ProjSpace.twist f 𝔓.toProj d) e
      (fun h x => he _ _ h x) _
      (hbij _ (s.1 0).down (inter_le_pullbackChart 𝔓 s))) j⟩

/-- Step 2: the presheaf tensor product of sections and the sections of the tensor product. -/
lemma nonempty_hsucc_tensor_equiv_ofModules [IsSeparated f] (K : X.OrderedAffineCover)
    (F M : X.Modules) (hF : Scheme.Modules.IsInvertible F) (hM : Scheme.Modules.IsInvertible M)
    (j : ℕ) :
    Nonempty (((OModulePresheaf.ofModules f F).tensor (OModulePresheaf.ofModules f M)).HSucc K j ≃ₗ[A]
      (OModulePresheaf.ofModules f (F ⊗ M)).HSucc K j) :=
  ⟨hsuccEquivOfBijective K (tensorSectionsAffHom (q := f) F M)
    (fun _ _ => tensorSectionsAffHom_bijective hF hM _) j⟩

/-- Step 3: Čech cohomology of an invertible module is its actual cohomology. -/
lemma nonempty_hsucc_ofModules_equiv [IsSeparated f] (K : X.OrderedAffineCover) (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M) (j : ℕ) :
    Nonempty ((OModulePresheaf.ofModules f M).HSucc K j ≃ₗ[A]
      (DerivedSections.relativeCohomology f (j + 1)).obj M) := by
  have : M.IsQuasicoherent :=
    Picard.IsLocallyFreeRankOne.isQuasicoherent (fun x => by
      obtain ⟨U, hx, ⟨e⟩⟩ := hM.exists_trivialization x
      exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫ e⟩⟩)
  exact ⟨hsuccEquivRelativeCohomology (R := CommRingCat.of A) (π := f) K M j⟩

/-- **Relative Serre vanishing.** Let `A` be noetherian, `f : X ⟶ Spec A` separated, and `L` an
invertible module with a projective presentation `𝔓` whose morphism to `ℙᴺ_A` is a closed
immersion. For every invertible `F`, the cohomology of `F ⊗ L^{⊗ d}` vanishes in all positive
degrees for all large `d`. -/
theorem exists_isZero_relativeCohomology_tensor_tensorPow [IsNoetherianRing A] [IsSeparated f]
    [IsClosedImmersion 𝔓.toProj] (hL : Scheme.Modules.IsInvertible L) (F : X.Modules)
    (hF : Scheme.Modules.IsInvertible F) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ i : ℕ, 0 < i →
      IsZero ((DerivedSections.relativeCohomology f i).obj (F ⊗ L.tensorPow d)) := by
  obtain ⟨d₀, hd₀⟩ := exists_forall_subsingleton_HSucc_tensor_twist 𝔓.toProj 𝔓.toProj_π
    (OModulePresheaf.ofModules f F)
    (OModulePresheaf.isCoherent_ofModules_of_locallyTrivial f F hF.exists_trivialization)
    (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial f F hF.exists_trivialization)
  refine ⟨d₀, fun d hd i hi => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨e, -, he, hbij⟩ := 𝔓.exists_linearMap_sections_tensorPow_twistObj_monoidalV2 d
  have hLd : Scheme.Modules.IsInvertible (L.tensorPow d) := hL.tensorPow_monoidalV2 d
  obtain ⟨e₁⟩ := nonempty_hsucc_twist_equiv_tensor 𝔓 F d e he hbij j
  obtain ⟨e₂⟩ := nonempty_hsucc_tensor_equiv_ofModules (f := f)
    (ProjSpace.stdCoverPullback 𝔓.toProj) F (L.tensorPow d) hF hLd j
  obtain ⟨e₃⟩ := nonempty_hsucc_ofModules_equiv (f := f) (ProjSpace.stdCoverPullback 𝔓.toProj)
    (F ⊗ L.tensorPow d) (hF.tensor_monoidalV2 hLd) j
  have h₀ := hd₀ d hd j
  have h₁ := e₁.toEquiv.subsingleton
  have h₂ := e₂.symm.toEquiv.subsingleton
  have h₃ := e₃.symm.toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end

end Langlands.AlgebraicGeometry.Modules.CechBridge
