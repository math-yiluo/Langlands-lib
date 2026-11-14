import Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistUniformVanishing
import Langlands.AlgebraicGeometry.Modules.CechEulerBridge
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion

/-! # Euler characteristics of twists on fibres are polynomials -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace Langlands.AlgebraicGeometry.Modules.FibreTwist

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The sections presheaf of a module is supported in the whole space. -/
lemma supportedIn_top {k : Type u} [CommRing k] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of k))
    (M : V.Modules) : (OModulePresheaf.ofModules π M).SupportedIn ⊤ := by
  intro W hW
  have hW' : ((W : V.Opens) : Set V) = ∅ := by simpa using hW
  have hbot : (W : V.Opens) = ⊥ := TopologicalSpace.Opens.ext (by simpa using hW')
  have : Subsingleton Γ(V, (W : V.Opens)) := by rw [hbot]; infer_instance
  exact Module.subsingleton Γ(V, (W : V.Opens)) _

/-- Euler characteristics of twists on the base change along a field point `Spec B ⟶ T` are
given by a polynomial of degree at most `N`. -/
theorem eulerPolynomial_of_point (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (𝓛X : X.Modules) (N : ℕ) (𝔓 : 𝓛X.ProjPresentation f N)
    [IsProper f] (h𝓛 : Scheme.Modules.IsInvertible 𝓛X) [IsClosedImmersion 𝔓.toProj]
    (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A))
    (F : (pullback f s).Modules) (hF : Scheme.Modules.IsInvertible F) (B : CommRingCat.{u})
    (hB : IsField B) (b : Spec B ⟶ T) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ N ∧ ∀ n : ℕ,
      ((∑ᶠ p : ℕ, (-1 : ℤ) ^ p * (Module.finrank B
        ((DerivedSections.relativeCohomology (pullback.snd (pullback.snd f s) b) p).obj
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd f s) b)).obj
            (twist ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) F n))) : ℤ) : ℤ) : ℚ) =
        P.eval (n : ℚ) := by
  let : Field B := hB.toField
  let gT := pullback.snd f s
  let a := pullback.fst gT b
  let q := pullback.snd gT b
  let φ : CommRingCat.of A ⟶ B := Spec.preimage (b ≫ s)
  let : Algebra A B := φ.hom.toAlgebra
  have sq : IsPullback (a ≫ pullback.fst f s) q f
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    have h := (IsPullback.of_hasPullback gT b).paste_horiz (IsPullback.of_hasPullback f s)
    have hφ : Spec.map (CommRingCat.ofHom (algebraMap A B)) = b ≫ s := Spec.map_preimage (b ≫ s)
    rw [hφ]
    exact h
  obtain ⟨𝔓', -, -, hpb⟩ := 𝔓.exists_baseChange_of_isPullback sq
  have : IsClosedImmersion 𝔓'.toProj :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb ‹_›
  let L := (Scheme.Modules.pullback (a ≫ pullback.fst f s)).obj 𝓛X
  have hL : Scheme.Modules.IsInvertible L := h𝓛.pullback _
  let Ft := (Scheme.Modules.pullback a).obj F
  have hFt : Scheme.Modules.IsInvertible Ft := hF.pullback _
  have hdim : topologicalKrullDim (pullback (C := Scheme.{u}) gT b) ≤ N :=
    ProjSpace.topologicalKrullDim_le_of_isClosedImmersion 𝔓'.toProj
  let K := ProjSpace.stdCoverPullback 𝔓'.toProj
  obtain ⟨P, hP, hPev⟩ := OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2
    q K Ft (OModulePresheaf.isCoherent_ofModules_of_locallyTrivial q Ft hFt.exists_trivialization)
    (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial q Ft hFt.exists_trivialization)
    ⊤ (supportedIn_top q Ft) N ((topologicalKrullDim_subspace_le _ _).trans hdim) L
    hL.exists_trivialization
  refine ⟨P, hP, fun n => ?_⟩
  rw [← hPev n]
  congr 1
  have hFLn : Scheme.Modules.IsInvertible (Ft ⊗ L.tensorPow n) :=
    hFt.tensor_monoidalV2 (hL.tensorPow_monoidalV2 n)
  have : (Ft ⊗ L.tensorPow n).IsQuasicoherent :=
    Picard.IsLocallyFreeRankOne.isQuasicoherent (fun x => by
      obtain ⟨U, hx, ⟨e⟩⟩ := hFLn.exists_trivialization x
      exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫ e⟩⟩)
  refine (finsum_congr fun p => ?_).trans
    (CechBridge.eulerChar_ofModules_eq (R := B) (π := q) K (Ft ⊗ L.tensorPow n)).symm
  congr 2
  exact ((DerivedSections.relativeCohomology q p).mapIso
    (pullbackTwistIso _ a ((Scheme.Modules.pullbackComp a (pullback.fst f s)).app 𝓛X) F n ≪≫
      twistTensorPowIso L _ n)).toLinearEquiv.finrank_eq

end Langlands.AlgebraicGeometry.Modules.FibreTwist
