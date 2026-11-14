import Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistCohomologyStatement
import Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityProof
import Langlands.Cohomology.PerfectComplexVanishing
import Langlands.AlgebraicGeometry.Modules.RelativeSerreVanishingInvertible
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback

/-! # Uniform vanishing of higher fibre cohomology of large twists -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Langlands.Cohomology Langlands.Cohomology.FibreDimension

namespace Langlands.AlgebraicGeometry.Modules

open DerivedSections

attribute [local instance] HasDerivedCategory.standard

namespace FibreTwist

section Twist

variable {X : Scheme.{u}} (𝓛 : X.Modules)

/-- `F(n) ≅ F ⊗ 𝓛^{⊗ n}`. -/
def twistTensorPowIso (F : X.Modules) : (n : ℕ) → twist 𝓛 F n ≅ F ⊗ 𝓛.tensorPow n
  | 0 => (ρ_ F).symm
  | n + 1 => whiskerRightIso (twistTensorPowIso F n) 𝓛 ≪≫ α_ F (𝓛.tensorPow n) 𝓛

/-- Pullback commutes with twisting. -/
def pullbackTwistIso {Y : Scheme.{u}} (φ : Y ⟶ X) {𝓛' : Y.Modules}
    (e : (Scheme.Modules.pullback φ).obj 𝓛 ≅ 𝓛') (F : X.Modules) :
    (n : ℕ) → (Scheme.Modules.pullback φ).obj (twist 𝓛 F n) ≅
      twist 𝓛' ((Scheme.Modules.pullback φ).obj F) n
  | 0 => Iso.refl _
  | n + 1 => Scheme.Modules.pullbackTensorObjIso φ _ _ ≪≫ tensorIso (pullbackTwistIso φ e F n) e

lemma isInvertible_twist {F : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hF : Scheme.Modules.IsInvertible F) : ∀ n : ℕ, Scheme.Modules.IsInvertible (twist 𝓛 F n)
  | 0 => hF
  | n + 1 => (isInvertible_twist h𝓛 hF n).tensor_monoidalV2 h𝓛

end Twist

section Model

open FibreSemicontinuity

/-- A complex and its base change along the identity have isomorphic homology. -/
def homologyBaseChangeIdIso {R : CommRingCat.{u}} (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    K.homology n ≅ ((ModuleComplex.baseChange (CommRingCat.Hom.hom (𝟙 R))).obj K).homology n :=
  HomologicalComplex.homologyMapIso
    (((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId R) (ComplexShape.up ℤ)).app K ≪≫
      (Functor.mapHomologicalComplexIdIso _ _).app K).symm) n

/-- **Fibre model with sections.** As `exists_fibreModel`, and moreover the homology of the model
in degree `n ≥ 0` is the cohomology of the restriction of `F` over `V`. -/
theorem exists_fibreModel_sections {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] [Flat g]
    (F : Y.Modules) (hF : Scheme.Modules.IsInvertible F) {V : T.Opens} (hV : IsAffineOpen V)
    [IsNoetherianRing Γ(T, V)] :
    ∃ K : CochainComplex (ModuleCat.{u} Γ(T, V)) ℤ, ModuleComplex.IsStrictlyPerfect K ∧
      (∀ (t : T) (ht : t ∈ V),
        (∀ n : ℕ, Nonempty (fibreCohomology g t F n ≅
          ((ModuleComplex.baseChange (T.evaluation V t ht).hom).obj K).homology n)) ∧
        (∀ n : ℤ, n < 0 → IsZero
          (((ModuleComplex.baseChange (T.evaluation V t ht).hom).obj K).homology n))) ∧
      ∀ n : ℕ, Nonempty (K.homology n ≅ (relativeCohomology (affineRestrict g hV) n).obj
        ((Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj F)) := by
  have : Flat (affineRestrict g hV) := by
    delta affineRestrict
    infer_instance
  obtain ⟨K, hK, hmod⟩ := exists_perfectModel (affineRestrict g hV)
    ((Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj F) (hF.pullback _)
  refine ⟨K, hK, fun t ht => ?_, fun n => ?_⟩
  · obtain ⟨e⟩ := hmod (T.residueField t) (T.evaluation V t ht)
    have hsq : IsPullback (pullback.fst (affineRestrict g hV) (Spec.map (T.evaluation V t ht)) ≫
        (g ⁻¹ᵁ V).ι) (pullback.snd (affineRestrict g hV) (Spec.map (T.evaluation V t ht))) g
        (T.fromSpecResidueField t) := by
      have := (IsPullback.of_hasPullback (affineRestrict g hV)
        (Spec.map (T.evaluation V t ht))).paste_horiz (isPullback_affineRestrict g hV)
      rwa [SpecMap_evaluation_fromSpec hV t ht] at this
    refine ⟨fun n => ?_, fun n hn => ?_⟩
    · obtain ⟨e'⟩ := nonempty_relativeCohomology_iso_chosenPullback hsq F n
      exact ⟨e'.symm ≪≫ (relativeCohomology _ n).mapIso
        ((Scheme.Modules.pullbackComp _ _).app F).symm ≪≫
        (DerivedPlus.homologyIsoOfIsoDerivedComplex _ e n).symm⟩
    · refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ n).app _).symm
      exact IsZero.of_iso (DerivedPlus.isZero_homology_of_neg _ _ hn)
        ((DerivedCategory.homologyFunctor _ n).mapIso e)
  · obtain ⟨e₀⟩ := hmod Γ(T, V) (𝟙 _)
    have hsq₀ : IsPullback (𝟙 _) (affineRestrict g hV) (affineRestrict g hV)
        (Spec.map (𝟙 Γ(T, V))) := by
      rw [Spec.map_id]
      exact IsPullback.id_horiz _
    obtain ⟨c₀⟩ := nonempty_relativeCohomology_iso_chosenPullback hsq₀
      ((Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj F) n
    exact ⟨homologyBaseChangeIdIso K n ≪≫ DerivedPlus.homologyIsoOfIsoDerivedComplex _ e₀ n ≪≫
      c₀.symm ≪≫ (relativeCohomology _ n).mapIso
        ((Scheme.Modules.pullbackId _).app ((Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj F))⟩

end Model

section Vanishing

open FibreSemicontinuity

/-- **Fibre vanishing from a model.** If the higher homology of a strictly perfect model
vanishes, then so does the higher cohomology of every fibre it computes. -/
lemma isZero_fibreCohomology_of_model {Y T : Scheme.{u}} (g : Y ⟶ T) (F : Y.Modules)
    {V : T.Opens} {K : CochainComplex (ModuleCat.{u} Γ(T, V)) ℤ}
    (hK : ModuleComplex.IsStrictlyPerfect K)
    (hfib : ∀ (t : T) (ht : t ∈ V) (n : ℕ), Nonempty (fibreCohomology g t F n ≅
      ((ModuleComplex.baseChange (T.evaluation V t ht).hom).obj K).homology n))
    (hpos : ∀ n : ℕ, 0 < n → IsZero (K.homology n)) (t : T) (ht : t ∈ V) (p : ℕ) (hp : 0 < p) :
    IsZero (fibreCohomology g t F p) := by
  have : ∀ i, Module.Finite Γ(T, V) (K.X i) := fun i => (hK.2 i).1
  have : ∀ i, Module.Projective Γ(T, V) (K.X i) := fun i => (hK.2 i).2
  obtain ⟨⟨a, b, -, hb⟩, -⟩ := hK
  have hpos' : ∀ i : ℤ, 0 < i → IsZero (K.homology i) := by
    intro i hi
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
    exact hpos m (by omega)
  have hdim := homologyDim_eq_zero_of_isZero_homology K
    (fun n hn => CochainComplex.isZero_of_isStrictlyLE K b n hn) hpos' p (by omega)
    (kerPrime (T.evaluation V t ht).hom)
  rw [← finrank_homology_baseChange_eq] at hdim
  have := finite_homology_baseChange K (T.evaluation V t ht).hom p
  have hsub : Subsingleton (((ModuleComplex.baseChange (T.evaluation V t ht).hom).obj K).homology p) :=
    Module.finrank_zero_iff.1 (by exact_mod_cast hdim)
  obtain ⟨e⟩ := hfib t ht p
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) e

end Vanishing

section Uniform

open FibreSemicontinuity

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Clause 1 of `ProjectiveFibreTwistCohomologyStatement`.** Every point of `T` has a
neighbourhood `V` and `n₀` such that `Hᵖ(X_{t'}, F(n)_{t'}) = 0` for `t' ∈ V`, `n ≥ n₀`, `p > 0`. -/
theorem uniformVanishing (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (𝓛X : X.Modules) (N : ℕ) (𝔓 : 𝓛X.ProjPresentation f N)
    [IsProper f] [Flat f] (h𝓛 : Scheme.Modules.IsInvertible 𝓛X) [IsClosedImmersion 𝔓.toProj]
    (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ Spec (CommRingCat.of A))
    (F : (pullback f s).Modules) (hF : Scheme.Modules.IsInvertible F) (t₀ : T) :
    ∃ V : T.Opens, t₀ ∈ V ∧ ∃ n₀ : ℕ, ∀ t' ∈ V, ∀ n p : ℕ, n₀ ≤ n → 0 < p →
      IsZero (fibreCohomology (pullback.snd f s) t'
        (twist ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) F n) p) := by
  obtain ⟨V, hV, ht₀, -⟩ := exists_isAffineOpen_mem_and_subset (show t₀ ∈ (⊤ : T.Opens) from trivial)
  have : IsNoetherianRing Γ(T, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let gT := pullback.snd f s
  let ι := (gT ⁻¹ᵁ V).ι
  let gV := affineRestrict gT hV
  have : Flat gV := by
    show Flat (affineRestrict gT hV)
    delta affineRestrict
    infer_instance
  -- the presentation over the affine piece
  let φ : CommRingCat.of A ⟶ Γ(T, V) := Spec.preimage (hV.fromSpec ≫ s)
  let : Algebra A Γ(T, V) := φ.hom.toAlgebra
  have sq : IsPullback (ι ≫ pullback.fst f s) gV f
      (Spec.map (CommRingCat.ofHom (algebraMap A Γ(T, V)))) := by
    have h := (isPullback_affineRestrict gT hV).paste_horiz (IsPullback.of_hasPullback f s)
    have hφ : Spec.map (CommRingCat.ofHom (algebraMap A Γ(T, V))) = hV.fromSpec ≫ s :=
      Spec.map_preimage (hV.fromSpec ≫ s)
    rw [hφ]
    exact h
  obtain ⟨𝔓', -, -, hpb⟩ := 𝔓.exists_baseChange_of_isPullback sq
  have : IsClosedImmersion 𝔓'.toProj :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb ‹_›
  let L := (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X
  have hL : Scheme.Modules.IsInvertible L := h𝓛.pullback _
  have hFY : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback ι).obj F) := hF.pullback _
  obtain ⟨d₀, hd₀⟩ := CechBridge.exists_isZero_relativeCohomology_tensor_tensorPow 𝔓' hL
    ((Scheme.Modules.pullback ι).obj F) hFY
  refine ⟨V, ht₀, d₀, fun t' ht' n p hn hp => ?_⟩
  have hFn := FibreTwist.isInvertible_twist _ (h𝓛.pullback (pullback.fst f s)) hF n
  obtain ⟨K, hK, hfib, hsec⟩ := exists_fibreModel_sections gT
    (twist ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) F n) hFn hV
  refine isZero_fibreCohomology_of_model gT _ hK (fun t ht m => (hfib t ht).1 m) (fun m hm => ?_)
    t' ht' p hp
  obtain ⟨e⟩ := hsec m
  refine IsZero.of_iso ?_ e
  refine IsZero.of_iso (hd₀ n hn m hm) ((relativeCohomology gV m).mapIso ?_)
  exact pullbackTwistIso _ ι ((Scheme.Modules.pullbackComp ι (pullback.fst f s)).app 𝓛X) F n ≪≫
    twistTensorPowIso L _ n

end Uniform

end FibreTwist

end Langlands.AlgebraicGeometry.Modules
