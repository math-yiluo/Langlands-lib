import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionEvaluationSections
import Langlands.AbelianScheme.PolarizedFiniteLevel.ProjectiveFrameSelection
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicSectionNondegeneracy
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingStatement
import Langlands.AlgebraicGeometry.LinearSystem.FieldPointHyperplane
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusIsoLocus
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicDirectImageProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicProjectiveEvaluation
import Langlands.AlgebraicGeometry.LinearSystem.CoefficientComparison
import Langlands.AlgebraicGeometry.Picard.FiniteFlatPointFibreSections
import Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentCore
import Langlands.AlgebraicGeometry.Modules.FiniteLocalBasisDescent
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Projective frames of torsion evaluations over an algebraically closed field -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.LinearSystem
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.ProjectiveSpace
open Langlands.AlgebraicGeometry.Modules.DerivedSections

universe u

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

/-- After pulling back along any morphism `y`, the full cubic evaluation sends the
pulled-back base section `σ` to the pullback of the cubic section `σ` along `y`. -/
theorem Datum.pullbackEvaluation_app_top (a : Datum P S g d n) {T : Scheme.{u}}
    (y : T ⟶ a.abelian.X.left) (σ : Γ(a.rigidificationModule, ⊤)) :
    ((Scheme.Modules.pullbackComp y a.abelian.X.hom).inv.app a.rigidificationModule ≫
        (Scheme.Modules.pullback y).map a.cubicEvaluationAdjoint).app ⊤
      (sectionPullbackLE (y ≫ a.abelian.X.hom) a.rigidificationModule le_top σ) =
      pullbackSection y a.cubicBundle.obj σ := by
  rw [pullbackSection_eq_sectionPullback, ← sectionPullbackLE_self]
  have e3 := pullbackComp_inv_sectionPullbackLE y a.abelian.X.hom
    a.rigidificationModule (W := ⊤) (le_refl (a.abelian.X.hom ⁻¹ᵁ ⊤)) le_top le_top σ
  have e4 := pullback_map_app_sectionPullbackLE y a.cubicEvaluationAdjoint
    (U := ⊤) (V := a.abelian.X.hom ⁻¹ᵁ ⊤) le_top
    (sectionPullbackLE a.abelian.X.hom a.rigidificationModule
      (le_refl (a.abelian.X.hom ⁻¹ᵁ ⊤)) σ)
  have e5 : a.cubicEvaluationAdjoint.app (a.abelian.X.hom ⁻¹ᵁ ⊤)
      (sectionPullbackLE a.abelian.X.hom a.rigidificationModule
        (le_refl (a.abelian.X.hom ⁻¹ᵁ ⊤)) σ) = σ := by
    rw [sectionPullbackLE_self, Datum.cubicEvaluationAdjoint_eq_evaluationAdjoint,
      Langlands.AlgebraicGeometry.ProjectiveBundle.evaluationAdjoint_sectionPullback]
    rfl
  rw [e5] at e4
  calc _ = ((Scheme.Modules.pullback y).map a.cubicEvaluationAdjoint).app ⊤
        (((Scheme.Modules.pullbackComp y a.abelian.X.hom).inv.app
          a.rigidificationModule).app ⊤
          (sectionPullbackLE (y ≫ a.abelian.X.hom) a.rigidificationModule le_top σ)) := rfl
    _ = _ := by rw [e3, e4]

/-- If the full cubic evaluation of a datum over an affine base is surjective, then
some global section of the cubic direct image has nonzero pullback along any
field-valued point of the abelian scheme. -/
theorem Datum.exists_pullbackSection_ne_zero (a : Datum P S g d n) [IsAffine S]
    [a.rigidificationModule.IsQuasicoherent] [Epi a.cubicEvaluationAdjoint]
    {κ : Type u} [Field κ] (y : Spec (CommRingCat.of κ) ⟶ a.abelian.X.left) :
    ∃ σ : Γ(a.rigidificationModule, ⊤), pullbackSection y a.cubicBundle.obj σ ≠ 0 := by
  classical
  let r := y ≫ a.abelian.X.hom
  let M := a.rigidificationModule
  let Ly := (LineBundle.pullback y).obj a.cubicBundle
  let θ : (Scheme.Modules.pullback r).obj M ⟶ Ly.obj :=
    (Scheme.Modules.pullbackComp y a.abelian.X.hom).inv.app M ≫
      (Scheme.Modules.pullback y).map a.cubicEvaluationAdjoint
  by_contra hz
  push Not at hz
  have hθzero (s : Γ((Scheme.Modules.pullback r).obj M, ⊤)) : θ.app ⊤ s = 0 := by
    obtain ⟨z, rfl⟩ := (pullbackTensorMap_bijective r M (le_top) (isAffineOpen_top _)
      (isAffineOpen_top S)).surjective s
    induction z using TensorProduct.inductionOn with
    | tmul c σ =>
      rw [pullbackTensorMap_tmul, Scheme.Modules.Hom.app_smul]
      erw [a.pullbackEvaluation_app_top y σ]
      rw [hz σ, smul_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  have : Epi θ := by
    dsimp only [θ]
    infer_instance
  have hsurj := Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.surjective_app_of_epi θ ⊤ (isAffineOpen_top _)
  obtain ⟨e⟩ := fieldLineBundleTriviality κ Ly
  have h1 : (1 : Γ(Spec (CommRingCat.of κ), ⊤)) ≠ 0 := by
    intro h
    have hh := congrArg (Scheme.ΓSpecIso (CommRingCat.of κ)).hom h
    exact one_ne_zero (by simpa only [map_one, map_zero] using hh)
  obtain ⟨s, hs⟩ := hsurj (e.inv.app ⊤ (1 : Γ(Spec (CommRingCat.of κ), ⊤)))
  have hezero : e.inv.app ⊤ (1 : Γ(Spec (CommRingCat.of κ), ⊤)) = 0 :=
    hs.symm.trans (hθzero s)
  apply h1
  apply (ConcreteCategory.bijective_of_isIso (e.inv.app ⊤)).injective
  simpa only [map_zero] using hezero

variable {K : Type u} [Field K]

/-- Over a field, surjectivity of the full cubic evaluation makes every basis of the
global cubic sections base-point free. -/
theorem Datum.basis_generates (a : Datum P (Spec (CommRingCat.of K)) g d n)
    [a.rigidificationModule.IsQuasicoherent] [Epi a.cubicEvaluationAdjoint] {m : ℕ}
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj)) :
    ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i) := by
  intro x
  by_contra hx
  push Not at hx
  obtain ⟨σ, hσ⟩ := a.exists_pullbackSection_ne_zero
    (κ := a.abelian.X.left.residueField x) (a.abelian.X.left.fromSpecResidueField x)
  apply hσ
  let F := (basisHyperplaneSectionEquiv a.abelian.X.hom basis).symm
    (show (relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj from σ)
  have hσF : (show GlobalSections a.cubicBundle.obj from σ) =
      linComb a.abelian.X.hom (fun i ↦ basis i) ((degreeOneBasis K m).equivFun F) := by
    rw [← basisHyperplaneSectionEquiv_eq_linComb]
    simp only [F, LinearEquiv.apply_symm_apply]
  change pullbackSection _ a.cubicBundle.obj (show GlobalSections a.cubicBundle.obj from σ) = 0
  rw [hσF, linComb, pullbackSection_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [pullbackSection_smul]
  have hi := hx i
  rw [mem_nonvanishingLocus, not_not] at hi
  have hi' : pullbackSection (a.abelian.X.left.fromSpecResidueField x) a.cubicBundle.obj
      (basis i) = 0 := hi
  rw [hi', smul_zero]

section ProductSections

variable {R : CommRingCat.{u}} {ι : Type} (N : ι → (Spec R).Modules) [HasProduct N]

/-- Global sections over a spectrum of a product of module sheaves are the product of
the global sections. -/
def moduleSpecΓPiIso :
    moduleSpecΓFunctor.obj (∏ᶜ N) ≅ ModuleCat.of R (∀ j, moduleSpecΓFunctor.obj (N j)) :=
  PreservesProduct.iso moduleSpecΓFunctor N ≪≫ ModuleCat.piIsoPi _

lemma moduleSpecΓPiIso_hom_apply (t : moduleSpecΓFunctor.obj (∏ᶜ N)) (j : ι) :
    (moduleSpecΓPiIso N).hom t j = moduleSpecΓFunctor.map (Pi.π N j) t := by
  have h1 : (moduleSpecΓPiIso N).hom t j =
      Pi.π (fun j => moduleSpecΓFunctor.obj (N j)) j
        ((PreservesProduct.iso moduleSpecΓFunctor N).hom t) := by
    rw [← ModuleCat.piIsoPi_hom_ker_subtype]
    rfl
  rw [h1, PreservesProduct.iso_hom, ← ConcreteCategory.comp_apply, piComparison_comp_π]

end ProductSections

/-- A line bundle on the spectrum of a field has one-dimensional global sections. -/
lemma finrank_moduleSpecΓ_lineBundle (L : LineBundle (Spec (CommRingCat.of K))) :
    Module.finrank K (moduleSpecΓFunctor.obj L.obj) = 1 := by
  have h1 := FiniteFlatPointFibre.finrank_relativeGlobalSections_lineBundle
    (𝟙 (Spec (CommRingCat.of K))) L
  rw [FiniteFlatPointFibre.finrank_relativeGlobalSections_structureSheaf _
    (IsLocalRing.closedPoint K), Scheme.Hom.finrank_eq_one_of_isIso] at h1
  rw [Pi.one_apply] at h1
  exact (moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.pushforwardId _).app L.obj)).toLinearEquiv.finrank_eq.symm.trans h1

/-- The global cubic sections of a datum over an algebraically closed field have
dimension `6^g*d`. -/
lemma Datum.finrank_cubicSections [IsAlgClosed K] (a : Datum P (Spec (CommRingCat.of K)) g d n)
    (hd : 0 < d) :
    Module.finrank K ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj) =
      cubicProjectiveDimension g d + 1 := by
  rw [cubicProjectiveDimension_add_one g d hd, ← (cubicFibreCohomology P K g d n hd a).2]
  exact ((relativeCohomologyZeroIso a.abelian.X.hom).app
    a.cubicBundle.obj).toLinearEquiv.finrank_eq.symm

/-- Lefschetz's theorem makes the cubic section map of any generating basis a closed
immersion into polynomial projective space. -/
lemma Datum.isClosedImmersion_cubicSectionMap (hL : CubicFieldEmbeddingStatement.{u})
    (hd : 0 < d) (a : Datum P (Spec (CommRingCat.of K)) g d n) {m : ℕ}
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i)) :
    IsClosedImmersion (a.cubicSectionMap basis hs) := by
  have h1 := (hL P K g d n hd a).2 m basis hs
  have h2 := relativeLinearSystemMap_toPolynomial a.abelian.X.hom
    (𝟙 (Spec (CommRingCat.of K))) hs
  have h3 : IsIso (Langlands.AlgebraicGeometry.RelativeProjectiveSpace.toPolynomial m
      (𝟙 (Spec (CommRingCat.of K)))) := by
    rw [Langlands.AlgebraicGeometry.RelativeProjectiveSpace.toPolynomial,
      Langlands.AlgebraicGeometry.RelativeProjectiveSpace.map_id]
    infer_instance
  have h4 : IsClosedImmersion (linearSystemMap (a.abelian.X.hom ≫ 𝟙 _) hs) := by
    rw [← h2]
    infer_instance
  rw [Category.comp_id] at h4
  exact h4

/-- The torsion point with coefficients `r` is the geometric fibre point with the same
coordinates. -/
lemma Datum.fibreCoordinates_left [IsAlgClosed K]
    (a : Datum P (Spec (CommRingCat.of K)) g d n) (r : Fin (2 * g) → ZMod n) :
    (Additive.toMul (a.level.fibreCoordinates K (𝟙 _) r)).val.left = a.torsionPoint r := by
  rw [← a.level.enumerateTuple_fibre K (𝟙 _) r]
  change (Over.homMk (𝟙 _) _ ≫
    (Additive.toMul (enumerateTuple a.level.sections r)).val).left = _
  rw [Over.comp_left]
  exact Category.id_comp _

/-- A frame evaluation over a field is an isomorphism once the joint evaluation of
global sections at the remaining torsion points is bijective. -/
lemma Datum.isIso_frameEvaluation_of_bijective
    (a : Datum P (Spec (CommRingCat.of K)) g d n)
    [a.rigidificationModule.IsQuasicoherent] {m : ℕ}
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (k : Fin (m + 2))
    (h : Function.Bijective
      (fun (s : Γ(a.rigidificationModule, ⊤)) (j : {j : Fin (m + 2) // j ≠ k}) =>
        (a.torsionEvaluation (ρ j)).app ⊤ s)) :
    IsIso (a.frameEvaluation ρ k) := by
  have := Langlands.AlgebraicGeometry.Modules.isFinitePresentation_of_hasFiniteLocalBasis _
    (a.hasFiniteLocalBasis_frameTarget ρ k)
  apply Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentCore.isIso_of_bijective_app_top
  let N := fun j : {j : Fin (m + 2) // j ≠ k} =>
    (Scheme.Modules.pullback (a.torsionPoint (ρ j))).obj a.cubicBundle.obj
  have hcomp : (fun s => (moduleSpecΓPiIso N).hom ((a.frameEvaluation ρ k).app ⊤ s)) =
      fun (s : Γ(a.rigidificationModule, ⊤)) (j : {j : Fin (m + 2) // j ≠ k}) =>
        (a.torsionEvaluation (ρ j)).app ⊤ s := by
    funext s j
    rw [moduleSpecΓPiIso_hom_apply]
    change ((a.frameEvaluation ρ k ≫ Pi.π N j).app ⊤) s = _
    rw [Datum.frameEvaluation, Pi.lift_comp_π]
  have hb : Function.Bijective (moduleSpecΓPiIso N).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [← hcomp] at h
  exact (Function.Bijective.of_comp_iff' hb _).mp h

/-- A frame all of whose evaluations are isomorphisms has the whole base as frame
locus. -/
lemma Datum.frameLocus_eq_top_of_isIso {S : Scheme.{u}} (a : Datum P S g d n) {m : ℕ}
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (h : ∀ k, IsIso (a.frameEvaluation ρ k)) :
    a.frameLocus ρ = ⊤ := by
  apply top_unique
  apply le_sSup
  intro k
  have := h k
  infer_instance

/-- **Frames over an algebraically closed field.** Assume Lefschetz's theorem, let `n`
be positive and invertible in the algebraically closed field `K`, and let `n^(2g)`
exceed `m + 1` times the uniform hyperplane bound, where `m + 1 = 6^g d`. Then some
choice of `m + 2` torsion indices makes every frame evaluation an isomorphism, so
the frame locus is the whole base. -/
theorem Datum.exists_frameLocus_eq_top [IsAlgClosed K] (hL : CubicFieldEmbeddingStatement.{u})
    (a : Datum P (Spec (CommRingCat.of K)) g d n) (hg : 0 < g) (hd : 0 < d) (hn : 0 < n)
    (hnK : (n : K) ≠ 0)
    (hsize : (cubicProjectiveDimension g d + 1) *
      (6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2)) < n ^ (2 * g)) :
    ∃ ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n,
      a.frameLocus ρ = ⊤ := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  have hFP := Langlands.AlgebraicGeometry.Modules.isFinitePresentation_of_hasFiniteLocalBasis _
    (hasFiniteLocalBasis_of_isLocallyFreeOfRank
      (cubicDirectImage P (Spec (CommRingCat.of K)) g d n hd a).1)
  have : Epi a.cubicEvaluationAdjoint := (hL P K g d n hd a).1
  let V := (relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj
  have hV : Module.finrank K V = cubicProjectiveDimension g d + 1 := a.finrank_cubicSections hd
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  let β : Module.Basis (Fin (cubicProjectiveDimension g d + 1)) K V :=
    Module.finBasisOfFinrankEq K V hV
  have hs := a.basis_generates β
  have hclosed := a.isClosedImmersion_cubicSectionMap hL hd β hs
  let W : (Fin (2 * g) → ZMod n) → ModuleCat.{u} K := fun r =>
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (a.torsionPoint r)).obj a.cubicBundle.obj)
  have hW : ∀ r, Module.finrank K (W r) = 1 := fun r =>
    finrank_moduleSpecΓ_lineBundle ((LineBundle.pullback (a.torsionPoint r)).obj a.cubicBundle)
  have hWfin : ∀ r, FiniteDimensional K (W r) := fun r =>
    Module.finite_of_finrank_eq_succ (hW r)
  let e : ∀ r, W r ≃ₗ[K] K := fun r =>
    LinearEquiv.ofFinrankEq _ _ ((hW r).trans (Module.finrank_self K).symm)
  let ℓ : ∀ r, V →ₗ[K] W r := fun r => (moduleSpecΓFunctor.map (a.torsionEvaluation r)).hom
  have hℓ : ∀ r (s : V), ℓ r s = 0 ↔ VanishesAlong a.cubicBundle (a.torsionPoint r) s := by
    intro r s
    change (a.torsionEvaluation r).app ⊤ s = 0 ↔
      pullbackSection (a.torsionPoint r) a.cubicBundle.obj s = 0
    rw [a.torsionEvaluation_app_top]
  let v : (Fin (2 * g) → ZMod n) → Module.Dual K V := fun r => (e r).toLinearMap ∘ₗ ℓ r
  have hbound : HyperplaneBound (K := K) v
      (6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2)) := by
    intro Λ hΛ
    obtain ⟨s, rfl⟩ := (Module.evalEquiv K V).surjective Λ
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hΛ (map_zero _)
    let F := (basisHyperplaneSectionEquiv a.abelian.X.hom β).symm s
    have hF : (F : ProjectiveCoordinateRing K (cubicProjectiveDimension g d)) ≠ 0 := by
      intro h
      apply hs0
      have hF0 : F = 0 := Subtype.ext h
      have h2 := congrArg (basisHyperplaneSectionEquiv a.abelian.X.hom β) hF0
      simpa only [F, LinearEquiv.apply_symm_apply, LinearEquiv.map_zero] using h2
    have hsF : (show GlobalSections a.cubicBundle.obj from s) =
        linComb a.abelian.X.hom (fun i ↦ β i) ((degreeOneBasis K _).equivFun F) := by
      rw [← basisHyperplaneSectionEquiv_eq_linComb]
      simp only [F, LinearEquiv.apply_symm_apply]
    have key : ∀ r, (Module.evalEquiv K V s) (v r) = 0 ↔
        (F : ProjectiveCoordinateRing K _) ∈ ((a.cubicSectionMap β hs)
          ((Additive.toMul (a.level.fibreCoordinates K (𝟙 _) r)).val.left
            (IsLocalRing.closedPoint K))).asHomogeneousIdeal := by
      intro r
      have h1 := vanishesAlong_linComb_iff a.abelian.X.hom (a.torsionPoint r)
        (fun i ↦ β i) hs ((degreeOneBasis K _).equivFun F)
      rw [← degreeOneBasis_expansion F, ← hsF] at h1
      rw [a.fibreCoordinates_left r]
      change (e r) (ℓ r s) = 0 ↔ _
      rw [LinearEquiv.map_eq_zero_iff]
      exact (hℓ r s).trans h1
    calc Nat.card {r // (Module.evalEquiv K V s) (v r) = 0}
        = Nat.card (TorsionHyperplaneSections (n := n) (a.cubicSectionMap β hs) F) :=
          Nat.card_congr ((Equiv.subtypeEquivRight key).trans
            (a.level.hyperplaneCoordinateEquiv _ F))
      _ ≤ _ := a.cubicSectionMap_torsionHyperplane_bound β cubicTorsionHyperplaneBound
          hg hd hn hnK hs hclosed F hF
  have hcard : Fintype.card (Fin (2 * g) → ZMod n) = n ^ (2 * g) := by
    simp [ZMod.card]
  obtain ⟨ρ, hρ⟩ := hbound.exists_frame (Subspace.dual_finrank_eq.trans hV)
    (by rwa [hcard])
  refine ⟨ρ, a.frameLocus_eq_top_of_isIso ρ fun k => ?_⟩
  apply a.isIso_frameEvaluation_of_bijective ρ k
  let Ψ : V →ₗ[K] ((j : {j : Fin (cubicProjectiveDimension g d + 2) // j ≠ k}) → W (ρ j)) :=
    LinearMap.pi fun j => ℓ (ρ j)
  have hcardk : Fintype.card {j : Fin (cubicProjectiveDimension g d + 2) // j ≠ k} =
      Module.finrank K (Module.Dual K V) := by
    simp [Fintype.card_subtype_compl, Subspace.dual_finrank_eq, hV]
  have hspan := (hρ k).span_eq_top_of_card_eq_finrank' hcardk
  have hinj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).mpr fun s hs0 => ?_
    rw [← Module.forall_dual_apply_eq_zero_iff K s]
    intro φ
    have hφ : φ ∈ Submodule.span K
        (Set.range fun j : {j : Fin (cubicProjectiveDimension g d + 2) // j ≠ k} =>
          v (ρ j)) := by
      rw [hspan]
      exact Submodule.mem_top
    have hle : Submodule.span K
        (Set.range fun j : {j : Fin (cubicProjectiveDimension g d + 2) // j ≠ k} =>
          v (ρ j)) ≤ LinearMap.ker (Module.Dual.eval K V s) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
      have hj : ℓ (ρ j) s = 0 := congrFun hs0 j
      change (e (ρ j)) (ℓ (ρ j) s) = 0
      rw [hj, map_zero]
    exact LinearMap.mem_ker.mp (hle hφ)
  have hfr : Module.finrank K V = Module.finrank K
      ((j : {j : Fin (cubicProjectiveDimension g d + 2) // j ≠ k}) → W (ρ j)) := by
    rw [(LinearEquiv.piCongrRight
        fun j : {j : Fin (cubicProjectiveDimension g d + 2) // j ≠ k} => e (ρ j)).finrank_eq,
      Module.finrank_fintype_fun_eq_card, hcardk, Subspace.dual_finrank_eq]
  have hbij : Function.Bijective Ψ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj⟩
  exact hbij

end Langlands.AbelianScheme.PolarizedFiniteLevel
