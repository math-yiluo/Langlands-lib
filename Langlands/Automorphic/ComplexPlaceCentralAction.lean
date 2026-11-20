import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Automorphic.PlaceEnvelopingAction
import Langlands.Global.ArchimedeanPlaceEnvelopingAdjoint
import Langlands.Global.ComplexEmbeddingEnveloping
import Langlands.Representation.Archimedean.ComplexStandardCentralCharacter
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction

/-! # Scalar action from complex-place standard modules -/

noncomputable section

universe u

open scoped Classical TensorProduct Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Langlands.Automorphic.OperatorRealization

open NumberField
open Langlands.Global Langlands.Global.ArchimedeanGL
open Langlands.Archimedean Langlands.Archimedean.InfinitesimalCharacter
open Langlands.Archimedean.ComplexGenericLarge Langlands.Archimedean.ComplexStandardCentralCharacter
open Langlands.Automorphic.ComplexPlaceParameter Langlands.LocalFactor.Archimedean
open Langlands.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

private theorem complexPlaceConjugation_of_mem_center (k : Matrix.unitaryGroup (Fin n) ℂ)
    (a : ComplexPlaceEnvelopingAlgebra n)
    (ha : a ∈ Subalgebra.center ℂ (ComplexPlaceEnvelopingAlgebra n)) :
    unitaryMatrixEnvelopingConjugation ℂ n k a = a := by
  let e := LieEnvelopingEquiv.enveloping (tensorLieEquiv (n := n))
  have he : e.toAlgHom.comp (unitaryMatrixEnvelopingConjugation ℂ n k).toAlgHom =
      (envMap (conjLieB (pairUnit k))).comp e.toAlgHom := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro X
    change e (unitaryMatrixEnvelopingConjugation ℂ n k (UniversalEnvelopingAlgebra.ι ℂ X)) =
      envMap (conjLieB (pairUnit k)) (e (UniversalEnvelopingAlgebra.ι ℂ X))
    simp only [unitaryMatrixEnvelopingConjugation_generator, e,
      LieEnvelopingEquiv.enveloping_generator, envMap_ι]
    apply congrArg (UniversalEnvelopingAlgebra.ι ℂ)
    induction X using TensorProduct.inductionOn with
    | tmul c X =>
      rw [unitaryMatrixComplexLieConjugation_tmul, unitaryMatrixRealLieConjugation_apply]
      change tensorEquiv (c ⊗ₜ[ℝ] (k.val * X * k⁻¹.val)) =
        conjLieB (pairUnit k) (tensorEquiv (c ⊗ₜ[ℝ] X))
      simp only [tensorEquiv_tmul, conjLieB_apply, pairUnit_val, pairUnit_inv_val,
        show k⁻¹.val = star k.val from rfl, map_mul, mul_smul_comm, smul_mul_assoc]
    | add X Y hX hY => simp only [map_add, hX, hY]
  apply e.injective
  have hea := Subalgebra.map_center_le_center e.surjective
    (show e a ∈ (Subalgebra.center ℂ _).map e.toAlgHom from ⟨a, ha, rfl⟩)
  exact (AlgHom.congr_fun he a).trans
    (pairFixesCenter_of_det_ne_zero k.val (det_ne_zero_of_unitary k)
      (pairUnit k) (pairUnit_val k) (e a) hea)

variable (S : OperatorRealization F n)

local instance complexPlaceCentralRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance complexPlaceCentralContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance complexPlaceCentralSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance complexPlaceCentralFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance complexPlaceCentralStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance complexPlaceCentralSpaceAddCommGroup :
    AddCommGroup S.Space := Submodule.addCommGroup _

private theorem exists_complexPlaceEnvelopingIntertwiner (v : CP)
    (ds : List ComplexCharacterData) (h : S.HasComplexPlaceParameter v ds) :
    ∃ A : complexStandardKFinite n ds →ₗ[ℂ] S.Space, Function.Injective A ∧
      ∀ a f, A (Langlands.Archimedean.envelopingAction (complexStandardLie n ds) a f) =
        S.envelopingAction (complexPlaceEnvelopingInclusion F n v a) (A f) := by
  obtain ⟨_, A, hA, _, hLie⟩ := h
  refine ⟨A, hA, fun a f => ?_⟩
  change A (Langlands.Archimedean.envelopingAction (complexStandardLie n ds) a f) =
    S.complexPlaceEnvelopingAction v a (A f)
  rw [S.complexPlaceEnvelopingAction_eq_lift]
  refine envelopingAction_intertwine (complexStandardLie n ds) (S.complexPlaceLieAction v)
    A (fun X f => ?_) a f
  have htmul (X : CM) : A (complexStandardLie n ds (1 ⊗ₜ[ℝ] X) f) =
      S.complexPlaceLieAction v (1 ⊗ₜ[ℝ] X) (A f) := by
    obtain ⟨hf, hAf⟩ := hLie X f
    have he : complexStandardLie n ds (1 ⊗ₜ[ℝ] X) f = ⟨_, hf⟩ :=
      Subtype.ext (ComplexSwapJacquet.coe_lie X f)
    rw [he]
    exact hAf
  let left : (ℂ ⊗[ℝ] CM) →ₗ[ℂ] S.Space :=
    (A.comp (LinearMap.applyₗ (R := ℂ) f)).comp (complexStandardLie n ds).toLinearMap
  let right : (ℂ ⊗[ℝ] CM) →ₗ[ℂ] S.Space :=
    (LinearMap.applyₗ (R := ℂ) (A f)).comp (S.complexPlaceLieAction v).toLinearMap
  have he : left = right := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c Y
    have hc : c ⊗ₜ[ℝ] Y = c • ((1 : ℂ) ⊗ₜ[ℝ] Y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc, left.map_smul, right.map_smul]
    exact congrArg (c • ·) (htmul Y)
  exact LinearMap.congr_fun he X

variable [IsTotallyComplex F]

private theorem complexEmbeddingCenterInclusion_val_block (v : CP) (k : Fin 2)
    (z : VermaGL.center n) :
    (complexEmbeddingCenterInclusion F n (complexEmbeddingIndex F (v, k)) z).val =
      complexPlaceEnvelopingInclusion F n v (blockEnveloping n k (z : VermaGL.glU n)) := by
  rw [complexEmbeddingCenterInclusion_val, complexEmbeddingEnvelopingInclusion_place,
    AlgHom.comp_apply]
  have h : LieEnvelopingEquiv.map
      (tensorLieEquiv.symm.toLieHom.comp (ProductLieEnveloping.lieSingle k)) =
      blockEnveloping n k := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro X
    change LieEnvelopingEquiv.map _ (UniversalEnvelopingAlgebra.ι ℂ X) =
      blockEnveloping n k (UniversalEnvelopingAlgebra.ι ℂ X)
    rw [LieEnvelopingEquiv.map_generator, blockEnveloping_ι, blockLie_apply,
      LieHom.comp_apply, LieEquiv.coe_coe, ProductLieEnveloping.lieSingle_apply]
    apply congrArg (fun Y : Fin 2 → CM => UniversalEnvelopingAlgebra.ι ℂ (tensorLieEquiv.symm Y))
    have hsingle (d₁ d₂ : DecidableEq (Fin 2)) :
        @Pi.single (Fin 2) (fun _ => CM) _ d₁ k X =
          @Pi.single (Fin 2) (fun _ => CM) _ d₂ k X :=
      congrArg (fun d => @Pi.single (Fin 2) (fun _ => CM) _ d k X) (Subsingleton.elim d₁ d₂)
    exact hsingle _ _
  rw [h]

private theorem embeddingBlockAction (hS : S.IsIrreducible) (v : CP) (k : Fin 2)
    (ds : List ComplexCharacterData) (hd : S.HasComplexPlaceParameter v ds)
    (μ : Fin n → ℂ)
    (hμ : (ds.map (if k = 0 then ComplexCharacterData.zExponent
      else ComplexCharacterData.zBarExponent)).Perm (List.ofFn fun i => μ i + rho n i))
    (z : VermaGL.center n) :
    S.envelopingAction
        (complexEmbeddingCenterInclusion F n (complexEmbeddingIndex F (v, k)) z).val =
      algebraMap ℂ (Module.End ℂ S.Space) (VermaShifted.upperCharacter n μ z) := by
  let Z := complexEmbeddingCenterInclusion F n (complexEmbeddingIndex F (v, k)) z
  let b := blockEnveloping n k (z : VermaGL.glU n)
  have hZ : Z.val = complexPlaceEnvelopingInclusion F n v b :=
    complexEmbeddingCenterInclusion_val_block v k z
  have hcomm : ∀ (a : automorphicOperatorAlgebra F n) (f : S.Space),
      S.envelopingAction Z.val (S.representation a f) =
        S.representation a (S.envelopingAction Z.val f) := by
    apply S.commute_representation_of_commute
    · intro d f
      exact (S.finiteRepresentation_envelopingAction d Z.val f).symm
    · intro k' f
      have hfix : envelopingConjugation F n k'.val Z.val = Z.val := by
        obtain ⟨p, hp⟩ := k'.property
        change ArchimedeanCompactFactors.toInfiniteAdelicGL F n p = k'.val at hp
        rw [← hp, hZ, envelopingConjugation_complexInclusion,
          complexPlaceConjugation_of_mem_center _ b (blockEnveloping_mem_center n k z)]
      rw [S.compactRepresentation_envelopingAction, hfix]
    · intro a f
      have h : Commute a Z.val := Subalgebra.mem_center_iff.mp Z.property a
      exact LinearMap.congr_fun (h.symm.map S.envelopingAction).eq f
  obtain ⟨c, hc⟩ := S.exists_eq_smul_of_commute hS (S.envelopingAction Z.val) hcomm
  obtain ⟨A, hA, hAb⟩ := exists_complexPlaceEnvelopingIntertwiner S v ds hd
  let : Nontrivial (complexStandardKFinite n ds) := complexStandardNontrivial n ds hd.1
  obtain ⟨f, hf⟩ := exists_ne (0 : complexStandardKFinite n ds)
  have hAf : A f ≠ 0 := fun h => hf (hA (h.trans A.map_zero.symm))
  let value := VermaShifted.upperCharacter n μ z
  have hlocal : Langlands.Archimedean.envelopingAction (complexStandardLie n ds) b f =
      value • f := by
    have h := LinearMap.congr_fun (envelopingAction_blockEnveloping n ds hd.1 k μ hμ z) f
    exact h.trans (Module.algebraMap_end_apply ℂ ℂ _ value f)
  have h : value • A f = c • A f := calc
    _ = A (value • f) := (A.map_smul value f).symm
    _ = A (Langlands.Archimedean.envelopingAction (complexStandardLie n ds) b f) :=
      congrArg A hlocal.symm
    _ = S.envelopingAction (complexPlaceEnvelopingInclusion F n v b) (A f) := hAb b f
    _ = c • A f := (congrArg (fun a => S.envelopingAction a (A f)) hZ.symm).trans (hc _)
  have hvalue : value = c := smul_left_injective ℂ hAf h
  exact LinearMap.ext fun g => (hc g).trans
    ((congrArg (fun t : ℂ => t • g) hvalue.symm).trans
      (Module.algebraMap_end_apply ℂ ℂ _ value g).symm)

/-- Matching shifted weights give the scalar action on the whole irreducible realization
as soon as the actual center character restricts to those block characters. -/
theorem hasInfinitesimalCharacter_of_complexPlaceParameters
    (hS : S.IsIrreducible) (ds : CP → List ComplexCharacterData)
    (hd : ∀ v, S.HasComplexPlaceParameter v (ds v))
    (χ : EnvelopingCenter F n →ₐ[ℂ] ℂ) (μ : EmbeddingIndex F → Fin n → ℂ)
    (hm : MatchesGlobalHighestWeight F n ds μ)
    (hχ : ∀ j z, χ (complexEmbeddingCenterInclusion F n j z) =
      VermaShifted.upperCharacter n (μ j) z) :
    S.HasInfinitesimalCharacter χ := by
  let act := S.envelopingAction.comp (Subalgebra.val (Subalgebra.center ℂ (EnvelopingAlgebra F n)))
  let sc := (Algebra.ofId ℂ (Module.End ℂ S.Space)).comp χ
  have h : act = sc := by
    apply complexEmbeddingCenter_hom_ext F n
    intro j z
    obtain ⟨⟨v, k⟩, rfl⟩ := (complexEmbeddingIndex F).surjective j
    change S.envelopingAction
        (complexEmbeddingCenterInclusion F n (complexEmbeddingIndex F (v, k)) z).val =
      algebraMap ℂ (Module.End ℂ S.Space)
        (χ (complexEmbeddingCenterInclusion F n (complexEmbeddingIndex F (v, k)) z))
    rw [hχ]
    apply embeddingBlockAction S hS v k (ds v) (hd v)
    fin_cases k
    · simpa using (hm v).2.1
    · simpa using (hm v).2.2
  intro z f
  simpa only [act, sc, AlgHom.comp_apply, Subalgebra.val_apply, Algebra.ofId_apply,
    Module.algebraMap_end_apply] using LinearMap.congr_fun (AlgHom.congr_fun h z) f

end Langlands.Automorphic.OperatorRealization
