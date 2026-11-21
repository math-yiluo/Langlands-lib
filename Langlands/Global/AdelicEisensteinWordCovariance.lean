import Langlands.Global.AdelicBlockHolomorphicOperatorActions
import Langlands.Global.AdelicEisensteinConvergentOperators
import Langlands.Global.EisensteinConvergenceAnchors

/-! # Covariance of holomorphic operator words on a common convergence region -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry NumberField Filter
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace Langlands.Global.EisensteinJet

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open AdelicGroupPoints GeneralLinearGroupPoints InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type w} [AddCommGroup V] [Module ℂ V]

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance wordGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local notation "Adeles" => AdelicGroupPoints F GLG
local notation "ScalarForms" => LinearMap.range (finitePlotSmoothEvaluation F GLG)
local notation "Operators" => FreeOperatorAlgebra F n
local notation "Enveloping" => ArchimedeanGL.EnvelopingAlgebra F n
local notation "RealLie" => ArchimedeanGL.RealLieAlgebra F n
local notation "generator" => ArchimedeanGL.envelopingGenerator F n
local notation "realGenerator" => fun X => generator (ArchimedeanGL.complexify F n X)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Pair the operators on a parameter family of inducing sections with the
concrete operators on the scalar values of finite-smooth rational functions. -/
def sectionOperatorPair (T : E → Operators →ₐ[ℂ] Module.End ℂ V) :
    Operators →ₐ[ℂ] ((E → Module.End ℂ V) × Module.End ℂ ScalarForms) :=
  (AlgHom.pi T).prod ((scalarFiniteSmoothOperatorAction F n).comp (freeOperatorProjection F n))

omit [NumberField F] in
private def realLieAction
    (D : Enveloping →ₐ[ℂ] Module.End ℂ V) (v : V) : RealLie →ₗ[ℝ] V :=
  (((LinearMap.applyₗ (R := ℂ) v).comp (D.toLinearMap.comp
    (ArchimedeanGL.envelopingGenerator F n).toLinearMap)).restrictScalars ℝ).comp
    (ArchimedeanGL.complexify F n).toLinearMap

set_option backward.isDefEq.respectTransparency false in
omit [NumberField F] in
private theorem enveloping_mem_subalgebra {A : Type*} [Ring A] [Algebra ℂ A]
    (S : Subalgebra ℂ A) (D : Enveloping →ₐ[ℂ] A) (hD : ∀ X, D (realGenerator X) ∈ S)
    (a : Enveloping) : D a ∈ S := by
  obtain ⟨b, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ArchimedeanGL.ComplexLieAlgebra F n)) a
  change D (UniversalEnvelopingAlgebra.mkAlgHom ℂ (ArchimedeanGL.ComplexLieAlgebra F n) b) ∈ S
  induction b using TensorAlgebra.induction with
  | algebraMap z =>
    exact (by simpa only [AlgHom.commutes] using S.algebraMap_mem z)
  | «ι» Z =>
    change D (generator Z) ∈ S
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      have hz : z ⊗ₜ[ℝ] X = z • ArchimedeanGL.complexify F n X := by
        rw [ArchimedeanGL.complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hz, map_smul, map_smul]
      exact S.smul_mem (hD X) z
    | add X Y hX hY => simpa only [map_add] using S.add_mem hX hY
  | mul a b ha hb => simpa only [map_mul] using S.mul_mem ha hb
  | add a b ha hb => simpa only [map_add] using S.add_mem ha hb

/-- Compact majorants and smooth outputs eventually for each fixed section,
together with the deformed generator formulas, give covariance for every
free operator on each finite holomorphic family. -/
theorem eventually_scalarAutomorphicOperator_eisensteinSeries_word
    {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
    {p : P ⟶ GLG} [IsClosedImmersion p.hom.hom.left]
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K)
    {d : ℕ} (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (ℱ : Filter E) (e : E → ComplexCharacterParameter F P)
    (j : V →ₗ[ℂ] (Adeles → ℂ))
    (hGood : ∀ v, ∀ᶠ t in ℱ, j v ∈ smoothConvergenceSections F GLG hK (e t))
    (hH : hK.HasSmoothHeightPairings hsmooth)
    (hSmooth : letI := fun q : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F q
      letI := smoothChartedSpace F GLG hsmooth
      ∀ v : V, ∀ b : FiniteAdelicGroupPoints F GLG,
        ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun a => j v (pair F GLG a b)))
    (R : E → Representation ℂ (FiniteAdelicGL F n) V)
    (C : Representation ℂ (standardInfiniteCompact F n) V)
    (D : E → Enveloping →ₐ[ℂ] Module.End ℂ V)
    (hRhol : ∀ g v, (fun t => R t g v) ∈ finiteHolomorphicSections E V)
    (hDhol : ∀ X v, (fun t => D t (realGenerator X) v) ∈ finiteHolomorphicSections E V)
    (hR : ∀ t g v, j (R t g v) = hK.parameterRightAction (e t)
      (ofFinite F GLG ((finiteHomeomorph F n).symm g)) (j v))
    (hC : ∀ k v, j (C k v) = fun x : Adeles =>
      j v (x * ofInfinite F GLG ((infiniteHomeomorph F n).symm k.val)))
    (hKinf : ∀ k : standardInfiniteCompact F n,
      ofInfinite F GLG ((infiniteHomeomorph F n).symm k.val) ∈ K)
    (hD : letI := fun q : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F q
      letI := smoothChartedSpace F GLG hsmooth
      ∀ t X v, j (D t (realGenerator X) v) = hK.parameterDirectionalSection hsmooth (e t)
        ((infiniteRealLieAlgebraEquiv F n hsmooth).symm X) (j v))
    (a : Operators) (f : E → V) (hf : f ∈ finiteHolomorphicSections E V) :
    ∀ᶠ t in ℱ, scalarAutomorphicOperator F n (freeOperatorProjection F n a)
        (hK.eisensteinSeries (j (f t)) (e t)) =
      hK.eisensteinSeries (j (sectionOperatorAction R C D t a (f t))) (e t) := by
  let := fun q : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F q
  let := smoothChartedSpace F GLG hsmooth
  let Q (t : E) := (smoothConvergenceSections F GLG hK (e t)).comap j
  let J (t : E) : Q t →ₗ[ℂ] ScalarForms :=
    (smoothEisensteinSeries F GLG hK (e t)).comp (j.restrict fun _ hx => hx)
  let S := sectionCovarianceAlgebra ℱ Q J hGood
  let O := scalarFiniteSmoothOperatorAction F n
  have hvalue {t : E} {v : V} (hv : v ∈ Q t) :
      (sectionOutput Q J t v).val = hK.eisensteinSeries (j v) (e t) := by
    rw [sectionOutput_of_mem Q J hv]
    rfl
  have hmem {t : E} {v : V} (hv : v ∈ Q t) :=
    (mem_smoothConvergenceSections F GLG hK (e t) (j v)).mp hv
  have hfin (g : FiniteAdelicGL F n) :
      ((fun t => R t g), O (finiteOperator F n g)) ∈ S := by
    refine mem_sectionCovarianceAlgebra_of_const ℱ Q J hGood _ (hRhol g) fun v => ?_
    filter_upwards [hGood v,
      eventually_mem_of_finiteHolomorphicSections ℱ Q hGood (hRhol g v)] with t ht hg
    obtain ⟨f₀, hf₀⟩ := (hmem ht).2
    apply Subtype.ext
    change (O _ (sectionOutput Q J t v)).val = (sectionOutput Q J t (R t g v)).val
    rw [scalarFiniteSmoothOperatorAction_apply, hvalue ht, hvalue hg]
    simpa only [ContinuousMulEquiv.apply_symm_apply] using
      scalarAutomorphicOperator_eisensteinSeries_finite F n hK (e t) (j v) (j (R t g v))
        ((finiteHomeomorph F n).symm g) f₀ hf₀ (hR t g v)
  have hcomp (k : standardInfiniteCompact F n) :
      ((fun _ : E => C k), O (compactOperator F n k)) ∈ S := by
    refine mem_sectionCovarianceAlgebra_of_const ℱ Q J hGood _
      (fun v => FiniteHolomorphicSections.const_mem (C k v)) fun v => ?_
    filter_upwards [hGood v, hGood (C k v)] with t ht hk
    obtain ⟨f₀, hf₀⟩ := (hmem ht).2
    apply Subtype.ext
    change (O _ (sectionOutput Q J t v)).val = (sectionOutput Q J t (C k v)).val
    rw [scalarFiniteSmoothOperatorAction_apply, hvalue ht, hvalue hk]
    exact scalarAutomorphicOperator_eisensteinSeries_compact F n hK (e t) (j v) (j (C k v))
      k (hKinf k) f₀ hf₀ (hC k v)
  let eLie : smoothModel F d ≃ₗ[ℝ] RealLie := infiniteRealLieAlgebraEquiv F n hsmooth
  let : FiniteDimensional ℝ RealLie :=
    FiniteDimensional.of_injective (ArchimedeanGL.realLieAlgebraToMatrix F n).toLinearMap
      (ArchimedeanGL.realLieAlgebraToMatrix F n).injective
  let b := Module.finBasis ℝ RealLie
  have hReal (X : RealLie) :
      ((fun t => D t (realGenerator X)), O (differentialOperator F n (realGenerator X))) ∈ S := by
    refine mem_sectionCovarianceAlgebra_of_const ℱ Q J hGood _ (hDhol X) fun v => ?_
    let L (t : E) : RealLie →ₗ[ℝ] V := realLieAction F n (D t) v
    have hB : ∀ᶠ t in ℱ, ∀ i, L t (b i) ∈ Q t := eventually_all.mpr fun i =>
      eventually_mem_of_finiteHolomorphicSections ℱ Q hGood (hDhol (b i) v)
    filter_upwards [hGood v, hB] with t ht htB
    have hspan : Submodule.span ℝ (Set.range b) ≤ ((Q t).restrictScalars ℝ).comap (L t) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact htB i)
    have hL (Y : RealLie) : L t Y ∈ Q t := hspan (by rw [b.span_eq]; exact Submodule.mem_top)
    have hmajor (Y : smoothModel F d) :
        hK.parameterDirectionalSection hsmooth (e t) Y (j v) ∈ hK.compactMajorantSections (e t) := by
      have heq := hD t (eLie Y) v
      change j (L t (eLie Y)) = hK.parameterDirectionalSection hsmooth (e t) (eLie.symm (eLie Y)) (j v)
        at heq
      rw [eLie.symm_apply_apply] at heq
      rw [← heq]
      exact (hmem (hL (eLie Y))).1
    obtain ⟨f₀, hf₀⟩ := (hmem ht).2
    have htwist := hK.contMDiff_parameterTwist_slice hsmooth hH (j v) (e t) (hSmooth v)
    apply Subtype.ext
    change (O _ (sectionOutput Q J t v)).val = (sectionOutput Q J t (L t X)).val
    rw [scalarFiniteSmoothOperatorAction_apply, hvalue ht, hvalue (hL X)]
    have he := scalarAutomorphicOperator_eisensteinSeries_realDirectional F n hK (e t) (j v) (j (L t X))
        hsmooth (eLie.symm X) f₀ hf₀ htwist (hmem ht).1 hmajor (hD t X v)
    change scalarAutomorphicOperator F n (differentialOperator F n (realGenerator (eLie (eLie.symm X))))
      (hK.eisensteinSeries (j v) (e t)) = hK.eisensteinSeries (j (L t X)) (e t) at he
    rwa [eLie.apply_symm_apply] at he
  let B : Enveloping →ₐ[ℂ] ((E → Module.End ℂ V) × Module.End ℂ ScalarForms) :=
    (AlgHom.pi D).prod (O.comp (differentialOperator F n))
  have hB (X : RealLie) : B (realGenerator X) ∈ S := hReal X
  have hBAll (d : Enveloping) : B d ∈ S := by
    refine @enveloping_mem_subalgebra F _ n
      ((E → Module.End ℂ V) × Module.End ℂ ScalarForms) _ _ S B ?_ d
    exact hB
  let A := sectionOperatorPair F n (sectionOperatorAction R C D)
  have hall (a : Operators) : A a ∈ S := by
    induction a using FreeAlgebra.induction with
    | grade0 z => simpa only [AlgHom.commutes] using S.algebraMap_mem z
    | grade1 x =>
      change ((fun t => sectionOperatorAction R C D t (FreeAlgebra.ι ℂ x)),
        O (freeOperatorProjection F n (FreeAlgebra.ι ℂ x))) ∈ S
      simp only [freeOperatorProjection_ι, sectionOperatorAction, FreeAlgebra.lift_ι_apply,
        operatorOfIndex]
      rcases x with ((g | k) | d)
      · exact hfin g
      · exact hcomp k
      · exact hBAll d
    | add a b ha hb => simpa only [map_add] using S.add_mem ha hb
    | mul a b ha hb => simpa only [map_mul] using S.mul_mem ha hb
  obtain ⟨hHol, hEq⟩ := hall a
  have hf' := FiniteHolomorphicSections.apply_mem (fun t => sectionOperatorAction R C D t a) hHol hf
  filter_upwards [hEq f hf, eventually_mem_of_finiteHolomorphicSections ℱ Q hGood hf,
    eventually_mem_of_finiteHolomorphicSections ℱ Q hGood hf'] with t he hv hv'
  have heq := congrArg Subtype.val he
  change (O (freeOperatorProjection F n a) (sectionOutput Q J t (f t))).val =
    (sectionOutput Q J t (sectionOperatorAction R C D t a (f t))).val at heq
  rwa [scalarFiniteSmoothOperatorAction_apply, hvalue hv, hvalue hv'] at heq

end Langlands.Global.EisensteinJet
