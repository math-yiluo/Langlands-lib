import Langlands.AlgebraicGeometry.FiniteEtale.AffineSplittingOfSections
import Langlands.AlgebraicGeometry.PointManifold.Analytic.IntegralAnalyticSection
import Langlands.AlgebraicGeometry.PointManifold.Analytic.UnramifiedLocalDiffeomorph
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionMaps
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting

/-! # Sections of finite étale maps to complex affine space -/

noncomputable section

open CategoryTheory _root_.AlgebraicGeometry
open Function Set Topology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.PointManifold.Analytic

open PointTopology

private def spectrumAlgPointHomeomorph (B : Type) [CommRing B] [Algebra ℂ B] :
    RingPoint ℂ (ringTest ℂ B) ℂ ≃ₜ AlgPoint ℂ B ℂ :=
  (affineSchemePointHomeomorph ℂ (ringTest ℂ B) ℂ).trans
    (AlgPoint.congr (spectrumCoordinateAlgEquiv ℂ B))

@[simp]
private theorem spectrumAlgPointHomeomorph_apply {B : Type} [CommRing B] [Algebra ℂ B]
    (p : RingPoint ℂ (ringTest ℂ B) ℂ) :
    spectrumAlgPointHomeomorph B p = AlgPoint.ofAlgHom (affineRingPointEquiv ℂ B ℂ p) := by
  change AlgPoint.congr (spectrumCoordinateAlgEquiv ℂ B)
    (affineSchemePointEquiv ℂ (ringTest ℂ B) ℂ p) = _
  rw [affineSchemePointEquiv_spectrum]
  apply AlgPoint.ext
  intro a
  exact congrArg (affineRingPointEquiv ℂ B ℂ p)
    ((spectrumCoordinateAlgEquiv ℂ B).apply_symm_apply a)

private theorem regularEvaluation_spectrum {B : Type} [CommRing B] [Algebra ℂ B]
    (p : RingPoint ℂ (ringTest ℂ B) ℂ) (a : AffineCoordinateRing ℂ (ringTest ℂ B)) :
    regularEvaluation p a = spectrumAlgPointHomeomorph B p (spectrumCoordinateAlgEquiv ℂ B a) := by
  rw [spectrumAlgPointHomeomorph_apply]
  exact congrArg (fun q : AlgPoint ℂ (AffineCoordinateRing ℂ (ringTest ℂ B)) ℂ => q a)
    (affineSchemePointEquiv_spectrum ℂ ℂ B p)

set_option maxHeartbeats 600000 in
/-- Each point over the origin of a finite étale algebra over complex affine space
extends to an algebraic section. -/
theorem exists_algHom_eval_zero_of_etale {n : ℕ} {A : Type} [CommRing A]
    [Algebra (MvPolynomial (Fin n) ℂ) A] [Algebra.Etale (MvPolynomial (Fin n) ℂ) A]
    [Module.Finite (MvPolynomial (Fin n) ℂ) A] [Algebra ℂ A]
    [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) A]
    (p : A →ₐ[ℂ] ℂ)
    (hp : ∀ r, p (algebraMap (MvPolynomial (Fin n) ℂ) A r) =
      MvPolynomial.eval (0 : Fin n → ℂ) r) :
    ∃ φ : A →ₐ[MvPolynomial (Fin n) ℂ] MvPolynomial (Fin n) ℂ,
      ∀ a, MvPolynomial.eval (0 : Fin n → ℂ) (φ a) = p a := by
  let R := MvPolynomial (Fin n) ℂ
  let X := ringTest ℂ A
  let Y := ringTest ℂ R
  let α := IsScalarTower.toAlgHom ℂ R A
  let f : X ⟶ Y := ringTestMap ℂ α
  let g (v : RingPoint ℂ X ℂ) : RingPoint ℂ Y ℂ := v ≫ f
  let eX := spectrumAlgPointHomeomorph A
  let eY := spectrumAlgPointHomeomorph R
  let e := AlgPoint.polynomialPointHomeomorph (R := ℂ) (S := ℂ) (Fin n)
  let q : (Fin n → ℂ) ≃ₜ RingPoint ℂ Y ℂ := e.symm.trans eY.symm
  have hg (v : RingPoint ℂ X ℂ) : eY (g v) = AlgPoint.precomp α (eX v) := by
    calc
      eY (g v) = AlgPoint.ofAlgHom (affineRingPointEquiv ℂ R ℂ (g v)) :=
        spectrumAlgPointHomeomorph_apply (B := R) (g v)
      _ = AlgPoint.precomp α (AlgPoint.ofAlgHom (affineRingPointEquiv ℂ A ℂ v)) :=
        congrArg AlgPoint.ofAlgHom (affineRingPointEquiv_postcomp_ringTestMap ℂ α v)
      _ = AlgPoint.precomp α (eX v) :=
        congrArg (AlgPoint.precomp α) (spectrumAlgPointHomeomorph_apply (B := A) v).symm
  have hq (x : Fin n → ℂ) : eY (q x) = AlgPoint.ofAlgHom (MvPolynomial.aeval x) :=
    eY.apply_symm_apply (e.symm x)
  have hproper : IsProperMap g := by
    have h := eY.symm.isHomeomorph.isProperMap.comp
      ((AlgPoint.isProperMap_precomp_of_moduleFinite (R := ℂ) (A := R) (B := A) (L := ℂ)).comp
        eX.isHomeomorph.isProperMap)
    convert h using 1
    funext v
    exact (eY.symm_apply_eq.mpr (hg v).symm).symm
  have : Etale f.left := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).2
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hY : SmoothOfRelativeDimension n Y.hom := by
    apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).2
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).2 inferInstance
  have hX : SmoothOfRelativeDimension n X.hom := by
    have : SmoothOfRelativeDimension 0 f.left :=
      (Etale.iff_smoothOfRelativeDimension_zero _).mp inferInstance
    let := hY
    rw [← Over.w f, ← Nat.zero_add n]
    infer_instance
  let := smoothAffineChartedSpace ℂ X n hX
  let := smoothAffineChartedSpace ℂ Y n hY
  have hd := smoothAffine_isLocalDiffeomorph_etale hX hY f
  change IsLocalDiffeomorph 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω g at hd
  have hlocal := hd.isLocalHomeomorph
  let := eX.symm.t2Space
  have hdiscrete (y : RingPoint ℂ Y ℂ) : IsDiscrete (g ⁻¹' {y}) := by
    apply IsDiscrete.of_openPartialHomeomorph g subset_rfl
    intro v _
    obtain ⟨h, hv, heq⟩ := hlocal v
    exact ⟨h, hv, heq.symm⟩
  have hcover : IsCoveringMap g := isCoveringMap_iff_isCoveringMapOn_univ.mpr
    (hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
      (fun y _ => (hproper.isCompact_preimage isCompact_singleton).finite (hdiscrete y)) (by
          simpa only [preimage_univ] using hlocal.isLocalHomeomorphOn))
  let v₀ := eX.symm (AlgPoint.ofAlgHom p)
  have hv₀ : g v₀ = q 0 := by
    apply eY.injective
    rw [hg, hq, eX.apply_symm_apply]
    exact AlgPoint.ext hp
  obtain ⟨s, ⟨hs₀, hs⟩, _⟩ := hcover.existsUnique_continuousMap_lifts
    ⟨q, q.continuous⟩ 0 v₀ hv₀
  have hgs (x : Fin n → ℂ) : g (s x) = q x := congrFun hs x
  have hqD : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω q := by
    apply ((smoothAffineRegularAtlas ℂ Y n hY).contMDiff_iff_regularAnalytic
      𝓘(ℂ, Fin n → ℂ) q).mpr
    intro r x
    apply ContDiffAt.contMDiffAt
    change ContDiffAt ℂ ω
      (fun y => regularEvaluation (q y : RingPoint ℂ (ringTest ℂ R) ℂ) r) x
    have heval (y : Fin n → ℂ) : regularEvaluation (q y) r =
        MvPolynomial.aeval y (spectrumCoordinateAlgEquiv ℂ R r) :=
      (regularEvaluation_spectrum (B := R) (q y) r).trans
        (congrArg (fun p : AlgPoint ℂ R ℂ => p (spectrumCoordinateAlgEquiv ℂ R r)) (hq y))
    rw [funext heval]
    exact (AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (A := ℂ) (B := ℂ) (f := id)
      (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt x)
      (spectrumCoordinateAlgEquiv ℂ R r)).contDiffAt
  have hsD : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω s := by
    intro x
    let h := hd (s x)
    have hD := h.localInverse_contMDiffAt
    rw [hgs x] at hD
    refine (hD.comp x (hqD x)).congr_of_eventuallyEq ?_
    filter_upwards [s.continuous.continuousAt.preimage_mem_nhds
      (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)] with y hy
    change s y = h.localInverse (q y)
    rw [← hgs y, h.localInverse_left_inv hy]
  let t (x : Fin n → ℂ) := (eX (s x)).toAlgHom
  have ht (x : Fin n → ℂ) (r : R) : t x (algebraMap R A r) = MvPolynomial.eval x r := by
    have he : AlgPoint.precomp α (eX (s x)) = AlgPoint.ofAlgHom (MvPolynomial.aeval x) := by
      rw [← hg, hgs, hq]
    exact congrArg (fun w : AlgPoint ℂ R ℂ => w r) he
  have htD (a : A) (x : Fin n → ℂ) : AnalyticAt ℂ (fun y => t y a) x := by
    have hD := (smoothAffine_contMDiff_regularEvaluation ℂ X n hX
      ((spectrumCoordinateAlgEquiv ℂ A).symm a)).comp hsD
    change ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω
      (fun y => regularEvaluation (s y : RingPoint ℂ (ringTest ℂ A) ℂ)
        ((spectrumCoordinateAlgEquiv ℂ A).symm a)) at hD
    have heval (y : Fin n → ℂ) : regularEvaluation (s y)
        ((spectrumCoordinateAlgEquiv ℂ A).symm a) = t y a :=
      (regularEvaluation_spectrum (B := A) (s y)
        ((spectrumCoordinateAlgEquiv ℂ A).symm a)).trans
          (congrArg (eX (s y)) ((spectrumCoordinateAlgEquiv ℂ A).apply_symm_apply a))
    rw [funext heval] at hD
    exact (hD x).contDiffAt.analyticAt
  obtain ⟨φ, hφ⟩ := exists_algHom_of_integral_analytic_section t ht htD
  exact ⟨φ, fun a => by rw [hφ, show t 0 a = p a by
    change eX (s 0) a = p a
    rw [hs₀, eX.apply_symm_apply]
    rfl]⟩

private theorem exists_small_algEquiv_pi_of_complex {n : ℕ} {A : Type} [CommRing A]
    [Algebra (MvPolynomial (Fin n) ℂ) A] [Algebra.Etale (MvPolynomial (Fin n) ℂ) A]
    [Module.Finite (MvPolynomial (Fin n) ℂ) A] :
    ∃ m : ℕ, Nonempty (A ≃ₐ[MvPolynomial (Fin n) ℂ] (Fin m → MvPolynomial (Fin n) ℂ)) := by
  let R := MvPolynomial (Fin n) ℂ
  let : Algebra R ℂ := (MvPolynomial.eval (0 : Fin n → ℂ)).toAlgebra
  let : Algebra ℂ A := ((algebraMap R A).comp MvPolynomial.C).toAlgebra
  let : IsScalarTower ℂ R A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower ℂ R ℂ := IsScalarTower.of_algebraMap_eq fun c =>
    (MvPolynomial.eval_C (f := (0 : Fin n → ℂ)) c).symm
  apply FiniteEtale.exists_algEquiv_pi_of_sections (K := ℂ)
  intro p
  obtain ⟨φ, hφ⟩ := exists_algHom_eval_zero_of_etale (p.restrictScalars ℂ) p.commutes
  exact ⟨φ, AlgHom.ext hφ⟩

/-- Every finite étale algebra over a complex polynomial ring splits over that ring. -/
theorem exists_algEquiv_pi_of_complex {n : ℕ} {A : Type*} [CommRing A]
    [Algebra (MvPolynomial (Fin n) ℂ) A] [Algebra.Etale (MvPolynomial (Fin n) ℂ) A]
    [Module.Finite (MvPolynomial (Fin n) ℂ) A] :
    ∃ m : ℕ, Nonempty (A ≃ₐ[MvPolynomial (Fin n) ℂ] (Fin m → MvPolynomial (Fin n) ℂ)) := by
  let R := MvPolynomial (Fin n) ℂ
  obtain ⟨s, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  let B := MvPolynomial (Fin s) R ⧸ RingHom.ker f.toRingHom
  let e : B ≃ₐ[R] A := Ideal.quotientKerAlgEquivOfSurjective hf
  let : Algebra.Etale R B := Algebra.Etale.of_equiv e.symm
  let : Module.Finite R B := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  obtain ⟨m, ⟨φ⟩⟩ := exists_small_algEquiv_pi_of_complex (n := n) (A := B)
  exact ⟨m, ⟨e.symm.trans φ⟩⟩

end Langlands.AlgebraicGeometry.PointManifold.Analytic
