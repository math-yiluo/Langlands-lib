import Langlands.GroupScheme.Derived.CentralIntersection.Unipotence
import Langlands.GroupScheme.Rational.PointTopology

/-! # Rational points of a closed subgroup of `GL_n` through the coordinate ring

For a matrix representation `ρ` of an affine group scheme over a field `K`, the classifying map
of the matrix of a rational point is evaluation at that point composed with pullback of the
coordinate functions of `GL_n`. When `ρ` is a closed immersion, an invertible matrix whose
classifying map kills the kernel of this pullback is the matrix of a rational point. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.CentralIntersection
  Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.RationalPoints.CentralNormKernel

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The pullback of the coordinate functions of `GL_n` along a representation. -/
def coordMap (ρ : MatrixRepresentation G n) :
    GeneralLinear.CoordinateRing n K →+* Γ(G.X.left, ⊤) :=
  ρ.hom.hom.left.appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (GeneralLinear.CoordinateRing n K))).inv.hom

theorem coordMap_algebraMap (ρ : MatrixRepresentation G n) (c : K) :
    coordMap ρ (algebraMap K (GeneralLinear.CoordinateRing n K) c) = scalarMap G.X c := by
  have h := scalarMap_naturality ρ.hom.hom c
  rw [scalarMap_generalLinear] at h
  exact h

/-- The classifying map of the matrix of a rational point is evaluation at the point after
pulling back coordinates. -/
theorem classify_rationalMatrix (ρ : MatrixRepresentation G n) (x : rationalPoints G) :
    ((GeneralLinear.classify (R := K) (ρ.rationalMatrix x) :
        GeneralLinear.CoordinateRing n K →ₐ[K] K) : GeneralLinear.CoordinateRing n K →+* K) =
      (evalPoint x).comp (coordMap ρ) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    have h1 : (Ideal.Quotient.mk (GeneralLinear.ideal n K)) (MvPolynomial.C c) =
        algebraMap K (GeneralLinear.CoordinateRing n K) c := rfl
    simp only [RingHom.comp_apply, h1, AlgHom.coe_toRingHom, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, coordMap_algebraMap]
    exact (evalPoint_scalarMap x c).symm
  · intro v
    have h1 : (Ideal.Quotient.mk (GeneralLinear.ideal n K)) (MvPolynomial.X v) =
        GeneralLinear.quotient n K (MvPolynomial.X v) := rfl
    simp only [RingHom.comp_apply, h1, AlgHom.coe_toRingHom]
    cases v with
    | entry i j =>
      rw [GeneralLinear.classify_entry, MatrixRepresentation.rationalMatrix_apply_apply]
      rfl
    | inverseEntry i j =>
      rw [GeneralLinear.classify_inverseEntry, MatrixRepresentation.rationalMatrix_apply, ← map_inv,
        Matrix.GeneralLinearGroup.map_apply, GeneralLinear.pointsEquiv_inv_apply]
      rfl

theorem classify_rationalMatrix_apply (ρ : MatrixRepresentation G n) (x : rationalPoints G)
    (f : GeneralLinear.CoordinateRing n K) :
    GeneralLinear.classify (R := K) (ρ.rationalMatrix x) f = evalPoint x (coordMap ρ f) :=
  RingHom.congr_fun (classify_rationalMatrix ρ x) f

/-- Rational points kill the kernel of the coordinate pullback. -/
theorem classify_rationalMatrix_eq_zero (ρ : MatrixRepresentation G n) (x : rationalPoints G)
    {f : GeneralLinear.CoordinateRing n K} (hf : f ∈ RingHom.ker (coordMap ρ)) :
    GeneralLinear.classify (R := K) (ρ.rationalMatrix x) f = 0 := by
  rw [classify_rationalMatrix_apply, RingHom.mem_ker.1 hf, map_zero]

/-- The structure algebra map of an affine scheme is the scalar map. -/
theorem affineCoordinateMap_eq_scalarMap (X : Over (Spec (CommRingCat.of K))) [IsAffine X.left] :
    affineCoordinateMap K X = scalarMap X := by
  have h : Spec.preimage (X.left.isoSpec.inv ≫ X.hom) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appTop := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp]
    rw [← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]
  exact congrArg (fun f => f.hom) h

/-- **Lifting.** For a closed embedding `ρ` of an affine group scheme, an invertible matrix
whose classifying map kills the kernel of the coordinate pullback is the matrix of a rational
point. -/
theorem exists_rationalMatrix_eq [IsAffine G.X.left] (ρ : MatrixRepresentation G n)
    [IsClosedImmersion ρ.hom.hom.left] (g : GL n K)
    (hg : ∀ f ∈ RingHom.ker (coordMap ρ), GeneralLinear.classify (R := K) g f = 0) :
    ∃ x : rationalPoints G, ρ.rationalMatrix x = g := by
  have : IsAffine (GeneralLinear.groupScheme n (CommRingCat.of K)).X.left :=
    inferInstanceAs (IsAffine (Spec _))
  have hsurj : Function.Surjective (coordMap ρ) :=
    ((IsClosedImmersion.isAffine_surjective_of_isAffine ρ.hom.hom.left).2).comp
      (Scheme.ΓSpecIso (CommRingCat.of (GeneralLinear.CoordinateRing n K))).commRingCatIsoToRingEquiv.symm.surjective
  let ψ₀ : Γ(G.X.left, ⊤) →+* K := (coordMap ρ).liftOfSurjective hsurj
    ⟨(GeneralLinear.classify (R := K) g : GeneralLinear.CoordinateRing n K →+* K),
      fun f hf => hg f hf⟩
  have hψ₀ : ψ₀.comp (coordMap ρ) =
      (GeneralLinear.classify (R := K) g : GeneralLinear.CoordinateRing n K →+* K) :=
    RingHom.liftOfSurjective_comp _ hsurj _
  let ψ : AffineCoordinateRing K G.X →ₐ[K] K :=
    { ψ₀ with
      commutes' := fun c => by
        change ψ₀ (affineCoordinateMap K G.X c) = c
        have hc : (affineCoordinateMap K G.X c : Γ(G.X.left, ⊤)) =
            coordMap ρ (algebraMap K (GeneralLinear.CoordinateRing n K) c) :=
          (RingHom.congr_fun (affineCoordinateMap_eq_scalarMap G.X) c).trans
            (coordMap_algebraMap ρ c).symm
        refine (congrArg ψ₀ hc).trans ?_
        have := RingHom.congr_fun hψ₀ (algebraMap K _ c)
        rw [RingHom.comp_apply] at this
        rw [this]
        exact (GeneralLinear.classify (R := K) g).commutes c }
  let p : rationalPoints G :=
    (rationalPointEquiv K G.X).symm ((affineSchemePointEquiv K G.X K).symm (AlgPoint.ofAlgHom ψ))
  have hp : ∀ a, evalPoint p a = ψ₀ a := by
    intro a
    have h := affineSchemePointEquiv_apply_eq_evaluation G (rationalPointEquiv K G.X p) a
    have h1 : affineSchemePointEquiv K G.X K (rationalPointEquiv K G.X p) a = ψ₀ a := by
      simp only [p, Equiv.apply_symm_apply]
      rfl
    rw [h1] at h
    rw [h]
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom (p.left.appTop a) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((rationalPointEquiv K G.X p).left.appTop a)
    rw [rationalPointEquiv_left]
    rfl
  refine ⟨p, ?_⟩
  apply (GeneralLinear.homEquiv (R := K) (S := K)).symm.injective
  change GeneralLinear.classify (R := K) (ρ.rationalMatrix p) = GeneralLinear.classify (R := K) g
  apply AlgHom.coe_ringHom_injective
  rw [classify_rationalMatrix, ← hψ₀]
  refine RingHom.ext fun f => ?_
  simp only [RingHom.comp_apply]
  exact hp _

end Langlands.BruhatTits.RationalPoints.CentralNormKernel
