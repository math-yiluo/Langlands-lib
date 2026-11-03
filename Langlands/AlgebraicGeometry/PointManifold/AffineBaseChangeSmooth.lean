import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeTopologyProof
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-! # Regular-function smoothness under actual affine base change -/

noncomputable section

universe u v w z

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold

open PointTopology

variable (C D K A : Type u)
  [CommRing C] [CommRing D] [CommRing K] [CommRing A]
  [Algebra C D] [Algebra C K] [Algebra C A] [Algebra D A]
  [IsScalarTower C D A]
  {B : Type v} [NormedCommRing B] [NormedAlgebra ℝ B] (c : A →+* B)
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type z} [TopologicalSpace M] [ChartedSpace H M]

/-- Tensor scalar extension preserves and reflects all smooth evaluation tests,
after the specified map on the value ring. -/
theorem contMDiff_algPoint_baseChange_iff (p : M → AlgPoint C K A) :
    (∀ t : D ⊗[C] K, ContMDiff I 𝓘(ℝ, B) ∞
      (fun x => c (AlgPoint.baseChangeEquiv C D K A (p x) t))) ↔
    (∀ a : K, ContMDiff I 𝓘(ℝ, B) ∞ (fun x => c (p x a))) := by
  constructor
  · intro hp a
    simpa only [AlgPoint.baseChangeEquiv_tmul, map_one, one_mul] using
      hp (1 ⊗ₜ[C] a)
  · intro hp t
    induction t using TensorProduct.inductionOn with
    | tmul d a =>
        simpa only [AlgPoint.baseChangeEquiv_tmul, map_mul, Function.comp_def] using
          (contDiff_mul (𝕜 := ℝ) (𝔸 := B)).contMDiff.comp
            (contMDiff_const.prodMk_space (hp a))
    | add t t' ht ht' =>
        change ContMDiff I 𝓘(ℝ, B) ∞
          (fun x => c ((AlgPoint.baseChangeEquiv C D K A (p x)).toAlgHom (t + t')))
        simpa only [map_add, AlgPoint.toAlgHom_apply, Function.comp_def] using
          (contDiff_add (𝕜 := ℝ) (F := B)).contMDiff.comp
            (ht.prodMk_space ht')

omit [CommRing D] [Algebra C D] [Algebra D A] [IsScalarTower C D A] in
/-- All global-function tests are the same as all coordinate tests in any actual
affine spectrum presentation. -/
theorem contMDiff_affinePresentation_iff
    (X : Over (Spec (CommRingCat.of C))) [IsAffine X.left]
    (e : X ≅ ringTest C K) (p : M → RingPoint C X A) :
    (∀ a : K, ContMDiff I 𝓘(ℝ, B) ∞
      (fun x => c (affineRingPointEquiv C K A (p x ≫ e.hom) a))) ↔
    (∀ a : AffineCoordinateRing C X, ContMDiff I 𝓘(ℝ, B) ∞
      (fun x => c (affineSchemePointEquiv C X A (p x) a))) := by
  have he (x : M) (a : AffineCoordinateRing C (ringTest C K)) :
      affineRingPointEquiv C K A (p x ≫ e.hom)
          (spectrumCoordinateAlgEquiv C K a) =
        affineSchemePointEquiv C X A (p x) (affineCoordinateAlgEquiv C e a) := by
    have hs := congrArg
      (fun q : AlgPoint C (AffineCoordinateRing C (ringTest C K)) A => q a)
      (affineSchemePointEquiv_spectrum C A K (p x ≫ e.hom))
    have hn := congrArg
      (fun q : AlgPoint C (AffineCoordinateRing C (ringTest C K)) A => q a)
      (affineSchemePointEquiv_natural C A e.hom (p x))
    exact hs.symm.trans hn
  constructor
  · intro hp a
    let a' := (affineCoordinateAlgEquiv C e).symm a
    have h := hp (spectrumCoordinateAlgEquiv C K a')
    exact h.congr (fun x => congrArg c
      ((he x a').trans (congrArg
        (fun b => affineSchemePointEquiv C X A (p x) b)
        ((affineCoordinateAlgEquiv C e).apply_symm_apply a))).symm)
  · intro hp a
    let a' := (spectrumCoordinateAlgEquiv C K).symm a
    have h := hp (affineCoordinateAlgEquiv C e a')
    exact h.congr (fun x => congrArg c
      ((he x a').symm.trans (congrArg
        (fun b => affineRingPointEquiv C K A (p x ≫ e.hom) b)
        ((spectrumCoordinateAlgEquiv C K).apply_symm_apply a))).symm)

variable (X : Over (Spec (CommRingCat.of C))) [IsAffine X.left]
  [TopologicalSpace A]

omit c I in
/-- The original pullback-adjunction map has the canonical tensor evaluation
coordinates, with no replacement of its actual point carrier. -/
theorem ringPointBaseChange_tensor_coordinates (p : RingPoint C X A) :
    AlgPoint.ofAlgHom
        (affineRingPointEquiv D (D ⊗[C] AffineCoordinateRing C X) A
          (ringPointBaseChangeEquiv C D A X p ≫
            (ringBaseChangeAffineOverIso C D X).hom)) =
      AlgPoint.baseChangeEquiv C D (AffineCoordinateRing C X) A
        (affineSchemePointEquiv C X A p) := by
  let q := ringPointBaseChangeEquiv C D A X p
  let T := D ⊗[C] AffineCoordinateRing C X
  let e := ringBaseChangeAffineOverIso C D X
  have hq :
      affinePresentationPointHomeomorph D A T e q =
        ringPointEquiv D (ringTest D T) A (q ≫ e.hom) := by
    apply Subtype.ext
    exact affinePresentationPointHomeomorph_apply D A T e q
  have ht :
      specPointEquiv D T A (affinePresentationPointHomeomorph D A T e q) =
        AlgPoint.ofAlgHom (affineRingPointEquiv D T A (q ≫ e.hom)) := by
    rw [hq]
    rfl
  have h := affineBaseChange_inverse_coordinates C D A X q
  rw [ht] at h
  change affineSchemePointEquiv C X A
      ((ringPointBaseChangeEquiv C D A X).symm
        (ringPointBaseChangeEquiv C D A X p)) = _ at h
  rw [Equiv.symm_apply_apply] at h
  exact ((AlgPoint.baseChangeEquiv C D (AffineCoordinateRing C X) A).apply_symm_apply
    (AlgPoint.ofAlgHom (affineRingPointEquiv D T A (q ≫ e.hom)))).symm.trans
      (congrArg (AlgPoint.baseChangeEquiv C D (AffineCoordinateRing C X) A) h.symm)

/-- Actual affine base change preserves and reflects all regular-function
smoothness tests after an arbitrary specified value-ring map. -/
theorem contMDiff_ringPoint_baseChange_iff (p : M → RingPoint C X A) :
    (∀ a : AffineCoordinateRing D (ringBaseChange C D X),
      ContMDiff I 𝓘(ℝ, B) ∞
        (fun x => c (affineSchemePointEquiv D (ringBaseChange C D X) A
          (ringPointBaseChangeEquiv C D A X (p x)) a))) ↔
    (∀ a : AffineCoordinateRing C X,
      ContMDiff I 𝓘(ℝ, B) ∞
        (fun x => c (affineSchemePointEquiv C X A (p x) a))) := by
  rw [← contMDiff_affinePresentation_iff D
    (D ⊗[C] AffineCoordinateRing C X) A c I
    (ringBaseChange C D X) (ringBaseChangeAffineOverIso C D X)]
  simp_rw [← AlgPoint.ofAlgHom_apply, ringPointBaseChange_tensor_coordinates]
  exact contMDiff_algPoint_baseChange_iff C D (AffineCoordinateRing C X) A c I
    (fun x => affineSchemePointEquiv C X A (p x))

/-- The actual point equivalence restricts to an equivalence of precisely the
specified regular-function-smooth parameter families. -/
def coefficientSmoothBaseChangeFamilyEquiv :
    {p : M → RingPoint C X A //
      ∀ a : AffineCoordinateRing C X, ContMDiff I 𝓘(ℝ, B) ∞
        (fun x => c (affineSchemePointEquiv C X A (p x) a))} ≃
    {p : M → RingPoint D (ringBaseChange C D X) A //
      ∀ a : AffineCoordinateRing D (ringBaseChange C D X),
        ContMDiff I 𝓘(ℝ, B) ∞
          (fun x => c (affineSchemePointEquiv D (ringBaseChange C D X) A (p x) a))} where
  toFun p := ⟨fun x => ringPointBaseChangeEquiv C D A X (p.1 x),
    (contMDiff_ringPoint_baseChange_iff C D A c I X p.1).mpr p.2⟩
  invFun p := ⟨fun x => (ringPointBaseChangeEquiv C D A X).symm (p.1 x), by
    apply (contMDiff_ringPoint_baseChange_iff C D A c I X _).mp
    simpa only [Equiv.apply_symm_apply] using p.2⟩
  left_inv p := by
    apply Subtype.ext
    funext x
    exact (ringPointBaseChangeEquiv C D A X).symm_apply_apply (p.1 x)
  right_inv p := by
    apply Subtype.ext
    funext x
    exact (ringPointBaseChangeEquiv C D A X).apply_symm_apply (p.1 x)

end Langlands.AlgebraicGeometry.PointManifold
