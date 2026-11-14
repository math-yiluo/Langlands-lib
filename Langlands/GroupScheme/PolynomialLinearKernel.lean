import Langlands.GroupScheme.SplitKernelRetractGeometry
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Scheme retracts for kernels with linear coordinates -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.PolynomialLinearKernel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section Matrix

variable {k : Type u} [Field k] {I J : Type u} [Fintype I] [Fintype J]

/-- Every finite matrix over a field admits an inner inverse. -/
theorem exists_innerInverse (M : Matrix J I k) :
    ∃ N : Matrix I J k, M * N * M = M := by
  classical
  let f := Matrix.toLin' M
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := s.exists_extend
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  change (f.comp g).comp f = f
  apply LinearMap.ext
  intro x
  apply funext
  intro j
  have hgs : g (f x) = s (f.rangeRestrict x) :=
    congrArg (fun t => t (f.rangeRestrict x)) hg
  have hsf := congrArg (fun t => t (f.rangeRestrict x)) hs
  exact congrArg (fun y : f.range => (y : J → k) j)
    ((congrArg f.rangeRestrict hgs).trans hsf)

variable (M : Matrix J I k) (N : Matrix I J k)

/-- Projection onto the linear kernel, evaluated in any algebra. -/
def project {R : Type u} [CommRing R] (φ : k →+* R) (x : I → R) : I → R :=
  x - N.map φ *ᵥ (M.map φ *ᵥ x)

theorem project_killed (h : M * N * M = M)
    {R : Type u} [CommRing R] (φ : k →+* R) (x : I → R) :
    M.map φ *ᵥ project M N φ x = 0 := by
  have hm : M.map φ * N.map φ * M.map φ = M.map φ := by
    simpa only [Matrix.map_mul] using congrArg (fun a => a.map φ) h
  rw [project, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm, sub_self]

theorem project_fix {R : Type u} [CommRing R] (φ : k →+* R)
    (x : I → R) (hx : M.map φ *ᵥ x = 0) : project M N φ x = x := by
  rw [project, hx, Matrix.mulVec_zero, sub_zero]

theorem project_naturality {R R' : Type u} [CommRing R] [CommRing R']
    (φ : k →+* R) (φ' : k →+* R') (a : R →+* R')
    (ha : ∀ c, a (φ c) = φ' c) (x : I → R) :
    project M N φ' (fun i => a (x i)) =
      fun i => a (project M N φ x i) := by
  have hM : (M.map φ).map a = M.map φ' := by ext i j; exact ha _
  have hN : (N.map φ).map a = N.map φ' := by ext i j; exact ha _
  ext i
  simp only [project, Pi.sub_apply, map_sub, RingHom.map_mulVec, Function.comp_def,
    hM, hN]

end Matrix

section Scheme

variable {k : Type u} [Field k] {I J : Type u} [Fintype I] [Fintype J]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  (e : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ G.X) ≃ (I → Γ(T.left, ⊤)))
  (he : ∀ {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) (x : T ⟶ G.X),
    e T' (a ≫ x) = fun i => a.left.appTop (e T x i))
  (d : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ H.X) ≃ (J → Γ(T.left, ⊤)))
  (hd : ∀ T, d T 1 = 0)
  (q : G ⟶ H) (M : Matrix J I k)
  (hq : ∀ T (x : T ⟶ G.X),
    d T (x ≫ q.hom.hom) = M.map (scalarMap T) *ᵥ e T x)
  (N : Matrix I J k) (hN : M * N * M = M)

/-- A linear projection in coordinates gives a morphism of the underlying schemes. -/
def projection : G.X ⟶ G.X :=
  (e G.X).symm (project M N (scalarMap G.X) (e G.X (𝟙 G.X)))

include he in
theorem coordinates_projection (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    e T (x ≫ projection e M N) = project M N (scalarMap T) (e T x) := by
  calc
    _ = fun i => x.left.appTop
        (project M N (scalarMap G.X) (e G.X (𝟙 G.X)) i) := by
      rw [he, projection, Equiv.apply_symm_apply]
    _ = project M N (scalarMap T)
        (fun i => x.left.appTop (e G.X (𝟙 G.X) i)) := by
      exact (project_naturality M N (scalarMap G.X) (scalarMap T) x.left.appTop.hom
        (fun c => scalarMap_naturality x c) _).symm
    _ = _ := by rw [← he x (𝟙 G.X), Category.comp_id]

include he d hd hq hN in
theorem projection_comp : projection e M N ≫ q.hom.hom = 1 := by
  apply (d G.X).injective
  rw [hq, hd]
  have hc := coordinates_projection e he M N G.X (𝟙 G.X)
  rw [Category.id_comp] at hc
  rw [hc]
  exact project_killed M N hN _ _

/-- The projection factors through the actual scheme-theoretic kernel. -/
def retraction : G.X ⟶ (kernel q).X :=
  (kernel_isPullback q).lift (projection e M N) (toUnit _) (by
    change projection e M N ≫ q.hom.hom = 1
    exact projection_comp e he d hd q M hq N hN)

@[reassoc]
theorem retraction_ι :
    retraction e he d hd q M hq N hN ≫ (kernelι q).hom.hom = projection e M N :=
  (kernel_isPullback q).lift_fst _ _ _

/-- The scheme projection is the identity on the full scheme-theoretic kernel. -/
theorem ι_retraction :
    (kernelι q).hom.hom ≫ retraction e he d hd q M hq N hN = 𝟙 (kernel q).X := by
  apply (cancel_mono (kernelι q).hom.hom).mp
  rw [Category.assoc, retraction_ι, Category.id_comp]
  apply (e (kernel q).X).injective
  rw [coordinates_projection e he]
  apply project_fix
  rw [← hq]
  have hz : (kernelι q).hom.hom ≫ q.hom.hom = 1 := by
    rw [(kernel_isPullback q).w]
    rfl
  rw [hz, hd]

include e he d hd M hq in
/-- A coordinate-linear homomorphism has smooth connected kernel if its affine
source is smooth and connected and its target is separated. -/
theorem smooth_connected_kernel
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsSeparated H.X.hom] :
    Smooth (kernel q).X.hom ∧ ConnectedSpace (kernel q).X.left := by
  obtain ⟨N, hN⟩ := exists_innerInverse M
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom (kernel q).X.hom := by
    rw [← (kernelι q).hom.hom.w]
    infer_instance
  let : IsAffine (kernel q).X.left := isAffine_of_isAffineHom (kernel q).X.hom
  exact ⟨AffineRetractGeometry.smooth_of_retract (kernelι q).hom.hom
      (retraction e he d hd q M hq N hN) (ι_retraction e he d hd q M hq N hN),
    AffineRetractGeometry.connectedSpace_of_retract (kernelι q).hom.hom
      (retraction e he d hd q M hq N hN) (ι_retraction e he d hd q M hq N hN)⟩

include e he d hd M hq in
/-- For a unipotent source, the same actual kernel is also unipotent. -/
theorem properties
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [LocallyOfFiniteType G.X.hom] [IsSeparated H.X.hom] (hG : IsUnipotent G) :
    Smooth (kernel q).X.hom ∧ ConnectedSpace (kernel q).X.left ∧
      IsUnipotent (kernel q) := by
  have hs := smooth_connected_kernel e he d hd q M hq
  exact ⟨hs.1, hs.2,
    unipotentClosedSubgroup k G (kernel q) (kernelι q)
      (show IsClosedImmersion (kernelι q).hom.hom.left from inferInstance) hG⟩

end Scheme

end Langlands.GroupScheme.PolynomialLinearKernel
