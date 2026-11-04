import Langlands.Algebra.FiniteHopfConvolutionPower
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.TauCeti.Algebra.AlgebraicGroup.Hopf.CentralPoint
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Points of kernels of central isogenies over a field are killed by a fixed power -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

section Spec

variable (A : Type u) [CommRing A] [HopfAlgebra k A]

/-- The identity of `Spec A` is the point given by the identity algebra map. -/
lemma id_spec_asOver_eq_mapMulEquiv :
    𝟙 ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))) =
      Spec.mapMulEquiv (toConv (AlgHom.id k A)) := by
  ext1
  simp [Spec.mapMulEquiv]

/-- In a finite commutative and cocommutative Hopf algebra, the identity point of its spectrum
is killed by the rank. -/
lemma id_spec_asOver_pow_finrank [Coalgebra.IsCocomm k A] [Module.Finite k A] :
    𝟙 ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))) ^ Module.finrank k A = 1 := by
  rw [id_spec_asOver_eq_mapMulEquiv, ← map_pow,
    FiniteHopfConvolutionPower.pow_finrank_eq_one, map_one]

/-- If the points of `Spec A` with values in `A ⊗ A` commute, then `A` is cocommutative. -/
lemma isCocomm_of_commute
    (h : ∀ (p q : (Spec (CommRingCat.of (A ⊗[k] A))).asOver (Spec (CommRingCat.of k)) ⟶
      (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))), p * q = q * p) :
    Coalgebra.IsCocomm k A := by
  rw [← TauCeti.HopfAlgebra.commute_includeLeft_includeRight_iff_isCocomm k A]
  show _ * _ = _ * _
  apply (Spec.mapMulEquiv (R := k) (S := A) (T := A ⊗[k] A)).injective
  rw [map_mul, map_mul]
  exact h _ _

end Spec

/-- **Points of a finite commutative group scheme over a field are killed by a fixed power.**
The exponent is the rank of the coordinate algebra. -/
theorem exists_pow_eq_one_of_isFinite (K : GroupScheme (Spec (CommRingCat.of k)))
    [IsCommMonObj K.X] [IsFinite K.X.hom] :
    ∃ N : ℕ, 0 < N ∧ ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ K.X), x ^ N = 1 := by
  have : IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom
  let A := AffineCoordinates.hopfAlgebra K
  let e := AffineCoordinates.hopfSpecIso K
  let Y := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))
  let f : Y ⟶ K.X := e.hom.hom.hom
  let g : K.X ⟶ Y := e.inv.hom.hom
  have : IsMonHom f := e.hom.hom.isMonHom_hom
  have hgf : g ≫ f = 𝟙 K.X := congrArg (fun φ => φ.hom.hom) e.inv_hom_id
  have hfg : f ≫ g = 𝟙 Y := congrArg (fun φ => φ.hom.hom) e.hom_inv_id
  have : IsIso f := ⟨g, hfg, hgf⟩
  have : IsIso f.left := (Over.forget _).map_isIso f
  have : Module.Finite k A := by
    have hfin : IsFinite (f.left ≫ K.X.hom) := inferInstance
    rw [Over.w] at hfin
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A))) at hfin
    rw [IsFinite.SpecMap_iff] at hfin
    exact RingHom.finite_algebraMap.mp hfin
  have : Coalgebra.IsCocomm k A := isCocomm_of_commute A fun p q => by
    apply (cancel_mono f).1
    rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]
  have : Nontrivial A :=
    (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial
  refine ⟨Module.finrank k A, Module.finrank_pos, fun T x => ?_⟩
  have hx : x = (x ≫ g) ≫ f := by rw [Category.assoc, hgf, Category.comp_id]
  have hy : (x ≫ g) ^ Module.finrank k A = 1 := by
    rw [← Category.comp_id (x ≫ g), ← MonObj.comp_pow, id_spec_asOver_pow_finrank,
      MonObj.comp_one]
  rw [hx, ← MonObj.pow_comp, hy, MonObj.one_comp]

/-- **The kernel of a central isogeny over a field has bounded exponent.** Some positive power
kills every point of the scheme-theoretic kernel, on every test scheme. -/
theorem IsCentralIsogeny.exists_pow_eq_one_kernel {G H : GroupScheme (Spec (CommRingCat.of k))}
    {π : G ⟶ H} (hπ : IsCentralIsogeny π) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ (kernel π).X), x ^ N = 1 := by
  have := hπ.isCentral_kernelι.isCommMonObj
  have := hπ.kernel_isFinite
  exact exists_pow_eq_one_of_isFinite (kernel π)

end Langlands.GroupScheme
