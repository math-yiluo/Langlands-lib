import Langlands.AlgebraicGeometry.PointTopology.RationalDensityStatement
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.AlgebraicGeometry.AffineSpace

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

theorem hasDenseRationalPoints_of_denseRange
    {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y)
    (hf : DenseRange f.left) (hX : HasDenseRationalPoints k X) :
    HasDenseRationalPoints k Y := by
  apply hf.dense_of_mapsTo f.left.continuous hX
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_range] at hx ⊢
  obtain ⟨q, a, rfl⟩ := hx
  exact ⟨q ≫ f, a, rfl⟩

theorem dense_polynomial_evaluation_primes
    (k : Type u) [Field k] [Infinite k] (n : Type u) :
    Dense (Set.range fun x : n → k =>
      PrimeSpectrum.comap (MvPolynomial.eval x)
        (⟨⊥, inferInstance⟩ : PrimeSpectrum k)) := by
  classical
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.dense_iff.mpr
  rintro _ ⟨f, rfl⟩ ⟨p, hp⟩
  have hf : f ≠ 0 := by
    intro h
    simp [h] at hp
  have he : ∃ x : n → k, MvPolynomial.eval x f ≠ 0 := by
    by_contra! h
    exact hf (MvPolynomial.funext fun x => by simpa using h x)
  obtain ⟨x, hx⟩ := he
  refine ⟨_, ?_, x, rfl⟩
  simpa using hx

theorem hasDenseRationalPoints_polynomialSpec
    (k : Type u) [Field k] [Infinite k] (n : Type u) :
    HasDenseRationalPoints k
      (Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial n k)))) := by
  apply (dense_polynomial_evaluation_primes k n).mono
  rintro _ ⟨x, rfl⟩
  let p : RationalPoint k
      (Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial n k)))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (MvPolynomial.eval x))) (by
      change Spec.map (CommRingCat.ofHom (MvPolynomial.eval x)) ≫
        Spec.map (CommRingCat.ofHom MvPolynomial.C) = 𝟙 _
      rw [← Spec.map_comp]
      convert Spec.map_id (CommRingCat.of k) using 1
      congr 1
      ext r
      exact MvPolynomial.eval_C r)
  exact Set.mem_iUnion.mpr ⟨p, ⟨(⟨⊥, inferInstance⟩ : PrimeSpectrum k), rfl⟩⟩

theorem hasDenseRationalPoints_affineSpace
    (k : Type u) [Field k] [Infinite k] (n : Type u) :
    HasDenseRationalPoints k
      (Over.mk (𝔸(n; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) := by
  let f :
      Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial n k))) ⟶
      Over.mk (𝔸(n; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) :=
    Over.homMk (AffineSpace.SpecIso n (CommRingCat.of k)).inv
      (AffineSpace.SpecIso_inv_over (n := n) (CommRingCat.of k))
  apply hasDenseRationalPoints_of_denseRange f ?_
    (hasDenseRationalPoints_polynomialSpec k n)
  apply Function.Surjective.denseRange
  intro a
  refine ⟨(AffineSpace.SpecIso n (CommRingCat.of k)).hom a, ?_⟩
  change ((AffineSpace.SpecIso n (CommRingCat.of k)).hom ≫
    (AffineSpace.SpecIso n (CommRingCat.of k)).inv) a = a
  simp

theorem hasDenseRationalPoints_open
    {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens)
    (hX : HasDenseRationalPoints k X) :
    HasDenseRationalPoints k (Over.mk (U.ι ≫ X.hom)) := by
  apply (hX.preimage U.ι.isOpenEmbedding.isOpenMap).mono
  intro x hx
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_range] at hx ⊢
  obtain ⟨p, a, ha⟩ := hx
  have hp : Set.range p.left ⊆ Set.range U.ι := by
    rintro _ ⟨b, rfl⟩
    have hab : a = b := by
      exact @Subsingleton.elim (PrimeSpectrum k) inferInstance a b
    exact ⟨x, hab ▸ ha.symm⟩
  let q : RationalPoint k (Over.mk (U.ι ≫ X.hom)) :=
    Over.homMk (IsOpenImmersion.lift U.ι p.left hp) (by
      change IsOpenImmersion.lift U.ι p.left hp ≫ U.ι ≫ X.hom = 𝟙 _
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact p.w)
  refine ⟨q, a, U.ι.isOpenEmbedding.injective ?_⟩
  change (IsOpenImmersion.lift U.ι p.left hp ≫ U.ι) a = U.ι x
  rw [IsOpenImmersion.lift_fac]
  exact ha

theorem rationalPointDensityToolkit :
    RationalPointDensityToolkitStatement.{u} := by
  intro k _ _
  exact ⟨hasDenseRationalPoints_affineSpace k,
    fun X U => hasDenseRationalPoints_open X U,
    fun _ _ f => hasDenseRationalPoints_of_denseRange f⟩

end Langlands.AlgebraicGeometry.PointTopology
