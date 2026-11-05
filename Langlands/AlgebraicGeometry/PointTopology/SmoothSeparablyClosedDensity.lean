import Langlands.AlgebraicGeometry.PointTopology.AffineDensity
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A separably closed field is infinite, including in imperfect characteristic. -/
theorem infinite_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k] :
    Infinite k := by
  rcases finite_or_infinite k with h | h
  · have := h
    infer_instance
  · exact h

/-- The finite-variable version of affine-space density, transported through
renaming to the published universe-matched polynomial density theorem. -/
theorem hasDenseRationalPoints_finitePolynomialSpec
    (k : Type u) [Field k] [Infinite k] (n : ℕ) :
    HasDenseRationalPoints k
      (Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)))) := by
  let e := MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n).symm
  let ψ := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  let g : Over.mk (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (Fin n) k))) :=
    Over.homMk ψ.hom (by
      change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom MvPolynomial.C) = _
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      exact RingHom.ext (fun r => e.commutes r))
  apply hasDenseRationalPoints_of_denseRange g ?_
    (hasDenseRationalPoints_polynomialSpec k (ULift.{u} (Fin n)))
  apply Function.Surjective.denseRange
  intro x
  refine ⟨ψ.inv x, ?_⟩
  change (ψ.inv ≫ ψ.hom) x = x
  simp

/-- A nonzero smooth algebra over a separably closed field has an actual
rational section. -/
theorem nonempty_rationalPoint_of_smooth_algebra
    (k : Type u) [Field k] [IsSepClosed k]
    (R : CommRingCat.{u}) [Nontrivial R] [Algebra k R] [Algebra.Smooth k R] :
    Nonempty (RationalPoint k
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))))) := by
  have : Infinite k := infinite_of_isSepClosed k
  obtain ⟨p⟩ := PrimeSpectrum.nonempty_iff_nontrivial.mpr (inferInstance : Nontrivial R)
  obtain ⟨f, hfp, n, a, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p.asIdeal)
  let := a
  have := ht
  have := he
  let S := Localization.Away f
  let P := MvPolynomial (Fin n) k
  let φ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of P) :=
    Spec.map (CommRingCat.ofHom (algebraMap P S))
  have : Etale φ := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  have hq : (Ideal.map (algebraMap R S) p.asIdeal).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) S p.asIdeal p.isPrime
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfp)
  let q : Spec (CommRingCat.of S) := ⟨Ideal.map (algebraMap R S) p.asIdeal, hq⟩
  have hd := hasDenseRationalPoints_finitePolynomialSpec k n
  obtain ⟨y, hy, hx⟩ := hd.exists_mem_open φ.isOpenMap.isOpen_range
    ⟨φ q, q, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_range] at hy
  obtain ⟨s, b, rfl⟩ := hy
  obtain ⟨x, hx⟩ := hx
  have hb : b = (default : Spec (CommRingCat.of k)) :=
    @Subsingleton.elim (PrimeSpectrum k) inferInstance b _
  have hx' : φ x = s.left (default : Spec (CommRingCat.of k)) := by
    simpa only [hb] using hx
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed φ s.left x hx'
  let j : Spec (CommRingCat.of S) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  have hj : j ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
      φ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* P)) := by
    dsimp [j, φ]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext t
    exact (IsScalarTower.algebraMap_apply k R S t).symm.trans
      (IsScalarTower.algebraMap_apply k P S t)
  refine ⟨Over.homMk (l ≫ j) ?_⟩
  change (l ≫ j) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = 𝟙 _
  rw [Category.assoc, hj, ← Category.assoc, hl]
  exact s.w

/-- Every nonempty smooth affine scheme over a separably closed field has an
actual rational section, with no algebraic rational-point proposition assumed. -/
theorem nonempty_rationalPoint_of_smooth_spec_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k]
    (R : CommRingCat.{u}) [Nontrivial R]
    (f : Spec R ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    Nonempty (RationalPoint k (Over.mk f)) := by
  obtain ⟨φ, rfl⟩ := Spec.homEquiv.symm.surjective f
  algebraize [φ.hom]
  have : Algebra.Smooth k R := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp ‹Smooth (Spec.map φ)›)
  exact nonempty_rationalPoint_of_smooth_algebra k R

/-- Choose an actual rational section of a nonempty smooth affine scheme over a
separably closed field using local étale charts. -/
def rationalPointOfSmoothSpecOverSepClosed
    (k : Type u) [Field k] [IsSepClosed k]
    (R : CommRingCat.{u}) [Nontrivial R]
    (f : Spec R ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    RationalPoint k (Over.mk f) :=
  (nonempty_rationalPoint_of_smooth_spec_of_isSepClosed k R f).some

/-- Actual rational sections are dense in every smooth scheme over a separably
closed field. -/
theorem hasDenseRationalPoints_of_smooth_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k]
    (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom] :
    HasDenseRationalPoints k X := by
  apply dense_iff_inter_open.mpr
  intro U hU ⟨x, hx⟩
  obtain ⟨R, j, hj, hxj, hjU⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⟨U, hU⟩) hx
  have : IsOpenImmersion j := hj
  obtain ⟨y, -⟩ := hxj
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨y⟩
  let p := rationalPointOfSmoothSpecOverSepClosed k R (j ≫ X.hom)
  let q : RationalPoint k X := p ≫ Over.homMk j rfl
  let z : Spec (CommRingCat.of k) := (⟨⊥, inferInstance⟩ : PrimeSpectrum k)
  refine ⟨q.left z, ?_, Set.mem_iUnion.mpr ⟨q, z, rfl⟩⟩
  apply hjU
  exact ⟨p.left z, rfl⟩

end Langlands.AlgebraicGeometry.PointTopology
