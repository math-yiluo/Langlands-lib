import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothOpenMapStatement
import Langlands.AlgebraicGeometry.PointTopology.HenselianRootLifting
import Langlands.AlgebraicGeometry.PointTopology.StandardEtalePoints
import Langlands.AlgebraicGeometry.PointTopology.RelativePolynomialPoints
import Langlands.AlgebraicGeometry.PointTopology.Localization
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Smooth maps are open on rational points over Henselian ultrametric fields

Near a point of a standard etale presentation, the defining polynomial has a simple root.
Its Taylor expansion at that root has continuous coefficients in the coefficient point, so
`HenselianRoot.eventually_exists_root` gives roots of the moved polynomial arbitrarily close
to the original root. Hence the projection from standard etale root coordinates to coefficient
points is open, and restriction along a standard etale presentation is open. Local standard
etale factorizations of smooth algebras through polynomial algebras, followed by the actual
affine-scheme and rational-point homeomorphisms, give the published statement. Completeness
of the field is never used.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open CategoryTheory Filter Polynomial
open _root_.AlgebraicGeometry
open scoped Topology

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianSmoothOpen

section StandardEtale

variable {K : Type u} [NontriviallyNormedField K]
variable {A : Type v} [CommRing A] [Algebra K A]
variable {B : Type w} [CommRing B] [Algebra K B] [Algebra A B] [IsScalarTower K A B]

omit [Algebra K B] [IsScalarTower K A B] in
/-- The root coordinate of a standard etale point is a simple root of the moved polynomial. -/
theorem standardEtalePoint_simple (P : StandardEtalePresentation A B)
    (z : StandardEtalePointCoordinates (K := K) P) :
    P.f.derivative.eval₂ z.1.1.toAlgHom.toRingHom z.1.2 ≠ 0 := by
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  intro hzero
  have h := congrArg (Polynomial.eval₂RingHom z.1.1.toAlgHom.toRingHom z.1.2) e
  simp only [map_add, map_mul, map_pow, Polynomial.coe_eval₂RingHom] at h
  rw [hzero, z.2.1, zero_mul, zero_mul, zero_add] at h
  exact pow_ne_zero n z.2.2 h.symm

variable [IsUltrametricDist K]
  [HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring]

/-- Every coefficient point near that of a standard etale point carries a root of the moved
defining polynomial within any prescribed distance of the original root. -/
theorem eventually_exists_near_root (P : StandardEtalePresentation A B)
    (z : StandardEtalePointCoordinates (K := K) P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 z.1.1, ∃ x : K, P.f.eval₂ p.toAlgHom.toRingHom x = 0 ∧ dist x z.1.2 < ε := by
  let G : AlgPoint K A K → K[X] := fun p => taylor z.1.2 (P.f.map p.toAlgHom.toRingHom)
  have hcoeff (k : ℕ) : (fun p => (G p).coeff k) =
      fun p => (hasseDeriv k P.f).eval₂ p.toAlgHom.toRingHom z.1.2 := by
    funext p
    simp only [G, taylor_coeff, hasseDeriv_map, eval_map]
  have hc (k : ℕ) : ContinuousAt (fun p => (G p).coeff k) z.1.1 := by
    rw [hcoeff]
    exact ((continuous_point_polynomial_eval (K := K) (hasseDeriv k P.f)).comp
      (continuous_id.prodMk continuous_const)).continuousAt
  have hN (p : AlgPoint K A K) : (G p).natDegree ≤ P.f.natDegree := by
    simp only [G, natDegree_taylor]
    exact natDegree_map_le
  have h0 : (G z.1.1).coeff 0 = 0 := by
    simp only [G, taylor_coeff_zero, eval_map]
    exact z.2.1
  have h1 : (G z.1.1).coeff 1 ≠ 0 := by
    simp only [G, taylor_coeff_one, derivative_map, eval_map]
    exact standardEtalePoint_simple P z
  filter_upwards [HenselianRoot.eventually_exists_root G P.f.natDegree hc hN h0 h1 hε]
    with p hp
  obtain ⟨y, hy, hyε⟩ := hp
  refine ⟨y + z.1.2, ?_, ?_⟩
  · simpa only [G, taylor_eval, eval_map] using hy
  · rwa [dist_eq_norm, add_sub_cancel_right]

/-- Over a field with Henselian norm valuation ring, restriction along a standard etale
presentation is open on actual points. -/
theorem isOpenMap_standardEtale (P : StandardEtalePresentation A B) :
    IsOpenMap (AlgPoint.precomp (S := K) (IsScalarTower.toAlgHom K A B)) := by
  have hprojection : IsOpenMap
      (fun z : StandardEtalePointCoordinates (K := K) P => z.1.1) := by
    intro U hU
    obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨z, hzV, rfl⟩
    let W : Set (AlgPoint K A K × K) :=
      {q | P.g.eval₂ q.1.toAlgHom.toRingHom q.2 ≠ 0}
    have hW : IsOpen W :=
      isOpen_ne_fun (continuous_point_polynomial_eval (K := K) P.g) continuous_const
    have hVW : V ∩ W ∈ 𝓝 (z.1.1, z.1.2) := (hV.inter hW).mem_nhds ⟨hzV, z.2.2⟩
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hVW
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hv
    filter_upwards [hu, eventually_exists_near_root P z hε] with p hpu hp
    obtain ⟨x, hx, hxε⟩ := hp
    have hpx : (p, x) ∈ V ∩ W := huv ⟨hpu, hball hxε⟩
    exact ⟨⟨(p, x), hx, hpx.2⟩, hpx.1, rfl⟩
  exact hprojection.comp (standardEtalePointHomeomorph (K := K) P).isOpenMap

end StandardEtale

/-- Over a field with Henselian norm valuation ring, restriction along a smooth algebra map
is open on actual points. -/
theorem isOpenMap_smoothAlgebra (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring]
    (A : Type v) [CommRing A] [Algebra K A]
    (B : Type w) [CommRing B] [Algebra K B] [Algebra A B]
    [IsScalarTower K A B] [Algebra.Smooth A B] :
    IsOpenMap (AlgPoint.precomp (S := K) (IsScalarTower.toAlgHom K A B)) := by
  classical
  let r : AlgPoint K B K → AlgPoint K A K :=
    AlgPoint.precomp (IsScalarTower.toAlgHom K A B)
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨q, hq, rfl⟩
  let p : Ideal B := RingHom.ker q.toAlgHom.toRingHom
  let : p.IsPrime := RingHom.ker_isPrime q.toAlgHom.toRingHom
  let : Algebra.IsSmoothAt A p := inferInstance
  obtain ⟨f, hfp, n, polyAlgebra, polyTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := p)
  let := polyAlgebra
  let := polyTower
  let := hEtale
  let : IsScalarTower K (MvPolynomial (Fin n) A) (Localization.Away f) :=
    IsScalarTower.of_algebraMap_eq fun k => by
      simp only [IsScalarTower.algebraMap_apply K A (Localization.Away f),
        IsScalarTower.algebraMap_apply K A (MvPolynomial (Fin n) A),
        IsScalarTower.algebraMap_apply A (MvPolynomial (Fin n) A) (Localization.Away f)]
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation
    (R := MvPolynomial (Fin n) A) (S := Localization.Away f)
  have hpoly := AlgPoint.isOpenMap_precomp_mvPolynomial (R := K) (A := A) (S := K) (Fin n)
  have hetale := isOpenMap_standardEtale (K := K) P
  let g : AlgPoint K (Localization.Away f) K → AlgPoint K B K :=
    AlgPoint.precomp (Algebra.algHom K B (Localization.Away f))
  have hcomp : r ∘ g =
      AlgPoint.precomp (S := K) (IsScalarTower.toAlgHom K A (MvPolynomial (Fin n) A)) ∘
        AlgPoint.precomp (S := K)
          (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) A) (Localization.Away f)) := by
    funext z
    apply AlgPoint.ext
    intro a
    change z.toAlgHom (algebraMap B (Localization.Away f) (algebraMap A B a)) =
      z.toAlgHom (algebraMap (MvPolynomial (Fin n) A) (Localization.Away f)
        (algebraMap A (MvPolynomial (Fin n) A) a))
    rw [← IsScalarTower.algebraMap_apply A B (Localization.Away f),
      ← IsScalarTower.algebraMap_apply A (MvPolynomial (Fin n) A) (Localization.Away f)]
  have hopen : IsOpenMap (r ∘ g) := by
    rw [hcomp]
    exact hpoly.comp hetale
  have hfq : q f ≠ 0 := hfp
  have hqunit : ∀ m : Submonoid.powers f, IsUnit (q m) :=
    (AlgPoint.unit_powers_iff f q).mpr (isUnit_iff_ne_zero.mpr hfq)
  let ql : AlgPoint K (Localization.Away f) K :=
    (AlgPoint.localizationPointEquiv (R := K) (S := K)
      (L := Localization.Away f) (Submonoid.powers f)).symm ⟨q, hqunit⟩
  have hql : g ql = q := by
    ext b
    exact AlgPoint.localizationPointEquiv_symm_algebraMap (R := K) (S := K)
      (L := Localization.Away f) (Submonoid.powers f) ⟨q, hqunit⟩ b
  have hV : IsOpen ((r ∘ g) '' (g ⁻¹' U)) :=
    hopen _ (hU.preimage (AlgPoint.continuous_precomp _))
  have hVmem : r q ∈ (r ∘ g) '' (g ⁻¹' U) := by
    refine ⟨ql, ?_, ?_⟩
    · change g ql ∈ U
      rwa [hql]
    · change r (g ql) = r q
      rw [hql]
  exact mem_of_superset (hV.mem_nhds hVmem) (by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨g t, ht, rfl⟩)

/-- On affine schemes over a field with Henselian norm valuation ring, smooth morphisms are
open on the actual global-section points. -/
theorem isOpenMap_affineSmoothPointMap (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring]
    {X Y : Over (Spec (CommRingCat.of K))} [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [Smooth f.left] :
    IsOpenMap (X := RingPoint K X K) (Y := RingPoint K Y K)
      (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K)) := by
  let A : Type u := AffineCoordinateRing K Y
  let B : Type u := AffineCoordinateRing K X
  let phi : A →ₐ[K] B := affineCoordinatePullback K f
  let : Algebra A B := phi.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq
    (fun k => (phi.commutes k).symm)
  have hs : RingHom.Smooth f.left.appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := f.left)).mp inferInstance
  let : Algebra.Smooth A B := hs
  have hopen : IsOpenMap (AlgPoint.precomp (S := K) phi) := by
    have h := isOpenMap_smoothAlgebra K A B
    have hphi : IsScalarTower.toAlgHom K A B = phi := by
      ext a
      rfl
    rwa [hphi] at h
  have heq : (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K)) =
      (affineSchemePointHomeomorph K Y K).symm ∘ AlgPoint.precomp phi ∘
        (affineSchemePointHomeomorph K X K) := by
    funext p
    apply (affineSchemePointEquiv K Y K).injective
    change affineSchemePointEquiv K Y K (p ≫ f) =
      (affineSchemePointEquiv K Y K)
        ((affineSchemePointEquiv K Y K).symm
          (AlgPoint.precomp phi (affineSchemePointEquiv K X K p)))
    rw [Equiv.apply_symm_apply]
    exact affineSchemePointEquiv_natural K K f p
  rw [heq]
  exact (affineSchemePointHomeomorph K Y K).symm.isOpenMap.comp
    (hopen.comp (affineSchemePointHomeomorph K X K).isOpenMap)

end HenselianSmoothOpen

/-- Smooth morphisms of affine schemes over a nontrivially normed ultrametric field with
Henselian norm valuation ring induce open maps on rational points. -/
theorem henselianSmoothRationalPointOpenMap :
    HenselianSmoothRationalPointOpenMapStatement.{u} := by
  intro K _ _ _ X Y _ _ f _
  let _ : TopologicalSpace (RationalPoint K X) := rationalPointTopology K X
  let _ : TopologicalSpace (RationalPoint K Y) := rationalPointTopology K Y
  have hopen := HenselianSmoothOpen.isOpenMap_affineSmoothPointMap K f
  have heq : (fun p : RationalPoint K X => p ≫ f) =
      (rationalPointHomeomorph K Y).symm ∘
        (fun q : RingPoint K X K => (q ≫ f : RingPoint K Y K)) ∘
          rationalPointHomeomorph K X := by
    funext p
    apply (rationalPointHomeomorph K Y).injective
    rw [Function.comp_apply, Function.comp_apply, Homeomorph.apply_symm_apply]
    exact rationalPointEquiv_natural K f p
  rw [heq]
  exact (rationalPointHomeomorph K Y).symm.isOpenMap.comp
    (hopen.comp (rationalPointHomeomorph K X).isOpenMap)

end Langlands.AlgebraicGeometry.PointTopology
