import Langlands.AlgebraicGeometry.PointTopology.SmoothAlgebraOpenStatement
import Langlands.AlgebraicGeometry.PointTopology.StandardEtaleOpenProof
import Langlands.AlgebraicGeometry.PointTopology.RelativePolynomialPoints
import Langlands.AlgebraicGeometry.PointTopology.Localization
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Smooth algebra maps are open on complete-field points -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open Filter
open scoped Topology

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Smooth restriction maps are open on actual complete-field algebra points. -/
theorem smoothAlgebraPointOpen : SmoothAlgebraPointOpenStatement.{u, v, w} := by
  classical
  intro K _ _ A _ _ B _ _ _ _ _
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
  have hetale := standardEtalePointOpen K (MvPolynomial (Fin n) A) (Localization.Away f) P
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

end Langlands.AlgebraicGeometry.PointTopology
