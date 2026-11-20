import Langlands.GroupScheme.Rational.RealPointTopology
import Langlands.GroupScheme.Rational.RealTorusNormTopology
import Langlands.GroupScheme.Rational.CorootRationalGaloisTransport
import Langlands.GroupScheme.Torus.SplitCocharacterGeneration
import Langlands.Geometry.Building.DescendedApartmentLinearPart
import Langlands.Geometry.Building.KPTorusCharacterFiltration
import Langlands.LinearAlgebra.RootDatumInvolutionNorm

/-! # The split torus image from fixed absolute coroots -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.CocharacterUniformizer (cocharacterPoints)

namespace Langlands.GroupScheme.RealPointTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

local notation "b" => algebraBaseMap ℝ ℂ

local instance : IsAlgClosure ℝ ℂ :=
  ⟨inferInstance, Algebra.IsAlgebraic.of_finite ℝ ℂ⟩

local instance (G : GroupScheme (Spec (CommRingCat.of ℝ))) :
    Group (RingPoint ℝ G.X ℝ) := G.ringPointGroup (CommAlgCat.of ℝ ℝ)

private theorem conj_mul_conj : Complex.conjAe * Complex.conjAe = 1 := by
  ext z
  simp

section GaloisEvaluation

variable (k K : Type) [Field k] [Field K] [Algebra k K]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "T_K" =>
  CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T

private theorem cocharacterPoints_eq_value (ν : cocharacterLattice T_K) (value : Kˣ) :
    cocharacterPoints K T_K ν value =
      rationalCocharacterValue k K T.toGrp (CommGroupScheme.groupHom ν) value := rfl

private theorem cocharacterPoints_rationalConjugate_of_fixed (σ : K ≃ₐ[k] K)
    (ν : cocharacterLattice T_K) (value : Kˣ) (hvalue : Units.map σ.toMonoidHom value = value) :
    rationalConjugate k K T.toGrp σ (cocharacterPoints K T_K ν value) =
      cocharacterPoints K T_K (cocharacterLattice.galoisRepresentation k K T σ ν) value := by
  have htransport :
      CommGroupScheme.groupHom (cocharacterLattice.galoisRepresentation k K T σ ν) =
        transportCocharacter (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) T.toGrp (CommGroupScheme.groupHom ν) := by
    exact (congrArg CommGroupScheme.groupHom
      (cocharacterLattice.galoisRepresentation_apply k K T σ ν)).trans
      (cocharacterLattice.groupHom_transport
        (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) T ν)
  rw [cocharacterPoints_eq_value k K T ν value, cocharacterPoints_eq_value k K T, htransport]
  have h := rationalCocharacterValue_rationalConjugate k K T.toGrp σ (CommGroupScheme.groupHom ν)
    value
  rwa [hvalue] at h

private theorem cocharacterPoints_add_generic (ν ν' : cocharacterLattice T_K) (value : Kˣ) :
    cocharacterPoints K T_K (ν + ν') value =
      cocharacterPoints K T_K ν value * cocharacterPoints K T_K ν' value :=
  comp_groupHom_add _ ν ν'

private theorem rationalExtend_norm_cocharacterPoints_of_quadratic
    [FiniteDimensional k K] [IsGalois k K] [IsAffine T.X.left]
    (σ : K ≃ₐ[k] K) (hne : (1 : K ≃ₐ[k] K) ≠ σ)
    (hgal : ∀ τ : K ≃ₐ[k] K, τ = 1 ∨ τ = σ)
    (ν : cocharacterLattice T_K) (value : Kˣ) (hvalue : Units.map σ.toMonoidHom value = value) :
    rationalExtend k K T.toGrp (rationalNorm k K T (cocharacterPoints K T_K ν value)) =
      cocharacterPoints K T_K (ν + cocharacterLattice.galoisRepresentation k K T σ ν) value := by
  classical
  have huniv : (Finset.univ : Finset (K ≃ₐ[k] K)) = {1, σ} := by
    ext τ
    simpa only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff] using hgal τ
  rw [rationalExtend_norm, huniv, Finset.prod_insert (by simpa using hne),
    Finset.prod_singleton, rationalConjugate_one, cocharacterPoints_rationalConjugate_of_fixed
      k K T σ ν value hvalue, cocharacterPoints_add_generic]

end GaloisEvaluation

variable {G : GroupScheme (Spec (CommRingCat.of ℝ))} [IsAffine G.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of ℝ))}
  (i : T.toGrp ⟶ G)

local notation "T_C" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "i_C" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private theorem conj_negOne_fixed : Units.map Complex.conjAe.toMonoidHom (-1 : ℂˣ) = -1 := by
  apply Units.ext
  change Complex.conjAe (-1 : ℂ) = -1
  rw [map_neg, map_one]

variable [IsAffine T.X.left]

private theorem one_ne_conj : (1 : ℂ ≃ₐ[ℝ] ℂ) ≠ Complex.conjAe := by
  intro h
  have hi := congrArg (fun e : ℂ ≃ₐ[ℝ] ℂ => (e Complex.I).im) h
  norm_num at hi

private theorem complex_galois_elements (σ : ℂ ≃ₐ[ℝ] ℂ) : σ = 1 ∨ σ = Complex.conjAe := by
  rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
  · exact Or.inl (AlgEquiv.coe_toAlgHom_injective h)
  · exact Or.inr (AlgEquiv.coe_toAlgHom_injective h)

set_option linter.defProp false in
private def rationalExtend_norm_cocharacterPoints_negOne (ν : cocharacterLattice T_C) :=
  rationalExtend_norm_cocharacterPoints_of_quadratic ℝ ℂ T Complex.conjAe one_ne_conj
    complex_galois_elements ν (-1) conj_negOne_fixed

variable [LocallyOfFiniteType T.X.hom]

private theorem map_rationalNorm_mem_identityComponent (hT : IsSplitTorus (T_C).toGrp)
    (x : rationalPoints (T_C).toGrp) :
    rationalPoints.map i (rationalNorm ℝ ℂ T x) ∈ identityComponentPreimage G := by
  let : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology ℝ T.X
  let f := (rationalRingPointMulEquiv G).toMonoidHom.comp (rationalPoints.map i)
  have hf : Continuous f := by
    change Continuous (fun p : rationalPoints T.toGrp => rationalPointEquiv ℝ G.X
      (p ≫ i.hom.hom))
    exact ((continuous_affineSchemePointMap ℝ ℝ i.hom.hom).comp
      (rationalPointHomeomorph ℝ T.X).continuous).congr
      (fun p => (rationalPointEquiv_natural ℝ i.hom.hom p).symm)
  have ht := GaloisNorm.rationalNorm_mem_connectedComponent_one T hT x
  have h : f (rationalNorm ℝ ℂ T x) ∈ connectedComponent (f 1) :=
    hf.mapsTo_connectedComponent 1 ht
  change f (rationalNorm ℝ ℂ T x) ∈ connectedComponent (1 : RingPoint ℝ G.X ℝ)
  simpa only [map_one f] using h

private theorem cocharacterPoints_mem_identityComponent_of_sign (hT : IsSplitTorus (T_C).toGrp)
    (ν : cocharacterLattice T)
    (hneg : rationalPoints.map i (cocharacterPoints ℝ T ν (-1)) ∈ identityComponentPreimage G)
    (u : ℝˣ) :
    rationalPoints.map i (cocharacterPoints ℝ T ν u) ∈ identityComponentPreimage G := by
  let v : ℝˣ := Units.mk0 (Real.sqrt |(u : ℝ)|)
    (ne_of_gt (Real.sqrt_pos.2 (abs_pos.2 (Units.ne_zero u))))
  have hv : ((v * v : ℝˣ) : ℝ) = |(u : ℝ)| := Real.mul_self_sqrt (abs_nonneg _)
  have hsq : rationalPoints.map i (cocharacterPoints ℝ T ν (v * v)) ∈
      identityComponentPreimage G := by
    rw [map_mul, ← pow_two, ← Complex.finrank_real_complex, ← rationalNorm_extend]
    exact map_rationalNorm_mem_identityComponent i hT _
  by_cases hu : 0 ≤ (u : ℝ)
  · have hval : u = v * v := Units.ext ((abs_of_nonneg hu).symm.trans hv.symm)
    rwa [hval]
  · have hval : u = -1 * (v * v) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul, hv, abs_of_neg (lt_of_not_ge hu),
        neg_neg]
    rw [hval, map_mul, map_mul]
    exact (identityComponentPreimage G).mul_mem hneg hsq

private def cocharacterIdentityLattice : Submodule ℤ (cocharacterLattice T_C) where
  carrier := {ν | rationalPoints.map i_C (cocharacterPoints ℂ T_C ν (-1)) ∈
    (identityComponentPreimage G).map (rationalExtend ℝ ℂ G)}
  zero_mem' := by
    have hz : cocharacterPoints ℂ T_C 0 (-1) = 1 := comp_groupHom_zero _
    simp only [Set.mem_ofPred_eq, hz, map_one, Subgroup.one_mem]
  add_mem' := by
    intro ν ν' hν hν'
    simp only [Set.mem_ofPred_eq, cocharacterPoints_add_generic ℝ ℂ T, map_mul]
    exact Subgroup.mul_mem _ hν hν'
  smul_mem' := by
    intro n ν hν
    have hn : cocharacterPoints ℂ T_C (n • ν) (-1) =
        cocharacterPoints ℂ T_C ν (-1) ^ n := comp_groupHom_zsmul _ n ν
    simp only [Set.mem_ofPred_eq, hn, map_zpow]
    exact Subgroup.zpow_mem _ hν n

omit [IsAffine T.X.left] [LocallyOfFiniteType T.X.hom] in
private theorem mem_cocharacterIdentityLattice (ν : cocharacterLattice T_C) :
    ν ∈ cocharacterIdentityLattice i ↔
      rationalPoints.map i_C (cocharacterPoints ℂ T_C ν (-1)) ∈
        (identityComponentPreimage G).map (rationalExtend ℝ ℂ G) := Iff.rfl

private theorem cocharacterNorm_mem_identityLattice (hT : IsSplitTorus (T_C).toGrp)
    (ν : cocharacterLattice T_C) :
    ν + cocharacterLattice.galoisRepresentation ℝ ℂ T Complex.conjAe ν ∈
      cocharacterIdentityLattice i := by
  apply (mem_cocharacterIdentityLattice i _).mpr
  let z := cocharacterPoints ℂ T_C ν (-1)
  refine ⟨rationalPoints.map i (rationalNorm ℝ ℂ T z),
    map_rationalNorm_mem_identityComponent i hT z, ?_⟩
  rw [rationalExtend_map ℝ ℂ i, rationalExtend_norm_cocharacterPoints_negOne]

omit [IsAffine T.X.left] [LocallyOfFiniteType T.X.hom] in
private theorem map_cocharacterPoints_negOne_mem_of_baseChange_mem
    (ν : cocharacterLattice T) (hν : cocharacterLattice.baseChange b T ν ∈
      cocharacterIdentityLattice i) :
    rationalPoints.map i (cocharacterPoints ℝ T ν (-1)) ∈ identityComponentPreimage G := by
  apply (Subgroup.mem_map_iff_mem
    (Langlands.Geometry.Building.rationalExtend_injective_of_isAffine ℝ ℂ G)).mp
  have hext := (Langlands.Geometry.Building.rationalExtend_cocharacterPoints ℝ ℂ T ν (-1)).trans
    (congrArg (cocharacterPoints ℂ T_C (cocharacterLattice.baseChange b T ν))
      (Units.map_neg_one (algebraMap ℝ ℂ)))
  rw [rationalExtend_map ℝ ℂ i, hext]
  exact (mem_cocharacterIdentityLattice i _).mp hν

omit [IsAffine T.X.left] [LocallyOfFiniteType T.X.hom] in
private theorem splitSubtorus_maps_identityComponent_of_values
    (hc : ∀ (ν : cocharacterLattice T) (u : ℝˣ),
      rationalPoints.map i (cocharacterPoints ℝ T ν u) ∈ identityComponentPreimage G)
    {S : CommGroupScheme (Spec (CommRingCat.of ℝ))} (hS : IsSplitTorus S.toGrp)
    (a : S ⟶ T) (s : rationalPoints S.toGrp) :
    rationalPoints.map (CommGroupScheme.groupHom a ≫ i) s ∈ identityComponentPreimage G := by
  classical
  obtain ⟨K, hK, ν, hprod⟩ := hS.exists_cocharacterPoints_prod
  let : Fintype K := hK
  obtain ⟨u, hu⟩ := hprod s
  have hm : rationalPoints.map (CommGroupScheme.groupHom a) s ∈
      (identityComponentPreimage G).comap (rationalPoints.map i) := by
    rw [hu, map_prod]
    apply Subgroup.prod_mem
    intro j _
    let p := (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of ℝ)))).symm (u j)
    have hcomp : rationalPoints.map (CommGroupScheme.groupHom a)
          (cocharacterPoints ℝ S (ν j) (u j)) =
        cocharacterPoints ℝ T (ν j ≫ a) (u j) := by
      change (p ≫ (CommGroupScheme.groupHom (ν j)).hom.hom) ≫
          (CommGroupScheme.groupHom a).hom.hom =
        p ≫ (CommGroupScheme.groupHom (ν j ≫ a)).hom.hom
      exact (comp_groupHom_comp p (ν j) a).symm
    rw [hcomp]
    exact hc (ν j ≫ a) (u j)
  simpa only [Subgroup.mem_comap, rationalPoints.map_apply, Grp.comp_hom_hom,
    Category.assoc] using hm

set_option linter.defProp false in
/-- Conjugation-fixed simple coroot values in the extended identity component
suffice to put the real split subtorus image in the real identity component. -/
def splitSubtorus_maps_identityComponent_of_fixedCoroots
    (hT : IsSplitTorus (T_C).toGrp)
    {J : Type} [Fintype J]
    (P : RootDatum J (characterLattice T_C) (cocharacterLattice T_C))
    [P.IsReduced] (hspan : P.corootSpan ℤ = ⊤)
    (σ : P.Aut) (hσ : ∀ x : cocharacterLattice T_C,
      σ.coweightEquiv x = cocharacterLattice.galoisRepresentation ℝ ℂ T Complex.conjAe x)
    (hfixed : ∀ (B : P.Base) (j : J), j ∈ B.support →
      σ.indexEquiv j = j →
      rationalPoints.map i_C (cocharacterPoints ℂ T_C (P.coroot j) (-1)) ∈
        (identityComponentPreimage G).map (rationalExtend ℝ ℂ G))
    {S : CommGroupScheme (Spec (CommRingCat.of ℝ))} (hS : IsSplitTorus S.toGrp)
    (a : S ⟶ T) (s : rationalPoints S.toGrp) :
    rationalPoints.map (CommGroupScheme.groupHom a ≫ i) s ∈ identityComponentPreimage G := by
  classical
  have hσinv : Function.Involutive σ.coweightEquiv := by
    intro x
    rw [hσ, hσ]
    change (cocharacterLattice.galoisRepresentation ℝ ℂ T Complex.conjAe *
      cocharacterLattice.galoisRepresentation ℝ ℂ T Complex.conjAe) x = x
    rw [← map_mul, conj_mul_conj, map_one]
    rfl
  obtain ⟨B, hB⟩ := Langlands.LinearAlgebra.exists_base_involution_norm P σ hspan hσinv
  have hsimple : Submodule.span ℤ (P.coroot '' {j | j ∈ B.support ∧ σ.indexEquiv j = j}) ≤
      cocharacterIdentityLattice i := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, ⟨hj, hfix⟩, rfl⟩
    exact (mem_cocharacterIdentityLattice i _).mpr (hfixed B j hj hfix)
  apply splitSubtorus_maps_identityComponent_of_values i _ hS a s
  intro ν u
  apply cocharacterPoints_mem_identityComponent_of_sign i hT ν _ u
  apply map_cocharacterPoints_negOne_mem_of_baseChange_mem i ν
  let x := cocharacterLattice.baseChange b T ν
  have hx := cocharacterLattice.galoisRepresentation_baseChange ℝ ℂ T Complex.conjAe ν
  obtain ⟨y, hy⟩ := hB x ((hσ x).trans hx)
  have hnorm : y + σ.coweightEquiv y ∈ cocharacterIdentityLattice i := by
    rw [hσ]
    exact cocharacterNorm_mem_identityLattice i hT y
  simpa only [sub_add_cancel] using Submodule.add_mem _ (hsimple hy) hnorm

end Langlands.GroupScheme.RealPointTopology
