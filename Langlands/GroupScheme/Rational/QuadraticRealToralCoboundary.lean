import Langlands.GroupScheme.Rational.QuadraticRealCover

/-! # Torus coboundaries from square roots over inert real places -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField
open Langlands.AlgebraicGeometry.PointTopology Langlands.Global.AdelicFunctoriality
open scoped NumberField.LiesOver InfiniteExtension CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuadraticToralReduction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

attribute [local instance] upperCompletion_isScalarTower

private theorem affinePointsBaseChange_postcomp {F K M : Type u} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    {T G : GroupScheme (Spec (CommRingCat.of F))} (i : T ⟶ G)
    (x : T.affinePoints (CommAlgCat.of F M)) :
    affinePointsBaseChangeMulEquiv F K M G (x ≫ i.hom.hom) =
      affinePointsBaseChangeMulEquiv F K M T x ≫ ((baseChange (algebraBaseMap F K)).map i).hom.hom := by
  rw [affinePointsBaseChangeMulEquiv_eq_ringPoint, affinePointsBaseChangeMulEquiv_eq_ringPoint]
  exact ringPointBaseChangeEquiv_natural F K M i.hom.hom x

section Inert

variable {F L : Type u} [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]
  {w : InfinitePlace F} (v : InfinitePlacesAbove L w)
  (hdeg : Module.finrank F L = 2) (hw : w.IsReal) (hv : v.1.IsComplex)
  (σ : L ≃ₐ[F] L)
  {G T : GroupScheme (Spec (CommRingCat.of F))} (i : T ⟶ G)

local notation "K" => w.Completion
local notation "M" => (upperCompletion v)
local notation "τ" => (inertConjugation v hdeg hw hv σ)
local notation "b" => (algebraBaseMap F K)
local notation "G₁" => (Functor.obj (baseChange b) G)
local notation "T₁" => (Functor.obj (baseChange b) T)

private theorem exists_lift_of_inert_square (ξ : Cocycle G (ringTest F L))
    (hc : SubgroupFunctor.range ((baseChange (algebraBaseMap F L)).map i) =
      (Functor.obj (baseChange (algebraBaseMap F L)) G).pointCentralizer
        ((baseChangeBasePointsEquiv (algebraBaseMap F L) G).symm (GaloisCocycle.value ξ σ)))
    (s : (G₁).affinePoints (CommAlgCat.of K M))
    (hs : s * s = GaloisCocycle.value (inertRestriction v ξ) τ) :
    ∃ t : (T₁).affinePoints (CommAlgCat.of K M), t ≫ ((baseChange b).map i).hom.hom = s := by
  let c := algebraBaseMap F L
  let B := baseChange c
  let e := ringTestRestrictScalarsIso F L M
  let r := ringTestMap F (IsScalarTower.toAlgHom F L M)
  let y := GaloisCocycle.value ξ σ
  let Z := ringTest L M
  let a := (affinePointsBaseChangeMulEquiv F K M G).symm s
  let x : G.affinePoints (CommAlgCat.of F M) := r ≫ y
  have ha : a * a = x := by
    rw [← map_mul, hs, inertRestriction_value]
  have hcomm : a * x = x * a := by rw [← ha, mul_assoc]
  let a' := (baseChangePointsEquiv c G Z).symm (e.hom ≫ a)
  have ha' : a' ∈ (SubgroupFunctor.range (B.map i)).carrier Z := by
    change a' ∈ (SubgroupFunctor.range ((baseChange c).map i)).carrier Z
    rw [hc, mem_pointCentralizer_baseChange_iff, MulEquiv.apply_symm_apply]
    have he : (Over.homMk (U := (Over.map c).obj Z) (V := Over.mk c) Z.hom (by simp)) =
        e.hom ≫ r := by
      apply Over.OverMorphism.ext
      change Z.hom = 𝟙 _ ≫ r.left
      rw [Category.id_comp]
      rfl
    rw [he, Category.assoc]
    change (e.hom ≫ a) * (e.hom ≫ x) = (e.hom ≫ x) * (e.hom ≫ a)
    rw [← MonObj.comp_mul, ← MonObj.comp_mul, hcomm]
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
    MulEquiv.apply_symm_apply, SubgroupFunctor.mem_range] at ha'
  obtain ⟨t', ht'⟩ := ha'
  let t := e.inv ≫ t'
  have ht : t ≫ i.hom.hom = a := by
    rw [Category.assoc, ht', Iso.inv_hom_id_assoc]
  refine ⟨affinePointsBaseChangeMulEquiv F K M T t, ?_⟩
  rw [← affinePointsBaseChange_postcomp i, ht, MulEquiv.apply_symm_apply]

/-- The lift to the descended centralizer torus is a coboundary on the
actual real pullback when the ambient quadratic value has a norm-one square root. -/
theorem isTrivial_toral_inert (hσ : σ ≠ 1) (hi : IsClosedSubgroup i)
    (ξ : Cocycle G (ringTest F L)) (d : Cocycle T (ringTest F L))
    (hc : SubgroupFunctor.range ((baseChange (algebraBaseMap F L)).map i) =
      (Functor.obj (baseChange (algebraBaseMap F L)) G).pointCentralizer
        ((baseChangeBasePointsEquiv (algebraBaseMap F L) G).symm (GaloisCocycle.value ξ σ)))
    (hmap : GaloisCocycle.value d σ ≫ i.hom.hom = GaloisCocycle.value ξ σ)
    (s : (G₁).affinePoints (CommAlgCat.of K M))
    (hs : s * s = GaloisCocycle.value (inertRestriction v ξ) τ)
    (hτs : GaloisPoint.conjugate K M G₁ τ s = s⁻¹) : (d.baseChangePullback b).IsTrivial := by
  apply (isTrivial_inertRestriction_iff v d hdeg hw hv).mp
  let : IsGalois K M := inert_isGalois v hw hv
  obtain ⟨t, ht⟩ := exists_lift_of_inert_square v hdeg hw hv σ i ξ hc s hs
  let i₁ := (baseChange b).map i
  let : Mono i₁.hom.hom := (hi.baseChange b).mono_overHom
  apply (GaloisCocycle.isTrivial_iff _).mpr
  refine ⟨t, fun ρ => ?_⟩
  have hcard : Nat.card (M ≃ₐ[K] M) = 2 :=
    (IsGalois.card_aut_eq_finrank K M).trans (completion_finrank_of_complex v hw hv)
  obtain ⟨q, -, hq⟩ := (Nat.card_eq_two_iff' (1 : M ≃ₐ[K] M)).mp hcard
  have hqτ : τ = q := hq τ (inertConjugation_ne v hdeg hw hv σ hσ)
  by_cases hρ : ρ = 1
  · subst ρ
    rw [GaloisCocycle.value, GaloisCocycle.arrow_one, Cocycle.toFun_self,
      GaloisPoint.conjugate_one, mul_inv_cancel]
  · have hρτ : ρ = τ := (hq ρ hρ).trans hqτ.symm
    rw [hρτ]
    apply (cancel_mono i₁.hom.hom).mp
    let r := ringTestMap F (IsScalarTower.toAlgHom F L M)
    have hval : GaloisCocycle.value (inertRestriction v d) τ ≫ i₁.hom.hom =
        GaloisCocycle.value (inertRestriction v ξ) τ := by
      apply (affinePointsBaseChangeMulEquiv F K M G).symm.injective
      have he := affinePointsBaseChange_postcomp («K» := K) i (r ≫ GaloisCocycle.value d σ)
      rw [← inertRestriction_value v d hdeg hw hv σ, MulEquiv.apply_symm_apply] at he
      rw [← he, MulEquiv.symm_apply_apply, inertRestriction_value v d hdeg hw hv σ,
        inertRestriction_value v ξ hdeg hw hv σ, Category.assoc, hmap]
    have hconj : GaloisPoint.conjugate K M T₁ τ t ≫ i₁.hom.hom =
        GaloisPoint.conjugate K M G₁ τ s := by
      change (ringTestMap K (τ).toAlgHom ≫ t) ≫ i₁.hom.hom = ringTestMap K (τ).toAlgHom ≫ s
      rw [Category.assoc, ht]
    rw [hval, MonObj.mul_comp, GrpObj.inv_comp, ht, hconj, hτs, inv_inv, hs]

end Inert

end Langlands.GroupScheme.QuadraticToralReduction
