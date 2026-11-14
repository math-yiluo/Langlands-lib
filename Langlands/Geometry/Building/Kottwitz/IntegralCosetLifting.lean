import Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement
import Langlands.GroupScheme.UnramifiedIntegralCosetDescent
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Integral-coset lifting for the actual rational Kottwitz map -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.Kottwitz

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Rational points whose actual coefficient extensions belong to `H`. -/
def rationalCoefficientPreimage (H : Subgroup (reductiveKPoints F F G)) :
    Subgroup (rationalPoints G) :=
  H.comap ((GaloisPoint.extend F (inertiaFixedField F) G).comp
    (rationalCoeffEquiv F G).toMonoidHom)

/-- A conditional lifting step in KP Corollary 11.7.5, on the actual Kottwitz maps.
The geometric exactness and model comparisons are explicit premises. -/
def IntegralCosetLiftingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (M : IntegralModel 𝒪[F] F G), M.IsSmooth →
    ConnectedSpace ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left →
    ∀ (H : Subgroup (reductiveKPoints F F G)),
      (∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (x : reductiveKPoints F F G),
        x ∈ H → GaloisPoint.conjugate F (inertiaFixedField F) G σ x ∈ H) →
      Function.Surjective ((reductiveKottwitz F F G hG).domRestrict H) →
      (∀ x : reductiveKPoints F F G,
        M.HasIntegralCoordinates (inertiaFixedField F) x ↔
          x ∈ H ∧ reductiveKottwitz F F G hG x = 1) →
      ReductiveKottwitzEquivariant F G hG →
      IsReductiveKottwitzRestriction F G hG (reductiveKottwitzRational F G hG) →
      Function.Surjective ((reductiveKottwitzRational F G hG).domRestrict
        (rationalCoefficientPreimage F G H))

/-- Equivariance makes the chosen lift's cocycle integral; integral-coset descent
then produces a rational lift in the same subgroup and with the same Kottwitz value. -/
theorem integralCosetLifting : IntegralCosetLiftingStatement.{u} := by
  intro F _ _ _ _ G hG _ _ M hM hconn H hstable hsurj hint hequiv hres a
  obtain ⟨x, hx⟩ := hsurj (reductiveInvariantInclusion F G hG a)
  have hxval : reductiveKottwitz F F G hG x.val =
      reductiveInvariantInclusion F G hG a := hx
  have hcint : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      M.HasIntegralCoordinates (inertiaFixedField F)
        (x.val⁻¹ * GaloisPoint.conjugate F (inertiaFixedField F) G σ x.val) := by
    intro σ
    apply (hint _).2
    refine ⟨H.mul_mem (H.inv_mem x.property) (hstable σ x.val x.property), ?_⟩
    have hfixed := a.toAdd.property σ
    have hconj : reductiveKottwitz F F G hG
        (GaloisPoint.conjugate F (inertiaFixedField F) G σ x.val) =
        reductiveKottwitz F F G hG x.val := by
      apply Multiplicative.toAdd.injective
      rw [hequiv, hxval]
      exact hfixed
    rw [map_mul, map_inv, hconj, inv_mul_cancel]
  obtain ⟨g, h, hh, hg⟩ := unramifiedIntegralCosetDescent F G M hM hconn x.val hcint
  obtain ⟨hhH, hhκ⟩ := (hint h).1 hh
  have hgH : g ∈ rationalCoefficientPreimage F G H := by
    change GaloisPoint.extend F (inertiaFixedField F) G (rationalCoeffEquiv F G g) ∈ H
    rw [hg]
    exact H.mul_mem x.property hhH
  refine ⟨⟨g, hgH⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.val_injective
  have hκ := hres g
  rw [hg, map_mul, hhκ, mul_one, hxval] at hκ
  exact congrArg Multiplicative.toAdd hκ

/-- The exact rational kernel and surjectivity on a subgroup give the specified
quotient isomorphism, including its value on every representative. -/
theorem rationalSubgroupQuotient_of_zeroKernel
    (hG : IsConnectedReductive G) (hzero : ZeroKernelStatement.{u})
    (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (Z : GroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G) (j : Z ⟶ G)
    (d : ZeroSubgroupDatum i j) (P : Subgroup (rationalPoints G))
    (hsurj : Function.Surjective ((reductiveKottwitzRational F G hG).domRestrict P)) :
    ∃ hN : (d.zeroSubgroup.subgroupOf P).Normal,
      letI := hN
      ∃ e : (P ⧸ d.zeroSubgroup.subgroupOf P) ≃*
          Multiplicative (ReductiveInvariantTarget F G hG),
        ∀ x : P, e (QuotientGroup.mk' (d.zeroSubgroup.subgroupOf P) x) =
          reductiveKottwitzRational F G hG x.val := by
  have hker : d.zeroSubgroup.subgroupOf P =
      ((reductiveKottwitzRational F G hG).domRestrict P).ker := by
    rw [MonoidHom.ker_domRestrict, hzero F G hG S Z i j d]
  have hN : (d.zeroSubgroup.subgroupOf P).Normal := by
    rw [hker]
    infer_instance
  refine ⟨hN, ?_⟩
  let := hN
  let e := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((reductiveKottwitzRational F G hG).domRestrict P) hsurj)
  exact ⟨e, fun _ => rfl⟩

end Langlands.Geometry.Building.Kottwitz
