import Langlands.GroupScheme.Rational.QuadraticOppositeBorelDescent
import Langlands.GroupScheme.Rational.GaloisTwistedPointDensity
import Langlands.GroupScheme.Rational.GeometricBorelOppositeCocharacter
import Langlands.GroupScheme.Rational.GeometricBorelMinimalParabolic
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.RadicalGaloisInnerTransport
import Langlands.GroupScheme.Rational.TorusTransporterOrbit
import Langlands.GroupScheme.Absolute.FlagInvariantAffineOpenCoverReduction
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry
import Langlands.GroupScheme.Reductive.StarActionQuasiSplitProof

/-! # Existence of a quadratic opposite-Borel torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

private theorem basePoint_smul_inf {S : Scheme.{u}} {G : GroupScheme S}
    (g : Over.mk (𝟙 S) ⟶ G.X) (A B : SubgroupFunctor G) :
    g • (A ⊓ B) = (g • A) ⊓ (g • B) := by
  apply SubgroupFunctor.ext
  intro Z
  apply Subgroup.ext
  intro z
  simp only [SubgroupFunctor.inf_carrier, Subgroup.mem_inf, SubgroupFunctor.mem_basePoint_smul]

variable {F Q : Type u} [Field F] [Infinite F] [Field Q] [Algebra F Q]
  [FiniteDimensional F Q] [IsGalois F Q]
  {G : GroupScheme (Spec (CommRingCat.of F))}

local notation "b" => algebraBaseMap F Q
local notation "GQ" => Functor.obj (GroupScheme.baseChange b) G

/-- A connected reductive group that is quasi-split over a quadratic extension
of an infinite field has a maximal torus obtained by intersecting a Borel
over the quadratic field with its conjugate. -/
theorem exists_quadraticOppositeBorelTorus
    (hdeg : Module.finrank F Q = 2) (hG : IsConnectedReductive G) (hqs : IsQuasiSplit GQ) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ G),
      IsQuadraticOppositeBorelTorus (Q := Q) t := by
  classical
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth (GQ).X.hom := hqs.isConnectedReductive.smooth
  let : IsAffineHom (GQ).X.hom := hqs.isConnectedReductive.isAffineHom
  let : IsAffine (GQ).X.left := isAffine_of_isAffineHom (GQ).X.hom
  have hcard : Nat.card (Q ≃ₐ[F] Q) = 2 := (IsGalois.card_aut_eq_finrank F Q).trans hdeg
  obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : Q ≃ₐ[F] Q)).mp hcard
  obtain ⟨B, j, hj⟩ := hqs.exists_isGeometricBorelSubgroup
  obtain ⟨TQ, t₀, ht⟩ := StarActionQuasiSplit.exists_isMaximalTorus_comp_of_isGeometricBorel
    hqs.isConnectedReductive hj
  let t := t₀ ≫ j
  obtain ⟨ν, hP, hC, hminus⟩ := hj.exists_oppositeDynamicBorel hqs.isConnectedReductive ht t₀ rfl
  let χ := CommGroupScheme.groupHom ν ≫ t
  let χ' := Dynamic.oppositeCocharacter χ
  let U := Dynamic.Affine.unipotentScheme χ
  let u := Dynamic.Affine.unipotentHom χ
  let P := Dynamic.Affine.parabolicScheme χ'
  let p := Dynamic.Affine.parabolicHom χ'
  have hp : IsGeometricBorelSubgroup p := by
    dsimp only [p, χ', χ]
    rw [← groupHom_neg_comp_eq_oppositeCocharacter]
    exact hminus
  let jσ := radicalGaloisHom j σ
  have hjσ : IsGeometricBorelSubgroup jσ :=
    (hj.baseChange hqs.isConnectedReductive (galoisBaseMap F Q σ)).comp_iso
      (descentBaseChangeIso b (galoisBaseMap F Q σ) (galoisBaseMap_over F Q σ) G)
  obtain ⟨w, E, hw'⟩ := minimalParabolicConjugacy Q GQ hqs.isConnectedReductive
    _ _ jσ p hjσ.isMinimalParabolicSubgroup hp.isMinimalParabolicSubgroup
  have hw : w • SubgroupFunctor.range jσ = SubgroupFunctor.range p := by
    rw [SubgroupFunctor.basePoint_smul_range, hw', SubgroupFunctor.range_iso_comp]
  let m := SubgroupFunctor.cellMultiplication u p
  have hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ')).IsRepresentedBy u := by
    simpa only [χ', Dynamic.oppositeCocharacter_oppositeCocharacter] using
      Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let hp' := Dynamic.Affine.isRepresentedBy_parabolicHom χ'
  let : IsOpenImmersion m.left := oppositeCellStatement Q GQ χ' U P u p hU hp'
  let R := (GQ).rightTranslationIso w
  let mW := m ≫ R.hom
  let : IsIso R.hom.left := (Over.forget _).map_isIso R.hom
  let : IsOpenImmersion mW.left := inferInstanceAs (IsOpenImmersion (m.left ≫ R.hom.left))
  have hW : IsOpen (Set.range mW.left) := IsOpenImmersion.isOpen_range mW.left
  have hnW : (Set.range mW.left).Nonempty := by
    let z : (Over.mk (𝟙 (Spec (CommRingCat.of Q)))) ⟶ U.X ⊗ P.X :=
      CartesianMonoidalCategory.lift 1 1
    exact ⟨_, z.left (IsLocalRing.closedPoint Q), rfl⟩
  have hd := galoisTwistedPointDensity_of_isGalois F Q G hG σ hσ 1
  obtain ⟨x, hx, hxD⟩ := hd.inter_open_nonempty _ hW hnW
  obtain ⟨a, y, hy⟩ := Set.mem_iUnion.mp hxD
  let e := GaloisPointComparison.baseChangeCoeffEquiv F Q G
  let g := e.symm a
  let a₀ : G.affinePoints (CommAlgCat.of F Q) := a
  let aσ : G.affinePoints (CommAlgCat.of F Q) := GaloisPoint.conjugate F Q G σ a₀
  let z := e.symm (a₀⁻¹ * 1 * aσ)
  have hy' : z.left y = x := hy
  have hzW : Set.range z.left ⊆ Set.range mW.left := by
    rintro _ ⟨y', rfl⟩
    have : Subsingleton ↥(Over.mk (𝟙 (Spec (CommRingCat.of Q)))).left :=
      inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of Q)))
    rw [show y' = y from Subsingleton.elim _ _, hy']
    exact hx
  have hcell : Set.range (z ≫ R.inv).left ⊆ Set.range m.left := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨v, hv⟩ := hzW ⟨s, rfl⟩
    refine ⟨v, ?_⟩
    change m.left v = R.inv.left (z.left s)
    rw [← hv]
    change m.left v = (m ≫ R.hom ≫ R.inv).left v
    rw [R.hom_inv_id, Category.comp_id]
  obtain ⟨v, v', hfactor⟩ := SubgroupFunctor.exists_cell_factors_of_range_subset u p
    (z ≫ R.inv) hcell
  let q := v ≫ u.hom.hom
  let q' := v' ≫ p.hom.hom
  have hz : z = q * q' * w := by
    have hr := congrArg (fun f => f ≫ R.hom) hfactor
    rw [Category.assoc, R.inv_hom_id, Category.comp_id] at hr
    change z = (q * q') ≫ (GQ).rightTranslation w at hr
    rwa [comp_rightTranslation, constantPoint_self] at hr
  have hgσ : GaloisPointComparison.rationalConjugate F Q G σ g = g * z := by
    apply e.injective
    have ha : e g = a₀ := e.apply_symm_apply a₀
    have hz' : e z = a₀⁻¹ * 1 * aσ := e.apply_symm_apply _
    rw [GaloisPointComparison.baseChangeCoeffEquiv_rationalConjugate, map_mul, ha, hz',
      mul_one, mul_inv_cancel_left]
  have hq : q • SubgroupFunctor.range j = SubgroupFunctor.range j := by
    have hu : q ∈ (SubgroupFunctor.range u).carrier (Over.mk (𝟙 (Spec (CommRingCat.of Q)))) :=
      SubgroupFunctor.mem_range.mpr ⟨v, rfl⟩
    rw [(Dynamic.Affine.isRepresentedBy_unipotentHom χ).2] at hu
    have hq := Dynamic.unipotent_le_parabolic χ _ hu
    rw [← hP.2] at hq
    obtain ⟨s, hs⟩ := SubgroupFunctor.mem_range.mp hq
    rw [← hs, SubgroupFunctor.basePoint_smul_range, range_comp_innerIso_of_mem]
  have hq' : q' • SubgroupFunctor.range p = SubgroupFunctor.range p := by
    dsimp only [q']
    rw [SubgroupFunctor.basePoint_smul_range, range_comp_innerIso_of_mem]
  have hop : SubgroupFunctor.range j ⊓ SubgroupFunctor.range p =
      SubgroupFunctor.range t := by
    rw [hP.2, hp'.2, Dynamic.parabolic_inf_opposite_eq_centralizer, hC]
  let j' := j ≫ ((GQ).innerIso g).hom
  let t' := t ≫ ((GQ).innerIso (g * q)).hom
  have hinter : SubgroupFunctor.range j' ⊓ SubgroupFunctor.range (radicalGaloisHom j' σ) =
      SubgroupFunctor.range t' := by
    dsimp only [j', t']
    rw [radicalGaloisHom_comp_innerIso, ← SubgroupFunctor.basePoint_smul_range,
      ← SubgroupFunctor.basePoint_smul_range, hgσ, mul_smul, ← basePoint_smul_inf,
      hz, mul_smul, hw, mul_smul, hq']
    rw [show SubgroupFunctor.range j ⊓ q • SubgroupFunctor.range p =
        q • (SubgroupFunctor.range j ⊓ SubgroupFunctor.range p) by
          rw [basePoint_smul_inf, hq],
      hop, ← mul_smul, SubgroupFunctor.basePoint_smul_range]
  obtain ⟨T, jT, hT, hTQ⟩ :=
    exists_quadraticOppositeBorelTorus_of_intersection hdeg σ hσ j' TQ t'
      (ht.comp_iso ((GQ).innerIso (g * q))) hinter
  exact ⟨T, jT, hdeg, hT, σ, B, j', hσ, hj.comp_iso ((GQ).innerIso g), hTQ⟩

end Langlands.GroupScheme
