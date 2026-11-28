import Langlands.GroupScheme.Rational.GaloisCocycleStronglyRegular
import Langlands.GroupScheme.Torus.MaximalBaseChangeReflection

/-! # Factorization through the centralizer of a quadratic cocycle value -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuadraticToralReduction

set_option backward.isDefEq.respectTransparency false

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [IsGalois F L] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- The nonidentity automorphism of a quadratic Galois extension enumerates the
Galois group together with the identity. -/
theorem quadratic_generator (h : Module.finrank F L = 2) :
    ∃ σ : L ≃ₐ[F] L, σ ≠ 1 ∧ σ * σ = 1 ∧ ∀ τ : L ≃ₐ[F] L, τ = 1 ∨ τ = σ := by
  have hc : Nat.card (L ≃ₐ[F] L) = 2 := (IsGalois.card_aut_eq_finrank F L).trans h
  obtain ⟨σ, hσ, huniq⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).mp hc
  refine ⟨σ, hσ, ?_, fun τ => ?_⟩
  · simpa only [hc, pow_two] using (pow_card_eq_one' (x := σ))
  · by_cases hτ : τ = 1
    · exact Or.inl hτ
    · exact Or.inr (huniq τ hτ)

/-- If a point has maximal-torus centralizer after a field extension, then its
centralizer over its own field is already a maximal torus. -/
theorem exists_maximalTorus_pointCentralizer_of_extension
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    {H : GroupScheme (Spec (CommRingCat.of K))} [IsSeparated H.X.hom]
    (z : rationalPoints H) {T : CommGroupScheme (Spec (CommRingCat.of E))}
    (j : T.toGrp ⟶ (baseChange (algebraBaseMap K E)).obj H) (hj : IsMaximalTorus j)
    (hz : SubgroupFunctor.range j =
      ((baseChange (algebraBaseMap K E)).obj H).pointCentralizer
        ((baseChangeBasePointsEquiv (algebraBaseMap K E) H).symm (toUnit _ ≫ z))) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of K))) (i : S.toGrp ⟶ H),
      IsMaximalTorus i ∧ SubgroupFunctor.range i = H.pointCentralizer z := by
  let b := algebraBaseMap K E
  let B := baseChange b
  obtain ⟨C, c, hc, hclosed⟩ := H.pointCentralizer_isClosedRepresentable z
  have hp : ((H.pointCentralizer z).baseChange b).IsRepresentedBy j :=
    ⟨hj.2.1.mono_overHom, by rw [pointCentralizer_baseChange, hz]⟩
  let e : B.obj C ≅ T.toGrp := (hc.baseChange b).isoOfIsRepresentedBy hp
  have he : e.hom ≫ j = B.map c := (hc.baseChange b).isoOfIsRepresentedBy_hom_comp hp
  have hC : IsTorus C := IsTorus.of_baseChange (K := E) (IsTorus.of_iso e hj.1)
  let S : CommGroupScheme (Spec (CommRingCat.of K)) := { C with comm := hC.isCommMonObj }
  have hmax : IsMaximalTorus (T := S) c := by
    apply IsMaximalTorus.of_baseChange (K := E) hclosed
    rw [← he]
    exact hj.iso_comp (T' := (CommGroupScheme.baseChange b).obj S) e
  exact ⟨S, c, hmax, hc.2⟩

/-- A quadratic cocycle with maximal-torus centralizer at its nonidentity
value lifts to the descended torus on the same cover. -/
theorem factor_of_quadratic_value (ξ : Cocycle G (ringTest F L))
    (σ : L ≃ₐ[F] L) (hσ₂ : σ * σ = 1) (hσcases : ∀ τ : L ≃ₐ[F] L, τ = 1 ∨ τ = σ)
    {S : CommGroupScheme (Spec (CommRingCat.of L))}
    (j : S.toGrp ⟶ (baseChange (algebraBaseMap F L)).obj G) (hj : IsMaximalTorus j)
    (hjc : SubgroupFunctor.range j = ((baseChange (algebraBaseMap F L)).obj G).pointCentralizer
      ((baseChangeBasePointsEquiv (algebraBaseMap F L) G).symm (GaloisCocycle.value ξ σ))) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (d : Cocycle T.toGrp (ringTest F L)),
      IsMaximalTorus i ∧ SubgroupFunctor.range ((baseChange (algebraBaseMap F L)).map i) =
        SubgroupFunctor.range j ∧ ∀ {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ ringTest F L),
        (d.map i).toFun a b = ξ.toFun a b := by
  let b := algebraBaseMap F L
  let y := GaloisCocycle.value ξ σ
  have hval : GaloisCocycle.value ξ (1 : L ≃ₐ[F] L) = 1 := by
    rw [GaloisCocycle.value, GaloisCocycle.arrow_one, Cocycle.toFun_self]
  have hinv : ringTestMap F σ.toAlgHom ≫ y = y⁻¹ := by
    have h := GaloisCocycle.value_mul ξ σ σ
    rw [hσ₂, hval] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hd := hj.2.1.overlap_range_eq_of_galois_range_eq (fun τ => by
    rw [← SubgroupFunctor.descentTransport_range, hjc]
    apply descentTransport_pointCentralizer_of_eq_or_inv b (galoisBaseMap F L τ)
      (galoisBaseMap_over F L τ) G y
    rcases hσcases τ with rfl | rfl
    · left
      change ringTestMap F (1 : L ≃ₐ[F] L).toAlgHom ≫ y = y
      rw [show ringTestMap F (1 : L ≃ₐ[F] L).toAlgHom = 𝟙 _ from ringTestMap_id F L,
        Category.id_comp]
    · exact Or.inr hinv)
  obtain ⟨T, i, e, hi, -, he⟩ := hj.exists_descent_of_overlap_range_eq hd
  have hr : SubgroupFunctor.range ((baseChange b).map i) = SubgroupFunctor.range j := by
    rw [he, SubgroupFunctor.range_iso_comp]
  have hfactor (τ : L ≃ₐ[F] L) : ∃ q : ringTest F L ⟶ T.X,
      q ≫ i.hom.hom = ξ.toFun (𝟙 _) (ringTestMap F τ.toAlgHom) := by
    rcases hσcases τ with rfl | rfl
    · refine ⟨1, ?_⟩
      rw [show ringTestMap F (1 : L ≃ₐ[F] L).toAlgHom = 𝟙 _
        from ringTestMap_id F L, Cocycle.toFun_self, MonObj.one_comp]
    · let z := (baseChangeBasePointsEquiv b G).symm y
      have hz : z ∈ (SubgroupFunctor.range ((baseChange b).map i)).carrier (Over.mk (𝟙 _)) := by
        rw [hr, hjc, mem_pointCentralizer]
        change z * (toUnit (Over.mk (𝟙 _)) ≫ z) = (toUnit (Over.mk (𝟙 _)) ≫ z) * z
        rw [toUnit_unique (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of L))))) (𝟙 _), Category.id_comp]
      obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hz
      refine ⟨baseChangeBasePointsEquiv b T.toGrp t, ?_⟩
      rw [← baseChangeBasePointsEquiv_comp, ht, MulEquiv.apply_symm_apply]
      rfl
  let : Mono i.hom.hom := hi.2.1.mono_overHom
  let htest := fun {Z} a b => Cocycle.factors_of_galois ξ i hfactor (Z := Z) a b
  refine ⟨T, i, ξ.lift i htest, hi, hr, fun a b => ?_⟩
  exact ξ.lift_toFun i htest a b

end Langlands.GroupScheme.QuadraticToralReduction
