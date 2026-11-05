import Langlands.GroupScheme.IntegralTorsorPoint
import Langlands.GroupScheme.Dynamic.FlagQuotientFiber
import Langlands.GroupScheme.IntegralModelReduction
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Parabolic-left coverings over complete valuation rings -/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.IntegralParabolicCovering

section Lift

variable (R : Type u) [CommRing R] (I : Ideal R) [I.IsMaximal]
variable [Finite (R ⧸ I)] [IsAdicComplete I R]
variable (G P : GroupScheme (Spec (CommRingCat.of R)))
variable {Q : Over (Spec (CommRingCat.of R))} (q : G.X ⟶ Q) (i : P ⟶ G)
variable [Mono i.hom.hom] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
variable [Smooth P.X.hom] [IsAffineHom P.X.hom]
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)

include hfib in
/-- Every integral point of an exact coset quotient lifts to the group. -/
theorem integral_lifts_of_flagQuotient
    (hconn : ConnectedSpace
      ((baseChange (Spec.algebraMap R (R ⧸ I))).obj P).X.left) :
    ∀ p : RingPoint R Q R, ∃ g : RingPoint R G.X R, g ≫ q = p := by
  intro p
  dsimp only [RingPoint] at p
  let p₀ : RationalPoint R Q := (rationalPointEquiv R Q).symm p
  let X := Dynamic.flagQuotientFiber G q p₀
  let : ModObj P.X X := Dynamic.flagQuotientFiberModObj G q p₀ P i hfib
  let x : RingPoint R X R := IntegralTorsorPoint.integralTorsorPoint R I P X hconn
    (inferInstance : Flat X.hom) (inferInstance : Surjective X.hom)
    (inferInstance : QuasiCompact X.hom)
    (Dynamic.flagQuotientFiber_leftSMul_isIso G q p₀ P i hfib)
  let x₀ : RationalPoint R X := (rationalPointEquiv R X).symm x
  refine ⟨rationalPointEquiv R G.X (x₀ ≫ Dynamic.flagQuotientFiberι G q p₀), ?_⟩
  rw [← rationalPointEquiv_natural]
  have hx : (x₀ ≫ Dynamic.flagQuotientFiberι G q p₀) ≫ q = p₀ := by
    rw [Category.assoc, Dynamic.flagQuotientFiberι_comp, ← Category.assoc]
    have ht : x₀ ≫ toUnit X = 𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of R)))) :=
      toUnit_unique _ _
    rw [ht, Category.id_comp]
  rw [hx]
  exact Equiv.apply_symm_apply _ _

end Lift

section Proper

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- A fraction-field point of a proper scheme extends to a valuation-ring point. -/
theorem exists_ringPoint_changeRing_eq (Q : Over (Spec (CommRingCat.of R)))
    [IsProper Q.hom] (x : RingPoint R Q K) :
    ∃ y : RingPoint R Q R, y.changeRing (Algebra.ofId R K) = x := by
  dsimp only [RingPoint] at x
  have hP : IsProper Q.hom := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hP
  have hv : ValuativeCriterion Q.hom := hP.1.1.1
  let sq : ValuativeCommSq Q.hom :=
    { R := R, K := K, i₁ := x.left, i₂ := 𝟙 _,
      commSq := ⟨(Over.w x).trans (Category.comp_id _).symm⟩ }
  obtain ⟨u⟩ := hv sq
  let l : sq.commSq.LiftStruct := default
  let y₀ : RationalPoint R Q := Over.homMk l.l l.fac_right
  refine ⟨rationalPointEquiv R Q y₀, ?_⟩
  apply RingPoint.ext
  change Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
    (rationalPointEquiv R Q y₀).left = x.left
  rw [rationalPointEquiv_left]
  exact l.fac_left

end Proper

section Covering

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
variable (I : Ideal R) [I.IsMaximal] [Finite (R ⧸ I)] [IsAdicComplete I R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable (G P : GroupScheme (Spec (CommRingCat.of R)))
variable {Q : Over (Spec (CommRingCat.of R))} (q : G.X ⟶ Q) (i : P ⟶ G)
variable [Mono i.hom.hom] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
variable [IsProper Q.hom] [Smooth P.X.hom] [IsAffineHom P.X.hom]
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)

include hfib in
/-- Every fraction-field point is a subgroup point times an integral point. -/
theorem exists_mul_integral
    (hconn : ConnectedSpace
      ((baseChange (Spec.algebraMap R (R ⧸ I))).obj P).X.left)
    (g : ringTest R K ⟶ G.X) :
    ∃ (h : ringTest R K ⟶ P.X) (k : ringTest R R ⟶ G.X),
      (h ≫ i.hom.hom) * (ringTestMap R (Algebra.ofId R K) ≫ k) = g := by
  obtain ⟨y, hy⟩ := exists_ringPoint_changeRing_eq R K Q (g⁻¹ ≫ q)
  obtain ⟨k, hk⟩ := integral_lifts_of_flagQuotient R I G P q i hfib hconn y
  let k' : ringTest R R ⟶ G.X := k
  have hq : g⁻¹ ≫ q = (show ringTest R K ⟶ G.X from
      k.changeRing (Algebra.ofId R K)) ≫ q := by
    rw [← hy, ← hk]
    exact (Category.assoc _ _ _).symm
  obtain ⟨h, hh⟩ := SubgroupFunctor.mem_range.mp ((hfib _ _ _).mp hq)
  let kinv : ringTest R R ⟶ G.X := k'⁻¹
  refine ⟨h, kinv, ?_⟩
  change (h ≫ i.hom.hom) * (ringTestMap R (Algebra.ofId R K) ≫ k'⁻¹) = g
  rw [GrpObj.comp_inv, hh, inv_inv]
  change g * ringTestMap R (Algebra.ofId R K) ≫ k' *
    (ringTestMap R (Algebra.ofId R K) ≫ k')⁻¹ = g
  rw [mul_inv_cancel_right]

include hfib in
/-- The literal parabolic-left product of fraction-field and integral points. -/
theorem range_mul_integral_eq_univ
    (hconn : ConnectedSpace
      ((baseChange (Spec.algebraMap R (R ⧸ I))).obj P).X.left) :
    Set.range (fun h : ringTest R K ⟶ P.X => (h ≫ i.hom.hom : ringTest R K ⟶ G.X)) *
      Set.range (fun k : ringTest R R ⟶ G.X =>
        ringTestMap R (Algebra.ofId R K) ≫ k) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨h, k, hg⟩ := exists_mul_integral R I K G P q i hfib hconn g
  exact ⟨h ≫ i.hom.hom, ⟨h, rfl⟩, ringTestMap R (Algebra.ofId R K) ≫ k, ⟨k, rfl⟩, hg⟩

include hfib in
/-- The covering with fraction-field points and integral sections in model-point form. -/
theorem exists_mul_rationalPoint
    (hconn : ConnectedSpace
      ((baseChange (Spec.algebraMap R (R ⧸ I))).obj P).X.left)
    (g : Over.mk (Spec.algebraMap R K) ⟶ G.X) :
    ∃ (h : Over.mk (Spec.algebraMap R K) ⟶ P.X) (k : RationalPoint R G.X),
      (h ≫ i.hom.hom) * ((Over.homMk (Spec.algebraMap R K) (by simp) :
        Over.mk (Spec.algebraMap R K) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ k) =
          g := by
  obtain ⟨h, k, hk⟩ := exists_mul_integral R I K G P q i hfib hconn g
  have hres : ((Over.homMk (Spec.algebraMap R K) (by simp) :
        Over.mk (Spec.algebraMap R K) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫
          (rationalPointEquiv R G.X).symm k) =
        (show Over.mk (Spec.algebraMap R K) ⟶ G.X from
          ringTestMap R (Algebra.ofId R K) ≫ k) := by
    apply Over.OverMorphism.ext
    change Spec.algebraMap R K ≫ ((rationalPointEquiv R G.X).symm k).left =
      Spec.algebraMap R K ≫ k.left
    exact congrArg (fun t => Spec.algebraMap R K ≫ t)
      (rationalPointEquiv_symm_left R G.X k)
  refine ⟨h, (rationalPointEquiv R G.X).symm k, ?_⟩
  exact (congrArg (fun z => (h ≫ i.hom.hom) * z) hres).trans hk

end Covering

section Model

open IntegralModel

variable {R : Type u} [CommRing R] [IsDomain R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {G P : GroupScheme (Spec (CommRingCat.of K))} {f : P ⟶ G}
  (M : IntegralModel R K G) (N : IntegralModel R K P) (φ : N.Hom M f)

/-- Points of the model over the fraction field are points of its chosen generic group. -/
theorem genericPoint_eq (g : rationalPoints G) :
    rationalPoints.map M.genericIso.hom
      ((baseChangeBasePointsEquiv (Spec.algebraMap R K) M.group).symm
        (baseChangeBasePointsEquiv (Spec.algebraMap R K) M.group
          (rationalPoints.map M.genericIso.inv g))) = g := by
  rw [MulEquiv.symm_apply_apply]
  change g ≫ (M.genericIso.inv ≫ M.genericIso.hom).hom.hom = g
  rw [Iso.inv_hom_id]
  exact Category.comp_id g

/-- The model map transports fraction-field model points to the generic map `f`. -/
theorem genericPoint_map (h : Over.mk (Spec.algebraMap R K) ⟶ N.group.X) :
    rationalPoints.map M.genericIso.hom
      ((baseChangeBasePointsEquiv (Spec.algebraMap R K) M.group).symm
        (h ≫ φ.hom.hom.hom)) =
      rationalPoints.map f (rationalPoints.map N.genericIso.hom
        ((baseChangeBasePointsEquiv (Spec.algebraMap R K) N.group).symm h)) := by
  have he : (baseChangeBasePointsEquiv (Spec.algebraMap R K) M.group).symm
      (h ≫ φ.hom.hom.hom) =
      (baseChangeBasePointsEquiv (Spec.algebraMap R K) N.group).symm h ≫
        ((baseChange (Spec.algebraMap R K)).map φ.hom).hom.hom := by
    apply (baseChangeBasePointsEquiv (Spec.algebraMap R K) M.group).injective
    rw [baseChangeBasePointsEquiv_comp, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
  rw [he]
  change _ ≫
      ((baseChange (Spec.algebraMap R K)).map φ.hom ≫ M.genericIso.hom).hom.hom = _
  rw [φ.generic_comm]
  rfl

/-- The integral-point map is the generic model point of the restricted section. -/
theorem integralPointMap_eq (x : M.integralSections) :
    M.integralPointMap x = rationalPoints.map M.genericIso.hom
      ((baseChangeBasePointsEquiv (Spec.algebraMap R K) M.group).symm
        ((Over.homMk (Spec.algebraMap R K) (by simp) :
          Over.mk (Spec.algebraMap R K) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫
            x)) :=
  rfl

section Factor

variable [ValuationRing R] [Finite (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {Q : Over (Spec (CommRingCat.of R))} (q : M.group.X ⟶ Q)
  [Mono φ.hom.hom.hom] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  [IsProper Q.hom] (hsmooth : N.IsSmooth) (hconn : N.HasConnectedSpecialFibre)
  (hfib : ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ M.group.X),
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range φ.hom).carrier T)

include hsmooth hconn hfib in
/-- Every fraction-field point is a generic subgroup point times an integral point. -/
theorem exists_parabolic_integral_factor (g : rationalPoints G) :
    ∃ (h : rationalPoints P) (x : M.integralSections),
      rationalPoints.map f h * M.integralPointMap x = g := by
  let : Smooth N.group.X.hom := hsmooth
  let : Finite (R ⧸ IsLocalRing.maximalIdeal R) :=
    (inferInstance : Finite (IsLocalRing.ResidueField R))
  have hconn' : ConnectedSpace ((baseChange (Spec.algebraMap R
      (R ⧸ IsLocalRing.maximalIdeal R))).obj N.group).X.left := hconn
  obtain ⟨h, x, hk⟩ := exists_mul_rationalPoint R (IsLocalRing.maximalIdeal R) K
    M.group N.group q φ.hom hfib hconn'
    (baseChangeBasePointsEquiv (Spec.algebraMap R K) M.group
      (rationalPoints.map M.genericIso.inv g))
  refine ⟨rationalPoints.map N.genericIso.hom
      ((baseChangeBasePointsEquiv (Spec.algebraMap R K) N.group).symm h), x, ?_⟩
  rw [← genericPoint_map M N φ h, integralPointMap_eq, ← map_mul, ← map_mul, hk]
  exact genericPoint_eq M g

/-- A chosen parabolic-left factorization of a fraction-field point. -/
def parabolicIntegralFactor (g : rationalPoints G) :
    rationalPoints P × M.integralSections :=
  ((exists_parabolic_integral_factor M N φ q hsmooth hconn hfib g).choose,
    (exists_parabolic_integral_factor M N φ q hsmooth hconn hfib g).choose_spec.choose)

/-- The chosen factors multiply back to the given fraction-field point. -/
theorem parabolicIntegralFactor_spec (g : rationalPoints G) :
    rationalPoints.map f (parabolicIntegralFactor M N φ q hsmooth hconn hfib g).1 *
      M.integralPointMap (parabolicIntegralFactor M N φ q hsmooth hconn hfib g).2 = g :=
  (exists_parabolic_integral_factor M N φ q hsmooth hconn hfib g).choose_spec.choose_spec

include hsmooth hconn hfib in
/-- The parabolic-left integral covering for actual models over a complete valuation ring. -/
theorem range_mul_integralPoints_eq_univ :
    Set.range (rationalPoints.map f) *
      (M.integralPoints : Set (rationalPoints G)) = Set.univ :=
  Set.eq_univ_of_forall fun g =>
    ⟨_, ⟨_, rfl⟩, _, (M.mem_integralPoints _).mpr ⟨_, rfl⟩,
      parabolicIntegralFactor_spec M N φ q hsmooth hconn hfib g⟩

end Factor

end Model

end Langlands.GroupScheme.IntegralParabolicCovering
