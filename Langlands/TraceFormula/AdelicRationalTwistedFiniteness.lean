import Langlands.BaseChange.CyclicNormLemma
import Langlands.TraceFormula.GeneralLinearEllipticClassFinitenessProof
import Langlands.TraceFormula.GeneralLinearWeilAdelicTwistStatement
import Langlands.TraceFormula.TwistedOrbital

/-! # Finiteness of rational twisted classes with an elliptic norm in a compact set -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open AdelicGroupAutomorphism BaseChange JacquetLanglands

universe u

section Matrix

variable (K L : Type u) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- Rational upper matrices whose cyclic norms have an adelic conjugate
in a compact regular elliptic set lie in finitely many rational twisted
conjugacy classes. -/
theorem exists_finite_rationalTwistedClasses
    (σ : L ≃ₐ[K] L) (l n : ℕ) (hσ : IsCyclicAlgebra σ l)
    (w : FinitePlace L) (Ω : Set (AdelicGL L n)) (hΩ : IsCompact Ω)
    (hEll : ∀ g ∈ Ω, IsRegularElliptic
      (FiniteAdelicGL.localProjection L n w (AdelicGL.finite L n g))) :
    ∃ T : Finset (RationalGL L n), ∀ δ : RationalGL L n,
      (∃ x : AdelicGL L n, x⁻¹ * AdelicGL.rational L n (cyclicNorm σ l δ) * x ∈ Ω) →
      ∃ t ∈ T, ∃ y : RationalGL L n, y⁻¹ * δ * entrywiseAut σ n y = t := by
  classical
  obtain ⟨R, hR⟩ := generalLinearEllipticClassFiniteness L n w Ω hΩ hEll
  let imageNorm (r : RationalGL L n) := ∃ δ : RationalGL L n, cyclicNorm σ l δ = r
  let preimage (r : RationalGL L n) :=
    if h : imageNorm r then Classical.choose h else 1
  refine ⟨(R.filter imageNorm).image preimage, ?_⟩
  intro δ hδ
  obtain ⟨_, r, hr, y, hy⟩ := hR (cyclicNorm σ l δ) hδ
  have hrNorm : imageNorm r := by
    refine ⟨y⁻¹ * δ * entrywiseAut σ n y, ?_⟩
    rwa [cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply]
  have hpre : cyclicNorm σ l (preimage r) = r := by
    rw [show preimage r = Classical.choose hrNorm from dite_eq_left hrNorm]
    exact Classical.choose_spec hrNorm
  exact ⟨preimage r, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hr, hrNorm⟩),
    (cyclicNormLemma K L σ l n hσ).2.2 δ (preimage r) ⟨y, hy.trans hpre.symm⟩⟩

/-- The arithmetic field action, reinterpreted as a ring automorphism of
the adeles preserving integer scalars. -/
private def adeleIntAut : (L ≃ₐ[K] L) →* (Adeles L ≃ₐ[ℤ] Adeles L) where
  toFun σ := (AdelicFunctoriality.adeleEquiv σ.toRingEquiv).toIntAlgEquiv
  map_one' := AlgEquiv.ext fun x ↦ by
    change AdelicFunctoriality.adeleEquiv (RingEquiv.refl L) x = x
    rw [AdelicFunctoriality.adeleEquiv_refl, RingEquiv.refl_apply]
  map_mul' σ τ := AlgEquiv.ext fun x ↦ by
    change AdelicFunctoriality.adeleEquiv (τ.toRingEquiv.trans σ.toRingEquiv) x =
      AdelicFunctoriality.adeleEquiv σ.toRingEquiv
        (AdelicFunctoriality.adeleEquiv τ.toRingEquiv x)
    rw [AdelicFunctoriality.adeleEquiv_trans, RingEquiv.trans_apply]

private theorem entrywiseAut_adeleIntAut (σ : L ≃ₐ[K] L) (n : ℕ) (g : AdelicGL L n) :
    entrywiseAut (adeleIntAut K L σ) n g =
      AdelicGLTransport.adelicEquiv n σ.toRingEquiv g := by
  apply Units.ext
  rfl

private theorem cyclicNorm_adelicRational (σ : L ≃ₐ[K] L) (l n : ℕ) (r : RationalGL L n) :
    cyclicNorm (adeleIntAut K L σ) l (AdelicGL.rational L n r) =
      AdelicGL.rational L n (cyclicNorm σ l r) := by
  rw [cyclicNorm, cyclicNorm, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply, ← map_pow, entrywiseAut_adeleIntAut]
  exact AdelicGLTransport.adelicEquiv_rational n (σ ^ k).toRingEquiv r

private theorem continuous_cyclicNorm_adeleIntAut (σ : L ≃ₐ[K] L) (l n : ℕ) :
    Continuous (fun g : AdelicGL L n ↦ cyclicNorm (adeleIntAut K L σ) l g) := by
  induction l with
  | zero => simp only [cyclicNorm_zero, continuous_const]
  | succ l ih =>
    simp only [cyclicNorm_succ, ← map_pow, entrywiseAut_adeleIntAut]
    exact ih.mul (AdelicGLTransport.adelicEquiv n (σ ^ l).toRingEquiv).continuous

private theorem finite_twistedClasses_of_coordinates {G : Type u} [Group G] [TopologicalSpace G]
    (σ : L ≃ₐ[K] L) (l n : ℕ) (hσ : IsCyclicAlgebra σ l) (w : FinitePlace L)
    (e : G ≃ₜ* AdelicGL L n) (H : Subgroup G) (R : Subgroup H) (θ : H ≃* H)
    (hθ : ∀ x : H, e (θ x : G) = entrywiseAut (adeleIntAut K L σ) n (e x))
    (hforward : ∀ r : R, ∃ a : RationalGL L n, AdelicGL.rational L n a = e (r.val : G))
    (hbackward : ∀ a : RationalGL L n, ∃ r : R, e (r.val : G) = AdelicGL.rational L n a)
    (Ω : Set H) (hΩ : IsCompact Ω)
    (hEll : ∀ g ∈ Ω, IsRegularElliptic (FiniteAdelicGL.localProjection L n w
      (AdelicGL.finite L n (cyclicNorm (adeleIntAut K L σ) l (e g))))) :
    ∃ T : Finset R, ∀ r : R, (∃ x : H, x⁻¹ * r.val * θ x ∈ Ω) →
      ∃ t ∈ T, IsTwistedConjugate R θ r.val t.val := by
  classical
  have hpow : adeleIntAut K L σ ^ l = 1 := by rw [← map_pow, hσ.pow_eq_one, map_one]
  let normMap : H → AdelicGL L n := fun g ↦ cyclicNorm (adeleIntAut K L σ) l (e g)
  let C := normMap '' Ω
  have hC : IsCompact C :=
    hΩ.image ((continuous_cyclicNorm_adeleIntAut K L σ l n).comp
      (e.continuous.comp continuous_subtype_val))
  have hCEll : ∀ g ∈ C, IsRegularElliptic
      (FiniteAdelicGL.localProjection L n w (AdelicGL.finite L n g)) := by
    rintro _ ⟨g, hg, rfl⟩
    exact hEll _ hg
  obtain ⟨T, hT⟩ := exists_finite_rationalTwistedClasses K L σ l n hσ w C hC hCEll
  choose lift hlift using hbackward
  refine ⟨T.image lift, ?_⟩
  rintro r ⟨x, hx⟩
  obtain ⟨a, ha⟩ := hforward r
  have hnorm : normMap (x⁻¹ * r.val * θ x) =
      (e x)⁻¹ * AdelicGL.rational L n (cyclicNorm σ l a) * e x := by
    change cyclicNorm (adeleIntAut K L σ) l
      (e ((x : G)⁻¹ * (r.val : G) * (θ x : G))) = _
    rw [map_mul, map_mul, map_inv, hθ, ← ha, cyclicNorm_twistedConj, hpow,
      entrywiseAut_one_apply, cyclicNorm_adelicRational]
  have hCmem : normMap (x⁻¹ * r.val * θ x) ∈ C := Set.mem_image_of_mem normMap hx
  rw [hnorm] at hCmem
  obtain ⟨t, ht, y, hy⟩ := hT a ⟨e x, hCmem⟩
  refine ⟨lift t, Finset.mem_image_of_mem lift ht, lift y, (lift y).property, ?_⟩
  apply Subtype.ext
  apply e.injective
  change e (((lift y).val : G)⁻¹ * (r.val : G) * (θ (lift y).val : G)) =
    e ((lift t).val : G)
  rw [map_mul, map_mul, map_inv, hθ, hlift, hlift, ← ha,
    entrywiseAut_adeleIntAut, AdelicGLTransport.adelicEquiv_rational, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (AdelicGL.rational L n) hy

end Matrix

private local instance (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

private local instance (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

/-- The broad compact norm-one support needed by the simple twisted trace
formula bounds the candidate rational twisted classes by a finite list.
The hypothesis uses the same upper-place ellipticity as that formula. -/
def AdelicRationalTwistedFinitenessStatement : Prop :=
  GeneralLinearWeilAdelicTwistStatement.{u} →
    ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
      ∀ (n : ℕ) (w : FinitePlace L) (Ω : Set (normOneSubgroup K Wₙ)), IsCompact Ω →
        let θ := normOneAut K (unitGaloisAut K L GLₙ σ)
        let Φ : AdelicGroupPoints K Wₙ → AdelicGL L n := fun g ↦
          GeneralLinearGroupPoints.adelicHomeomorph L n
            (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L GLₙ)
              (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L))
              (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom
              (AdelicGaloisUnit.weilAdelicEquiv K L GLₙ g))
        let N : AdelicGroupPoints K Wₙ → AdelicGroupPoints K Wₙ := fun g ↦
          ((List.range l).map fun k ↦ adelicAut K (unitGaloisAut K L GLₙ (σ ^ k)) g).prod
        (∀ g ∈ Ω, IsRegularElliptic (FiniteAdelicGL.localProjection L n w
          (AdelicGL.finite L n (Φ (N g))))) →
        ∃ T : Finset (rationalNormOneSubgroup K Wₙ), ∀ r : rationalNormOneSubgroup K Wₙ,
          (∃ x : normOneSubgroup K Wₙ, x⁻¹ * (r : normOneSubgroup K Wₙ) * θ x ∈ Ω) →
          ∃ t ∈ T, IsTwistedConjugate (rationalNormOneSubgroup K Wₙ) θ
            (r : normOneSubgroup K Wₙ) (t : normOneSubgroup K Wₙ)

set_option maxRecDepth 2500 in
set_option maxHeartbeats 3200000 in
theorem adelicRationalTwistedFiniteness : AdelicRationalTwistedFinitenessStatement.{u} := by
  classical
  intro hweil K _ _ L _ _ _ _ σ l hσ n w Ω hΩ θ Φ N hEll
  let H := normOneSubgroup K Wₙ
  let R := rationalNormOneSubgroup K Wₙ
  obtain ⟨⟨e, he⟩, ht, hr⟩ := hweil K L n
  have heΦ : ⇑e = Φ := he
  have ht' (τ : L ≃ₐ[K] L) (g : AdelicGroupPoints K Wₙ) :
      e (adelicAut K (unitGaloisAut K L GLₙ τ) g) =
        entrywiseAut (adeleIntAut K L τ) n (e g) := by
    calc
      _ = Φ (adelicAut K (unitGaloisAut K L GLₙ τ) g) := congrFun heΦ _
      _ = AdelicGLTransport.adelicEquiv n τ.toRingEquiv (Φ g) := ht τ g
      _ = AdelicGLTransport.adelicEquiv n τ.toRingEquiv (e g) :=
        congrArg _ (congrFun heΦ g).symm
      _ = _ := (entrywiseAut_adeleIntAut K L τ n (e g)).symm
  have hN (g : AdelicGroupPoints K Wₙ) :
      e (N g) = cyclicNorm (adeleIntAut K L σ) l (e g) := by
    change e (((List.range l).map fun k ↦ adelicAut K (unitGaloisAut K L GLₙ (σ ^ k)) g).prod) = _
    rw [map_list_prod, List.map_map, cyclicNorm]
    congr 1
    apply List.map_congr_left
    intro k _
    simpa only [Function.comp_apply, map_pow] using ht' (σ ^ k) g
  have hforward (r : R) :
      ∃ a : RationalGL L n, AdelicGL.rational L n a = e (r.val : AdelicGroupPoints K Wₙ) := by
    rw [heΦ]
    exact (hr _).mp (rationalNormOneSubgroupInclusion K Wₙ r).property
  have hbackward (a : RationalGL L n) : ∃ r : R,
      e (r.val : AdelicGroupPoints K Wₙ) = AdelicGL.rational L n a := by
    have hq : e.symm (AdelicGL.rational L n a) ∈ rationalSubgroup K Wₙ := by
      apply (hr _).mpr
      exact ⟨a, (e.apply_symm_apply _).symm.trans (congrFun heΦ _)⟩
    obtain ⟨q, hq⟩ := hq
    refine ⟨⟨rationalNormOne K Wₙ q, ⟨q, rfl⟩⟩, ?_⟩
    change e (AdelicGroupPoints.rational K Wₙ q) = _
    rw [hq, ContinuousMulEquiv.apply_symm_apply]
  refine finite_twistedClasses_of_coordinates K L σ l n hσ w e H R θ.toMulEquiv
    (fun x ↦ ht' σ x) hforward hbackward Ω hΩ ?_
  intro g hg
  rw [← hN, heΦ]
  exact hEll _ hg

end Langlands.TraceFormula
