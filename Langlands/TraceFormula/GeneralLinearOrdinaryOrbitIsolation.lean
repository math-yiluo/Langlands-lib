import Langlands.TraceFormula.GeneralLinearEllipticClassFinitenessProof
import Langlands.TraceFormula.RationalRegularOrbitCutoff
import Langlands.TraceFormula.PositiveAverageOrbitSupport
import Langlands.Group.GL.LocalFieldTopology
import Langlands.Global.CompletionPadic

/-!
# Isolating one rational class of the norm-one group by a cutoff at a finite place

See `GeneralLinearOrdinaryOrbitIsolation.md`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.JacquetLanglands

universe u

/-- If a finite set of rational elements meets every rational class whose conjugates enter a set
`C`, and every element of the set is conjugate to `r₀` whenever its conjugates meet the support
of `f` (contained in `C`), then every rational element whose conjugates meet the support of `f`
is rationally conjugate to `r₀`. -/
theorem isTwistedConjugate_of_finiteSupportCutoff' {H : Type u} [Group H]
    (Q : Subgroup H) (θ : H →* H) (C : Set H) (T : Finset Q) (r₀ : H)
    (hT : ∀ r : Q, (∃ x : H, twistedConj θ x r.val ∈ C) →
      ∃ t ∈ T, IsTwistedConjugate Q θ r.val t.val)
    (f : H → ℂ) (hf : Function.support f ⊆ C)
    (hcut : ∀ t ∈ T, (∃ x : H, f (twistedConj θ x (t : H)) ≠ 0) →
      IsTwistedConjugate Q θ (t : H) r₀)
    (r : Q) (h : ∃ x : H, f (twistedConj θ x (r : H)) ≠ 0) :
    IsTwistedConjugate Q θ (r : H) r₀ := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨t, ht, y, hy, hyt⟩ := hT r ⟨x, hf hx⟩
  change twistedConj θ y (r : H) = (t : H) at hyt
  have ht' : f (twistedConj θ (y⁻¹ * x) (t : H)) ≠ 0 := by
    rwa [← hyt, twistedConj_mul, mul_inv_cancel_left]
  obtain ⟨z, hz, hz₀⟩ := hcut t ht ⟨y⁻¹ * x, ht'⟩
  refine ⟨y * z, Q.mul_mem hy hz, ?_⟩
  change twistedConj θ (y * z) (r : H) = r₀
  rw [← twistedConj_mul, hyt]
  exact hz₀

local instance ordinaryIsolationIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance ordinaryIsolationSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

theorem localProjection_finite_rational (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (v : FinitePlace K) (x : GeneralLinear n K) :
    FiniteAdelicGL.localProjection K n v (AdelicGL.finite K n (AdelicGL.rational K n x)) =
      Matrix.GeneralLinearGroup.map (algebraMap K (FiniteCompletion K v)) x := by
  ext i j
  rfl

/-- A compact set of norm-one points that is regular elliptic at `v` meets the conjugates of
only finitely many rational classes. -/
theorem exists_finite_ordinary_normOneClasses' (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (v : FinitePlace K) (C : Set (normOneSubgroup K GLₙ)) (hC : IsCompact C)
    (hEll : ∀ g ∈ C, IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n g)))) :
    ∃ R : Finset (rationalNormOneSubgroup K GLₙ), ∀ r : rationalNormOneSubgroup K GLₙ,
      (∃ x : normOneSubgroup K GLₙ, x⁻¹ * r.val * x ∈ C) →
      ∃ t ∈ R, IsTwistedConjugate (rationalNormOneSubgroup K GLₙ)
        (MonoidHom.id (normOneSubgroup K GLₙ)) r.val t.val := by
  classical
  let e := GeneralLinearGroupPoints.adelicHomeomorph K n
  let p : normOneSubgroup K GLₙ → AdelicGL K n := fun g ↦ e (g : AdelicGroupPoints K GLₙ)
  let D := p '' C
  have hD : IsCompact D := hC.image (e.continuous.comp continuous_subtype_val)
  have hDEll : ∀ g ∈ D, IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n g)) := by
    rintro _ ⟨g, hg, rfl⟩
    exact hEll g hg
  let j := rationalNormOne K GLₙ
  let i := GeneralLinearGroupPoints.rationalEquiv K n
  let lift (r : RationalGL K n) : rationalNormOneSubgroup K GLₙ :=
    ⟨j (i.symm r), ⟨i.symm r, rfl⟩⟩
  obtain ⟨R, hR⟩ := generalLinearEllipticClassFiniteness K n v D hD hDEll
  refine ⟨R.image lift, ?_⟩
  rintro ⟨r, ⟨q, rfl⟩⟩ ⟨x, hx⟩
  have hxD : p (x⁻¹ * j q * x) ∈ D := Set.mem_image_of_mem p hx
  change e ((x : AdelicGroupPoints K GLₙ)⁻¹ * AdelicGroupPoints.rational K GLₙ q *
    (x : AdelicGroupPoints K GLₙ)) ∈ D at hxD
  rw [map_mul, map_mul, map_inv, GeneralLinearGroupPoints.adelicHomeomorph_rational] at hxD
  obtain ⟨_, t, ht, y, hy⟩ := hR (i q) ⟨e x, hxD⟩
  refine ⟨lift t, Finset.mem_image_of_mem lift ht, (lift y).val, (lift y).property, ?_⟩
  change (j (i.symm y))⁻¹ * j q * j (i.symm y) = j (i.symm t)
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg j
  apply i.injective
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hy

set_option maxHeartbeats 1600000 in
/-- **Isolation of one rational class by a cutoff at a finite place.** Let `C` be a compact set of
norm-one points that is regular elliptic at the finite place `v`, and let `q₀` be a rational
point whose matrix is regular semisimple. Every open neighbourhood `V` of the image of `q₀` in
`GL_n(K_v)` contains a compact open neighbourhood `U` with the following property. If `fOne` is
supported in `C` and its nonzero values occur only at points whose component at `v` lies in `U`,
then every rational norm-one element with a conjugate in the support of `fOne` is rationally
conjugate to `q₀`. -/
theorem ordinaryOrbitIsolation (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (v : FinitePlace K) [LocallyCompactSpace (GeneralLinear n (FiniteCompletion K v))]
    [TotallyDisconnectedSpace (GeneralLinear n (FiniteCompletion K v))]
    (C : Set (normOneSubgroup K GLₙ)) (hC : IsCompact C)
    (hEll : ∀ g ∈ C, IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n g))))
    (q₀ : RationalGroupPoints K GLₙ)
    (hreg : IsRegularSemisimple (GeneralLinearGroupPoints.rationalEquiv K n q₀))
    (V : Set (GeneralLinear n (FiniteCompletion K v))) (hV : IsOpen V)
    (hq : Matrix.GeneralLinearGroup.map (algebraMap K (FiniteCompletion K v))
      (GeneralLinearGroupPoints.rationalEquiv K n q₀) ∈ V) :
    ∃ U : Set (GeneralLinear n (FiniteCompletion K v)), IsCompact U ∧ IsClopen U ∧
      Matrix.GeneralLinearGroup.map (algebraMap K (FiniteCompletion K v))
        (GeneralLinearGroupPoints.rationalEquiv K n q₀) ∈ U ∧ U ⊆ V ∧
      ∀ fOne : normOneSubgroup K GLₙ → ℂ, Function.support fOne ⊆ C →
        (∀ z, fOne z ≠ 0 → FiniteAdelicGL.localProjection K n v
          (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n z)) ∈ U) →
        ∀ r : rationalNormOneSubgroup K GLₙ,
          (∃ x : normOneSubgroup K GLₙ, fOne (x⁻¹ * r.val * x) ≠ 0) →
          IsTwistedConjugate (rationalNormOneSubgroup K GLₙ)
            (MonoidHom.id (normOneSubgroup K GLₙ)) r.val (rationalNormOne K GLₙ q₀) := by
  classical
  let H := normOneSubgroup K GLₙ
  let RG := rationalNormOneSubgroup K GLₙ
  let i := GeneralLinearGroupPoints.rationalEquiv K n
  let e := GeneralLinearGroupPoints.adelicHomeomorph K n
  let iota := algebraMap K (FiniteCompletion K v)
  obtain ⟨R, hR⟩ := exists_finite_ordinary_normOneClasses' K n v C hC hEll
  have hRational (r : RG) : ∃ q : RationalGroupPoints K GLₙ, rationalNormOne K GLₙ q = r.val :=
    r.property
  choose rG hrG using hRational
  obtain ⟨U, hUc, hUcl, hqU, hUV, hcut⟩ := exists_rationalRegularOrbitCutoff iota
    (R.image fun r => i (rG r)) (i q₀) hreg hV hq
  refine ⟨U, hUc, hUcl, hqU, hUV, ?_⟩
  intro fOne hsupp hloc
  apply isTwistedConjugate_of_finiteSupportCutoff' RG (MonoidHom.id H) C R
    (rationalNormOne K GLₙ q₀) hR fOne hsupp
  rintro r hr ⟨x, hx⟩
  have hx' := hloc _ hx
  have hr' : (r.val : AdelicGroupPoints K GLₙ) = AdelicGroupPoints.rational K GLₙ (rG r) :=
    congrArg Subtype.val (hrG r).symm
  have hval : ((twistedConj (MonoidHom.id H) x (r : H) : H) : AdelicGroupPoints K GLₙ) =
      (x : AdelicGroupPoints K GLₙ)⁻¹ * AdelicGroupPoints.rational K GLₙ (rG r) *
        (x : AdelicGroupPoints K GLₙ) := by
    change ((x⁻¹ * (r : H) * x : H) : AdelicGroupPoints K GLₙ) = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hr']
  rw [hval, map_mul e, map_mul e, map_inv e, GeneralLinearGroupPoints.adelicHomeomorph_rational,
    map_mul (AdelicGL.finite K n), map_mul (AdelicGL.finite K n), map_inv (AdelicGL.finite K n),
    map_mul (FiniteAdelicGL.localProjection K n v), map_mul (FiniteAdelicGL.localProjection K n v),
    map_inv (FiniteAdelicGL.localProjection K n v), localProjection_finite_rational] at hx'
  obtain ⟨a, ha⟩ := hcut (i (rG r)) (Finset.mem_image_of_mem _ hr) ⟨_, hx'⟩
  refine ⟨rationalNormOne K GLₙ (i.symm a), ⟨i.symm a, rfl⟩, ?_⟩
  change (rationalNormOne K GLₙ (i.symm a))⁻¹ * r.val * rationalNormOne K GLₙ (i.symm a) =
    rationalNormOne K GLₙ q₀
  rw [← hrG r, ← map_inv, ← map_mul, ← map_mul]
  apply congrArg (rationalNormOne K GLₙ)
  apply i.injective
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using ha

end Langlands.TraceFormula
