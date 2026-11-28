import Langlands.TraceFormula.BaseChangeTermPairing
import Langlands.TraceFormula.GeneralLinearWeilTwistedClosedOrbitProof
import Langlands.TraceFormula.GeneralLinearWeilTwistedEllipticRepresentatives
import Langlands.TraceFormula.AdelicRegularCentralizer
import Langlands.TraceFormula.AdelicRegularCentralizerCompact
import Langlands.BaseChange.ExactRegularNormCentralizer
import Langlands.BaseChange.CyclicNormLemma
import Langlands.Global.CyclicAdeleFixedCoefficients
import Langlands.Global.IdeleNormAbsoluteValue
import Mathlib.Topology.Algebra.Group.OpenMapping

/-!
# Norm pairing of rational points of `Res_{L/K} GL_n` and `GL_n`

Matrix coordinates of rational norm-one points of `Res_{L/K} GL_n` and of `GL_n`, the norm
relation `BaseChangeNormRelated` between them, and its properties derived from the cyclic norm
lemma: every rational point of the Weil restriction is related to some rational point of
`GL_n`, the relation is invariant under rational (twisted) conjugation on both sides, and it
determines rational (twisted) conjugacy classes uniquely in both directions.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Matrix
open scoped CategoryTheory.MonObj NNReal
open Langlands.BaseChange Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme Langlands.JacquetLanglands Langlands.QuotientIntegration
open Langlands.Global.AdelicFunctoriality Langlands.Global.AdelicBlockDeterminantCharacter
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

local instance baseChangeNormPairingGLAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance baseChangeNormPairingGLSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option hygiene false in
local notation "Θₙ" => normOneAut K (unitGaloisAut K L GLₙ σ)

section Coordinates

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- A norm-one point of `Res_{L/K} GL_n` is rational exactly when its matrix coordinate is. -/
theorem mem_rationalNormOneSubgroup_weil_iff (x : normOneSubgroup K Wₙ) :
    x ∈ rationalNormOneSubgroup K Wₙ ↔
      cyclicWeilAdelicMap K L n (x : AdelicGroupPoints K Wₙ) ∈ (AdelicGL.rational L n).range := by
  constructor
  · intro hx
    exact ((generalLinearWeilAdelicTwist K L n).2.2 _).mp
      (rationalNormOneSubgroupInclusion K Wₙ ⟨x, hx⟩).property
  · intro hx
    have hm : (x : AdelicGroupPoints K Wₙ) ∈ rationalSubgroup K Wₙ :=
      ((generalLinearWeilAdelicTwist K L n).2.2 _).mpr hx
    obtain ⟨z, hz⟩ := hm
    exact ⟨z, Subtype.ext hz⟩

set_option maxHeartbeats 1000000 in
/-- Every rational matrix over `L` is the coordinate of a rational norm-one point of
`Res_{L/K} GL_n`. -/
theorem exists_rationalNormOne_weil (a : GeneralLinear n L) :
    ∃ x : rationalNormOneSubgroup K Wₙ,
      cyclicWeilAdelicMap K L n ((x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) =
        AdelicGL.rational L n a := by
  obtain ⟨e, he⟩ := (generalLinearWeilAdelicTwist K L n).1
  let g : AdelicGroupPoints K Wₙ := e.symm (AdelicGL.rational L n a)
  have hg : cyclicWeilAdelicMap K L n g = AdelicGL.rational L n a := by
    have h := congrFun he g
    change e g = cyclicWeilAdelicMap K L n g at h
    rw [← h]
    exact e.apply_symm_apply _
  have hrat : g ∈ rationalSubgroup K Wₙ :=
    ((generalLinearWeilAdelicTwist K L n).2.2 g).mpr ⟨a, hg.symm⟩
  obtain ⟨p, hp⟩ := hrat
  refine ⟨⟨rationalNormOne K Wₙ p, p, rfl⟩, ?_⟩
  change cyclicWeilAdelicMap K L n (AdelicGroupPoints.rational K Wₙ p) = _
  rw [hp, hg]

/-- A norm-one point of `GL_n` is rational exactly when its matrix coordinate is. -/
theorem mem_rationalNormOneSubgroup_gl_iff (y : normOneSubgroup K GLₙ) :
    y ∈ rationalNormOneSubgroup K GLₙ ↔
      GeneralLinearGroupPoints.adelicHomeomorph K n (y : AdelicGroupPoints K GLₙ) ∈
        (AdelicGL.rational K n).range := by
  constructor
  · intro hy
    obtain ⟨q, hq⟩ := (rationalNormOneSubgroupInclusion K GLₙ ⟨y, hy⟩).property
    refine ⟨GeneralLinearGroupPoints.rationalEquiv K n q, ?_⟩
    rw [← GeneralLinearGroupPoints.adelicHomeomorph_rational]
    exact congrArg _ hq
  · rintro ⟨b, hb⟩
    let p := (GeneralLinearGroupPoints.rationalEquiv K n).symm b
    refine ⟨p, Subtype.ext ?_⟩
    apply (GeneralLinearGroupPoints.adelicHomeomorph K n).injective
    change GeneralLinearGroupPoints.adelicHomeomorph K n (AdelicGroupPoints.rational K GLₙ p) = _
    rw [GeneralLinearGroupPoints.adelicHomeomorph_rational, ← hb]
    exact congrArg _ ((GeneralLinearGroupPoints.rationalEquiv K n).apply_symm_apply b)

/-- Every rational matrix over `K` is the coordinate of a rational norm-one point of `GL_n`. -/
theorem exists_rationalNormOne_gl (b : GeneralLinear n K) :
    ∃ y : rationalNormOneSubgroup K GLₙ,
      GeneralLinearGroupPoints.adelicHomeomorph K n
          ((y : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ) = AdelicGL.rational K n b := by
  let p := (GeneralLinearGroupPoints.rationalEquiv K n).symm b
  refine ⟨⟨rationalNormOne K GLₙ p, p, rfl⟩, ?_⟩
  change GeneralLinearGroupPoints.adelicHomeomorph K n (AdelicGroupPoints.rational K GLₙ p) = _
  rw [GeneralLinearGroupPoints.adelicHomeomorph_rational]
  exact congrArg _ ((GeneralLinearGroupPoints.rationalEquiv K n).apply_symm_apply b)

omit [FiniteDimensional K L] in
/-- The entrywise adele inclusion of a rational matrix is the rational matrix over `L`. -/
theorem adeleInclusion_map_rational (b : GeneralLinear n K) :
    Matrix.GeneralLinearGroup.map (adeleInclusion (K := K) (L := L)) (AdelicGL.rational K n b) =
      AdelicGL.rational L n (baseChange K L n b) := by
  ext i j
  exact adeleInclusion_diagonal (b i j)

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
/-- The matrix coordinate of the ordered norm `g Θ(g) ⋯ Θ^{l-1}(g)` of a point with rational
coordinate `a` is the rational cyclic norm of `a`. -/
theorem cyclicWeilAdelicMap_norm (σ : L ≃ₐ[K] L) (l : ℕ) (x : AdelicGroupPoints K Wₙ)
    (a : GeneralLinear n L) (ha : cyclicWeilAdelicMap K L n x = AdelicGL.rational L n a) :
    cyclicWeilAdelicMap K L n
        (((List.range l).map fun k => adelicAut K (unitGaloisAut K L GLₙ σ ^ k) x).prod) =
      AdelicGL.rational L n (cyclicNorm σ l a) := by
  obtain ⟨E, hE⟩ := (generalLinearWeilAdelicTwist K L n).1
  have hEΦ : ⇑E = cyclicWeilAdelicMap K L n := hE
  have hPow (k : ℕ) : unitGaloisAut K L GLₙ σ ^ k = unitGaloisAut K L GLₙ (σ ^ k) := by
    simpa only [unitGaloisAutHom_apply] using (map_pow (unitGaloisAutHom K L GLₙ) σ k).symm
  rw [← hEΦ, map_list_prod, cyclicNorm, map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  change E (adelicAut K (unitGaloisAut K L GLₙ σ ^ k) x) =
    AdelicGL.rational L n (entrywiseAut (σ ^ k) n a)
  rw [hPow]
  calc
    _ = cyclicWeilAdelicMap K L n (adelicAut K (unitGaloisAut K L GLₙ (σ ^ k)) x) :=
      congrFun hEΦ _
    _ = AdelicGLTransport.adelicEquiv n (σ ^ k).toRingEquiv (cyclicWeilAdelicMap K L n x) :=
      (generalLinearWeilAdelicTwist K L n).2.1 _ _
    _ = AdelicGLTransport.adelicEquiv n (σ ^ k).toRingEquiv (AdelicGL.rational L n a) := by
      rw [ha]
    _ = _ := AdelicGLTransport.adelicEquiv_rational n (σ ^ k).toRingEquiv a

omit [NumberField K] [FiniteDimensional K L] in
/-- Twisted conjugation of rational matrices commutes with the adelic Galois transport. -/
theorem twistedConj_adelicEquiv_rational (σ : L ≃ₐ[K] L) (x δ : GeneralLinear n L) :
    twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) (AdelicGL.rational L n x)
        (AdelicGL.rational L n δ) =
      AdelicGL.rational L n (x⁻¹ * δ * entrywiseAut σ n x) := by
  rw [twistedConj_apply, map_mul, map_mul, map_inv, AdelicGLTransport.adelicEquiv_rational]
  rfl

set_option maxHeartbeats 1000000 in
/-- Matrix coordinates of a twisted conjugate of norm-one points of `Res_{L/K} GL_n`. -/
theorem cyclicWeilAdelicMap_twistedConj (σ : L ≃ₐ[K] L) (h x : normOneSubgroup K Wₙ)
    (c a : GeneralLinear n L)
    (hc : cyclicWeilAdelicMap K L n (h : AdelicGroupPoints K Wₙ) = AdelicGL.rational L n c)
    (ha : cyclicWeilAdelicMap K L n (x : AdelicGroupPoints K Wₙ) = AdelicGL.rational L n a) :
    cyclicWeilAdelicMap K L n ((twistedConj Θₙ h x : normOneSubgroup K Wₙ) :
        AdelicGroupPoints K Wₙ) =
      AdelicGL.rational L n (c⁻¹ * a * entrywiseAut σ n c) := by
  obtain ⟨E, hE⟩ := (generalLinearWeilAdelicTwist K L n).1
  have hEΦ : ⇑E = cyclicWeilAdelicMap K L n := hE
  have h₁ := generalLinearWeilNormOne_twistedConj (σ := σ) E hEΦ h x
  rw [hEΦ, hc, ha, twistedConj_adelicEquiv_rational] at h₁
  exact h₁

set_option maxHeartbeats 1000000 in
/-- Norm-one points of `Res_{L/K} GL_n` with equal matrix coordinates are equal. -/
theorem normOne_weil_ext {x y : normOneSubgroup K Wₙ}
    (h : cyclicWeilAdelicMap K L n (x : AdelicGroupPoints K Wₙ) =
      cyclicWeilAdelicMap K L n (y : AdelicGroupPoints K Wₙ)) : x = y := by
  obtain ⟨E, hE⟩ := (generalLinearWeilAdelicTwist K L n).1
  apply Subtype.ext
  apply E.injective
  rw [congrFun hE, congrFun hE]
  exact h

omit [FiniteDimensional K L] in
/-- Norm-one points of `GL_n` with equal matrix coordinates are equal. -/
theorem normOne_gl_ext {x y : normOneSubgroup K GLₙ}
    (h : GeneralLinearGroupPoints.adelicHomeomorph K n (x : AdelicGroupPoints K GLₙ) =
      GeneralLinearGroupPoints.adelicHomeomorph K n (y : AdelicGroupPoints K GLₙ)) : x = y :=
  Subtype.ext ((GeneralLinearGroupPoints.adelicHomeomorph K n).injective h)

end Coordinates

section Relation

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] {n : ℕ}

variable (σ : L ≃ₐ[K] L) (l : ℕ) in
/-- The norm relation between norm-one points of `Res_{L/K} GL_n` and of `GL_n`: the matrix
coordinate of the ordered norm `r Θ(r) ⋯ Θ^{l-1}(r)` is conjugate by a rational matrix over
`L` to the entrywise adele inclusion of the matrix coordinate of `q`. -/
def BaseChangeNormRelated (r : normOneSubgroup K Wₙ) (q : normOneSubgroup K GLₙ) : Prop :=
  ∃ y : GeneralLinear n L,
    cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
        adelicAut K (unitGaloisAut K L GLₙ σ ^ k) (r : AdelicGroupPoints K Wₙ)).prod) *
        AdelicGL.rational L n y =
      AdelicGL.rational L n y *
        Matrix.GeneralLinearGroup.map (adeleInclusion (K := K) (L := L))
          (GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ))

set_option maxHeartbeats 1000000 in
/-- In matrix coordinates, the norm relation is the association of `a ∈ GL_n(L)` with
`b ∈ GL_n(K)`: `N(a)` is conjugate in `GL_n(L)` to `b`. -/
theorem baseChangeNormRelated_iff (σ : L ≃ₐ[K] L) (l : ℕ) (r : normOneSubgroup K Wₙ)
    (q : normOneSubgroup K GLₙ) {a : GeneralLinear n L} {b : GeneralLinear n K}
    (ha : cyclicWeilAdelicMap K L n (r : AdelicGroupPoints K Wₙ) = AdelicGL.rational L n a)
    (hb : GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ) =
      AdelicGL.rational K n b) :
    BaseChangeNormRelated σ l r q ↔ IsNormAssociated σ l a b := by
  unfold BaseChangeNormRelated IsNormAssociated
  rw [cyclicWeilAdelicMap_norm σ l _ a ha, hb, adeleInclusion_map_rational]
  refine exists_congr fun y => ?_
  rw [← map_mul, ← map_mul, (AdelicGL.rational_injective L n).eq_iff, mul_assoc,
    inv_mul_eq_iff_eq_mul]

set_option maxHeartbeats 1000000 in
/-- Every rational norm-one point of `Res_{L/K} GL_n` is related to a rational norm-one point
of `GL_n` (norm lemma, existence). -/
theorem exists_baseChangeNormRelated (σ : L ≃ₐ[K] L) (l : ℕ) (hcyc : IsCyclicAlgebra σ l)
    (x : rationalNormOneSubgroup K Wₙ) :
    ∃ y : rationalNormOneSubgroup K GLₙ,
      BaseChangeNormRelated σ l (x : normOneSubgroup K Wₙ) (y : normOneSubgroup K GLₙ) := by
  obtain ⟨a, ha⟩ := (mem_rationalNormOneSubgroup_weil_iff (x : normOneSubgroup K Wₙ)).mp x.2
  obtain ⟨b, hab⟩ := (cyclicNormLemma K L σ l n hcyc).1 a
  obtain ⟨y, hy⟩ := exists_rationalNormOne_gl (K := K) (n := n) b
  exact ⟨y, (baseChangeNormRelated_iff σ l _ _ ha.symm hy).mpr hab⟩

set_option maxHeartbeats 1000000 in
/-- The norm relation is invariant under rational twisted conjugation on the Weil
restriction side. -/
theorem baseChangeNormRelated_of_twistedConj_left (σ : L ≃ₐ[K] L) (l : ℕ)
    (hcyc : IsCyclicAlgebra σ l) (x x' : rationalNormOneSubgroup K Wₙ)
    (y : rationalNormOneSubgroup K GLₙ)
    (h : BaseChangeNormRelated σ l (x : normOneSubgroup K Wₙ) (y : normOneSubgroup K GLₙ))
    (hx : IsTwistedConjugate (rationalNormOneSubgroup K Wₙ) (Θₙ).toMonoidHom
      (x : normOneSubgroup K Wₙ) (x' : normOneSubgroup K Wₙ)) :
    BaseChangeNormRelated σ l (x' : normOneSubgroup K Wₙ) (y : normOneSubgroup K GLₙ) := by
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨a, ha⟩ := (mem_rationalNormOneSubgroup_weil_iff (x : normOneSubgroup K Wₙ)).mp x.2
  obtain ⟨c, hc⟩ := (mem_rationalNormOneSubgroup_weil_iff g).mp hg
  rw [← hgx]
  obtain ⟨b, hb⟩ := (mem_rationalNormOneSubgroup_gl_iff (y : normOneSubgroup K GLₙ)).mp y.2
  have hab := (baseChangeNormRelated_iff σ l _ _ ha.symm hb.symm).mp h
  have h' := cyclicWeilAdelicMap_twistedConj σ g (x : normOneSubgroup K Wₙ) c a hc.symm ha.symm
  refine (baseChangeNormRelated_iff σ l _ _ h' hb.symm).mpr ?_
  have := hab.twistedConj hcyc.pow_eq_one c 1
  simpa only [inv_one, one_mul, mul_one] using this

set_option maxHeartbeats 1000000 in
/-- The norm relation is invariant under rational conjugation on the `GL_n` side. -/
theorem baseChangeNormRelated_of_conj_right (σ : L ≃ₐ[K] L) (l : ℕ)
    (hcyc : IsCyclicAlgebra σ l) (x : rationalNormOneSubgroup K Wₙ)
    (y y' : rationalNormOneSubgroup K GLₙ)
    (h : BaseChangeNormRelated σ l (x : normOneSubgroup K Wₙ) (y : normOneSubgroup K GLₙ))
    (hy : IsTwistedConjugate (rationalNormOneSubgroup K GLₙ)
      (MonoidHom.id (normOneSubgroup K GLₙ))
      (y : normOneSubgroup K GLₙ) (y' : normOneSubgroup K GLₙ)) :
    BaseChangeNormRelated σ l (x : normOneSubgroup K Wₙ) (y' : normOneSubgroup K GLₙ) := by
  obtain ⟨g, hg, hgy⟩ := hy
  obtain ⟨a, ha⟩ := (mem_rationalNormOneSubgroup_weil_iff (x : normOneSubgroup K Wₙ)).mp x.2
  obtain ⟨c, hc⟩ := (mem_rationalNormOneSubgroup_gl_iff g).mp hg
  obtain ⟨b, hb⟩ := (mem_rationalNormOneSubgroup_gl_iff (y : normOneSubgroup K GLₙ)).mp y.2
  have hab := (baseChangeNormRelated_iff σ l _ _ ha.symm hb.symm).mp h
  have hb' : GeneralLinearGroupPoints.adelicHomeomorph K n
      ((y' : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ) =
        AdelicGL.rational K n (c⁻¹ * b * c) := by
    rw [← hgy]
    change GeneralLinearGroupPoints.adelicHomeomorph K n
      ((g : AdelicGroupPoints K GLₙ)⁻¹ * ((y : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ) *
        (g : AdelicGroupPoints K GLₙ)) = _
    rw [map_mul, map_mul, map_inv, ← hc, ← hb, map_mul, map_mul, map_inv]
  refine (baseChangeNormRelated_iff σ l _ _ ha.symm hb').mpr ?_
  have := hab.twistedConj hcyc.pow_eq_one 1 c
  simpa only [inv_one, one_mul, mul_one, map_one] using this

set_option maxHeartbeats 1000000 in
/-- Two rational points of `Res_{L/K} GL_n` related to the same rational point of `GL_n` are
rationally twisted-conjugate (norm lemma, part (2)). -/
theorem isTwistedConjugate_of_baseChangeNormRelated (σ : L ≃ₐ[K] L) (l : ℕ)
    (hcyc : IsCyclicAlgebra σ l) (x x' : rationalNormOneSubgroup K Wₙ)
    (y : rationalNormOneSubgroup K GLₙ)
    (h : BaseChangeNormRelated σ l (x : normOneSubgroup K Wₙ) (y : normOneSubgroup K GLₙ))
    (h' : BaseChangeNormRelated σ l (x' : normOneSubgroup K Wₙ) (y : normOneSubgroup K GLₙ)) :
    IsTwistedConjugate (rationalNormOneSubgroup K Wₙ) (Θₙ).toMonoidHom
      (x : normOneSubgroup K Wₙ) (x' : normOneSubgroup K Wₙ) := by
  obtain ⟨a, ha⟩ := (mem_rationalNormOneSubgroup_weil_iff (x : normOneSubgroup K Wₙ)).mp x.2
  obtain ⟨a', ha'⟩ := (mem_rationalNormOneSubgroup_weil_iff (x' : normOneSubgroup K Wₙ)).mp x'.2
  obtain ⟨b, hb⟩ := (mem_rationalNormOneSubgroup_gl_iff (y : normOneSubgroup K GLₙ)).mp y.2
  obtain ⟨g, hg⟩ := (baseChangeNormRelated_iff σ l _ _ ha.symm hb.symm).mp h
  obtain ⟨g', hg'⟩ := (baseChangeNormRelated_iff σ l _ _ ha'.symm hb.symm).mp h'
  obtain ⟨z, hz⟩ := (cyclicNormLemma K L σ l n hcyc).2.2 a a' ⟨g * g'⁻¹, by
    rw [← hg'] at hg
    calc (g * g'⁻¹)⁻¹ * cyclicNorm σ l a * (g * g'⁻¹)
        = g' * (g⁻¹ * cyclicNorm σ l a * g) * g'⁻¹ := by group
      _ = cyclicNorm σ l a' := by rw [hg]; group⟩
  exact isTwistedConjugate_of_rational_coordinates (σ := σ) x x' a a' z ha.symm ha'.symm hz

set_option maxHeartbeats 1000000 in
/-- Two rational points of `GL_n` related to the same rational point of `Res_{L/K} GL_n` are
rationally conjugate (norm lemma, part (1b)). -/
theorem isConjugate_of_baseChangeNormRelated (σ : L ≃ₐ[K] L) (l : ℕ)
    (hcyc : IsCyclicAlgebra σ l) (x : rationalNormOneSubgroup K Wₙ)
    (y y' : rationalNormOneSubgroup K GLₙ)
    (h : BaseChangeNormRelated σ l (x : normOneSubgroup K Wₙ) (y : normOneSubgroup K GLₙ))
    (h' : BaseChangeNormRelated σ l (x : normOneSubgroup K Wₙ) (y' : normOneSubgroup K GLₙ)) :
    IsTwistedConjugate (rationalNormOneSubgroup K GLₙ) (MonoidHom.id (normOneSubgroup K GLₙ))
      (y : normOneSubgroup K GLₙ) (y' : normOneSubgroup K GLₙ) := by
  obtain ⟨a, ha⟩ := (mem_rationalNormOneSubgroup_weil_iff (x : normOneSubgroup K Wₙ)).mp x.2
  obtain ⟨b, hb⟩ := (mem_rationalNormOneSubgroup_gl_iff (y : normOneSubgroup K GLₙ)).mp y.2
  obtain ⟨b', hb'⟩ := (mem_rationalNormOneSubgroup_gl_iff (y' : normOneSubgroup K GLₙ)).mp y'.2
  have hab := (baseChangeNormRelated_iff σ l _ _ ha.symm hb.symm).mp h
  have hab' := (baseChangeNormRelated_iff σ l _ _ ha.symm hb'.symm).mp h'
  obtain ⟨z, hz⟩ := (cyclicNormLemma K L σ l n hcyc).2.1 a b b' hab hab'
  obtain ⟨g, hg⟩ := exists_rationalNormOne_gl (K := K) (n := n) z
  refine ⟨g, g.2, normOne_gl_ext ?_⟩
  change GeneralLinearGroupPoints.adelicHomeomorph K n
    (((g : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ)⁻¹ *
      ((y : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ) *
        ((g : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ)) = _
  rw [map_mul, map_mul, map_inv, hg, ← hb, ← hb', ← hz, map_mul, map_mul, map_inv]

end Relation

end Langlands.TraceFormula
