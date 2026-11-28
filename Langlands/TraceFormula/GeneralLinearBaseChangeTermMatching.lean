import Langlands.TraceFormula.GeneralLinearBaseChangeCentralizerEquiv

/-!
# Matching geometric terms of `Res_{L/K} GL_n` and `GL_n`

For related rational norm-one points `r` of `Res_{L/K} GL_n` and `q` of `GL_n`, with `Φ(N(r))`
regular elliptic at a finite place of `L` or `q` regular elliptic at a finite place of `K`,
the centralizer isomorphism transports the measures of a geometric term in either direction.
A hypothesis comparing orbital integrals for transported measures then matches the terms.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Matrix MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.BaseChange Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme Langlands.JacquetLanglands Langlands.QuotientIntegration
open Langlands.Global.AdelicFunctoriality
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

local instance baseChangeTermMatchingGLAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance baseChangeTermMatchingGLSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option hygiene false in
local notation "Θₙ" => normOneAut K (unitGaloisAut K L GLₙ σ)

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section Hypotheses

/-- The orbital integral matching hypothesis of `GeneralLinearBaseChangeTraceComparisonStatement`,
with the identifications `Φ`, `N` and `ΦG` written out. For rational norm-one points `r` of
`Res_{L/K} GL_n` and `q` of `GL_n` and `y ∈ GL_n(L)` with `Φ(N(r)) y = y ΦG(q)`, where `Φ(N(r))`
is regular elliptic at `w` or `q` is regular elliptic at `v`, every isomorphism `e` of the
`θ`-centralizer of `r` onto the centralizer of `q` with `ΦG(e(x)) = y⁻¹ Φ(x) y`, and all
measures as described there with `μq = e_* μr`, the twisted orbital integral of `φOne` at `r`
equals `c` times the orbital integral of `fOne` at `q`. -/
def BaseChangeOrbitalMatching {K L : Type u} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l n : ℕ)
    (w : Langlands.Global.FinitePlace L) (v : Langlands.Global.FinitePlace K)
    (φOne : normOneSubgroup K Wₙ → ℂ) (fOne : normOneSubgroup K GLₙ → ℂ) (c : ℂ) : Prop :=
  ∀ r ∈ rationalNormOneSubgroup K Wₙ, ∀ q ∈ rationalNormOneSubgroup K GLₙ,
    ∀ y : GL (Fin n) L,
    cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
        adelicAut K (unitGaloisAut K L GLₙ σ ^ k) (r : AdelicGroupPoints K Wₙ)).prod) *
        AdelicGL.rational L n y =
      AdelicGL.rational L n y *
        Matrix.GeneralLinearGroup.map (adeleInclusion (K := K) (L := L))
          (GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ)) →
    (IsRegularElliptic (FiniteAdelicGL.localProjection L n w
        (AdelicGL.finite L n (cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
          adelicAut K (unitGaloisAut K L GLₙ σ ^ k) (r : AdelicGroupPoints K Wₙ)).prod)))) ∨
      IsRegularElliptic (FiniteAdelicGL.localProjection K n v
        (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n
          (q : AdelicGroupPoints K GLₙ))))) →
    ∀ (e : twistedCentralizer (Θₙ) r ≃*
        twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q),
      (∀ x : twistedCentralizer (Θₙ) r,
        Matrix.GeneralLinearGroup.map (adeleInclusion (K := K) (L := L))
            (GeneralLinearGroupPoints.adelicHomeomorph K n
              ((e x : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ)) =
          (AdelicGL.rational L n y)⁻¹ *
            cyclicWeilAdelicMap K L n ((x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) *
              AdelicGL.rational L n y) →
    ∀ [MeasurableSpace (LeftQuotient (twistedCentralizer (Θₙ) r))]
      [BorelSpace (LeftQuotient (twistedCentralizer (Θₙ) r))]
      (μr : Measure (twistedCentralizer (Θₙ) r))
      [μr.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μr] [μr.IsOpenPosMeasure]
      (νr : Measure (LeftQuotient (twistedCentralizer (Θₙ) r))),
      IsCompatible (twistedCentralizer (Θₙ) r)
        (Measure.haar : Measure (normOneSubgroup K Wₙ)) μr νr →
    ∀ [MeasurableSpace (LeftQuotient
          (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))]
      [BorelSpace (LeftQuotient
          (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))]
      (μq : Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))
      [μq.IsMulRightInvariant]
      (νq : Measure (LeftQuotient
          (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))),
      μr.map e = μq →
      IsCompatible (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q)
        (Measure.haar : Measure (normOneSubgroup K GLₙ)) μq νq →
      twistedOrbitalIntegral (Θₙ) r νr φOne = c * orbitalIntegral q νq fOne

/-- The vanishing hypothesis of `GeneralLinearBaseChangeTraceComparisonStatement`, with the
identifications `Φ`, `N` and `ΦG` written out. For every rational norm-one point `q` of `GL_n`
regular elliptic at `v` such that `Φ(N(r)) y ≠ y ΦG(q)` for all rational norm-one points `r` of
`Res_{L/K} GL_n` and all `y ∈ GL_n(L)`, the orbital integral of `fOne` at `q` vanishes for
every right-invariant centralizer measure finite on compacts and positive on nonempty open sets
and every compatible quotient measure. -/
def BaseChangeOrbitalVanishing {K L : Type u} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l n : ℕ)
    (v : Langlands.Global.FinitePlace K) (fOne : normOneSubgroup K GLₙ → ℂ) : Prop :=
  ∀ q ∈ rationalNormOneSubgroup K GLₙ,
    IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n
        (q : AdelicGroupPoints K GLₙ)))) →
    (∀ r ∈ rationalNormOneSubgroup K Wₙ, ∀ y : GL (Fin n) L,
      cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
          adelicAut K (unitGaloisAut K L GLₙ σ ^ k) (r : AdelicGroupPoints K Wₙ)).prod) *
          AdelicGL.rational L n y ≠
        AdelicGL.rational L n y *
          Matrix.GeneralLinearGroup.map (adeleInclusion (K := K) (L := L))
            (GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ))) →
    ∀ [MeasurableSpace (LeftQuotient
          (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))]
      [BorelSpace (LeftQuotient
          (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))]
      (μq : Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))
      [μq.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μq] [μq.IsOpenPosMeasure]
      (νq : Measure (LeftQuotient
          (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))),
      IsCompatible (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q)
        (Measure.haar : Measure (normOneSubgroup K GLₙ)) μq νq →
      orbitalIntegral q νq fOne = 0

end Hypotheses

section Matching

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] {n l : ℕ} {σ : L ≃ₐ[K] L}

private theorem mul_comm_of_mulEquiv' {A B : Type*} [Mul A] [Mul B] (e : A ≃* B)
    (h : ∀ b b' : B, b * b' = b' * b) (x x' : A) : x * x' = x' * x :=
  e.injective (by rw [map_mul, map_mul]; exact h _ _)

/-- A matching hypothesis for orbital integrals stated with a topological group automorphism
`θ` holds for the underlying monoid homomorphism: both twisted centralizers and both twisted
orbital integrals agree definitionally. -/
theorem orbitalMatch_toMonoidHom {H G : Type*} [Group H] [Group G]
    [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (θ : H ≃ₜ* H) (δ : H) (δ' : G) (μH : Measure H) (μG : Measure G)
    (φ : H → ℂ) (f : G → ℂ) (c : ℂ) (P : G → H → Prop)
    (h : ∀ (e : twistedCentralizer θ δ ≃* twistedCentralizer (MonoidHom.id G) δ'),
        (∀ x : twistedCentralizer θ δ, P (e x : G) (x : H)) →
        ∀ [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
          [BorelSpace (LeftQuotient (twistedCentralizer θ δ))]
          (μr : Measure (twistedCentralizer θ δ))
          [μr.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μr] [μr.IsOpenPosMeasure]
          (νr : Measure (LeftQuotient (twistedCentralizer θ δ))),
          IsCompatible (twistedCentralizer θ δ) μH μr νr →
        ∀ [MeasurableSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) δ'))]
          [BorelSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) δ'))]
          (μq : Measure (twistedCentralizer (MonoidHom.id G) δ'))
          [μq.IsMulRightInvariant]
          (νq : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id G) δ'))),
          μr.map e = μq →
          IsCompatible (twistedCentralizer (MonoidHom.id G) δ') μG μq νq →
          twistedOrbitalIntegral θ δ νr φ = c * orbitalIntegral δ' νq f) :
    ∀ (e : twistedCentralizer θ.toMonoidHom δ ≃* twistedCentralizer (MonoidHom.id G) δ'),
        (∀ x : twistedCentralizer θ.toMonoidHom δ, P (e x : G) (x : H)) →
        ∀ [MeasurableSpace (LeftQuotient (twistedCentralizer θ.toMonoidHom δ))]
          [BorelSpace (LeftQuotient (twistedCentralizer θ.toMonoidHom δ))]
          (μr : Measure (twistedCentralizer θ.toMonoidHom δ))
          [μr.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μr] [μr.IsOpenPosMeasure]
          (νr : Measure (LeftQuotient (twistedCentralizer θ.toMonoidHom δ))),
          IsCompatible (twistedCentralizer θ.toMonoidHom δ) μH μr νr →
        ∀ [MeasurableSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) δ'))]
          [BorelSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) δ'))]
          (μq : Measure (twistedCentralizer (MonoidHom.id G) δ'))
          [μq.IsMulRightInvariant]
          (νq : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id G) δ'))),
          μr.map e = μq →
          IsCompatible (twistedCentralizer (MonoidHom.id G) δ') μG μq νq →
          twistedOrbitalIntegral θ.toMonoidHom δ νr φ = c * orbitalIntegral δ' νq f :=
  @h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- For rational norm-one points `r` of `Res_{L/K} GL_n` and `q` of `GL_n` with
`Φ(N(r)) y = y ι(q)` and either regularity condition, there is a topological group isomorphism
of the `θ`-centralizer of `r` onto the centralizer of `q` given by `x ↦ y⁻¹ x y` in adelic
matrix coordinates; it matches rational points, and both centralizers are commutative. -/
theorem exists_baseChangeCentralizerEquiv_of_related (hcyc : IsCyclicAlgebra σ l)
    (r : rationalNormOneSubgroup K Wₙ) (q : rationalNormOneSubgroup K GLₙ)
    (y : GeneralLinear n L)
    (hy : cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
        adelicAut K (unitGaloisAut K L GLₙ σ ^ k)
          ((r : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ)).prod) *
        AdelicGL.rational L n y =
      AdelicGL.rational L n y *
        Matrix.GeneralLinearGroup.map (adeleInclusion (K := K) (L := L))
          (GeneralLinearGroupPoints.adelicHomeomorph K n
            ((q : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ)))
    (w : Langlands.Global.FinitePlace L) (v : Langlands.Global.FinitePlace K)
    (hreg : IsRegularElliptic (FiniteAdelicGL.localProjection L n w
        (AdelicGL.finite L n (cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
          adelicAut K (unitGaloisAut K L GLₙ σ ^ k)
            ((r : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ)).prod)))) ∨
      IsRegularElliptic (FiniteAdelicGL.localProjection K n v
        (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n
          ((q : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ))))) :
    ∃ e : twistedCentralizer (Θₙ).toMonoidHom (r : normOneSubgroup K Wₙ) ≃ₜ*
        twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) (q : normOneSubgroup K GLₙ),
      (∀ x : twistedCentralizer (Θₙ).toMonoidHom (r : normOneSubgroup K Wₙ),
        Matrix.GeneralLinearGroup.map (adeleInclusion (K := K) (L := L))
            (GeneralLinearGroupPoints.adelicHomeomorph K n
              ((e x : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ)) =
          (AdelicGL.rational L n y)⁻¹ *
            cyclicWeilAdelicMap K L n ((x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) *
              AdelicGL.rational L n y) ∧
      (∀ x : twistedCentralizer (Θₙ).toMonoidHom (r : normOneSubgroup K Wₙ),
        (e x : normOneSubgroup K GLₙ) ∈ rationalNormOneSubgroup K GLₙ ↔
          (x : normOneSubgroup K Wₙ) ∈ rationalNormOneSubgroup K Wₙ) ∧
      (∀ x x' : twistedCentralizer (Θₙ).toMonoidHom (r : normOneSubgroup K Wₙ),
        x * x' = x' * x) ∧
      (∀ x x' : twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ))
        (q : normOneSubgroup K GLₙ), x * x' = x' * x) := by
  obtain ⟨a, ha⟩ := (mem_rationalNormOneSubgroup_weil_iff (r : normOneSubgroup K Wₙ)).mp r.2
  obtain ⟨b, hb⟩ := (mem_rationalNormOneSubgroup_gl_iff (q : normOneSubgroup K GLₙ)).mp q.2
  have hbreg := isRegularSemisimple_of_baseChangeNormRelated σ l _ _ ha.symm hb.symm hy w v hreg
  obtain ⟨e, hcoord, hrat⟩ := exists_baseChangeCentralizerEquiv hcyc _ _ ha.symm hb.symm hy hbreg
  have hq := centralizer_commutative_of_isRegularSemisimple (q : normOneSubgroup K GLₙ)
    hb.symm hbreg
  refine ⟨e, fun x => ?_, hrat, mul_comm_of_mulEquiv' e.toMulEquiv hq, hq⟩
  rw [← adelicCoefficientExtension_apply]
  exact hcoord x

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- A rational norm-one point of `Res_{L/K} GL_n` whose norm is regular elliptic at a finite
place of `L` admits measures for its geometric term. -/
theorem nonempty_twistedGeometricMeasures_baseChange (hcyc : IsCyclicAlgebra σ l)
    [(Measure.haar : Measure (normOneSubgroup K Wₙ)).IsMulRightInvariant]
    (w : Langlands.Global.FinitePlace L) (v : Langlands.Global.FinitePlace K)
    (r : rationalNormOneSubgroup K Wₙ)
    (hreg : IsRegularElliptic (FiniteAdelicGL.localProjection L n w
      (AdelicGL.finite L n (cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
        adelicAut K (unitGaloisAut K L GLₙ σ ^ k)
          ((r : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ)).prod))))) :
    Nonempty (TwistedGeometricMeasures (rationalNormOneSubgroup K Wₙ) (Θₙ).toMonoidHom
      (r : normOneSubgroup K Wₙ) Measure.haar) := by
  obtain ⟨q, y, hy⟩ := exists_baseChangeNormRelated σ l hcyc r
  obtain ⟨e, -, -, hcr, -⟩ :=
    exists_baseChangeCentralizerEquiv_of_related hcyc r q y hy w v (Or.inl hreg)
  exact nonempty_twistedGeometricMeasures_of_commutative
    (isDiscrete_rationalNormOneSubgroup K Wₙ) (Θₙ).continuous hcr

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
/-- Matching of the geometric terms at related rational points. Assume that the twisted
orbital integral of `φ¹` at `r` equals `c` times the orbital integral of `f¹` at `q` whenever
the centralizer measures correspond under an isomorphism of the form `x ↦ y⁻¹ x y`. Then
every choice of measures for the term at `r` has a choice for the term at `q` with the same
rational covolume and matching orbital integrals, and every choice for the term at `q` has
a choice for the term at `r` with matching orbital integrals. -/
theorem baseChange_termMatch (hcyc : IsCyclicAlgebra σ l)
    [(Measure.haar : Measure (normOneSubgroup K Wₙ)).IsMulRightInvariant]
    [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant]
    (w : Langlands.Global.FinitePlace L) (v : Langlands.Global.FinitePlace K)
    (φOne : normOneSubgroup K Wₙ → ℂ) (fOne : normOneSubgroup K GLₙ → ℂ) (c : ℂ)
    (hM : BaseChangeOrbitalMatching σ l n w v φOne fOne c)
    (r : rationalNormOneSubgroup K Wₙ) (q : rationalNormOneSubgroup K GLₙ)
    (hA : BaseChangeNormRelated σ l (r : normOneSubgroup K Wₙ) (q : normOneSubgroup K GLₙ))
    (hreg : IsRegularElliptic (FiniteAdelicGL.localProjection L n w
        (AdelicGL.finite L n (cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
          adelicAut K (unitGaloisAut K L GLₙ σ ^ k)
            ((r : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ)).prod)))) ∨
      IsRegularElliptic (FiniteAdelicGL.localProjection K n v
        (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n
          ((q : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ))))) :
    TwistedTermMatchesOrdinaryTerm (rationalNormOneSubgroup K Wₙ)
        (rationalNormOneSubgroup K GLₙ) (Θₙ).toMonoidHom Measure.haar Measure.haar φOne fOne c
        (r : normOneSubgroup K Wₙ) (q : normOneSubgroup K GLₙ) ∧
      OrdinaryTermMatchesTwistedTerm (rationalNormOneSubgroup K Wₙ)
        (rationalNormOneSubgroup K GLₙ) (Θₙ).toMonoidHom Measure.haar Measure.haar φOne fOne c
        (r : normOneSubgroup K Wₙ) (q : normOneSubgroup K GLₙ) := by
  obtain ⟨y, hy⟩ := hA
  obtain ⟨e, hcoord, hrat, hcr, hcq⟩ :=
    exists_baseChangeCentralizerEquiv_of_related hcyc r q y hy w v hreg
  have hM0 := hM (r : normOneSubgroup K Wₙ) r.2 (q : normOneSubgroup K GLₙ) q.2 y hy hreg
  have hM' := orbitalMatch_toMonoidHom (Θₙ) (r : normOneSubgroup K Wₙ)
      (q : normOneSubgroup K GLₙ) Measure.haar Measure.haar φOne fOne c
      (fun g x => Matrix.GeneralLinearGroup.map (adeleInclusion (K := K) (L := L))
          (GeneralLinearGroupPoints.adelicHomeomorph K n (g : AdelicGroupPoints K GLₙ)) =
        (AdelicGL.rational L n y)⁻¹ * cyclicWeilAdelicMap K L n (x : AdelicGroupPoints K Wₙ) *
          AdelicGL.rational L n y)
      hM0 e.toMulEquiv hcoord
  constructor
  · intro d
    obtain ⟨d', hd'c, hd'r⟩ := exists_twistedGeometricMeasures_map
      (Measure.haar : Measure (normOneSubgroup K GLₙ)) continuous_id e hrat hcq d
    refine ⟨d', hd'r.symm, ?_⟩
    have := d.rightInvariant
    have := d.finiteOnCompacts
    have := d.openPos
    have := d'.rightInvariant
    exact hM' d.centralizer d.orbital d.orbital_compatible d'.centralizer d'.orbital hd'c.symm
      d'.orbital_compatible
  · intro d'
    have hrat' (z : twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ))
        (q : normOneSubgroup K GLₙ)) :
        (e.symm z : normOneSubgroup K Wₙ) ∈ rationalNormOneSubgroup K Wₙ ↔
          (z : normOneSubgroup K GLₙ) ∈ rationalNormOneSubgroup K GLₙ := by
      rw [← hrat (e.symm z), e.apply_symm_apply]
    obtain ⟨d, hdc, -⟩ := exists_twistedGeometricMeasures_map
      (Measure.haar : Measure (normOneSubgroup K Wₙ)) (Θₙ).continuous e.symm hrat' hcr d'
    refine ⟨d, ?_⟩
    have := d.rightInvariant
    have := d.finiteOnCompacts
    have := d.openPos
    have := d'.rightInvariant
    have hmap : d.centralizer.map e.toMulEquiv = d'.centralizer := by
      change d.centralizer.map e = d'.centralizer
      have hm1 : Measurable ⇑e := e.continuous.measurable
      have hm2 : Measurable ⇑e.symm := e.symm.continuous.measurable
      ext s hs
      rw [hdc, Measure.map_apply hm1 hs, Measure.map_apply hm2 (hm1 hs)]
      congr 1
      ext z
      simp only [Set.mem_preimage, ContinuousMulEquiv.apply_symm_apply]
    exact hM' d.centralizer d.orbital d.orbital_compatible d'.centralizer d'.orbital hmap
      d'.orbital_compatible

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- Vanishing of the geometric terms at rational points of `GL_n` related to no rational
point of `Res_{L/K} GL_n`, from the vanishing of their orbital integrals for all measures. -/
theorem baseChange_orbitalIntegral_eq_zero (σ : L ≃ₐ[K] L) (l : ℕ)
    [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant]
    (v : Langlands.Global.FinitePlace K) (fOne : normOneSubgroup K GLₙ → ℂ)
    (hOff : BaseChangeOrbitalVanishing σ l n v fOne)
    (q : rationalNormOneSubgroup K GLₙ)
    (hreg : IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n
        ((q : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ)))))
    (hnone : ∀ r : rationalNormOneSubgroup K Wₙ,
      ¬ BaseChangeNormRelated σ l (r : normOneSubgroup K Wₙ) (q : normOneSubgroup K GLₙ))
    (d' : TwistedGeometricMeasures (rationalNormOneSubgroup K GLₙ)
      (MonoidHom.id (normOneSubgroup K GLₙ)) (q : normOneSubgroup K GLₙ) Measure.haar) :
    orbitalIntegral (q : normOneSubgroup K GLₙ) d'.orbital fOne = 0 := by
  have := d'.rightInvariant
  have := d'.finiteOnCompacts
  have := d'.openPos
  exact hOff (q : normOneSubgroup K GLₙ) q.2 hreg (fun r hr y h => hnone ⟨r, hr⟩ ⟨y, h⟩)
    d'.centralizer d'.orbital d'.orbital_compatible

end Matching

end Langlands.TraceFormula
