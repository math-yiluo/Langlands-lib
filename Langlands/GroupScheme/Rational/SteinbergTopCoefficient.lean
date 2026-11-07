import Langlands.GroupScheme.Rational.SteinbergLowerRemainders
import Langlands.GroupScheme.Rational.SimpleRootHighestCoefficient
import Mathlib.Algebra.BigOperators.Ring.List

/-! # The actual Steinberg diagonal from local highest-root nonvanishing -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped BigOperators Matrix Classical

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (s : p.SimpleReflectionRepresentatives)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- A root degree beyond its actual polynomial bound kills the full ordered coefficient. -/
theorem steinbergCoefficientMatrix_eq_zero_of_degreeBound_le
    (m : Fin r → ℕ) (j : Fin r)
    (hm : degreeBound (ρ.restrict (x (e j)).hom) ≤ m j) :
    steinbergCoefficientMatrix x s ρ e m = 0 := by
  apply List.prod_eq_zero
  apply List.mem_ofFn.mpr
  refine ⟨j, ?_⟩
  rw [coefficientMatrix_eq_zero_of_degreeBound_le _ hm, zero_mul]

/-- Every actual monomial coefficient, including degrees outside the finite
expansion bounds, is the trace of the corresponding actual ordered coefficient. -/
theorem steinbergRestriction_trace_coeff_eq_trace (d : Fin r →₀ ℕ) :
    (steinbergRestriction e x s ρ.traceClassFunction).coeff d =
      Matrix.trace (steinbergCoefficientMatrix x s ρ e d) := by
  classical
  by_cases hbound : ∀ j, d j < degreeBound (ρ.restrict (x (e j)).hom)
  · let m : steinbergCoefficientDegrees e x ρ := fun j => ⟨d j, hbound j⟩
    have he : steinbergCoefficientExponent e x ρ m = d := by
      ext j
      exact steinbergCoefficientExponent_apply e x ρ m j
    simpa only [he] using steinbergRestriction_trace_coeff_at_exponent e x s ρ m
  · push Not at hbound
    obtain ⟨j, hj⟩ := hbound
    rw [steinbergCoefficientMatrix_eq_zero_of_degreeBound_le e x s ρ d j hj,
      Matrix.trace_zero, steinbergRestriction_trace_eq_sum_coefficients, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro m hm
    rw [mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_prod_X_pow]
    have hdne : d ≠ steinbergCoefficientExponent e x ρ m := by
      intro he
      have hj' := congrArg (fun d : Fin r →₀ ℕ => d j) he
      rw [steinbergCoefficientExponent_apply] at hj'
      have := (m j).isLt
      omega
    change Matrix.trace (steinbergCoefficientMatrix x s ρ e (fun j => m j)) *
      (if d = steinbergCoefficientExponent e x ρ m then 1 else 0) = 0
    rw [ite_eq_right hdne, mul_zero]

end Langlands.GroupScheme.SplitPinning

namespace Langlands.RootDatum.Triangular

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    {P : RootPairing ι ℤ X Y} {b : P.Base} [Fintype ι]

/-- In the root span, the simple-coroot pairings detect a weight. -/
theorem eq_zero_of_mem_rootSpan_of_forall_simple_coroot {x : X}
    (hx : x ∈ P.rootSpan ℤ)
    (hp : ∀ a ∈ b.support, P.toLinearMap x (P.coroot a) = 0) : x = 0 := by
  have hspan : ∀ y ∈ Submodule.span ℤ (P.coroot '' b.support), P.toLinearMap x y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      exact hp a ha
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul t y _ hy => simp [hy]
  have hcor (a : ι) : P.toLinearMap x (P.coroot a) = 0 :=
    hspan _ (b.coroot_mem_span_int a)
  apply P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hx
  rw [P.rootForm_apply_apply]
  apply Finset.sum_eq_zero
  intro a ha
  change P.toLinearMap x (P.coroot a) * P.toLinearMap x (P.coroot a) = 0
  rw [hcor, zero_mul]

end Langlands.RootDatum.Triangular

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (s : p.SimpleReflectionRepresentatives)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- The actual weight projector is identity on its weight and zero on every other weight. -/
theorem representationWeightProjector_of_mem
    (lam mu : characterLattice p.torus) {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ mu) :
    p.representationWeightProjector ρ lam v = if mu = lam then v else 0 := by
  classical
  let := p.isSplitTorus.isAffineHom
  have h := (ρ.restrict p.inclusion).characterProjector_of_mem
    ((rationalCharacters.equivCharacterLattice p.torus).symm lam)
    ((rationalCharacters.equivCharacterLattice p.torus).symm mu) hv
  simpa only [representationWeightProjector, EquivLike.apply_eq_iff_eq] using h

/-- The actual character coefficient is a projection onto the entire weight space. -/
theorem representationWeightProjector_isProj (lam : characterLattice p.torus) :
    LinearMap.IsProj (p.representationWeightSpace ρ lam)
      (p.representationWeightProjector ρ lam) := by
  classical
  constructor
  · intro v
    have hv : v ∈ ⨆ mu, p.representationWeightSpace ρ mu :=
      p.iSup_representationWeightSpace_eq_top ρ ▸ Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun v =>
      p.representationWeightProjector ρ lam v ∈ p.representationWeightSpace ρ lam)
      hv ?_ ?_ ?_
    · intro mu w hw
      rw [representationWeightProjector_of_mem ρ lam mu hw]
      split_ifs with h
      · subst mu
        exact hw
      · exact zero_mem _
    · rw [map_zero]
      exact zero_mem _
    · intro v w hv hw
      rw [map_add]
      exact add_mem hv hw
  · intro v hv
    rw [representationWeightProjector_of_mem ρ lam lam hv]
    simp

/-- If a coefficient tuple closes at a unique occurring weight of dimension one,
its trace is the scalar by which it acts on that line. -/
theorem steinbergCoefficientMatrix_trace_eq_scalar
    (m : Fin r → ℕ) (lam : characterLattice p.torus) (c : k)
    (hdim : Module.finrank k (p.representationWeightSpace ρ lam) = 1)
    (huniq : ∀ mu : characterLattice p.torus,
      p.representationWeightSpace ρ mu ≠ ⊥ →
        (∀ j, (m j : ℤ) = p.rootDatum.toLinearMap mu (p.rootDatum.coroot (e j))) → mu = lam)
    (hscalar : ∀ v : n → k, v ∈ p.representationWeightSpace ρ lam →
      steinbergCoefficientMatrix x s ρ e m *ᵥ v = c • v) :
    Matrix.trace (steinbergCoefficientMatrix x s ρ e m) = c := by
  classical
  obtain ⟨b, mu, hb⟩ := exists_representationWeightBasis ρ
  have hdiag (j : n) :
      b.coord j (steinbergCoefficientMatrix x s ρ e m *ᵥ b j) =
        b.coord j (c • p.representationWeightProjector ρ lam (b j)) := by
    by_cases hj : mu j = lam
    · have hm : b j ∈ p.representationWeightSpace ρ lam := hj ▸ hb j
      rw [hscalar _ hm, representationWeightProjector_of_mem ρ lam (mu j) (hb j),
        ite_eq_left hj]
    · have hn : p.representationWeightSpace ρ (mu j) ≠ ⊥ := by
        intro hz
        have hm := hb j
        rw [hz, Submodule.mem_bot] at hm
        exact b.ne_zero j hm
      have hpair : ¬ ∀ i, (m i : ℤ) =
          p.rootDatum.toLinearMap (mu j) (p.rootDatum.coroot (e i)) :=
        fun h => hj (huniq (mu j) hn h)
      have hp := representationWeightProjector_steinbergCoefficient e x s ρ m (hb j)
      rw [ite_eq_right hpair] at hp
      have hc := congrArg (b.coord j) hp
      rw [weightBasis_coord_representationWeightProjector ρ b mu hb] at hc
      rw [representationWeightProjector_of_mem ρ lam (mu j) (hb j), ite_eq_right hj,
        smul_zero]
      exact hc
  have htr : LinearMap.trace k (n → k)
      (Matrix.toLin' (steinbergCoefficientMatrix x s ρ e m)) =
      LinearMap.trace k (n → k) (c • p.representationWeightProjector ρ lam) := by
    rw [LinearMap.trace_eq_matrix_trace k b, LinearMap.trace_eq_matrix_trace k b]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
      Matrix.toLin'_apply, LinearMap.smul_apply]
    exact Finset.sum_congr rfl (fun j _ => hdiag j)
  rw [← Matrix.trace_toLin'_eq, htr, map_smul,
    (representationWeightProjector_isProj ρ lam).trace, hdim,
    Nat.cast_one, smul_eq_mul, mul_one]

end Langlands.GroupScheme.SplitPinning

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (s : p.SimpleReflectionRepresentatives)
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a)

/-- The actual fundamental highest-weight pairings are the own-variable exponent tuple. -/
theorem fundamentalHighestWeight_pairing_single (i j : Fin r) :
    p.rootDatum.toLinearMap (F (e i)).highestWeight (p.rootDatum.coroot (e j)) =
      ((Finsupp.single i 1 : Fin r →₀ ℕ) j : ℤ) := by
  classical
  rw [(F (e i)).isFundamentalWeight (e j)]
  simp [Finsupp.single_apply, eq_comm]

/-- The own-variable ordered coefficient restricts to the actual highest-weight line. -/
def fundamentalTopOperator (i : Fin r) :
    p.representationWeightSpace (F (e i)).representation (F (e i)).highestWeight →ₗ[k]
      p.representationWeightSpace (F (e i)).representation (F (e i)).highestWeight where
  toFun v := ⟨steinbergCoefficientMatrix x s (F (e i)).representation e
      (Finsupp.single i 1 : Fin r →₀ ℕ) *ᵥ v, by
    have h := steinbergCoefficientMatrix_mem_weightSpace x s (F (e i)).representation
      e (Finsupp.single i 1 : Fin r →₀ ℕ) v.property
    rw [(coefficientWeightPath_closed_iff e _ _).mpr
      (fun j => (fundamentalHighestWeight_pairing_single e F i j).symm)] at h
    exact h⟩
  map_add' v w := Subtype.ext (Matrix.mulVec_add _ (v : Fin (F (e i)).dimension → k) w)
  map_smul' c v := Subtype.ext (Matrix.mulVec_smul _ c (v : Fin (F (e i)).dimension → k))

@[simp] theorem fundamentalTopOperator_apply (i : Fin r)
    (v : p.representationWeightSpace (F (e i)).representation (F (e i)).highestWeight) :
    (fundamentalTopOperator e x s F i v : Fin (F (e i)).dimension → k) =
      steinbergCoefficientMatrix x s (F (e i)).representation e
        (Finsupp.single i 1 : Fin r →₀ ℕ) *ᵥ v := rfl

private theorem ofFn_prod_preserves_nonzero {K : Type*} [Field K]
    {n : Type} [Fintype n] [DecidableEq n]
    (r : ℕ) (M : Fin r → Matrix n n K) (V : Submodule K (n → K))
    (h : ∀ j v, v ∈ V → v ≠ 0 → M j *ᵥ v ∈ V ∧ M j *ᵥ v ≠ 0)
    {v : n → K} (hv : v ∈ V) (hv0 : v ≠ 0) :
    (List.ofFn M).prod *ᵥ v ∈ V ∧ (List.ofFn M).prod *ᵥ v ≠ 0 := by
  induction r with
  | zero => simpa using And.intro hv hv0
  | succ r ih =>
    obtain ⟨ht, ht0⟩ := ih (fun j => M j.succ) (fun j => h j.succ)
    simpa only [List.ofFn_succ, List.prod_cons, Matrix.mulVec_mulVec] using
      h 0 _ ht ht0

/-- Local pairing-one nonvanishing makes the full own-variable coefficient
injective on the actual highest-weight line. -/
theorem fundamentalTopOperator_apply_ne_zero [IsAlgClosed k]
    (hroot : SplitSimpleRootHighestCoefficientNonvanishingStatement.{u}) (i : Fin r)
    (v : p.representationWeightSpace (F (e i)).representation (F (e i)).highestWeight)
    (hv : v ≠ 0) : fundamentalTopOperator e x s F i v ≠ 0 := by
  have hv0 : (v : Fin (F (e i)).dimension → k) ≠ 0 :=
    fun h => hv (Subtype.ext h)
  let m : Fin r → ℕ := (Finsupp.single i 1 : Fin r →₀ ℕ)
  have hfac (j : Fin r) (w : Fin (F (e i)).dimension → k)
      (hw : w ∈ p.representationWeightSpace (F (e i)).representation (F (e i)).highestWeight)
      (hw0 : w ≠ 0) :
      (coefficientMatrix ((F (e i)).representation.restrict (x (e j)).hom) (m j) *
        ((F (e i)).representation.rationalMatrix (s (e j)).point :
          Matrix (Fin (F (e i)).dimension) (Fin (F (e i)).dimension) k)) *ᵥ w ∈
            p.representationWeightSpace (F (e i)).representation (F (e i)).highestWeight ∧
      (coefficientMatrix ((F (e i)).representation.restrict (x (e j)).hom) (m j) *
        ((F (e i)).representation.rationalMatrix (s (e j)).point :
          Matrix (Fin (F (e i)).dimension) (Fin (F (e i)).dimension) k)) *ᵥ w ≠ 0 := by
    have hmem := coefficientMatrix_mul_normalizer_mem_weightSpace x s
      (F (e i)).representation (e j) (m j) hw
    rw [p.coefficientWeightStep_eq_self_of_pairing _ _ _
      (fundamentalHighestWeight_pairing_single e F i j).symm] at hmem
    refine ⟨hmem, ?_⟩
    by_cases hji : j = i
    · subst j
      have hp : p.rootDatum.toLinearMap (F (e i)).highestWeight
          (p.rootDatum.coroot (e i)) = 1 := by
        simpa using fundamentalHighestWeight_pairing_single e F i i
      simpa only [m, Finsupp.single_eq_same, Matrix.mulVec_mulVec] using
        hroot k G p (F (e i)).dimension (F (e i)).representation
          (F (e i)).highestWeight (F (e i)).isHighestWeight (e i) hp
          (x (e i)) (s (e i)) w hw hw0
    · have hm0 : m j = 0 := by simp [m, Ne.symm hji]
      rw [hm0, coefficientMatrix_zero, Matrix.one_mul]
      intro hz
      apply hw0
      apply Matrix.mulVec_injective_of_isUnit
        (Units.isUnit ((F (e i)).representation.rationalMatrix (s (e j)).point))
      simpa only [Matrix.mulVec_zero] using hz
  have hprod := ofFn_prod_preserves_nonzero r _ _ hfac v.property hv0
  intro hz
  exact hprod.2 (congrArg Subtype.val hz)

end Langlands.GroupScheme.SplitPinning

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)

/-- Among weights below a highest weight, its simple-coroot pairings determine it uniquely. -/
theorem highestWeight_eq_of_occurring_of_pairings
    (lam : characterLattice p.torus) (hhigh : p.IsHighestWeight ρ lam)
    (mu : characterLattice p.torus) (hmu : p.representationWeightSpace ρ mu ≠ ⊥)
    (hp : ∀ a : p.base.support,
      p.rootDatum.toLinearMap lam (p.rootDatum.coroot a) =
        p.rootDatum.toLinearMap mu (p.rootDatum.coroot a)) : mu = lam := by
  let : Fintype p.rootIndex := Fintype.ofFinite p.rootIndex
  apply Eq.symm
  apply sub_eq_zero.mp
  apply Langlands.RootDatum.Triangular.eq_zero_of_mem_rootSpan_of_forall_simple_coroot
    (b := p.base)
  · exact Langlands.RootDatum.Triangular.positiveCone_le_rootSpan (hhigh.2.2.2 mu hmu)
  · intro a ha
    rw [map_sub, LinearMap.sub_apply, hp ⟨a, ha⟩, sub_self]

variable {r : ℕ} (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (s : p.SimpleReflectionRepresentatives)
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a)

/-- The actual fundamental trace diagonal is nonzero once the local pairing-one
root coefficient is known to be nonzero on reflected highest vectors. -/
theorem fundamentalTraceDiagonal_ne_zero_of_simpleRootHighestCoefficient [IsAlgClosed k]
    (hroot : SplitSimpleRootHighestCoefficientNonvanishingStatement.{u}) (i : Fin r) :
    fundamentalTraceDiagonal e x s F i ≠ 0 := by
  let V := p.representationWeightSpace (F (e i)).representation (F (e i)).highestWeight
  let T : V →ₗ[k] V := fundamentalTopOperator e x s F i
  have hdim : Module.finrank k V = 1 := (F (e i)).isHighestWeight.2.2.1
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hdim]; omega)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hv (T v)
  have hc0 : c ≠ 0 := by
    intro hz
    have hTv : T v ≠ 0 := fundamentalTopOperator_apply_ne_zero e x s F hroot i v hv
    apply hTv
    rw [← hc, hz, zero_smul]
  have hTscalar (w : V) : T w = c • w := by
    obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_eq_one hdim hv w
    rw [map_smul, ← hc]
    exact smul_comm a c v
  have hscalar (w : Fin (F (e i)).dimension → k)
      (hw : w ∈ p.representationWeightSpace (F (e i)).representation (F (e i)).highestWeight) :
      steinbergCoefficientMatrix x s (F (e i)).representation e
        (Finsupp.single i 1 : Fin r →₀ ℕ) *ᵥ w = c • w :=
    congrArg Subtype.val (hTscalar ⟨w, hw⟩)
  have huniq (mu : characterLattice p.torus)
      (hmu : p.representationWeightSpace (F (e i)).representation mu ≠ ⊥)
      (hm : ∀ j, (((Finsupp.single i 1 : Fin r →₀ ℕ) j : ℕ) : ℤ) =
        p.rootDatum.toLinearMap mu (p.rootDatum.coroot (e j))) :
      mu = (F (e i)).highestWeight := by
    apply highestWeight_eq_of_occurring_of_pairings (F (e i)).representation
      (F (e i)).highestWeight (F (e i)).isHighestWeight mu hmu
    intro a
    obtain ⟨j, rfl⟩ := e.surjective a
    exact (fundamentalHighestWeight_pairing_single e F i j).trans (hm j)
  have htrace := steinbergCoefficientMatrix_trace_eq_scalar e x s (F (e i)).representation
    (Finsupp.single i 1 : Fin r →₀ ℕ) (F (e i)).highestWeight c hdim huniq hscalar
  change (steinbergRestriction e x s (F (e i)).representation.traceClassFunction).coeff
    (Finsupp.single i 1) ≠ 0
  rw [steinbergRestriction_trace_coeff_eq_trace, htrace]
  exact hc0

end Langlands.GroupScheme.SplitPinning

namespace Langlands.GroupScheme

/-- The generic local pairing-one root-string theorem suffices for the entire
actual triangular character calculation. It remains an explicit input. -/
theorem splitSteinbergCharacterTriangular_of_simpleRootHighestCoefficient
    (hroot : SplitSimpleRootHighestCoefficientNonvanishingStatement.{u}) :
    SplitSteinbergCharacterTriangularStatement.{u} := by
  intro k _ _ G _ p _ r e F x s
  exact SplitPinning.hasTriangularFundamentalRestriction_of_diagonal_ne_zero e x s F
    (SplitPinning.fundamentalTraceDiagonal_ne_zero_of_simpleRootHighestCoefficient e x s F hroot)

end Langlands.GroupScheme
