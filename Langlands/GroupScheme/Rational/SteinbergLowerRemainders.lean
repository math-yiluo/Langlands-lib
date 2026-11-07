import Langlands.GroupScheme.Rational.SteinbergMonomialSupport
import Langlands.GroupScheme.Rational.DominantWeightTriangularity
import Langlands.GroupScheme.Rational.SteinbergCharacterTriangularity

/-! # Well-founded lower-variable remainders for actual fundamental traces -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators Matrix

namespace Langlands.RootDatum.Triangular

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    {P : RootPairing ι ℤ X Y} {b : P.Base}

private theorem corootCone_pairing_nonneg {x : X} (hx : IsDominant P b x)
    {y : Y} (hy : y ∈ AddSubmonoid.closure (P.coroot '' b.support)) :
    0 ≤ P.toLinearMap x y := by
  induction hy using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact hx a ha
  | zero => simp
  | add y z _ _ hy hz =>
    simpa only [map_add] using add_nonneg hy hz

/-- The canonical root form is nonnegative between two dominant weights. -/
theorem rootForm_nonneg_of_isDominant [Fintype ι] {x y : X}
    (hx : IsDominant P b x) (hy : IsDominant P b y) : 0 ≤ P.RootForm x y := by
  rw [P.rootForm_apply_apply]
  apply Finset.sum_nonneg
  intro a ha
  change 0 ≤ P.toLinearMap x (P.coroot a) * P.toLinearMap y (P.coroot a)
  rcases b.coroot_mem_or_neg_mem a with h | h
  · exact mul_nonneg (corootCone_pairing_nonneg hx h) (corootCone_pairing_nonneg hy h)
  · have hx' := corootCone_pairing_nonneg hx h
    have hy' := corootCone_pairing_nonneg hy h
    simp only [map_neg] at hx' hy'
    exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

/-- Adding a dominant weight cannot decrease the canonical squared length. -/
theorem rootForm_self_le_of_dominant_difference [Fintype ι] {x y : X}
    (hx : IsDominant P b x) (hdiff : IsDominant P b (y - x)) :
    P.RootForm x x ≤ P.RootForm y y := by
  have h1 := rootForm_nonneg_of_isDominant hx hdiff
  have h2 := rootForm_nonneg_of_isDominant hdiff hx
  have h3 := P.zero_le_rootForm (y - x)
  simp only [map_sub, LinearMap.sub_apply] at h1 h2 h3
  linarith

end Langlands.RootDatum.Triangular

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (s : p.SimpleReflectionRepresentatives)
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a)

/-- The canonical squared length of the supplied fundamental highest weight. -/
def fundamentalWeightLength (a : p.base.support) : ℕ :=
  letI : Fintype p.rootIndex := Fintype.ofFinite p.rootIndex
  (p.rootDatum.RootForm (F a).highestWeight (F a).highestWeight).toNat

/-- Strict increase in fundamental-weight length is a well-founded variable order. -/
theorem fundamentalWeightLength_wellFounded :
    WellFounded (fun i j : Fin r =>
      fundamentalWeightLength F (e i) < fundamentalWeightLength F (e j)) :=
  (measure (fun i : Fin r => fundamentalWeightLength F (e i))).wf

/-- The actual coefficient of the variable corresponding to a fundamental trace. -/
def fundamentalTraceDiagonal (i : Fin r) : k :=
  (steinbergRestriction e x s (F (e i)).character).coeff (Finsupp.single i 1)

/-- Remove the own-variable linear term from the actual restricted fundamental trace. -/
def fundamentalTraceRemainder (i : Fin r) : MvPolynomial (Fin r) k :=
  steinbergRestriction e x s (F (e i)).character -
    MvPolynomial.C (fundamentalTraceDiagonal e x s F i) * MvPolynomial.X i

/-- Removing the own-variable term cancels precisely that monomial coefficient. -/
@[simp] theorem fundamentalTraceRemainder_coeff_self (i : Fin r) :
    (fundamentalTraceRemainder e x s F i).coeff (Finsupp.single i 1) = 0 := by
  classical
  simp [fundamentalTraceRemainder, fundamentalTraceDiagonal, MvPolynomial.coeff_C_mul]

/-- A variable in a non-leading trace monomial has strictly smaller
fundamental-weight length than the source fundamental character. -/
theorem fundamentalWeightLength_lt_of_trace_coeff_ne_zero
    (i j : Fin r) (d : Fin r →₀ ℕ)
    (hcoeff : (steinbergRestriction e x s (F (e i)).character).coeff d ≠ 0)
    (hdne : d ≠ Finsupp.single i 1) (hj : 0 < d j) :
    fundamentalWeightLength F (e j) < fundamentalWeightLength F (e i) := by
  classical
  let : Fintype p.rootIndex := Fintype.ofFinite p.rootIndex
  obtain ⟨lam, hocc, hdom, hpair⟩ :=
    exists_dominant_weight_of_steinbergRestriction_trace_coeff_ne_zero
      e x s (F (e i)).representation d hcoeff
  have hFD (a : p.base.support) :
      Langlands.RootDatum.Triangular.IsDominant p.rootDatum p.base (F a).highestWeight := by
    intro b hb
    change 0 ≤ p.rootDatum.toLinearMap (F a).highestWeight
      (p.rootDatum.coroot (⟨b, hb⟩ : p.base.support))
    rw [(F a).isFundamentalWeight ⟨b, hb⟩]
    split_ifs <;> omega
  have hlamD : Langlands.RootDatum.Triangular.IsDominant p.rootDatum p.base lam :=
    fun a ha => hdom ⟨a, ha⟩
  have hnorm := Langlands.RootDatum.Triangular.rootForm_self_le_of_isDominant
    hlamD (hFD (e i)) ((F (e i)).isHighestWeight.2.2.2 lam hocc)
  have hlamne : lam ≠ (F (e i)).highestWeight := by
    intro heq
    apply hdne
    ext t
    have ht := hpair t
    rw [heq, (F (e i)).isFundamentalWeight (e t)] at ht
    by_cases hti : t = i
    · subst t
      simp at ht ⊢
      omega
    · have heti : e t ≠ e i := fun he => hti (e.injective he)
      simp [heti, Ne.symm hti] at ht ⊢
      omega
  have hlt : p.rootDatum.RootForm lam lam <
      p.rootDatum.RootForm (F (e i)).highestWeight (F (e i)).highestWeight := by
    have hle := hnorm.1
    have hne : p.rootDatum.RootForm lam lam ≠
        p.rootDatum.RootForm (F (e i)).highestWeight (F (e i)).highestWeight :=
      fun h => hlamne (hnorm.2 h)
    omega
  have hdiff : p.IsDominantWeight (lam - (F (e j)).highestWeight) := by
    intro a
    obtain ⟨t, rfl⟩ := e.surjective a
    rw [map_sub, LinearMap.sub_apply, ← hpair t,
      (F (e j)).isFundamentalWeight (e t)]
    split_ifs with ht
    · have htj : t = j := e.injective ht
      subst t
      omega
    · omega
  have hdiffD : Langlands.RootDatum.Triangular.IsDominant p.rootDatum p.base
      (lam - (F (e j)).highestWeight) := fun a ha => hdiff ⟨a, ha⟩
  have hleJ := Langlands.RootDatum.Triangular.rootForm_self_le_of_dominant_difference
    (hFD (e j)) hdiffD
  have hnonneg := p.rootDatum.zero_le_rootForm (F (e j)).highestWeight
  change (p.rootDatum.RootForm (F (e j)).highestWeight (F (e j)).highestWeight).toNat <
    (p.rootDatum.RootForm (F (e i)).highestWeight (F (e i)).highestWeight).toNat
  omega

/-- Every actual trace remainder involves only variables of strictly smaller
fundamental-weight length. -/
theorem fundamentalTraceRemainder_hasLowerRemainders :
    Langlands.CommutativeAlgebra.TriangularPolynomial.HasLowerRemainders
      (fun j i : Fin r => fundamentalWeightLength F (e j) < fundamentalWeightLength F (e i))
      (fundamentalTraceRemainder e x s F) := by
  classical
  intro i j hvars
  obtain ⟨d, hd, hjd⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hvars
  have hcoeffR := MvPolynomial.mem_support_iff.mp hd
  have hdne : d ≠ Finsupp.single i 1 := by
    intro heq
    subst d
    exact hcoeffR (fundamentalTraceRemainder_coeff_self e x s F i)
  have hcoeff : (steinbergRestriction e x s (F (e i)).character).coeff d ≠ 0 := by
    have heq : (fundamentalTraceRemainder e x s F i).coeff d =
        (steinbergRestriction e x s (F (e i)).character).coeff d := by
      simp [fundamentalTraceRemainder, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
        Ne.symm hdne]
    exact fun hz => hcoeffR (heq.trans hz)
  exact fundamentalWeightLength_lt_of_trace_coeff_ne_zero e x s F i j d hcoeff hdne
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hjd))

/-- Nonvanishing of the actual diagonal coefficients completes triangularity;
the well-founded lower-variable condition is already proved. -/
theorem hasTriangularFundamentalRestriction_of_diagonal_ne_zero
    (hdiag : ∀ i, fundamentalTraceDiagonal e x s F i ≠ 0) :
    HasTriangularFundamentalRestriction e x s F := by
  refine ⟨(fun j i => fundamentalWeightLength F (e j) < fundamentalWeightLength F (e i)),
    fundamentalWeightLength_wellFounded e F,
    (fun i => Units.mk0 _ (hdiag i)), fundamentalTraceRemainder e x s F,
    fundamentalTraceRemainder_hasLowerRemainders e x s F, ?_⟩
  intro i
  change steinbergRestriction e x s (F (e i)).character =
    MvPolynomial.C (fundamentalTraceDiagonal e x s F i) * MvPolynomial.X i +
      (steinbergRestriction e x s (F (e i)).character -
        MvPolynomial.C (fundamentalTraceDiagonal e x s F i) * MvPolynomial.X i)
  ring

end Langlands.GroupScheme.SplitPinning
