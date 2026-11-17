import Langlands.GroupScheme.Rational.SemistandardWeylTransporters
import Langlands.GroupScheme.Rational.MinimalParabolicSplitComponent

/-! # The proper/group split under actual semistandard Levi comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} {P Q : SubgroupFunctor G}

/-- Rational conjugation on every test scheme preserves the whole subgroup. -/
theorem IsRationallyConjugate.eq_top_iff (h : P.IsRationallyConjugate Q) :
    P = ⊤ ↔ Q = ⊤ := by
  obtain ⟨g, hg⟩ := h
  constructor
  · intro hP
    have hQ := (eq_comap_iso_iff (G.innerIso g)).mp hg
    rw [hP, comap_top] at hQ
    exact hQ.symm
  · intro hQ
    simpa only [hQ, comap_top] using hg

end SubgroupFunctor

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

/-- A semistandard parabolic is the whole group exactly when its literal Levi
is the whole group. The precise fixed-torus dynamic coverage remains explicit. -/
theorem semistandardParabolic_eq_top_iff_levi_eq_top
    (hcoverage : SemistandardSpectralDynamicCoverageStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (p : SemistandardSpectralIndex i) :
    p.parabolic = ⊤ ↔ p.levi = ⊤ := by
  obtain ⟨ζ, rfl⟩ := hcoverage k G hG T i hi p
  let := hG.smooth
  let := hG.isAffineHom
  exact Dynamic.parabolic_eq_top_iff_centralizer_eq_top
    hG.hasTrivialUnipotentRadical (CommGroupScheme.groupHom ζ ≫ i)

/-- Exact structural preservation needed for proper truncation in VII.1.4:
rationally conjugate actual Levis have the same group/proper status. -/
def SemistandardProperSplitComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i) (p q : SemistandardSpectralIndex i),
    p.levi.IsRationallyConjugate q.levi →
      (p.parabolic = ⊤ ↔ q.parabolic = ⊤)

/-- The published fixed-torus dynamic-coverage target suffices for the exact
split comparison; no analytic Fourier comparison is a premise of this proof. -/
theorem semistandardProperSplitComparison_of_dynamicCoverage
    (hcoverage : SemistandardSpectralDynamicCoverageStatement.{u}) :
    SemistandardProperSplitComparisonStatement.{u} := by
  intro k _ G hG T i hi p q hpq
  rw [semistandardParabolic_eq_top_iff_levi_eq_top hcoverage hG hi p,
    semistandardParabolic_eq_top_iff_levi_eq_top hcoverage hG hi q]
  exact hpq.eq_top_iff

section Comparisons

variable (hsplit : SemistandardProperSplitComparisonStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (p q : SemistandardSpectralIndex i)

include hsplit hG hi

/-- The comparison between different parabolics with the same literal Levi
cannot mix the proper and group parts. -/
theorem semistandardParabolic_eq_top_iff_of_sameLevi (hlevi : p.levi = q.levi) :
    p.parabolic = ⊤ ↔ q.parabolic = ⊤ := by
  apply hsplit k G hG T i hi p q
  rw [hlevi]
  exact SubgroupFunctor.IsRationallyConjugate.refl _

/-- The same comparison in the proper-part formulation. -/
theorem semistandardParabolic_ne_top_iff_of_sameLevi (hlevi : p.levi = q.levi) :
    p.parabolic ≠ ⊤ ↔ q.parabolic ≠ ⊤ :=
  not_congr (semistandardParabolic_eq_top_iff_of_sameLevi hsplit hG hi p q hlevi)

variable (hcentral : torusCentralizer i ≤ p.levi)

/-- Every actual Weyl equality transporter preserves the group part. An
inclusion transporter alone is deliberately insufficient. -/
theorem semistandardParabolic_eq_top_iff_of_weylConjugacy
    (w : semistandardWeylConjugacySet i p.toLevi q.toLevi hcentral) :
    p.parabolic = ⊤ ↔ q.parabolic = ⊤ :=
  hsplit k G hG T i hi p q
    (isRationallyConjugate_of_mem_semistandardWeylConjugacySet
      i p.toLevi q.toLevi hcentral w)

/-- Every actual Weyl equality transporter also preserves the proper part. -/
theorem semistandardParabolic_ne_top_iff_of_weylConjugacy
    (w : semistandardWeylConjugacySet i p.toLevi q.toLevi hcentral) :
    p.parabolic ≠ ⊤ ↔ q.parabolic ≠ ⊤ :=
  not_congr (semistandardParabolic_eq_top_iff_of_weylConjugacy
    hsplit hG hi p q hcentral w)

/-- Preservation holds for the genuine left target-Weyl quotient, with no
choice of orbit-image quotient or normalizer representative. -/
theorem semistandardParabolic_eq_top_iff_of_weylConjugacyQuotient
    (w : SemistandardWeylConjugacyQuotient i p.toLevi q.toLevi hcentral) :
    p.parabolic = ⊤ ↔ q.parabolic = ⊤ := by
  induction w using Quotient.inductionOn with
  | h s =>
    exact semistandardParabolic_eq_top_iff_of_weylConjugacy
      hsplit hG hi p q hcentral s

/-- Proper-part preservation on the same genuine Weyl quotient. -/
theorem semistandardParabolic_ne_top_iff_of_weylConjugacyQuotient
    (w : SemistandardWeylConjugacyQuotient i p.toLevi q.toLevi hcentral) :
    p.parabolic ≠ ⊤ ↔ q.parabolic ≠ ⊤ :=
  not_congr (semistandardParabolic_eq_top_iff_of_weylConjugacyQuotient
    hsplit hG hi p q hcentral w)

end Comparisons

end Langlands.GroupScheme
