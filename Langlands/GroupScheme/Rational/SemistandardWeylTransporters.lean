import Langlands.GroupScheme.Rational.SemistandardSpectralIndex
import Langlands.GroupScheme.Rational.StandardLeviLiftIndependence
import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Mathlib.Data.Fintype.Quotient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Literal semistandard Levi Weyl transporters and their left quotients -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

/-- The precise centralizer-containment input for the published Weyl action on
all-test semistandard Levi subgroup functors. -/
def SemistandardLeviCentralizerContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i → ∀ M : SemistandardSpectralLevi i,
        torusCentralizer i ≤ M.val

/-- Fixed-torus dynamic coverage supplies the exact containment input. This
conditional reduction does not assert that coverage has been proved. -/
theorem semistandardLeviCentralizerContainment_of_dynamicCoverage
    (h : SemistandardSpectralDynamicCoverageStatement.{u}) :
    SemistandardLeviCentralizerContainmentStatement.{u} := by
  intro k _ G hG T i hi M
  obtain ⟨p, hp⟩ := M.property
  obtain ⟨ζ, hζ⟩ := h k G hG T i hi p
  have he := congrArg SemistandardSpectralIndex.levi hζ
  rw [← hp, ← he]
  exact torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ζ)

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G)

/-- `W^M`: the image in the actual `N(k)/Z(k)` of the normalizer points
belonging to the literal Levi's rational-point subgroup. -/
def semistandardLeviRelativeWeylSubgroup (M : SemistandardSpectralLevi i) :
    Subgroup (relativeWeylGroup i) :=
  (M.val.rationalPoints.subgroupOf (normalizerPoints i)).map
    (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))

theorem mem_semistandardLeviRelativeWeylSubgroup
    (M : SemistandardSpectralLevi i) (w : relativeWeylGroup i) :
    w ∈ semistandardLeviRelativeWeylSubgroup i M ↔
      ∃ n : normalizerPoints i, (n : rationalPoints G) ∈ M.val.rationalPoints ∧
        (QuotientGroup.mk n : relativeWeylGroup i) = w := by
  rfl

/-- Under the exact centralizer containment, every lift tests `W^M` membership
by membership in the same literal Levi, not a chosen model. -/
theorem mk_mem_semistandardLeviRelativeWeylSubgroup_iff
    (M : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (n : normalizerPoints i) :
    (QuotientGroup.mk n : relativeWeylGroup i) ∈
        semistandardLeviRelativeWeylSubgroup i M ↔
      (n : rationalPoints G) ∈ M.val.rationalPoints := by
  rw [mem_semistandardLeviRelativeWeylSubgroup]
  constructor
  · rintro ⟨m, hm, he⟩
    have hz : m⁻¹ * n ∈ (centralizerPoints i).subgroupOf (normalizerPoints i) :=
      QuotientGroup.eq.mp he
    have hzM : (m : rationalPoints G)⁻¹ * (n : rationalPoints G) ∈
        M.val.rationalPoints := by
      apply hM (Over.mk (𝟙 _))
      change (m : rationalPoints G)⁻¹ * (n : rationalPoints G) ∈
        (torusCentralizer i).carrier (Over.mk (𝟙 _))
      rw [torusCentralizer_carrier_base]
      exact hz
    simpa only [mul_inv_cancel_left] using M.val.rationalPoints.mul_mem hm hzM
  · intro hn
    exact ⟨n, hn, rfl⟩

/-- The unquotiented V.1 transporter: `w M w⁻¹ ⊆ M'` on all test schemes.
The source Levi's containment proof is an explicit input. -/
def semistandardWeylTransporterSet (M M' : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) : Set (relativeWeylGroup i) :=
  {w | relativeWeylConjugateSubgroupFunctor i M.val hM w ≤ M'.val}

/-- The equality transporter used for conjugate Levis in VII.2. This is kept
separate from V.1's inclusion transporter. -/
def semistandardWeylConjugacySet (M M' : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) : Set (relativeWeylGroup i) :=
  {w | relativeWeylConjugateSubgroupFunctor i M.val hM w = M'.val}

theorem semistandardWeylConjugacySet_subset_transporter
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val) :
    semistandardWeylConjugacySet i M M' hM ⊆
      semistandardWeylTransporterSet i M M' hM :=
  fun _ hw => le_of_eq hw

/-- Exact all-test representative formula for the inclusion transporter. -/
theorem mk_mem_semistandardWeylTransporterSet_iff
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (n : normalizerPoints i) :
    (QuotientGroup.mk n : relativeWeylGroup i) ∈
        semistandardWeylTransporterSet i M M' hM ↔
      M.val.comap (G.innerIso (n : rationalPoints G)).inv ≤ M'.val :=
  Iff.rfl

/-- Exact all-test representative formula for the equality transporter. -/
theorem mk_mem_semistandardWeylConjugacySet_iff
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (n : normalizerPoints i) :
    (QuotientGroup.mk n : relativeWeylGroup i) ∈
        semistandardWeylConjugacySet i M M' hM ↔
      M.val.comap (G.innerIso (n : rationalPoints G)).inv = M'.val :=
  Iff.rfl

/-- Left multiplication by the target Levi's actual Weyl subgroup preserves
the all-test inclusion transporter. -/
theorem mul_mem_semistandardWeylTransporterSet
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    {u w : relativeWeylGroup i}
    (hu : u ∈ semistandardLeviRelativeWeylSubgroup i M')
    (hw : w ∈ semistandardWeylTransporterSet i M M' hM) :
    u * w ∈ semistandardWeylTransporterSet i M M' hM := by
  obtain ⟨m, hm, rfl⟩ := (mem_semistandardLeviRelativeWeylSubgroup i M' u).mp hu
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  change M.val.comap (G.innerIso
    ((m : rationalPoints G) * (n : rationalPoints G))).inv ≤ M'.val
  change M.val.comap (G.innerIso (n : rationalPoints G)).inv ≤ M'.val at hw
  rw [← innerIso_inv_hom, mul_inv_rev, innerIso_mul_hom,
    SubgroupFunctor.comap_comp, innerIso_inv_hom, innerIso_inv_hom]
  have hfix : M'.val.comap (G.innerIso (m : rationalPoints G)).inv = M'.val := by
    rw [← innerIso_inv_hom]
    exact M'.val.comap_innerIso_hom_eq_of_mem (M'.val.rationalPoints.inv_mem hm)
  exact (SubgroupFunctor.comap_mono hw).trans_eq hfix

/-- Left multiplication by the target Weyl subgroup also preserves equality
of the literal Levi subgroup functors. -/
theorem mul_mem_semistandardWeylConjugacySet
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    {u w : relativeWeylGroup i}
    (hu : u ∈ semistandardLeviRelativeWeylSubgroup i M')
    (hw : w ∈ semistandardWeylConjugacySet i M M' hM) :
    u * w ∈ semistandardWeylConjugacySet i M M' hM := by
  obtain ⟨m, hm, rfl⟩ := (mem_semistandardLeviRelativeWeylSubgroup i M' u).mp hu
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  change M.val.comap (G.innerIso
    ((m : rationalPoints G) * (n : rationalPoints G))).inv = M'.val
  change M.val.comap (G.innerIso (n : rationalPoints G)).inv = M'.val at hw
  rw [← innerIso_inv_hom, mul_inv_rev, innerIso_mul_hom,
    SubgroupFunctor.comap_comp, innerIso_inv_hom, innerIso_inv_hom, hw,
    ← innerIso_inv_hom]
  exact M'.val.comap_innerIso_hom_eq_of_mem (M'.val.rationalPoints.inv_mem hm)

/-- The source's LEFT target-Weyl quotient of the inclusion transporter.
`rightRel` identifies `s,t` when `t*s⁻¹ ∈ W^M'`. -/
def semistandardWeylTransporterRel (M M' : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) :
    Setoid (semistandardWeylTransporterSet i M M' hM) :=
  (QuotientGroup.rightRel (semistandardLeviRelativeWeylSubgroup i M')).comap Subtype.val

/-- `W^M' \ {w ∈ W^G | w M w⁻¹ ⊆ M'}`, with Weyl multiplicities retained. -/
abbrev SemistandardWeylTransporterQuotient (M M' : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) : Type u :=
  Quotient (semistandardWeylTransporterRel i M M' hM)

/-- The source's LEFT target-Weyl relation on the equality transporter. -/
def semistandardWeylConjugacyRel (M M' : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) :
    Setoid (semistandardWeylConjugacySet i M M' hM) :=
  (QuotientGroup.rightRel (semistandardLeviRelativeWeylSubgroup i M')).comap Subtype.val

/-- `W(M'|G|M)` with equality of literal Levi functors. -/
abbrev SemistandardWeylConjugacyQuotient (M M' : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) : Type u :=
  Quotient (semistandardWeylConjugacyRel i M M' hM)

/-- Equality of classes is exactly left multiplication by the target Weyl subgroup. -/
theorem semistandardWeylConjugacyQuotient_mk_eq_iff
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (s t : semistandardWeylConjugacySet i M M' hM) :
    Quotient.mk (semistandardWeylConjugacyRel i M M' hM) s = Quotient.mk _ t ↔
      t.val * s.val⁻¹ ∈ semistandardLeviRelativeWeylSubgroup i M' :=
  Quotient.eq.trans QuotientGroup.rightRel_apply

/-- Every quotient class has a literal relative-Weyl transporter representative. -/
theorem semistandardWeylConjugacyQuotient_mk_surjective
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val) :
    Function.Surjective (Quotient.mk (semistandardWeylConjugacyRel i M M' hM)) :=
  Quotient.mk_surjective

section Descend
variable {A : Type v}

/-- Descend a summand only after its exact left target-Weyl invariance has
been supplied. No representative or orbit-image quotient is substituted. -/
def semistandardWeylConjugacyDescend
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (term : semistandardWeylConjugacySet i M M' hM → A)
    (hterm : ∀ s t, t.val * s.val⁻¹ ∈
      semistandardLeviRelativeWeylSubgroup i M' → term s = term t) :
    SemistandardWeylConjugacyQuotient i M M' hM → A :=
  Quotient.lift term (fun s t hst => hterm s t (QuotientGroup.rightRel_apply.mp hst))

@[simp] theorem semistandardWeylConjugacyDescend_mk
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (term : semistandardWeylConjugacySet i M M' hM → A)
    (hterm : ∀ s t, t.val * s.val⁻¹ ∈
      semistandardLeviRelativeWeylSubgroup i M' → term s = term t)
    (s : semistandardWeylConjugacySet i M M' hM) :
    semistandardWeylConjugacyDescend i M M' hM term hterm
      (Quotient.mk _ s) = term s :=
  rfl

end Descend

instance (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    [Finite (relativeWeylGroup i)] :
    Finite (SemistandardWeylTransporterQuotient i M M' hM) := inferInstance

instance (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    [Finite (relativeWeylGroup i)] :
    Finite (SemistandardWeylConjugacyQuotient i M M' hM) := inferInstance

/-- Actual reductivity and maximal splitness supply finiteness; genericity
is obtained from the published existence theorem. -/
theorem finite_semistandardWeylQuotients (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (M M' : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) :
    Finite (SemistandardWeylTransporterQuotient i M M' hM) ∧
      Finite (SemistandardWeylConjugacyQuotient i M M' hM) := by
  let := hG.isAffineHom
  let := hG.smooth
  let := hi.isSplitSubtorus.mono
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  let := (relativeWeylCoxeter k G hG T i hi ν hν).1
  exact ⟨inferInstance, inferInstance⟩

/-- An actual equality transporter gives literal rational conjugacy. -/
theorem isRationallyConjugate_of_mem_semistandardWeylConjugacySet
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (w : semistandardWeylConjugacySet i M M' hM) :
    M.val.IsRationallyConjugate M'.val := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective w.val
  have hw := w.property
  change relativeWeylConjugateSubgroupFunctor i M.val hM w.val = M'.val at hw
  rw [← hn, relativeWeylConjugateSubgroupFunctor_mk] at hw
  exact ⟨(n : rationalPoints G),
    (SubgroupFunctor.eq_comap_iso_iff (G.innerIso (n : rationalPoints G))).mpr hw⟩

/-- Nonconjugate literal Levis have an empty equality-transporter quotient. -/
theorem isEmpty_semistandardWeylConjugacyQuotient
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (h : ¬ M.val.IsRationallyConjugate M'.val) :
    IsEmpty (SemistandardWeylConjugacyQuotient i M M' hM) := by
  refine ⟨fun q => ?_⟩
  induction q using Quotient.inductionOn with
  | h w => exact h (isRationallyConjugate_of_mem_semistandardWeylConjugacySet i M M' hM w)

section Sum
variable {A : Type v} [AddCommMonoid A] [Finite (relativeWeylGroup i)]

/-- Elementary summation over the genuine quotient, before a spectral
summand is supplied by the normalized-comparison and packet constructions. -/
def semistandardWeylConjugacySum (M M' : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val)
    (term : SemistandardWeylConjugacyQuotient i M M' hM → A) : A :=
  letI := Fintype.ofFinite (SemistandardWeylConjugacyQuotient i M M' hM)
  ∑ s, term s

@[simp] theorem semistandardWeylConjugacySum_zero
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val) :
    semistandardWeylConjugacySum i M M' hM
      (fun _ => (0 : A)) = 0 := by
  classical
  simp [semistandardWeylConjugacySum]

theorem semistandardWeylConjugacySum_congr
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (term term' : SemistandardWeylConjugacyQuotient i M M' hM → A)
    (h : ∀ s, term s = term' s) :
    semistandardWeylConjugacySum i M M' hM term =
      semistandardWeylConjugacySum i M M' hM term' := by
  unfold semistandardWeylConjugacySum
  exact Finset.sum_congr rfl (fun s _ => h s)

/-- A descended sum can be computed using the quotient's chosen representatives;
the descent law ensures that other representative systems give the same value. -/
theorem semistandardWeylConjugacySum_descend
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (term : semistandardWeylConjugacySet i M M' hM → A)
    (hterm : ∀ s t, t.val * s.val⁻¹ ∈
      semistandardLeviRelativeWeylSubgroup i M' → term s = term t) :
    semistandardWeylConjugacySum i M M' hM
      (semistandardWeylConjugacyDescend i M M' hM term hterm) =
      semistandardWeylConjugacySum i M M' hM (fun q => term q.out) := by
  apply semistandardWeylConjugacySum_congr
  intro q
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

theorem semistandardWeylConjugacySum_of_not_conjugate
    (M M' : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (h : ¬ M.val.IsRationallyConjugate M'.val)
    (term : SemistandardWeylConjugacyQuotient i M M' hM → A) :
    semistandardWeylConjugacySum i M M' hM term = 0 := by
  let := isEmpty_semistandardWeylConjugacyQuotient i M M' hM h
  simp [semistandardWeylConjugacySum]
end Sum

/-- The precise remaining classification input: rational conjugacy of literal
Levis is realized by an actual relative Weyl element. -/
def SemistandardWeylConjugacyCoverageStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i → ∀ (M M' : SemistandardSpectralLevi i)
      (hM : torusCentralizer i ≤ M.val),
      M.val.IsRationallyConjugate M'.val →
        Nonempty (SemistandardWeylConjugacyQuotient i M M' hM)

/-- V.1's inclusion transporter equals the equality transporter when its two
literal Levis are conjugate. This geometric comparison is not assumed by the
carrier construction and remains a named target. -/
def SemistandardWeylTransporterEqualityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i → ∀ (M M' : SemistandardSpectralLevi i)
      (hM : torusCentralizer i ≤ M.val),
      M.val.IsRationallyConjugate M'.val →
        semistandardWeylTransporterSet i M M' hM =
          semistandardWeylConjugacySet i M M' hM

end Langlands.GroupScheme
