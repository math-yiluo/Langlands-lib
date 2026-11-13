import Langlands.Representation.Classification.TadicBlockRing
import Langlands.Representation.Classification.MultisegmentConstituentRealTwistCompatibilityProof
import Langlands.Representation.Classification.SegmentSocleProductHighestDerivativeProof
import Langlands.Representation.Classification.SegmentHeadDecreasingSocle
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Representation.Filtration.ExactFamilyLengthProof

/-!
# The shifted highest derivative of a unitarizable `⟨a⟩`

Under Bernstein's Theorem 2.5(iii), the shifted highest derivative `ν^(1/2) π^(h)` of an
irreducible unitarizable Zelevinsky socle `π = ⟨a⟩` is an irreducible unitarizable
Zelevinsky socle of `ν^(1/2) a⁻`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.TadicBlockDerivative

open Aubert Aubert.SegmentPolynomialSurjectivity PadicField.TopologicalData
open SmoothRep SmoothRep.IrreducibleGrothendieckProof Derivative TadicBlockRing

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

attribute [local instance] ringR

/-- An irreducible subquotient of an irreducible representation is isomorphic to it. -/
theorem nonempty_iso_of_isSubquotient {N : ℕ}
    {A B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hA : letI := T.topology; A.IsIrreducible) (hB : letI := T.topology; B.IsIrreducible)
    (h : letI := T.topology; SmoothRep.IsSubquotient A B) :
    letI := T.topology; Nonempty (A ≅ B) := by
  let := T.topology
  have hBfl := SmoothRep.hasFiniteLength_of_isIrreducible hB
  have hpos := (compositionMultiplicity_pos_iff_isSubquotient ⟨B, hBfl⟩ A hA).mpr h
  have hc := coeff_gradedInclusion_ofRepresentation F T N B hBfl A hA
  change coeff F T N _ (cls F T B hBfl) = _ at hc
  rw [cls_eq_basisClass F T hB] at hc
  by_cases he : GeneralLinear.irreducibleIsoClass N F.Carrier A hA =
      GeneralLinear.irreducibleIsoClass N F.Carrier B hB
  · exact (SmoothRep.irreducibleIsoClass_eq_iff hA hB).mp he
  · rw [coeff_basisClass_of_ne F T N (Ne.symm he)] at hc
    have : (0 : ℤ) < compositionMultiplicity ⟨B, hBfl⟩ A := by exact_mod_cast hpos
    omega

/-- An irreducible subrepresentation of a nonprecedence-ordered product of segment socles
is a Zelevinsky socle of its multisegment. -/
theorem isZelevinskySocle_of_isZelevinskySubrepresentation {n : ℕ}
    {d : T.SegmentProductDatum.{max uF uV, uF} n}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsZelevinskySubrepresentation π) : d.multisegment.IsZelevinskySocle π := by
  let := T.topology
  obtain ⟨ho, hs, hπ, j, hj⟩ := h
  obtain ⟨S, -, -, hS⟩ := orderedMultisegmentSocleExistence.{uF, uV} F T n d ho hs
  obtain ⟨e⟩ := hS.nonempty_equiv_of_subrepresentation hπ j hj
  exact ⟨d, rfl, ho, hs, hS.of_targetEquiv e.symm⟩


/-- **The shifted highest derivative of a unitarizable `⟨a⟩`** (Bernstein's Theorem 2.5(iii)
with the weak form of Zelevinsky's Theorem 8.1): it lives on `GL_M` with `M < N`, is
irreducible and unitarizable, `a⁻` has degree `M`, and for `M > 0` it is a Zelevinsky
socle of `ν^(1/2) a⁻`. -/
theorem exists_shiftedHighestDerivative_socle
    (hB3 : BernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T) {N : ℕ} (hN : 0 < N)
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier))
    (hirr : letI := T.topology; Representation.IsIrreducible π.representation)
    (hu : letI := T.topology; IsUnitarizable π.representation)
    {a : T.Multisegment.{max uF uV, uF}} (ha : a.IsZelevinskySocle π) :
    letI := T.topology
    ∃ (M : ℕ) (π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear M F.Carrier)),
      M < N ∧ Representation.IsIrreducible π'.representation ∧
        IsUnitarizable π'.representation ∧ (Multisegment.dropLast a).degree = M ∧
        (0 < M → ((Multisegment.dropLast a).twist (1 / 2)).IsZelevinskySocle π') := by
  let := T.topology
  let ψ := ψ₀ F T
  obtain ⟨d, hd, hz⟩ := ha
  have hsub := hz.isZelevinskySubrepresentation
  obtain ⟨hk, d', π'', hd'm, hd'sub, hsq⟩ := highestDerivativeLabelStep F T ψ N hN d π hsub
  have hkpos : 0 < ∑ i, (d.segments i).rank := sum_rank_pos F T d hN
  obtain ⟨-, hs, hsoc⟩ := hz
  obtain ⟨-, j, hj, -⟩ := hsoc
  have hvan := (segmentSocleProductHighestDerivative.{uF, max uF uV} F T ψ N d hs
    (∑ i, (d.segments i).rank) hk rfl).1
  have higher : ∀ (j' : ℕ) (hj' : j' ≤ N), (∑ i, (d.segments i).rank) < j' →
      Subsingleton ((generalLinearDerivative T ψ N j' hj').obj π) := by
    intro j' hj' hkj
    have hinj := LevelCalculus.map_injective_of_exact
      (generalLinearDerivativeExactness.{uF, max uF uV} F T ψ N j' hj') (SmoothRep.ofHom j) hj
    have := hvan j' hj' hkj
    exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
  have hπ''irr : π''.IsIrreducible := hd'sub.2.2.1
  have hnt'' : Nontrivial π'' := SegmentHeadSupport.nontrivial_of_isIrreducible hπ''irr
  have hnz : Nontrivial ((generalLinearDerivative T ψ N _ hk).obj π) :=
    ExactFamilyLength.nontrivial_of_isSubquotient hsq
  let hdo : GeneralLinearHighestDerivativeOrderData T ψ π :=
    ⟨_, hk, hkpos, hnz, higher⟩
  obtain ⟨hirr', hu'⟩ := hB3 N hN ψ π hirr hu hdo
  have hDirr : ((generalLinearDerivative T ψ N _ hk).obj π).IsIrreducible :=
    (isIrreducible_twist_iff _ _).mp hirr'
  obtain ⟨e⟩ := nonempty_iso_of_isSubquotient F T hπ''irr hDirr hsq
  have hsocD : (Multisegment.dropLast a).IsZelevinskySocle
      ((generalLinearDerivative T ψ N _ hk).obj π) := by
    have h1 := isZelevinskySocle_of_isZelevinskySubrepresentation F T hd'sub
    rw [hd'm, hd] at h1
    exact Multisegment.IsZelevinskySocle.of_iso h1 e
  refine ⟨N - ∑ i, (d.segments i).rank, shiftedHighestDerivative F T ψ hdo,
    by omega, hirr', hu', ?_, fun hM => ?_⟩
  · obtain ⟨d'', hd'', -⟩ := hsocD
    rw [← hd'']
    exact degree_multisegment F T d''
  · exact ((multisegmentConstituentRealTwistCompatibility.{uF, max uF uV} F T _ hM
      (Multisegment.dropLast a) (1 / 2) _).1).mp hsocD

end Langlands.Classification.TadicBlockDerivative
