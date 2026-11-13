import Langlands.Representation.Classification.SpehUnitarizabilityReductionStatement
import Langlands.Representation.Classification.SpehLengthOneProof
import Langlands.Representation.Classification.SpehExistenceProof
import Langlands.Representation.Classification.SupercuspidalInductionTransports
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Classification.SpehHermitian

/-!
# Proof of Tadic's local reduction for Speh representations

Conditional on Tadic 1986, Proposition 2.9, Bernstein's Theorem 2.5(i) and the
weak form of 2.5(ii), and the three Speh inputs, every Speh representation
`u(delta, k)` is unitarizable. The argument is the induction on `k` of Tadic
1986, Lemma 6.2, as presented in Badulescu 2014, Theorem 1.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

namespace SpehUnitarityReduction

/-- Irreducibility is unchanged by an exact rank transport. -/
private theorem irreducible_cast {a b : ℕ} (h : a = b)
    (X : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    Representation.IsIrreducible
        (h ▸ X : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)).representation ↔
      Representation.IsIrreducible X.representation := by
  subst h
  rfl

/-- Unitarizability is unchanged by an exact rank transport. -/
private theorem unitarizable_cast {a b : ℕ} (h : a = b)
    (X : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    IsUnitarizable
        (h ▸ X : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)).representation ↔
      IsUnitarizable X.representation := by
  subst h
  rfl

/-- Irreducibility of `pi(sigma, alpha)` is unchanged by an exact rank transport
of `sigma`. -/
private theorem complementary_cast {a b : ℕ} (h : a = b) (ha : 0 < a) (hb : 0 < b)
    (X : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)) (α : ℝ) :
    letI := T.topology
    Representation.IsIrreducible (complementaryProduct F T hb
        (h ▸ X : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)) α).representation ↔
      Representation.IsIrreducible (complementaryProduct F T ha X α).representation := by
  subst h
  rfl

/-- Irreducibility of `pi(sigma, alpha)` on the whole interval `(-1/2, 1/2)`,
from irreducibility away from `alpha = 0` and Bernstein's theorem at `0`. -/
private theorem complementary_irreducible
    (h2 : BernsteinUnitaryProductIrreducibility.{uF, uV} F T)
    {n : ℕ} (hn : 0 < n)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hσi : letI := T.topology; Representation.IsIrreducible σ.representation)
    (hσu : letI := T.topology; IsUnitarizable σ.representation)
    (hne : letI := T.topology
      ∀ α ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), α ≠ 0 →
        Representation.IsIrreducible (complementaryProduct F T hn σ α).representation) :
    letI := T.topology
    ∀ α ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
      Representation.IsIrreducible (complementaryProduct F T hn σ α).representation := by
  let := T.topology
  intro α hα
  by_cases h0 : α = 0
  · subst h0
    let e := T.twistedProductInducedZeroIso (BlockShape.uniform 2 n hn) (fun _ => σ)
      (fun i => if (i : ℕ) = 0 then (0 : ℝ) else -0) (fun i => by split_ifs <;> simp)
    have hprod := (h2 (2 * n) (BlockShape.uniform 2 n hn) (fun _ => σ)
      (fun _ => ⟨hσi, hσu⟩)).1
    exact (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso e)).mpr hprod
  · exact hne α hα h0

/-- An irreducible quotient is an irreducible subquotient. -/
private theorem isSubquotient_of_isIrreducibleQuotient {n : ℕ}
    {A B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : letI := T.topology; IsIrreducibleQuotient A.representation B.representation) :
    letI := T.topology
    SmoothRep.IsSubquotient B A := by
  let := T.topology
  obtain ⟨-, q, hq⟩ := h
  exact SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom q, hq⟩

/-- Length one: `u(delta, 1)` is `delta`, which is unitarizable. -/
private theorem lengthOne (d : SpehDatum.{uF, uV} F T) (hd : d.IsDiscreteSeries)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (d.withLength 1 Nat.one_pos).degree F.Carrier))
    (hπ : (d.withLength 1 Nat.one_pos).IsSpeh π) :
    letI := T.topology
    IsUnitarizable π.representation := by
  let := T.topology
  have hdeg : (d.withLength 1 Nat.one_pos).degree = (d.withLength 1 Nat.one_pos).rank :=
    Nat.one_mul _
  obtain ⟨e⟩ := (spehLengthOneComparison F T (d.withLength 1 Nat.one_pos) hdeg π rfl hd).mp hπ
  have hδ : IsUnitarizable
      (hdeg ▸ π : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (d.withLength 1 Nat.one_pos).rank F.Carrier)).representation :=
    (isUnitarizable_iff_of_equiv (SmoothRep.equivOfIso e)).mpr hd.2.1
  exact (unitarizable_cast F T hdeg π).mp hδ

/-- The centered induction of length two is the end point
`nu^(1/2) delta × nu^(-1/2) delta` of the complementary series of `delta`. -/
private theorem centeredInduced_two (d : SpehDatum.{uF, uV} F T) (hm : 0 < 2) :
    (d.withLength 2 hm).centeredInduced =
      complementaryProduct F T d.rank_pos d.delta (1 / 2) := by
  have hexp : (d.withLength 2 hm).exponent =
      fun i : Fin 2 => if (i : ℕ) = 0 then (1 / 2 : ℝ) else -(1 / 2) := by
    funext i
    fin_cases i <;> simp [SpehDatum.exponent, SpehDatum.withLength] <;> norm_num
  show T.twistedProductInduced (BlockShape.uniform 2 d.rank d.rank_pos) (fun _ => d.delta)
      (d.withLength 2 hm).exponent =
    T.twistedProductInduced (BlockShape.uniform 2 d.rank d.rank_pos) (fun _ => d.delta)
      (fun i => if (i : ℕ) = 0 then (1 / 2 : ℝ) else -(1 / 2))
  rw [hexp]
  rfl

/-- The complementary input for a representative of `u(delta, 1)`. -/
private theorem step_h5 (h5 : SpehComplementaryIrreducibility.{uF, uV} F T)
    (d : SpehDatum.{uF, uV} F T) (hd : d.IsDiscreteSeries)
    (S : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (d.withLength 1 Nat.one_pos).degree F.Carrier))
    (hS : (d.withLength 1 Nat.one_pos).IsSpeh S)
    (α : ℝ) (hα : α ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) (h0 : α ≠ 0) :
    letI := T.topology
    Representation.IsIrreducible (complementaryProduct F T
      (Nat.mul_pos (d.withLength 1 Nat.one_pos).length_pos d.rank_pos) S α).representation :=
  h5 (d.withLength 1 Nat.one_pos) hd S hS α hα h0

/-- Exact rank transport of that representative from `GL_(1 * r)` to `GL_r`. -/
private theorem step_cast
    (d : SpehDatum.{uF, uV} F T)
    (S : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (d.withLength 1 Nat.one_pos).degree F.Carrier))
    (hdeg : (d.withLength 1 Nat.one_pos).degree = (d.withLength 1 Nat.one_pos).rank)
    (α : ℝ)
    (h : letI := T.topology
      Representation.IsIrreducible (complementaryProduct F T
        (Nat.mul_pos (d.withLength 1 Nat.one_pos).length_pos d.rank_pos) S α).representation) :
    letI := T.topology
    Representation.IsIrreducible (complementaryProduct F T (d.withLength 1 Nat.one_pos).rank_pos
      (hdeg ▸ S) α).representation :=
  (complementary_cast F T hdeg _ _ S α).mpr h

/-- An isomorphism of the transported representative with `delta` carries
irreducibility to `nu^alpha delta × nu^(-alpha) delta`. -/
private theorem step_iso
    (d : SpehDatum.{uF, uV} F T)
    (S : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (d.withLength 1 Nat.one_pos).degree F.Carrier))
    (hdeg : (d.withLength 1 Nat.one_pos).degree = (d.withLength 1 Nat.one_pos).rank)
    (e : (hdeg ▸ S) ≅ (d.withLength 1 Nat.one_pos).delta)
    (α : ℝ)
    (h : letI := T.topology
      Representation.IsIrreducible (complementaryProduct F T (d.withLength 1 Nat.one_pos).rank_pos
        (hdeg ▸ S) α).representation) :
    letI := T.topology
    Representation.IsIrreducible
      (complementaryProduct F T d.rank_pos d.delta α).representation := by
  let := T.topology
  let e2 : complementaryProduct F T (d.withLength 1 Nat.one_pos).rank_pos (hdeg ▸ S) α ≅
      complementaryProduct F T d.rank_pos d.delta α :=
    T.twistedProductInducedIso (BlockShape.uniform 2 d.rank d.rank_pos) (fun _ => e)
      (fun i => if (i : ℕ) = 0 then α else -α)
  exact (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso e2)).mp h

/-- Irreducibility of `nu^alpha delta × nu^(-alpha) delta` on `(-1/2, 1/2)`. -/
private theorem delta_complementary_irreducible
    (h2 : BernsteinUnitaryProductIrreducibility.{uF, uV} F T)
    (h5 : SpehComplementaryIrreducibility.{uF, uV} F T)
    (d : SpehDatum.{uF, uV} F T) (hd : d.IsDiscreteSeries) :
    letI := T.topology
    ∀ α ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
      Representation.IsIrreducible
        (complementaryProduct F T d.rank_pos d.delta α).representation := by
  let := T.topology
  refine complementary_irreducible F T h2 d.rank_pos d.delta hd.1 hd.2.1 ?_
  intro α hα h0
  have hdeg : (d.withLength 1 Nat.one_pos).degree = (d.withLength 1 Nat.one_pos).rank :=
    Nat.one_mul _
  obtain ⟨S, hS⟩ := spehExistenceUniqueness F T (d.withLength 1 Nat.one_pos) hd
  obtain ⟨e⟩ := (spehLengthOneComparison F T _ hdeg S rfl hd).mp hS
  exact step_iso F T d S hdeg e α (step_cast F T d S hdeg α (step_h5 F T h5 d hd S hS α hα h0))

end SpehUnitarityReduction

open SpehUnitarityReduction in
/-- Tadic's local induction (Tadic 1986, Lemma 6.2; Badulescu 2014,
Theorem 1): the published hypotheses imply that every Speh representation is
unitarizable. -/
theorem spehUnitarizabilityLocalReduction :
    SpehUnitarizabilityLocalReduction.{uF, uV} F T := by
  intro h1 h2 h3 hin
  obtain ⟨h5, h6a, h6b⟩ := hin
  let := T.topology
  intro d hd
  have key : ∀ (k : ℕ) (hk : 0 < k)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (d.withLength k hk).degree F.Carrier)),
      (d.withLength k hk).IsSpeh π → IsUnitarizable π.representation := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk π hπ
      match k, hk, π, hπ, ih with
      | 1, _, π, hπ, _ => exact lengthOne F T d hd π hπ
      | 2, hk, π, hπ, _ =>
        have hirr := delta_complementary_irreducible F T h2 h5 d hd
        have hend := (h1 d.rank d.rank_pos d.delta (1 / 2) hd.1 hd.2.1 (by norm_num)
          hirr).2
        have hsub : SmoothRep.IsSubquotient π (d.withLength 2 hk).centeredInduced :=
          isSubquotient_of_isIrreducibleQuotient F T hπ.2.1
        rw [centeredInduced_two F T d hk] at hsub
        exact hend π hπ.2.1.1 hsub
      | m + 3, hk, π, hπ, ih =>
        let e := d.withLength (m + 2) (by omega)
        have he : e.IsDiscreteSeries := hd
        have hk2 : 2 ≤ e.length := by show 2 ≤ m + 2; omega
        obtain ⟨S, hS⟩ := spehExistenceUniqueness F T e he
        obtain ⟨Sdown, hSdown⟩ := spehExistenceUniqueness F T
          (e.withLength (e.length - 1) (Nat.sub_pos_of_lt hk2)) he
        have hSi : Representation.IsIrreducible S.representation := hS.2.1.1
        have hSu : IsUnitarizable S.representation :=
          ih (m + 2) (by omega) (by omega) S hS
        -- irreducibility of the complementary series of `u(delta, m + 2)`
        have hne := h5 e he S hS
        have hirr := complementary_irreducible F T h2
          (Nat.mul_pos e.length_pos e.rank_pos) S hSi hSu hne
        have hend := (h1 e.degree (Nat.mul_pos e.length_pos e.rank_pos) S (1 / 2) hSi hSu
          (by norm_num) hirr).2
        -- the constituent `u(delta, m + 3) × u(delta, m + 1)`
        have hπ' : (e.withLength (e.length + 1) (Nat.succ_pos _)).IsSpeh π := hπ
        have hXi := h6a e hk2 he π Sdown hπ' hSdown
        have hXsub := h6b e hk2 he S π Sdown hS hπ' hSdown hXi
        have hdeg : (e.withLength (e.length + 1) (Nat.succ_pos _)).degree +
            (e.withLength (e.length - 1) (Nat.sub_pos_of_lt hk2)).degree = 2 * e.degree := by
          show (m + 2 + 1) * d.rank + (m + 2 - 1) * d.rank = 2 * ((m + 2) * d.rank)
          rw [show m + 2 - 1 = m + 1 by omega]
          ring
        have hXu := (unitarizable_cast F T hdeg _).mp
          (hend _ ((irreducible_cast F T hdeg _).mpr hXi) (hXsub hdeg))
        -- Bernstein's weak 2.5(ii) on the binary product
        have hfac := h3 _ (BlockShape.binary _ _
            (Nat.mul_pos (Nat.succ_pos e.length) e.rank_pos)
            (Nat.mul_pos (Nat.sub_pos_of_lt hk2) e.rank_pos))
          ((T.binaryPairFamilyFunctor
            (Nat.mul_pos (Nat.succ_pos e.length) e.rank_pos)
            (Nat.mul_pos (Nat.sub_pos_of_lt hk2) e.rank_pos)).obj (π, Sdown))
          (by
            intro i
            fin_cases i
            · exact ⟨hπ.2.1.1,
                SpehDatum.hasNonzeroInvariantSesquilinearForm_of_isSpeh F T _ π hπ'⟩
            · exact ⟨hSdown.2.1.1,
                SpehDatum.hasNonzeroInvariantSesquilinearForm_of_isSpeh F T _ Sdown hSdown⟩)
          hXi hXu
        exact hfac (0 : Fin 2)
  intro π hπ
  exact key d.length d.length_pos π hπ
