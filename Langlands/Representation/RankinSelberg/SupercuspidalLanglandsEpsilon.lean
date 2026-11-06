import Langlands.Representation.RankinSelberg.LanglandsFactorDescent
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.Group.GL.ReverseBlocks
import Langlands.Group.GL.RankReindex

/-!
# Langlands-data epsilon factors of supercuspidal pairs

By second adjointness, an irreducible supercuspidal quotient of `i(π_1, …, π_r)`
forces `r = 1`, and then the quotient is equivalent to the sole block. Hence the
epsilon factor defined through square-integrable Langlands data is the JPSS
epsilon factor on pairs of irreducible supercuspidal representations.
-/

noncomputable section

namespace Langlands

open GeneralLinear CategoryTheory

universe uF uV uW uV' uW'

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Essential square-integrability implies admissibility: undo the real-power
twist, whose kernel is open. -/
theorem IsEssentiallySquareIntegrable.isAdmissible {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    (h : T.IsEssentiallySquareIntegrable ρ) :
    letI := T.topology
    IsAdmissible ρ := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  obtain ⟨s, hs⟩ := h
  exact (isAdmissible_twist_iff (realPowerCharacter (T.determinantNorm n) (-s)) ρ
    (isOpen_ker_realPowerCharacter _ (T.isOpen_ker_determinantNorm n) (-s))).mp
      hs.isAdmissible

namespace SquareIntegrableLanglandsDatum

variable {r : ℕ} (d : SquareIntegrableLanglandsDatum.{uV, uF} T (r + 1))

/-- For a datum with one block, that block as a representation of the ambient
`GL_{r+1}`, transported along the entry-preserving reindex by the rank equality. -/
def singleBlockRepresentation (h : d.shape.length = 1) :
    letI := T.topology
    Representation ℂ (GeneralLinear (r + 1) F.Carrier) (d.blocks (d.shape.singleBlockIndex h)) :=
  letI := T.topology
  (d.blocks (d.shape.singleBlockIndex h)).representation.comp
    (reindex (R := F.Carrier) (finCongr (d.shape.singleBlock_size h
      (d.shape.singleBlockIndex h)))).symm.toMonoidHom

/-- An irreducible supercuspidal quotient of `i(π_1, …, π_r)` forces `r = 1`.
Otherwise the parabolic is proper, the opposite Jacquet module of the quotient
vanishes, and second adjointness makes the quotient map zero. -/
theorem length_eq_one_of_isSupercuspidal
    {J : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier)}
    (hJ : letI := T.topology; IsSupercuspidal J.representation)
    (hd : d.IsLanglandsQuotient J) : d.shape.length = 1 := by
  let := T.topology
  by_contra hlen
  have hB : d.shape.parabolic F.Carrier ≠ ⊤ := by
    intro htop
    have hs := CuspidalSupport.block_indices_subsingleton_of_parabolic_eq_top d.shape htop
    have hle : d.shape.length ≤ 1 := by
      simpa only [Fintype.card_fin] using Fintype.card_le_one_iff_subsingleton.mpr hs
    have h0 : d.shape.length = 0 := by omega
    have hsum := d.shape.sum_eq
    have : IsEmpty (Fin d.shape.length) := by rw [h0]; infer_instance
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    omega
  let σ : Rep.{uV} ℂ (d.shape.Levi F.Carrier) :=
    Rep.of (d.shape.blockTensor fun i => (d.blocks i).representation)
  have hσ : IsAdmissible σ.ρ :=
    FiniteTensor.isAdmissible_external _
      fun i => (d.essentiallySquareIntegrable i).isAdmissible
  let π : Rep.{max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier) := Rep.of J.representation
  have hπ : IsAdmissible π.ρ := hJ.1
  obtain ⟨E, -⟩ := Parabolic.normalizedSecondAdjointness.{uF, uV, max uF uV}.1 p F T
    (r + 1) (Nat.succ_pos r) d.shape
  obtain ⟨hJirr, q, hq⟩ := hd
  have hvan : Subsingleton (Jacquet.Coinvariants J.representation
      (d.shape.oppositeUnipotentSubgroup F.Carrier)) := by
    have h := hJ.2 d.shape.reverse ((d.shape.reverse_parabolic_ne_top_iff F.Carrier).mpr hB)
      (d.shape.reverseMatrix F.Carrier)
    change Subsingleton (Jacquet.Coinvariants J.representation
      ((d.shape.reverse.unipotentSubgroup F.Carrier).map
        (MulAut.conj (d.shape.reverseMatrix F.Carrier)).toMonoidHom)) at h
    rwa [d.shape.reverse_unipotentSubgroup_map_conj F.Carrier] at h
  let q' : (T.normalizedParabolicInduced d.shape σ.ρ).IntertwiningMap π.ρ := q
  have hzero : E σ π hσ hπ q' = 0 := by
    let : Subsingleton (CuspidalJacquetMultiplicity.oppositeJacquet T d.shape π) := hvan
    ext v
    exact Subsingleton.elim _ _
  have hq0 : q' = 0 := (E σ π hσ hπ).injective (hzero.trans (map_zero _).symm)
  obtain ⟨a, b, hab⟩ :=
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible _ hJirr
  obtain ⟨x, rfl⟩ := hq a
  obtain ⟨y, rfl⟩ := hq b
  have hx : q' x = 0 := by rw [hq0]; rfl
  have hy : q' y = 0 := by rw [hq0]; rfl
  exact hab (hx.trans hy.symm)

/-- The sole block of a supercuspidal Langlands quotient, transported to the
ambient rank, is equivalent to the quotient. -/
theorem nonempty_equiv_of_isSupercuspidal
    {J : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier)}
    (hJ : letI := T.topology; IsSupercuspidal J.representation)
    (hd : d.IsLanglandsQuotient J) :
    letI := T.topology
    ∃ h : d.shape.length = 1,
      Nonempty (Representation.Equiv (d.singleBlockRepresentation h) J.representation) := by
  let := T.topology
  have h1 := d.length_eq_one_of_isSupercuspidal hJ hd
  refine ⟨h1, ?_⟩
  obtain ⟨hJirr, q, hq⟩ := hd
  let i := d.shape.singleBlockIndex h1
  let φ := T.singleBlockNormalizedProductEquiv d.shape h1
    (fun i => (d.blocks i).representation) (fun i => (d.blocks i).isSmooth) i
  let q' : (T.normalizedProductInduced d.shape
      (fun i => (d.blocks i).representation)).IntertwiningMap J.representation := q
  let f := q'.comp φ.symm.toIntertwiningMap
  have hirr : Representation.IsIrreducible ((d.blocks i).representation.comp
      (reindex (R := F.Carrier) (finCongr (d.shape.singleBlock_size h1 i))).symm.toMonoidHom) :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff _ _).mpr (d.irreducible i)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨φ x, congrArg q' (φ.symm_apply_apply x)⟩
  have hinj : Function.Injective f := by
    have := hirr
    rcases Representation.IsIrreducible.injective_or_eq_zero f with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ :=
        CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible _ hJirr
      obtain ⟨x, rfl⟩ := hf a
      obtain ⟨y, rfl⟩ := hf b
      apply hab
      rw [h]
      rfl
  exact ⟨Representation.IntertwiningMap.ofBijective f ⟨hinj, hf⟩⟩

end SquareIntegrableLanglandsDatum

end PadicField.TopologicalData

namespace RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}

/-- The natural-rank epsilon relation transports along a rank equality realized
by the entry-preserving reindex, followed by representation equivalences. -/
theorem isPadicRankEpsilonFactor_reindex_iff {k m t s : ℕ} (hk : k = m) (ht : t = s)
    {V : Type uV} {W : Type uW} {V' : Type uV'} {W' : Type uW'}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {π : Representation ℂ (GeneralLinear k F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear t F.Carrier) W}
    {π' : Representation ℂ (GeneralLinear m F.Carrier) V'}
    {σ' : Representation ℂ (GeneralLinear s F.Carrier) W'}
    (φ : Representation.Equiv
      (π.comp (reindex (R := F.Carrier) (finCongr hk)).symm.toMonoidHom) π')
    (φ' : Representation.Equiv
      (σ.comp (reindex (R := F.Carrier) (finCongr ht)).symm.toMonoidHom) σ')
    {e : ℂˣ × ℤ} :
    IsPadicRankEpsilonFactor F ψ ν π σ e ↔ IsPadicRankEpsilonFactor F ψ ν π' σ' e := by
  subst hk ht
  have e₀ : π.Equiv
      (π.comp (reindex (R := F.Carrier) (finCongr (rfl : k = k))).symm.toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun g => by
      change π g = π ((reindex (R := F.Carrier) (finCongr rfl)).symm g)
      rw [reindex_finCongr_rfl]
      rfl
  have e₁ : σ.Equiv
      (σ.comp (reindex (R := F.Carrier) (finCongr (rfl : t = t))).symm.toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ W) fun g => by
      change σ g = σ ((reindex (R := F.Carrier) (finCongr rfl)).symm g)
      rw [reindex_finCongr_rfl]
      rfl
  exact IsPadicRankEpsilonFactor.congr_equiv (e₀.trans φ) (e₁.trans φ')

/-- On pairs of supercuspidal representations, the epsilon factor defined through
square-integrable Langlands data is the JPSS epsilon factor of the pair. -/
theorem IsLanglandsPairEpsilonFactor.isPadicSymmetricEpsilonFactor_of_isSupercuspidal
    {r t : ℕ}
    {π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier)}
    {σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear (t + 1) F.Carrier)}
    (hπ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal π.representation)
    (hσ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal σ.representation)
    {e : ℂˣ × ℤ} (he : IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e) :
    letI := F.canonicalTopologicalData.topology
    IsPadicSymmetricEpsilonFactor F ψ ν π.representation σ.representation e := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨⟨d, hd⟩, ⟨d', hd'⟩, hall⟩ := he
  obtain ⟨b, hb, rfl⟩ := hall d d' hd hd'
  obtain ⟨h1, ⟨φ⟩⟩ := d.nonempty_equiv_of_isSupercuspidal hπ hd
  obtain ⟨h1', ⟨φ'⟩⟩ := d'.nonempty_equiv_of_isSupercuspidal hσ hd'
  let i := d.shape.singleBlockIndex h1
  let j := d'.shape.singleBlockIndex h1'
  have hi : ∀ i' : Fin d.shape.length, i' ≠ i → False :=
    fun i' hi' => hi' (d.shape.eq_singleBlockIndex h1 i')
  have hj : ∀ j' : Fin d'.shape.length, j' ≠ j → False :=
    fun j' hj' => hj' (d'.shape.eq_singleBlockIndex h1' j')
  have hprod : epsilonFactorProduct b = b i j := by
    change (∏ i', ∏ j', (b i' j').1, ∑ i', ∑ j', (b i' j').2) = b i j
    rw [Fintype.prod_eq_single i (fun i' hi' => (hi i' hi').elim),
      Fintype.prod_eq_single j (fun j' hj' => (hj j' hj').elim),
      Fintype.sum_eq_single i (fun i' hi' => (hi i' hi').elim),
      Fintype.sum_eq_single j (fun j' hj' => (hj j' hj').elim)]
  rw [hprod, ← isPadicRankEpsilonFactor_succ]
  exact (isPadicRankEpsilonFactor_reindex_iff (d.shape.singleBlock_size h1 i)
    (d'.shape.singleBlock_size h1' j) φ φ').mp (hb i j)

end RankinSelberg

end Langlands
