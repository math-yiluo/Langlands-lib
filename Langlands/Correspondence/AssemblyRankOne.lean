import Langlands.Correspondence.AssemblyRelation
import Langlands.Correspondence.RankOneComparison
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Weil.Local.ContinuityProof

/-!
# Rank-one compatibility of the Henniart assembly

If `c` is an assembly of `c0` and `c0` is compatible with rank-one characters, then
so is `c`. A rank-one parameter has a single block of length one, so its assembled
class is the Langlands head of a one-segment multisegment of length one, which is
the supercuspidal class itself.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uK uG uV uW uι uF uP uA

namespace Classification

variable {G : Type uG} [Group G] {V W : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- An irreducible head of an irreducible representation is equivalent to it. -/
theorem IsIrreducibleHead.nonempty_equiv_of_isIrreducible {ρ : Representation ℂ G V}
    {π : Representation ℂ G W} (h : IsIrreducibleHead ρ π)
    (hρ : Representation.IsIrreducible ρ) : Nonempty (ρ.Equiv π) := by
  obtain ⟨hπ, q, hq, -⟩ := h
  have := hρ
  have := hπ
  have : Nontrivial π.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  have hq0 : q ≠ 0 := by
    intro h0
    obtain ⟨w, hw⟩ := exists_ne (0 : π.asModule)
    obtain ⟨v, hv⟩ := hq w
    apply hw
    rw [← hv, h0]
    rfl
  have hinj := (Representation.IsIrreducible.injective_or_eq_zero q).resolve_right hq0
  exact ⟨q.ofBijective ⟨hinj, hq⟩⟩

end Classification

/-- Precomposition of an equivalence with a group homomorphism. -/
def Representation.Equiv.compHom {G : Type uG} {H : Type uW} [Group G] [Group H]
    {V : Type uV} {W : Type uι} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : H →* G)
    (e : ρ.Equiv σ) : Representation.Equiv (ρ.comp φ) (σ.comp φ) :=
  Representation.Equiv.mk e.toLinearEquiv fun h => e.isIntertwining' (φ h)

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Rank transport respects equivalences of representations. -/
def castRankCongrEquiv {r s : ℕ} (h : r = s)
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)}
    {B : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear r F.Carrier)}
    (e : letI := T.topology; A.representation.Equiv B.representation) :
    letI := T.topology
    (T.castRank h A).representation.Equiv (T.castRank h B).representation := by
  subst h
  exact e

/-- Reindexing a rank-transported representation is a single rank transport. -/
def castRankCompEquiv {r s t : ℕ} (h₁ : r = s) (h₂ : s = t)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    Representation.Equiv ((T.castRank h₁ A).representation.comp
      (GeneralLinear.reindex (R := F.Carrier) (finCongr h₂)).symm.toMonoidHom)
      (T.castRank (h₁.trans h₂) A).representation := by
  subst h₁
  subst h₂
  exact T.castRankEquiv rfl A

/-- The Langlands head of the one-segment multisegment `{[ρ]}` is equivalent to every
supercuspidal representative of `ρ`, transported to the ambient rank. -/
theorem singletonSegment_isLanglandsHead_equiv {n : ℕ} (ρ : CuspidalDatum.{uV, uF} T)
    {J : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hJ : ({T.singletonSegment ρ} : Multisegment.{uV, uF} T).IsLanglandsHead J)
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) :
    letI := T.topology
    ∃ h : ρ.rank = n,
      Nonempty (J.representation.Equiv (T.castRank h A.obj).representation) := by
  let := T.topology
  obtain ⟨⟨len, segs, hsum, blocks⟩, hd, -, hheads, hhead⟩ := hJ
  have hl : List.ofFn segs = [T.singletonSegment ρ] := Multiset.coe_eq_singleton.mp hd
  have hlen : len = 1 := by simpa using congrArg List.length hl
  subst hlen
  have hsegs : segs = fun _ => T.singletonSegment ρ := by
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simpa [List.ofFn_succ] using hl
  subst hsegs
  obtain ⟨A₁, hA₁, hhead₁⟩ := hheads 0
  -- The segment level: the head of `i(A₁)` is `A₁`.
  let e₁ := T.singletonSegmentInducedEquiv ρ.rank_pos A₁.obj
  have hsrc₁ : Representation.IsIrreducible
      (T.segmentInduced A₁.obj 1 ρ.rank_pos).representation :=
    (Weil.IsomorphismInvariance.irreducible_iff e₁).mpr
      (T.isIrreducible_castRank _ A₁.obj A₁.property.1)
  obtain ⟨f₁⟩ := Classification.IsIrreducibleHead.nonempty_equiv_of_isIrreducible
    hhead₁ hsrc₁
  let e₂ := f₁.symm.trans e₁
  -- The product level: a one-block product is its factor.
  let B := T.segmentShape (fun _ : Fin 1 => T.singletonSegment ρ) hsum
  have hB : B.length = 1 := rfl
  let i₀ : Fin B.length := ⟨0, Nat.one_pos⟩
  have hsize : 1 * ρ.rank = n := B.singleBlock_size hB i₀
  let e₃ := T.singleBlockNormalizedProductEquiv B hB (fun i => (blocks i).representation)
    (fun i => (blocks i).isSmooth) i₀
  let e₄ := Representation.Equiv.compHom
    (GeneralLinear.reindex (R := F.Carrier) (finCongr hsize)).symm.toMonoidHom e₂
  let e₅ := T.castRankCompEquiv (Nat.one_mul ρ.rank).symm hsize A₁.obj
  let e₆ := (e₃.trans e₄).trans e₅
  have hsrc₂ : Representation.IsIrreducible
      (SegmentProductDatum.mk 1 (fun _ => T.singletonSegment ρ) hsum blocks).induced.representation :=
    (Weil.IsomorphismInvariance.irreducible_iff e₆).mpr
      (T.isIrreducible_castRank _ A₁.obj A₁.property.1)
  obtain ⟨f₂⟩ := Classification.IsIrreducibleHead.nonempty_equiv_of_isIrreducible
    hhead hsrc₂
  -- Two representatives of `ρ` are isomorphic.
  obtain ⟨i₁⟩ := (GeneralLinear.SupercuspidalRep.isoClass_eq_iff A₁ A).mp (hA₁.trans hA.symm)
  let e₇ := T.castRankCongrEquiv ((Nat.one_mul ρ.rank).symm.trans hsize)
    (SmoothRep.equivOfIso ((GeneralLinear.supercuspidalProperty (F := F.Carrier)
      (n := ρ.rank)).ι.mapIso i₁))
  exact ⟨_, ⟨f₂.symm.trans (e₆.trans e₇)⟩⟩

end PadicField.TopologicalData

namespace WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- A block of length one is its Weil factor. -/
def blockOneRepresentationEquiv (ν : G →* Kˣ) (B : FiniteRepresentation.{uK, uG, uV} K G) :
    (block ν B 1).representation.Equiv B.representation where
  toLinearEquiv := (TensorProduct.congr (LinearEquiv.refl K B)
    (LinearEquiv.funUnique (Fin 1) K K)).trans (TensorProduct.rid K B)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro (v : B) (w : Fin 1 → K)
    change (Special.action ν 1 g w 0) • B.representation g v = B.representation g (w 0 • v)
    rw [map_smul, Special.action_apply, Fin.val_zero, pow_zero, one_mul]

/-- A block whose length is one is its Weil factor. -/
def blockRepresentationEquivOfLengthOne (ν : G →* Kˣ)
    (B : FiniteRepresentation.{uK, uG, uV} K G) {k : ℕ} (hk : k = 1) :
    (block ν B k).representation.Equiv B.representation := by
  subst hk
  exact blockOneRepresentationEquiv ν B

/-- A direct sum over a one-element index type is its unique summand. -/
def directSumUniqueRepresentationEquiv {ν : G →* Kˣ} {ι : Type uι} [Fintype ι] [Unique ι]
    (A : ι → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    (directSum A).representation.Equiv (A default).representation where
  toLinearEquiv := (DirectSum.linearEquivFunOnFintype K ι fun i => A i).trans
    (LinearEquiv.piUnique K fun i => A i)
  isIntertwining' g := by
    ext x
    rfl

end WeilDeligneRepresentation

namespace Correspondence

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rankOneFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance rankOneGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- Every endomorphism of a line is semisimple. -/
theorem isSemisimple_of_finrank_eq_one {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (h : Module.finrank ℂ V = 1) (f : Module.End ℂ V) : f.IsSemisimple := by
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h f
  rw [hc]
  exact Module.End.IsSemisimple_smul c Module.End.isSemisimple_id

/-- A continuous rank-one representation with zero monodromy is a Frobenius-semisimple
local parameter. -/
theorem isLocalFrobeniusSemisimpleParameter_zeroMonodromy
    (A : Weil.Local.LocalWeilRepresentation.{uF, uP} F) (hc : A.IsContinuous)
    (hr : A.rank = 1) :
    Weil.Local.IsLocalFrobeniusSemisimpleParameter F
      (WeilDeligneRepresentation.zeroMonodromy
        (Weil.Local.localNormCharacter F).toMonoidHom A) :=
  ⟨((Weil.Local.localWeilContinuity F A).2.2.1).mp hc,
    fun g _ => isSemisimple_of_finrank_eq_one hr (A.representation g)⟩

/-- The zero-monodromy parameter class of a continuous rank-one representation. -/
def rankOneZeroMonodromyClass (A : Weil.Local.LocalWeilRepresentation.{uF, uP} F)
    (hc : A.IsContinuous) (hr : A.rank = 1) : WeilDeligneClass.{uF, uP} F 1 :=
  ⟨Quotient.mk _ ⟨WeilDeligneRepresentation.zeroMonodromy
      (Weil.Local.localNormCharacter F).toMonoidHom A,
    isLocalFrobeniusSemisimpleParameter_zeroMonodromy F A hc hr⟩, hr⟩

theorem parameterForget_rankOneZeroMonodromyClass
    (A : Weil.Local.LocalWeilRepresentation.{uF, uP} F) (hc : A.IsContinuous)
    (hr : A.rank = 1) :
    parameterForget F (rankOneZeroMonodromyClass F A hc hr) =
      WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy
        (Weil.Local.localNormCharacter F).toMonoidHom A) :=
  rfl

/-- Zero monodromy turns a representation equivalence into a pair equivalence. -/
def zeroMonodromyEquiv {A : FiniteRepresentation.{0, uF, uV} ℂ (Weil.Local.localWeilGroup F)}
    {B : FiniteRepresentation.{0, uF, uW} ℂ (Weil.Local.localWeilGroup F)}
    (e : A.representation.Equiv B.representation) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.zeroMonodromy (Weil.Local.localNormCharacter F).toMonoidHom A)
      (WeilDeligneRepresentation.zeroMonodromy
        (Weil.Local.localNormCharacter F).toMonoidHom B) where
  representationEquiv := e
  comm_monodromy := by
    change e.toLinearMap ∘ₗ (0 : Module.End ℂ A) = (0 : Module.End ℂ B) ∘ₗ e.toLinearMap
    simp

/-- `∑ (d i + 1)(m i + 1) = 1` forces one block with `d = m = 0`. -/
theorem blockShape_eq_of_sum_eq_one {r : ℕ} (d m : Fin r → ℕ)
    (h : ∑ i, (d i + 1) * (m i + 1) = 1) : r = 1 ∧ ∀ i, d i = 0 ∧ m i = 0 := by
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin r)), 1 ≤ (d i + 1) * (m i + 1) :=
    fun i _ => Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero _)
      (Nat.succ_ne_zero _))
  have hcard := Finset.card_nsmul_le_sum Finset.univ (fun i => (d i + 1) * (m i + 1)) 1 hle
  rw [h, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hcard
  have hr : r ≠ 0 := by
    rintro rfl
    simp at h
  obtain rfl : r = 1 := by omega
  refine ⟨rfl, fun i => ?_⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [Fin.sum_univ_one] at h
  have hd : d 0 + 1 ≤ 1 :=
    calc d 0 + 1 = (d 0 + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (d 0 + 1) * (m 0 + 1) := Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))
      _ = 1 := h
  have hm : m 0 + 1 ≤ 1 :=
    calc m 0 + 1 = 1 * (m 0 + 1) := (Nat.one_mul _).symm
      _ ≤ (d 0 + 1) * (m 0 + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le _))
      _ = 1 := h
  omega

/-- A block sum in rank one has a single block, of Weil dimension one and length one. -/
theorem isBlockSum_rankOne {r : ℕ} {d m : Fin r → ℕ}
    {σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat}
    {D : WeilDeligneClass.{uF, uP} F 1} (h : IsBlockSum F σ m D) :
    r = 1 ∧ ∀ i, d i = 0 ∧ m i = 0 := by
  obtain ⟨B, A, hB, hA, ⟨e⟩⟩ := h
  have hrankB : ∀ i, (B i).rank = d i + 1 := by
    intro i
    have h₁ := congrArg FiniteRepresentation.classRank (hB i)
    rw [FiniteRepresentation.classRank_classOf] at h₁
    rw [h₁]
    exact (σ i).property
  have hrankA : A.rank = 1 := by
    have h₁ := congrArg WeilDeligneRepresentation.classRank hA
    exact h₁.trans D.property
  have hsum := e.representationEquiv.toLinearEquiv.finrank_eq
  change (WeilDeligneRepresentation.directSum _).rank = A.rank at hsum
  rw [WeilDeligneRepresentation.rank_directSum, hrankA] at hsum
  simp only [WeilDeligneRepresentation.rank_block, hrankB] at hsum
  exact blockShape_eq_of_sum_eq_one d m hsum

/-- In a one-block, length-one block sum of a zero-monodromy class, the Weil factor is
the class of the zero-monodromy representative. -/
theorem weilClassForget_eq_of_isBlockSum {d m : Fin 1 → ℕ}
    {σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat} (hm : m 0 = 0)
    {D : WeilDeligneClass.{uF, uP} F 1} (h : IsBlockSum F σ m D)
    (A₀ : Weil.Local.LocalWeilRepresentation.{uF, uP} F)
    (hA₀ : WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy
      (Weil.Local.localNormCharacter F).toMonoidHom A₀) = parameterForget F D) :
    weilClassForget F (σ 0) = FiniteRepresentation.classOf A₀ := by
  obtain ⟨B, A, hB, hA, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := (WeilDeligneRepresentation.classOf_eq_iff _ _).mp (hA.trans hA₀.symm)
  rw [← hB 0, FiniteRepresentation.classOf_eq_iff]
  let ν := (Weil.Local.localNormCharacter F).toMonoidHom
  let e₁ := WeilDeligneRepresentation.blockRepresentationEquivOfLengthOne ν (B 0)
    (k := m 0 + 1) (by rw [hm])
  let e₂ := WeilDeligneRepresentation.directSumUniqueRepresentationEquiv
    (fun i => WeilDeligneRepresentation.block ν (B i) (m i + 1))
  exact ⟨(e₁.symm.trans e₂.symm).trans
    (e.representationEquiv.trans e'.representationEquiv)⟩

/-- A supercuspidal representative and an automorphic representative of the same
class are equivalent. -/
theorem nonempty_equiv_of_supercuspidalToAutomorphic {n : ℕ+}
    (S : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := n))
    (A : AutomorphicObject.{uF, uA} F n)
    (h : automorphicClassOf F A = supercuspidalToAutomorphic F S.isoClass) :
    Nonempty (S.obj.representation.Equiv A.obj.representation) :=
  (automorphicClassOf_eq_iff F S.toIrreducibleAdmissible A).mp h.symm

/-- The multisegment of a single length-one block is the singleton segment. -/
theorem multisegmentOf_rankOne (c0 : SupercuspidalMap.{uF, uP, uA} F)
    (σ : IrreducibleWeilClass.{uF, uP} F 1) :
    multisegmentOf F c0 (d := fun _ : Fin 1 => 0) (fun _ => σ) (fun _ => 0) =
      {F.canonicalTopologicalData.singletonSegment (cuspidalDatumOf F c0 (d := 0) σ)} := by
  unfold multisegmentOf
  rw [List.ofFn_succ, List.ofFn_zero]
  rfl

/-- The assembly of a supercuspidal map compatible with rank-one characters is
compatible with rank-one characters. -/
theorem rankOneCompatibility_of_assembly {c0 : SupercuspidalMap.{uF, uP, uA} F}
    {c : FullMap.{uF, uP, uA} F} {e : ReciprocityCandidate F}
    (hc : IsAssemblyOf F c0 c) (h0 : SupercuspidalRankOneCompatibility F e c0) :
    RankOneCompatibility F e c := by
  intro χ
  obtain ⟨σ, ⟨Aσ, hAσ, ⟨eσ⟩⟩, A', hA', ⟨eA'⟩⟩ := h0 χ
  obtain ⟨x, hA₀⟩ := Quotient.exists_rep σ.val
  obtain ⟨A₀, hc₀, hi₀⟩ := x
  have hcls : weilClassForget F σ = FiniteRepresentation.classOf A₀ := by
    unfold weilClassForget
    rw [← hA₀]
    rfl
  have hr : A₀.rank = 1 := by
    have h₁ := σ.property
    unfold weilClassForget at hcls
    rw [hcls] at h₁
    exact h₁
  obtain ⟨f⟩ := (FiniteRepresentation.classOf_eq_iff _ _).mp (hAσ.trans hcls)
  let D := rankOneZeroMonodromyClass F A₀ hc₀ hr
  refine ⟨D, ⟨_, rfl, ⟨zeroMonodromyEquiv F (eσ.trans f)⟩⟩, ?_⟩
  obtain ⟨r, d, m, σ', hB, hH⟩ := hc 1 D
  obtain ⟨rfl, hdm⟩ := isBlockSum_rankOne F hB
  have hd : d = fun _ => 0 := funext fun i => (hdm i).1
  have hm : m = fun _ => 0 := funext fun i => (hdm i).2
  subst hd hm
  have hσ : weilClassForget F (σ' 0) = weilClassForget F σ :=
    (weilClassForget_eq_of_isBlockSum F rfl hB A₀ rfl).trans hcls.symm
  have hσ' : σ' = fun _ => σ := by
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact weilClassForget_injective F hσ
  subst hσ'
  obtain ⟨Ah, J, hAh, hJ, ⟨eJ⟩⟩ := hH
  rw [multisegmentOf_rankOne] at hJ
  obtain ⟨S, hS⟩ : ∃ S : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := 1),
      S.isoClass = c0 1 σ := Quotient.exists_rep _
  obtain ⟨h₁, ⟨eJS⟩⟩ := F.canonicalTopologicalData.singletonSegment_isLanglandsHead_equiv
    (cuspidalDatumOf F c0 (d := 0) σ) hJ S hS
  obtain ⟨eS⟩ := nonempty_equiv_of_supercuspidalToAutomorphic F (n := 1) S A' (hS ▸ hA')
  exact ⟨Ah, hAh, ⟨eA'.trans (eS.symm.trans (eJS.symm.trans eJ))⟩⟩

end Correspondence

end Langlands
