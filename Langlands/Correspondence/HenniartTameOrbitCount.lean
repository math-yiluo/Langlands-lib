import Langlands.Representation.IrreducibleLine
import Langlands.Correspondence.HenniartWildInertia
import Langlands.Correspondence.HenniartTameTypes
import Langlands.Correspondence.HenniartWeilRankOneCountProof

/-!
# Wild inertia orbits and the orbit formula

Wild classes of the Weil group are compared with wild classes of its inertia subgroup, the
types over a Frobenius-stable orbit of wild classes are counted, and the orbit formula
`WeilTameOrbitFormulaStatement` is derived from the Frobenius parametrization of tame fields.
-/

noncomputable section

namespace Langlands.Henniart.TameOrbit

open Weil.Local FiniteRepresentation Clifford WildInertia
open VirtualRepresentation.LocalWeil.Ramification

universe uG uK uW

section Transport

variable {N N' : Type uG} [Group N] [TopologicalSpace N] [Group N'] [TopologicalSpace N']

/-- Pull back an open-kernel irreducible object along a continuous isomorphism. -/
def objMap (e : N ≃ₜ* N')
    (A : {A : FiniteRepresentation.{0, uG, uW} ℂ N' // OpenKernelIrreducibleProperty N' A}) :
    {A : FiniteRepresentation.{0, uG, uW} ℂ N // OpenKernelIrreducibleProperty N A} :=
  ⟨restrict e.toMulEquiv.toMonoidHom A.1, by
    have := A.2.1
    exact Langlands.CuspidalSupport.isIrreducible_comp_of_surjective A.1.representation _
      e.surjective, by
    change IsOpen ((e.toMulEquiv.toMonoidHom : N → N') ⁻¹' (A.1.representation.ker : Set N'))
    exact A.2.2.preimage e.continuous⟩

/-- Pull back open-kernel irreducible classes along a continuous isomorphism. -/
def classMap (e : N ≃ₜ* N') :
    OpenKernelIrreducibleClasses.{uG, uW} N' → OpenKernelIrreducibleClasses.{uG, uW} N :=
  Quotient.map (objMap e) fun _ _ ⟨f⟩ => ⟨restrictEquiv _ f⟩

/-- The pullback of a class is the class of the pullback. -/
theorem classMap_mk (e : N ≃ₜ* N')
    (A : {A : FiniteRepresentation.{0, uG, uW} ℂ N' // OpenKernelIrreducibleProperty N' A}) :
    classMap e (Quotient.mk _ A) = Quotient.mk _ (objMap e A) := rfl

/-- Pulling back along `e` and then along `e⁻¹` is the identity. -/
theorem classMap_symm_classMap (e : N ≃ₜ* N') (c : OpenKernelIrreducibleClasses.{uG, uW} N') :
    classMap e.symm (classMap e c) = c := by
  induction c using Quotient.inductionOn with
  | h A =>
    apply Quotient.sound
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => ?_⟩
    change A.1.representation (e (e.symm n)) = A.1.representation n
    rw [ContinuousMulEquiv.apply_symm_apply]

/-- Pulling back along `e⁻¹` and then along `e` is the identity. -/
theorem classMap_classMap_symm (e : N ≃ₜ* N') (c : OpenKernelIrreducibleClasses.{uG, uW} N) :
    classMap e (classMap e.symm c) = c := by
  induction c using Quotient.inductionOn with
  | h A =>
    apply Quotient.sound
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => ?_⟩
    change A.1.representation (e.symm (e n)) = A.1.representation n
    rw [ContinuousMulEquiv.symm_apply_apply]

/-- Pullback preserves the rank. -/
theorem rank_classMap (e : N ≃ₜ* N') (c : OpenKernelIrreducibleClasses.{uG, uW} N') :
    openKernelIrreducibleRank N (classMap e c) = openKernelIrreducibleRank N' c := by
  induction c using Quotient.inductionOn with
  | h A => rfl

end Transport

section Wild

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- Inertia of the Weil group is nonarchimedean. -/
instance nonarchimedean_localInertia : NonarchimedeanGroup (localInertia K) :=
  localInertia_nonarchimedean K

/-- Wild inertia is normal in inertia. -/
instance wildIn_normal : (wildIn K).Normal :=
  (weilWildInertia_normal K).subgroupOf _

/-- Wild classes of inertia regarded as wild classes of the Weil group. -/
abbrev toW : OpenKernelIrreducibleClasses.{uK, uW} (wildIn K) → WildClasses.{uK, uW} K :=
  classMap (wildEquiv K).symm

/-- Wild classes of the Weil group regarded as wild classes of inertia. -/
abbrev ofW : WildClasses.{uK, uW} K → OpenKernelIrreducibleClasses.{uK, uW} (wildIn K) :=
  classMap (wildEquiv K)

/-- The two transports are inverse. -/
theorem toW_ofW (c : WildClasses.{uK, uW} K) : toW K (ofW K c) = c :=
  classMap_symm_classMap _ c

theorem ofW_toW (c : OpenKernelIrreducibleClasses.{uK, uW} (wildIn K)) : ofW K (toW K c) = c :=
  classMap_classMap_symm _ c

theorem toW_injective : Function.Injective (toW.{uK, uW} K) := fun c c' h => by
  rw [← ofW_toW K c, ← ofW_toW K c', h]

/-- Conjugation by an element of inertia commutes with the transport. -/
theorem toW_smul (g : localInertia K) (c : OpenKernelIrreducibleClasses.{uK, uW} (wildIn K)) :
    toW K (g • c) = (g : localWeilGroup K) • toW K c := by
  induction c using Quotient.inductionOn with
  | h A =>
    apply Quotient.sound
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => ?_⟩
    change A.1.representation (MulAut.conjNormal g⁻¹ ((wildEquiv K).symm n)) =
      A.1.representation ((wildEquiv K).symm (MulAut.conjNormal (g : localWeilGroup K)⁻¹ n))
    congr 1

/-- Pullback along conjugation by `φ` corresponds to the action of `φ⁻¹`. -/
theorem toW_wildPullback (φ : localWeilGroup K)
    (hN : ∀ x, x ∈ wildIn K ↔ TameTypes.frobConj K φ x ∈ wildIn K)
    (c : OpenKernelIrreducibleClasses.{uK, uW} (wildIn K)) :
    toW K (wildPullback (TameTypes.frobConj K φ) hN c) = φ⁻¹ • toW K c := by
  induction c using Quotient.inductionOn with
  | h A =>
    apply Quotient.sound
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => ?_⟩
    change A.1.representation (restrictAut (TameTypes.frobConj K φ).toMulEquiv hN
        ((wildEquiv K).symm n)) =
      A.1.representation ((wildEquiv K).symm (MulAut.conjNormal φ⁻¹⁻¹ n))
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    simp [restrictAut]
    rfl

/-- Triviality on an upper group, read on inertia. -/
theorem wildClassTrivialAt_toW (v : ℝ)
    (A : {A : FiniteRepresentation.{0, uK, uW} ℂ (wildIn K) //
      OpenKernelIrreducibleProperty (wildIn K) A}) :
    wildClassTrivialAt K v (toW K (Quotient.mk _ A)) ↔
      ∀ n : wildIn K, ((n : localInertia K) : localWeilGroup K) ∈ upperGroup K v →
        A.1.representation n = 1 := by
  change WildTrivialAt K v (objMap (wildEquiv K).symm A).1 ↔ _
  constructor
  · intro h n hn
    have h1 := h (wildEquiv K n) hn
    change A.1.representation ((wildEquiv K).symm (wildEquiv K n)) = 1 at h1
    rwa [ContinuousMulEquiv.symm_apply_apply] at h1
  · intro h w hw
    exact h ((wildEquiv K).symm w) hw

/-- Rank is unchanged by the transport. -/
theorem rank_toW (c : OpenKernelIrreducibleClasses.{uK, uW} (wildIn K)) :
    openKernelIrreducibleRank _ (toW K c) = openKernelIrreducibleRank _ c :=
  rank_classMap _ c

/-- Positive upper groups lie in wild inertia. -/
theorem upperGroup_le_weilWildInertia {v : ℝ} (hv : 0 < v) :
    upperGroup K v ≤ weilWildInertia K := by
  intro w hw
  change localProjection K w ∈
    (⨆ (v : ℝ) (_ : 0 < v), Ramification.Padic.absoluteUpperRamificationGroup K v).topologicalClosure
  exact Subgroup.le_topologicalClosure _ (Subgroup.mem_iSup_of_mem v (Subgroup.mem_iSup_of_mem hv hw))

/-- A closed subgroup of inertia containing all positive upper groups contains wild
inertia. -/
theorem wildIn_le_of_isClosed {H : Subgroup (localInertia K)} (hH : IsClosed (H : Set (localInertia K)))
    (h : ∀ v : ℝ, 0 < v → ∀ w : localInertia K, (w : localWeilGroup K) ∈ upperGroup K v → w ∈ H) :
    wildIn K ≤ H := by
  let e := localInertiaEquiv K
  let ι := (K.absoluteInertia K.canonicalTopologicalData).subtype
  let T : Subgroup (Field.absoluteGaloisGroup K.Carrier) := (H.map e.toMulEquiv.toMonoidHom).map ι
  have hT : IsClosed (T : Set (Field.absoluteGaloisGroup K.Carrier)) := by
    have h1 : IsClosed (e '' (H : Set (localInertia K))) := e.toHomeomorph.isClosedMap _ hH
    have h2 := (K.absoluteInertia_isClosed K.canonicalTopologicalData).isClosedEmbedding_subtypeVal.isClosedMap _ h1
    convert h2 using 1
    ext σ
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  have hsup : (⨆ (v : ℝ) (_ : 0 < v), Ramification.Padic.absoluteUpperRamificationGroup K v) ≤ T := by
    refine iSup₂_le fun v hv σ hσ => ?_
    have hσI : σ ∈ K.absoluteInertia K.canonicalTopologicalData := by
      rw [← Ramification.HerbrandBridge.absoluteUpperCanonicalInertia K]
      exact Ramification.Padic.absoluteUpperRamificationGroup_antitone K hv.le hσ
    let w := e.symm ⟨σ, hσI⟩
    have hw : localProjection K w = σ := congrArg Subtype.val (e.apply_symm_apply ⟨σ, hσI⟩)
    have hwH : w ∈ H := h v hv w ((mem_upperGroup K v _).mpr (by rw [hw]; exact hσ))
    exact ⟨e w, ⟨w, hwH, rfl⟩, hw⟩
  have hcl : Ramification.Padic.wildInertia K ≤ T :=
    Subgroup.topologicalClosure_minimal _ hsup hT
  intro n hn
  obtain ⟨_, ⟨h', hh', rfl⟩, hσ⟩ := hcl hn
  have : e h' = e n := Subtype.ext hσ
  rw [e.injective this] at hh'
  exact hh'

/-- The break of a type with a triviality threshold is at most `b ≥ 0` exactly when the type
is trivial on every upper group of index greater than `b`. -/
theorem inertiaBreak_le_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (localInertia K) V}
    (hne : ∃ v : ℝ, 0 ≤ v ∧ ∀ n : localInertia K, (n : localWeilGroup K) ∈ upperGroup K v →
      ρ n = 1) {b : ℝ} (hb : 0 ≤ b) :
    Numerical.inertiaBreak K ρ ≤ b ↔ ∀ v : ℝ, b < v → ∀ n : localInertia K,
      (n : localWeilGroup K) ∈ upperGroup K v → ρ n = 1 := by
  have hbdd : BddBelow {v : ℝ | 0 ≤ v ∧ ∀ n : localInertia K,
      (n : localWeilGroup K) ∈ upperGroup K v → ρ n = 1} := ⟨0, fun v hv => hv.1⟩
  unfold Numerical.inertiaBreak
  constructor
  · intro h v hv
    obtain ⟨s, hs, hsv⟩ := exists_lt_of_csInf_lt hne (h.trans_lt hv)
    intro n hn
    exact hs.2 n (upperGroup_antitone K hsv.le hn)
  · intro h
    apply le_of_forall_pos_le_add
    intro ε hε
    exact csInf_le hbdd ⟨by linarith, h (b + ε) (by linarith)⟩

/-- An open normal subgroup of inertia of index prime to `p` contains wild inertia. -/
theorem wildIn_le_of_coprime (U : Subgroup (localInertia K)) [U.Normal]
    (hU : IsOpen (U : Set (localInertia K))) (hcop : Nat.Coprime U.index p) : wildIn K ≤ U := by
  intro n hn
  obtain ⟨b, hb⟩ := pPowerOpen_wildIn K (U.comap (wildIn K).subtype)
    (hU.preimage continuous_subtype_val)
  have h1 : n ^ p ^ b ∈ U := hb ⟨n, hn⟩
  have h2 : n ^ U.index ∈ U := U.pow_index_mem n
  let q : localInertia K ⧸ U := QuotientGroup.mk n
  have hq1 : q ^ p ^ b = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact h1
  have hq2 : q ^ U.index = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact h2
  have h3 : orderOf q ∣ Nat.gcd (p ^ b) U.index :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq1) (orderOf_dvd_of_pow_eq_one hq2)
  have hcop' : Nat.gcd (p ^ b) U.index = 1 := Nat.Coprime.pow_left b hcop.symm
  rw [hcop', Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff n).mp h3

/-- Open subgroups of every index prime to `p` containing wild inertia, from the Frobenius
parametrization of tame fields. -/
theorem exists_index_of_parametrization
    (hpar : TameWeilFrobeniusParametrizationStatement.{uK}) (φ : localWeilGroup K)
    (hφ : localDegreeInt K φ = 1) (d : ℕ) (hd : Nat.Coprime d p) :
    ∃ U : Subgroup (localInertia K), wildIn K ≤ U ∧ IsOpen (U : Set (localInertia K)) ∧
      U.index = d := by
  have hpd : ¬ p ∣ d := fun h =>
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hd.symm h
  obtain ⟨D⟩ := hpar p K d hpd φ hφ
  let U := D.kernel.toSubgroup.subgroupOf (localInertia K)
  have : U.Normal := Subgroup.Normal.subgroupOf D.kernel.isNormal' _
  have hUo : IsOpen (U : Set (localInertia K)) :=
    D.kernel.isOpen'.preimage continuous_subtype_val
  have hidx : U.index = d := by
    change Nat.card (localInertia K ⧸ U) = d
    rw [← Nat.card_congr D.cosetEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact ⟨U, wildIn_le_of_coprime K U hUo (hidx ▸ hd), hUo, hidx⟩

end Wild

section TrivialClass

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- The lifted line has dimension one. -/
theorem finrank_ulift : Module.finrank ℂ (ULift.{uW} ℂ) = 1 := by
  rw [(ULift.moduleEquiv (R := ℂ) (M := ℂ)).finrank_eq, Module.finrank_self]

/-- The trivial one-dimensional representation of wild inertia. -/
def trivObj : WildObj.{uK, uW} (wildIn K) :=
  ⟨FiniteRepresentation.of (Representation.trivial ℂ (wildIn K) (ULift.{uW} ℂ)),
    Representation.isIrreducible_of_complex_finrank_eq_one _ finrank_ulift, by
    change IsOpen (((1 : wildIn K →* Module.End ℂ (ULift.{uW} ℂ))).ker : Set (wildIn K))
    rw [MonoidHom.ker_one]
    exact isOpen_univ⟩

/-- The trivial representation acts by the identity. -/
theorem trivObj_apply (n : wildIn K) : (trivObj.{uK, uW} K).1.representation n = 1 := rfl

/-- Every element of inertia fixes the trivial class. -/
theorem stabilizer_trivObj :
    MulAction.stabilizer (localInertia K) (wildClass (trivObj.{uK, uW} K)) = ⊤ := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
  rw [smul_wildClass]
  exact (wildClass_eq_iff _ _).mpr ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => rfl⟩

/-- An irreducible representation of wild inertia on which it acts trivially is the trivial
class. -/
theorem wildClass_eq_triv (A : WildObj.{uK, uW} (wildIn K))
    (hA : ∀ n, A.1.representation n = 1) : wildClass A = wildClass (trivObj.{uK, uW} K) := by
  let A' : Representation ℂ Unit A.1 := 1
  have hcomp : A.1.representation = A'.comp (1 : wildIn K →* Unit) :=
    MonoidHom.ext fun n => hA n
  have hirr : A'.IsIrreducible := by
    apply Langlands.FiniteRepresentation.SplitDegree.isIrreducible_of_comp A' (1 : wildIn K →* Unit)
    rw [← hcomp]
    exact A.2.1
  have : IsMulCommutative Unit := ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  have h1 : Module.finrank ℂ A.1 = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := A')
  let e : A.1 ≃ₗ[ℂ] ULift.{uW} ℂ := LinearEquiv.ofFinrankEq _ _ (h1.trans finrank_ulift.symm)
  refine (wildClass_eq_iff _ _).mpr ⟨Representation.Equiv.mk e fun n => ?_⟩
  change e.toLinearMap ∘ₗ A.1.representation n = (1 : Module.End ℂ (ULift.{uW} ℂ)) ∘ₗ e.toLinearMap
  rw [hA n]
  rfl

end TrivialClass

section RankOne

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- Conjugation by a Weil element preserves wild inertia. -/
theorem frobConj_mem_iff (φ : localWeilGroup K) (x : localInertia K) :
    x ∈ wildIn K ↔ TameTypes.frobConj K φ x ∈ wildIn K := by
  change (x : localWeilGroup K) ∈ weilWildInertia K ↔ φ * x * φ⁻¹ ∈ weilWildInertia K
  constructor
  · intro h
    exact (weilWildInertia_normal K).conj_mem _ h φ
  · intro h
    have h1 := (weilWildInertia_normal K).conj_mem _ h φ⁻¹
    simpa [mul_assoc] using h1

/-- The upper group of index `v` inside inertia. -/
abbrev upperIn (v : ℝ) : Subgroup (localInertia K) := (upperGroup K v).subgroupOf (localInertia K)

theorem upperIn_le_wildIn {v : ℝ} (hv : 0 < v) : upperIn K v ≤ wildIn K :=
  fun _ hn => upperGroup_le_weilWildInertia K hv hn

/-- A type with a triviality threshold lies over the trivial class exactly when it has rank one
and break at most zero. -/
theorem over_trivObj_iff (B : TypeObj.{uK, uW} (localInertia K))
    (hne : ∃ v : ℝ, 0 ≤ v ∧ ∀ n : localInertia K, (n : localWeilGroup K) ∈ upperGroup K v →
      B.1.representation n = 1) :
    Over (wildIn K) B (trivObj.{uK, uW} K) ↔
      Module.finrank ℂ B.1 = 1 ∧ Numerical.inertiaBreak K B.1.representation ≤ 0 := by
  have hab := commutatorsIn_wildIn K
  have hcyc := cyclicOpenQuotients_wildIn K
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [finrank_of_over hab hcyc B (trivObj K) h, stabilizer_trivObj, Subgroup.index_top,
        one_mul]
      exact finrank_ulift
    · refine (inertiaBreak_le_iff K hne le_rfl).mpr fun v hv n hn => ?_
      have : (upperIn K v).Normal :=
        Subgroup.Normal.subgroupOf (Numerical.upperGroup_normal' K v) _
      exact (trivial_iff_of_over hab hcyc B (trivObj K) h (upperIn K v)
        (upperIn_le_wildIn K hv)).mpr (fun _ _ => rfl) n hn
  · rintro ⟨-, hb⟩
    have htriv := (inertiaBreak_le_iff K hne le_rfl).mp hb
    have hBo : IsOpen (B.1.representation.ker : Set (localInertia K)) :=
      (isContinuous_iff_isOpen_ker B.1).mp B.2.1
    have hle : wildIn K ≤ B.1.representation.ker :=
      wildIn_le_of_isClosed K (Subgroup.isClosed_of_isOpen _ hBo) fun v hv w hw =>
        htriv v hv w hw
    obtain ⟨A, hA⟩ := exists_over (N := wildIn K) B
    have hAt := (trivial_iff_of_over hab hcyc B A hA (wildIn K) le_rfl).mp
      (fun m hm => hle hm)
    have hA1 : ∀ n, A.1.representation n = 1 := fun n => hAt n n.2
    obtain ⟨e⟩ := (wildClass_eq_iff _ _).mp (wildClass_eq_triv K A hA1)
    exact over_of_equiv (Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun _ => rfl) e hA

/-- Integer degree one means degree one. -/
theorem localDegree_eq_of_int {φ : localWeilGroup K} (hφ : localDegreeInt K φ = 1) :
    localDegree K φ = Multiplicative.ofAdd (1 : ℤ) := by
  rw [← hφ]
  rfl

/-- Given open subgroups of inertia containing wild inertia of every index prime to `p`, the tame
characters of inertia fixed by conjugation by a degree-one element are `q - 1` in number. -/
theorem encard_tameCharacters_fixed (φ : localWeilGroup K) (hφ : localDegreeInt K φ = 1)
    (hexists : ∀ d : ℕ, Nat.Coprime d p → ∃ U : Subgroup (localInertia K), wildIn K ≤ U ∧
      IsOpen (U : Set (localInertia K)) ∧ U.index = d) :
    {ψ ∈ tameCharactersTop (wildIn K) |
        ψ.comp (TameTypes.frobConj K φ).toMulEquiv.toMonoidHom = ψ}.encard =
      ((K.canonicalTopologicalData.residueCardinality - 1 : ℕ) : ℕ∞) := by
  have hφ' := localDegree_eq_of_int K hφ
  have hfixed := encard_fixed_liesOver.{uK, 0} (commutatorsIn_wildIn K)
    (cyclicOpenQuotients_wildIn K) (Fact.out : p.Prime)
    (fun U hNU hUo => coprime_index_of_wildIn_le K hNU hUo) hexists
    (fun c => (pPowerOpen_wildIn K).rank c) (fun χ hχ => (pPowerOpen_wildIn K).char_pow χ hχ)
    (TameTypes.frobConj K φ) (frobConj_mem_iff K φ) (wildClass (trivObj.{uK, 0} K))
    ⟨1, by
      rw [one_smul, wildPullback_mk]
      exact (wildClass_eq_iff _ _).mpr
        ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun _ => rfl⟩⟩
  rw [← hfixed]
  have hset : {x : TypeClasses.{uK, 0} (localInertia K) |
      typePullback (TameTypes.frobConj K φ) x = x ∧
        LiesOver (wildIn K) x (wildClass (trivObj.{uK, 0} K))} =
      {x | typePullback (TameTypes.frobConj K φ) x = x ∧ TameTypes.typeRank K x ∣ 0 + 1 ∧
        ((0 + 1 : ℕ) : ℝ) * TameTypes.typeBreak K x ≤ ((0 : ℕ) : ℝ)} := by
    ext x
    induction x using Quotient.inductionOn with
    | h B =>
      constructor
      · rintro ⟨hfix, hl⟩
        have hne := (TameTypes.exists_nat_of_fixed K φ hφ' B hfix).2
        obtain ⟨h1, h2⟩ := (over_trivObj_iff K B hne).mp ((liesOver_iff B (trivObj K)).mp hl)
        refine ⟨hfix, ?_, ?_⟩
        · change Module.finrank ℂ B.1 ∣ 0 + 1
          rw [h1]
        · change ((0 + 1 : ℕ) : ℝ) * Numerical.inertiaBreak K B.1.representation ≤ ((0 : ℕ) : ℝ)
          simpa using h2
      · rintro ⟨hfix, h1, h2⟩
        have hne := (TameTypes.exists_nat_of_fixed K φ hφ' B hfix).2
        refine ⟨hfix, (liesOver_iff B (trivObj K)).mpr ((over_trivObj_iff K B hne).mpr ⟨?_, ?_⟩)⟩
        · exact Nat.dvd_one.mp h1
        · change ((0 + 1 : ℕ) : ℝ) * Numerical.inertiaBreak K B.1.representation ≤ ((0 : ℕ) : ℝ)
            at h2
          simpa using h2
  rw [hset, ← TameTypes.weilConductorCount_eq.{uK, 0} K φ hφ' 0 0]
  have h := (weilRankOneCount.{uK, 0} p K).1
  unfold Numerical.weilConductorCount
  simpa using h

end RankOne

section Orbit

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

omit [Fact p.Prime] in
/-- Divisibility of `u · p^a` into `p^r · m`, for `u` and `m` prime to `p`. -/
theorem dvd_mul_iff_of_coprime {u a r m : ℕ} (hu : Nat.Coprime u p) (hm : Nat.Coprime m p) :
    u * p ^ a ∣ p ^ r * m ↔ u ∣ m ∧ p ^ a ∣ p ^ r := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 : u ∣ p ^ r * m := (Dvd.intro _ rfl).trans h
      exact (Nat.Coprime.pow_right r hu).dvd_of_dvd_mul_left h1
    · have h1 : p ^ a ∣ p ^ r * m := (Dvd.intro_left _ rfl).trans h
      exact (Nat.Coprime.pow_left a hm.symm).dvd_of_dvd_mul_right h1
  · rintro ⟨h1, h2⟩
    rw [mul_comm (p ^ r)]
    exact mul_dvd_mul h1 h2

/-- For an open normal subgroup `J` of the Weil group inside inertia, of index in inertia prime to
`p`, the transported class of `A` is fixed by `J` exactly when the index of the stabilizer of the
class of `A` in inertia divides the index of `J` in inertia. -/
theorem jFixed_iff (J : OpenNormalSubgroup (localWeilGroup K))
    (hJ : J.toSubgroup ≤ localInertia K)
    (hm : ¬ p ∣ (J.toSubgroup.subgroupOf (localInertia K)).index)
    (A : WildObj.{uK, uW} (wildIn K)) :
    (∀ g ∈ J.toSubgroup, g • toW K (wildClass A) = toW K (wildClass A)) ↔
      (MulAction.stabilizer (localInertia K) (wildClass A)).index ∣
        (J.toSubgroup.subgroupOf (localInertia K)).index := by
  let J' := J.toSubgroup.subgroupOf (localInertia K)
  have : J'.Normal := Subgroup.Normal.subgroupOf J.isNormal' _
  have hJo : IsOpen (J' : Set (localInertia K)) := J.isOpen'.preimage continuous_subtype_val
  have hcop : Nat.Coprime J'.index p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)
  have hNJ : wildIn K ≤ J' := wildIn_le_of_coprime K J' hJo hcop
  rw [← le_iff_index_dvd (commutatorsIn_wildIn K) (cyclicOpenQuotients_wildIn K) hNJ
    (le_stabilizer _) hJo (isOpen_stabilizer A)]
  constructor
  · intro hfix g hg
    have h1 := hfix (g : localWeilGroup K) hg
    rw [← toW_smul] at h1
    exact toW_injective K h1
  · intro hle g hg
    have h1 : (⟨g, hJ hg⟩ : localInertia K) • wildClass A = wildClass A :=
      hle (show (⟨g, hJ hg⟩ : localInertia K) ∈ J' from hg)
    have h2 := congrArg (toW K) h1
    rw [toW_smul] at h2
    exact h2

/-- For a type over `A` with a triviality threshold and `b ≥ 0`, the break of the type is at most
`b` exactly when the transported class of `A` is trivial at every index greater than `b`. -/
theorem break_iff (B : TypeObj.{uK, uW} (localInertia K)) (A : WildObj.{uK, uW} (wildIn K))
    (h : Over (wildIn K) B A)
    (hne : ∃ v : ℝ, 0 ≤ v ∧ ∀ n : localInertia K, (n : localWeilGroup K) ∈ upperGroup K v →
      B.1.representation n = 1) {b : ℝ} (hb : 0 ≤ b) :
    Numerical.inertiaBreak K B.1.representation ≤ b ↔
      ∀ v : ℝ, b < v → wildClassTrivialAt K v (toW K (wildClass A)) := by
  rw [inertiaBreak_le_iff K hne hb]
  refine forall_congr' fun v => imp_congr_right fun hv => ?_
  have hv0 : 0 < v := lt_of_le_of_lt hb hv
  have : (upperIn K v).Normal := Subgroup.Normal.subgroupOf (Numerical.upperGroup_normal' K v) _
  rw [wildClassTrivialAt_toW]
  exact trivial_iff_of_over (commutatorsIn_wildIn K) (cyclicOpenQuotients_wildIn K) B A h
    (upperIn K v) (upperIn_le_wildIn K hv0)

/-- Let `φ` have degree one and let `J` be an open normal subgroup of the Weil group inside inertia
of index `m` in inertia, `p ∤ m`. A type over `A` fixed by conjugation by `φ` has rank dividing
`p ^ r * m` and `p ^ r * m · break ≤ j` exactly when the transported class of `A` lies in
`tameOrbitClasses K J r m j`. -/
theorem good_iff (φ : localWeilGroup K) (hφ : localDegreeInt K φ = 1)
    (J : OpenNormalSubgroup (localWeilGroup K)) (hJ : J.toSubgroup ≤ localInertia K)
    {r m j : ℕ} (hm : ¬ p ∣ m) (hJm : (J.toSubgroup.subgroupOf (localInertia K)).index = m)
    (B : TypeObj.{uK, uW} (localInertia K)) (A : WildObj.{uK, uW} (wildIn K))
    (hfix : typePullback (TameTypes.frobConj K φ) (typeClass B) = typeClass B)
    (h : Over (wildIn K) B A) :
    (TameTypes.typeRank K (typeClass B) ∣ p ^ r * m ∧
        ((p ^ r * m : ℕ) : ℝ) * TameTypes.typeBreak K (typeClass B) ≤ j) ↔
      toW K (wildClass A) ∈ tameOrbitClasses.{uK, uW} K J.toSubgroup r m j := by
  have hab := commutatorsIn_wildIn K
  have hcyc := cyclicOpenQuotients_wildIn K
  have hp : p.Prime := Fact.out
  have hφ' := localDegree_eq_of_int K hφ
  have hne := (TameTypes.exists_nat_of_fixed K φ hφ' B hfix).2
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hm (h0 ▸ dvd_zero p)
  have hpos : (0 : ℝ) < ((p ^ r * m : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (pow_pos hp.pos r) hm0)
  have hbreak : ((p ^ r * m : ℕ) : ℝ) * TameTypes.typeBreak K (typeClass B) ≤ j ↔
      ∀ v : ℝ, (j : ℝ) / ((p ^ r * m : ℕ) : ℝ) < v →
        wildClassTrivialAt K v (toW K (wildClass A)) := by
    rw [← break_iff K B A h hne (div_nonneg (Nat.cast_nonneg j) hpos.le)]
    change _ * Numerical.inertiaBreak K B.1.representation ≤ _ ↔
      Numerical.inertiaBreak K B.1.representation ≤ _
    rw [le_div_iff₀ hpos, mul_comm]
  obtain ⟨a, ha⟩ := (pPowerOpen_wildIn K).rank (wildClass A)
  have ha' : Module.finrank ℂ A.1 = p ^ a := ha
  have hrank : TameTypes.typeRank K (typeClass B) =
      (MulAction.stabilizer (localInertia K) (wildClass A)).index * p ^ a := by
    change Module.finrank ℂ B.1 = _
    rw [finrank_of_over hab hcyc B A h, ha']
  have hcopH := coprime_index_of_wildIn_le K (le_stabilizer (wildClass A)) (isOpen_stabilizer A)
  have hmcop : Nat.Coprime m p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  rw [hrank, dvd_mul_iff_of_coprime hcopH hmcop, hbreak]
  change _ ↔ (∀ g ∈ J.toSubgroup, g • toW K (wildClass A) = toW K (wildClass A)) ∧
    openKernelIrreducibleRank _ (toW K (wildClass A)) ∣ p ^ r ∧
      ∀ v : ℝ, (j : ℝ) / ((p ^ r * m : ℕ) : ℝ) < v → wildClassTrivialAt K v (toW K (wildClass A))
  rw [rank_toW, jFixed_iff K J hJ (hJm ▸ hm) A, hJm, ha]
  tauto

/-- For a type over `A` fixed by conjugation by `φ`, the inertia orbit of the transported class
of `A` is stable under `φ`. -/
theorem orbit_stable (φ : localWeilGroup K) (B : TypeObj.{uK, uW} (localInertia K))
    (A : WildObj.{uK, uW} (wildIn K))
    (hfix : typePullback (TameTypes.frobConj K φ) (typeClass B) = typeClass B)
    (h : Over (wildIn K) B A) :
    (Quotient.mk'' (φ • toW K (wildClass A)) :
        MulAction.orbitRel.Quotient (localInertia K) (WildClasses.{uK, uW} K)) =
      Quotient.mk'' (toW K (wildClass A)) := by
  have hab := commutatorsIn_wildIn K
  have hcyc := cyclicOpenQuotients_wildIn K
  have hN := frobConj_mem_iff K φ
  have hpb : Over (wildIn K) B (wildObjPullback (TameTypes.frobConj K φ) hN A) := by
    have h1 := over_pullback B A h (TameTypes.frobConj K φ) hN
    rw [typePullback_mk] at hfix
    obtain ⟨e⟩ := (typeClass_eq_iff _ _).mp hfix
    exact over_of_equiv e (Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun _ => rfl) h1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_over hab hcyc B A _ h hpb
  have h2 : φ⁻¹ • toW K (wildClass A) = (g : localWeilGroup K) • toW K (wildClass A) := by
    rw [← toW_wildPullback K φ hN, ← toW_smul, wildPullback_mk, hg]
  apply Quotient.sound
  let u : localInertia K := ⟨φ * (g : localWeilGroup K)⁻¹ * φ⁻¹,
    (localInertia_normal K).conj_mem _ (inv_mem g.2) φ⟩
  refine ⟨u, ?_⟩
  change (φ * (g : localWeilGroup K)⁻¹ * φ⁻¹) • toW K (wildClass A) = φ • toW K (wildClass A)
  rw [mul_smul, mul_smul, h2, inv_smul_smul]

/-- The transported classes under one type lie in one inertia orbit. -/
theorem orbit_eq (B : TypeObj.{uK, uW} (localInertia K)) (A A' : WildObj.{uK, uW} (wildIn K))
    (h : Over (wildIn K) B A) (h' : Over (wildIn K) B A') :
    (Quotient.mk'' (toW K (wildClass A')) :
        MulAction.orbitRel.Quotient (localInertia K) (WildClasses.{uK, uW} K)) =
      Quotient.mk'' (toW K (wildClass A)) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_over (commutatorsIn_wildIn K) (cyclicOpenQuotients_wildIn K)
    B A A' h h'
  apply Quotient.sound
  refine ⟨g, ?_⟩
  change (g : localWeilGroup K) • toW K (wildClass A) = toW K (wildClass A')
  rw [hg, toW_smul]

/-- With `φ` and `J` as in `good_iff` and a class `c'` in `tameOrbitClasses K J r m j`: a type class
fixed by conjugation by `φ`, counted by the conductor bound, with some class under it in the
inertia orbit of `c'`, is exactly a type class fixed by conjugation by `φ` lying over `ofW K c'`. -/
theorem fiber_iff (φ : localWeilGroup K) (hφ : localDegreeInt K φ = 1)
    (J : OpenNormalSubgroup (localWeilGroup K)) (hJ : J.toSubgroup ≤ localInertia K)
    {r m j : ℕ} (hm : ¬ p ∣ m) (hJm : (J.toSubgroup.subgroupOf (localInertia K)).index = m)
    (c' : WildClasses.{uK, uW} K) (hc' : c' ∈ tameOrbitClasses.{uK, uW} K J.toSubgroup r m j)
    (x : TypeClasses.{uK, uW} (localInertia K)) :
    ((typePullback (TameTypes.frobConj K φ) x = x ∧ TameTypes.typeRank K x ∣ p ^ r * m ∧
        ((p ^ r * m : ℕ) : ℝ) * TameTypes.typeBreak K x ≤ j) ∧
      ∃ A : WildObj.{uK, uW} (wildIn K), LiesOver (wildIn K) x (wildClass A) ∧
        (Quotient.mk'' c' : MulAction.orbitRel.Quotient (localInertia K) (WildClasses.{uK, uW} K)) =
          Quotient.mk'' (toW K (wildClass A))) ↔
      typePullback (TameTypes.frobConj K φ) x = x ∧ LiesOver (wildIn K) x (ofW K c') := by
  obtain ⟨B, rfl⟩ := Quotient.exists_rep x
  constructor
  · rintro ⟨hx, A, hl, ho⟩
    refine ⟨hx.1, ?_⟩
    obtain ⟨u, hu⟩ := Quotient.exact ho
    have hc0 : ofW K c' = wildClass (conjugateOpenKernelIrreducible (wildIn K) u A) := by
      apply toW_injective K
      rw [toW_ofW, ← smul_wildClass, toW_smul]
      exact hu.symm
    rw [hc0]
    exact (liesOver_iff B _).mpr (over_smul B A ((liesOver_iff B A).mp hl) u)
  · rintro ⟨hfix, hl⟩
    obtain ⟨A, hA⟩ := Quotient.exists_rep (ofW K c')
    have hl' : LiesOver (wildIn K) (typeClass B) (wildClass A) := by
      change LiesOver (wildIn K) (typeClass B) (Quotient.mk _ A)
      rw [hA]
      exact hl
    have hO : Over (wildIn K) B A := (liesOver_iff B A).mp hl'
    have htoW : toW K (wildClass A) = c' := by
      change toW K (Quotient.mk _ A) = c'
      rw [hA]
      exact toW_ofW K c'
    refine ⟨⟨hfix, (good_iff K φ hφ J hJ hm hJm B A hfix hO).mpr (htoW ▸ hc')⟩, A, hl', ?_⟩
    rw [htoW]

/-- **Orbit formula.** Let `φ` have degree one and let `J` be an open normal subgroup of the Weil
group inside inertia of index `m` in inertia, `p ∤ m`. Given open subgroups of inertia containing
wild inertia of every index prime to `p`, the conductor count `C_K(p^r m, j)` is `q_K - 1` times the number of
Frobenius-stable inertia orbits of tame classes. -/
theorem orbitFormula (φ : localWeilGroup K) (hφ : localDegreeInt K φ = 1)
    (hexists : ∀ d : ℕ, Nat.Coprime d p → ∃ U : Subgroup (localInertia K), wildIn K ≤ U ∧
      IsOpen (U : Set (localInertia K)) ∧ U.index = d)
    (J : OpenNormalSubgroup (localWeilGroup K)) (hJ : J.toSubgroup ≤ localInertia K)
    {r m j : ℕ} (hm : ¬ p ∣ m) (hJm : (J.toSubgroup.subgroupOf (localInertia K)).index = m) :
    Numerical.weilConductorCount.{uK, uW} K (p ^ r * m - 1) j =
      ((K.canonicalTopologicalData.residueCardinality - 1 : ℕ) : ℕ∞) *
        (frobeniusStableTameOrbits.{uK, uW} K J.toSubgroup r m j φ).encard := by
  have hp : p.Prime := Fact.out
  have hφ' := localDegree_eq_of_int K hφ
  have hN := frobConj_mem_iff K φ
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero p)
  have hk : p ^ r * m - 1 + 1 = p ^ r * m :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hm0))
  rw [TameTypes.weilConductorCount_eq K φ hφ' (p ^ r * m - 1) j, hk,
    mul_comm ((K.canonicalTopologicalData.residueCardinality - 1 : ℕ) : ℕ∞)]
  let R : TypeClasses.{uK, uW} (localInertia K) →
      MulAction.orbitRel.Quotient (localInertia K) (WildClasses.{uK, uW} K) → Prop :=
    fun x o => ∃ A : WildObj.{uK, uW} (wildIn K), LiesOver (wildIn K) x (wildClass A) ∧
      o = Quotient.mk'' (toW K (wildClass A))
  apply Numerical.encard_eq_mul_of_fibers R
  · intro x hx
    obtain ⟨B, rfl⟩ := Quotient.exists_rep x
    obtain ⟨A, hA⟩ := exists_over (N := wildIn K) B
    refine ⟨Quotient.mk'' (toW K (wildClass A)), ⟨toW K (wildClass A),
      (good_iff K φ hφ J hJ hm hJm B A hx.1 hA).mp hx.2, rfl,
      orbit_stable K φ B A hx.1 hA⟩, A, (liesOver_iff B A).mpr hA, rfl⟩
  · intro x _ o _ o' _ ho ho'
    obtain ⟨B, rfl⟩ := Quotient.exists_rep x
    obtain ⟨A, hl, rfl⟩ := ho
    obtain ⟨A', hl', rfl⟩ := ho'
    exact (orbit_eq K B A A' ((liesOver_iff B A).mp hl) ((liesOver_iff B A').mp hl')).symm
  · rintro o ⟨c', hc', rfl, hst⟩
    let Fib := {x : TypeClasses.{uK, uW} (localInertia K) |
      typePullback (TameTypes.frobConj K φ) x = x ∧ LiesOver (wildIn K) x (ofW K c')}
    have hFib := fiber_iff K φ hφ J hJ hm hJm c' hc'
    have hc0 : ∃ h : localInertia K,
        wildPullback (TameTypes.frobConj K φ) hN (ofW K c') = h • ofW K c' := by
      obtain ⟨u, hu⟩ := Quotient.exact hst
      have hmem : φ⁻¹ * ((u : localWeilGroup K))⁻¹ * φ ∈ localInertia K := by
        have h1 := (localInertia_normal K).conj_mem _ (inv_mem u.2) φ⁻¹
        rwa [inv_inv] at h1
      refine ⟨⟨_, hmem⟩, ?_⟩
      apply toW_injective K
      rw [toW_wildPullback, toW_smul, toW_ofW]
      change φ⁻¹ • c' = (φ⁻¹ * ((u : localWeilGroup K))⁻¹ * φ) • c'
      have hu' : (u : localWeilGroup K) • c' = φ • c' := hu
      rw [mul_smul, mul_smul, ← hu', inv_smul_smul]
    have hcount : Fib.encard = ((K.canonicalTopologicalData.residueCardinality - 1 : ℕ) : ℕ∞) := by
      rw [← encard_tameCharacters_fixed K φ hφ hexists]
      exact encard_fixed_liesOver.{uK, uW} (commutatorsIn_wildIn K)
        (cyclicOpenQuotients_wildIn K) hp
        (fun U hNU hUo => coprime_index_of_wildIn_le K hNU hUo) hexists
        (fun c => (pPowerOpen_wildIn K).rank c) (fun χ hχ => (pPowerOpen_wildIn K).char_pow χ hχ)
        (TameTypes.frobConj K φ) hN (ofW K c') hc0
    have hfin : Fib.Finite := Set.finite_of_encard_eq_coe hcount
    have : Finite Fib := hfin.to_subtype
    have hcard : Nat.card Fib = K.canonicalTopologicalData.residueCardinality - 1 := by
      rw [Nat.card_coe_set_eq]
      have h1 := hfin.cast_ncard_eq
      rw [hcount] at h1
      exact_mod_cast h1
    let e : Fin (K.canonicalTopologicalData.residueCardinality - 1) ≃ Fib :=
      (finCongr hcard.symm).trans (Finite.equivFin Fib).symm
    refine ⟨fun i => (e i).1, fun i i' h => e.injective (Subtype.ext h), fun i => ?_, ?_⟩
    · exact (hFib (e i).1).mpr (e i).2
    · intro x hx hR
      obtain ⟨i, hi⟩ := e.surjective ⟨x, (hFib x).mp ⟨hx, hR⟩⟩
      exact ⟨i, congrArg Subtype.val hi⟩

end Orbit

end Langlands.Henniart.TameOrbit

namespace Langlands.Henniart

/-- The orbit formula follows from the Frobenius parametrization of tame fields, which supplies
open subgroups of inertia of every index prime to `p`. -/
theorem weilTameOrbitFormula_of_parametrization
    (hpar : TameWeilFrobeniusParametrizationStatement.{uK}) :
    WeilTameOrbitFormulaStatement.{uK, uW} := by
  intro p _ K r m j hm J hJ hJm φ hφ
  exact TameOrbit.orbitFormula K φ hφ
    (fun d hd => TameOrbit.exists_index_of_parametrization K hpar φ hφ d hd) J hJ hm hJm

end Langlands.Henniart
