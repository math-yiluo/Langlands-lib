import Langlands.AllFieldBZ.Representation.CuspidalSupport.DualAveraging
import Langlands.AllFieldBZ.Representation.Jacquet.OppositeCanonicalLiftProof
import Langlands.AllFieldBZ.Representation.Parabolic.NaturalJacquetDualityStatement
import Langlands.Representation.Parabolic.NaturalJacquetDualityProof

/-!
# All-field port of `Langlands.Representation.Parabolic.NaturalJacquetDualityProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.NaturalJacquetDualityProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding StandardNaturalJacquetDualityClause blockScalar_commute_of_mem_leviSubgroup eventually_pow_conj_mem hasBlockIwahoriFactorization_conj jacquetModuleEquiv_normalizedJacquet jacquetModuleEquiv_normalizedJacquetMap oppositeJacquet_ρ_apply standardNaturalJacquetDuality standardPairingData standardPairingData_admits
open Langlands.GeneralLinear
open Langlands.Geometric
open scoped Topology
open scoped NNReal
universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

section Iwahori
variable {n : ℕ} (B : BlockShape n)

/-- Block scalars commute with the embedded Levi subgroup. -/
theorem blockScalar_commute_of_mem_leviSubgroup (a : Fin B.length → F.Carrierˣ)
    {m : GeneralLinear n F.Carrier} (hm : m ∈ B.leviSubgroup F.Carrier) :
    m * B.blockScalar F.Carrier a = B.blockScalar F.Carrier a * m := by
  obtain ⟨m', rfl⟩ := hm
  change B.leviEmbedding F.Carrier m' * B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a) =
    B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a) * B.leviEmbedding F.Carrier m'
  rw [← map_mul, ← map_mul, B.blockScalarLevi_commute F.Carrier a m']

/-- Conjugation by an embedded Levi element preserves block Iwahori factorization. -/
theorem hasBlockIwahoriFactorization_conj :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)} {m : GeneralLinear n F.Carrier},
      m ∈ B.leviSubgroup F.Carrier → B.HasBlockIwahoriFactorization_allFieldBZ T K →
        B.HasBlockIwahoriFactorization_allFieldBZ T (Jacquet.conjOpenSubgroup m K) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro K m hm hK
  have hN := B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier hm
  have hNbar := B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier hm
  have hconj : ∀ {x : GeneralLinear n F.Carrier}, x ∈ K →
      m * x * m⁻¹ ∈ Jacquet.conjOpenSubgroup m K := by
    intro x hx
    rw [Jacquet.mem_conjOpenSubgroup]
    have e : m⁻¹ * (m * x * m⁻¹) * m = x := by group
    rw [e]
    exact hx
  refine ⟨⟨B.iwahoriProduct_injective F.Carrier _, ?_⟩, ?_⟩
  · rintro ⟨k, hk⟩
    have hk' : m⁻¹ * k * m ∈ K := (Jacquet.mem_conjOpenSubgroup m K k).mp hk
    obtain ⟨⟨l, ml, u⟩, hlmu⟩ := hK.1.2 ⟨m⁻¹ * k * m, hk'⟩
    have hval : l.val * ml.val * u.val = m⁻¹ * k * m := congrArg Subtype.val hlmu
    obtain ⟨hlK, hlN⟩ := (B.mem_iwahoriLower F.Carrier _ _).mp l.property
    obtain ⟨hmK, hmM⟩ := (B.mem_iwahoriLevi F.Carrier _ _).mp ml.property
    obtain ⟨huK, huN⟩ := (B.mem_iwahoriUpper F.Carrier _ _).mp u.property
    refine ⟨(⟨m * l.val * m⁻¹, (B.mem_iwahoriLower F.Carrier _ _).mpr
        ⟨hconj hlK, (Subgroup.mem_normalizer_iff.mp hNbar _).mp hlN⟩⟩,
      ⟨m * ml.val * m⁻¹, (B.mem_iwahoriLevi F.Carrier _ _).mpr
        ⟨hconj hmK, (B.leviSubgroup F.Carrier).mul_mem
          ((B.leviSubgroup F.Carrier).mul_mem hm hmM) ((B.leviSubgroup F.Carrier).inv_mem hm)⟩⟩,
      ⟨m * u.val * m⁻¹, (B.mem_iwahoriUpper F.Carrier _ _).mpr
        ⟨hconj huK, (Subgroup.mem_normalizer_iff.mp hN _).mp huN⟩⟩), ?_⟩
    apply Subtype.ext
    change m * l.val * m⁻¹ * (m * ml.val * m⁻¹) * (m * u.val * m⁻¹) = k
    calc m * l.val * m⁻¹ * (m * ml.val * m⁻¹) * (m * u.val * m⁻¹) =
        m * (l.val * ml.val * u.val) * m⁻¹ := by group
      _ = k := by rw [hval]; group
  · intro a ha
    have hK2 := hK.2 a ha
    have hc : Commute m (B.blockScalar F.Carrier a) :=
      blockScalar_commute_of_mem_leviSubgroup F B a hm
    constructor
    · intro g hg
      obtain ⟨hgK, hgN⟩ := (B.mem_iwahoriUpper F.Carrier _ g).mp hg
      have hg' : m⁻¹ * g * m ∈ B.iwahoriUpper F.Carrier K.toSubgroup :=
        (B.mem_iwahoriUpper F.Carrier _ _).mpr
          ⟨(Jacquet.mem_conjOpenSubgroup m K g).mp hgK,
            (Subgroup.mem_normalizer_iff''.mp hN g).mp hgN⟩
      have h1 := ((B.mem_iwahoriUpper F.Carrier _ _).mp (hK2.1 _ hg')).1
      refine (B.mem_iwahoriUpper F.Carrier _ _).mpr
        ⟨?_, B.blockScalar_conj_mem_unipotentSubgroup F.Carrier a hgN⟩
      refine (Jacquet.mem_conjOpenSubgroup m K _).mpr ?_
      rw [inv_conj_conj_of_commute hc]
      exact h1
    · intro g hg
      obtain ⟨hgK, hgN⟩ := (B.mem_iwahoriLower F.Carrier _ g).mp hg
      have hg' : m⁻¹ * g * m ∈ B.iwahoriLower F.Carrier K.toSubgroup :=
        (B.mem_iwahoriLower F.Carrier _ _).mpr
          ⟨(Jacquet.mem_conjOpenSubgroup m K g).mp hgK,
            (Subgroup.mem_normalizer_iff''.mp hNbar g).mp hgN⟩
      have h1 := ((B.mem_iwahoriLower F.Carrier _ _).mp (hK2.2 _ hg')).1
      refine (B.mem_iwahoriLower F.Carrier _ _).mpr
        ⟨?_, B.blockScalar_inv_conj_mem_oppositeUnipotentSubgroup F.Carrier a hgN⟩
      have e := inv_conj_conj_of_commute hc.inv_right g
      rw [inv_inv] at e
      refine (Jacquet.mem_conjOpenSubgroup m K _).mpr ?_
      rw [e]
      exact h1

/-- A block Iwahori factorization writes each element as lower times Levi times upper. -/
theorem HasBlockIwahoriFactorization.factor :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)}, B.HasBlockIwahoriFactorization_allFieldBZ T K →
      ∀ k ∈ K, ∃ l ∈ K, l ∈ B.oppositeUnipotentSubgroup F.Carrier ∧
        ∃ m ∈ K, m ∈ B.leviSubgroup F.Carrier ∧
          ∃ u ∈ K, u ∈ B.unipotentSubgroup F.Carrier ∧ k = l * m * u := by
  let := T.topology
  intro K hK k hk
  obtain ⟨⟨l, m, u⟩, h⟩ := hK.1.2 ⟨k, hk⟩
  exact ⟨l.val, l.property.1, l.property.2, m.val, m.property.1, m.property.2,
    u.val, u.property.1, u.property.2, (congrArg Subtype.val h).symm⟩

/-- Inverse block-scalar conjugation keeps lower elements of a factorized subgroup inside it. -/
theorem HasBlockIwahoriFactorization.lower_conj :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)}, B.HasBlockIwahoriFactorization_allFieldBZ T K →
      ∀ {a : Fin B.length → F.Carrierˣ}, B.IsWeaklyContracting_allFieldBZ T a →
        ∀ l ∈ K, l ∈ B.oppositeUnipotentSubgroup F.Carrier →
          (B.blockScalar F.Carrier a)⁻¹ * l * B.blockScalar F.Carrier a ∈ K := by
  let := T.topology
  intro K hK a ha l hl hlN
  exact ((hK.2 a ha).2 l ⟨hl, hlN⟩).1

/-- Powers of a block scalar keep upper elements of a factorized subgroup inside it. -/
theorem HasBlockIwahoriFactorization.upper_conj_pow :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)}, B.HasBlockIwahoriFactorization_allFieldBZ T K →
      ∀ {a : Fin B.length → F.Carrierˣ}, B.IsWeaklyContracting_allFieldBZ T a →
        ∀ u ∈ K, u ∈ B.unipotentSubgroup F.Carrier → ∀ r : ℕ,
          B.blockScalar F.Carrier a ^ r * u * (B.blockScalar F.Carrier a ^ r)⁻¹ ∈ K := by
  let := T.topology
  intro K hK a ha u hu huN r
  suffices h : B.blockScalar F.Carrier a ^ r * u * (B.blockScalar F.Carrier a ^ r)⁻¹ ∈
      B.iwahoriUpper F.Carrier K.toSubgroup from h.1
  induction r with
  | zero => simpa using (⟨hu, huN⟩ : u ∈ B.iwahoriUpper F.Carrier K.toSubgroup)
  | succ r ih =>
    have e : B.blockScalar F.Carrier a ^ (r + 1) * u * (B.blockScalar F.Carrier a ^ (r + 1))⁻¹ =
        B.blockScalar F.Carrier a *
          (B.blockScalar F.Carrier a ^ r * u * (B.blockScalar F.Carrier a ^ r)⁻¹) *
            (B.blockScalar F.Carrier a)⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      simp only [mul_assoc]
    rw [e]
    exact (hK.2 a ha).1 _ ih

/-- High powers of a strict block scalar conjugate a compact set of upper elements
into any identity neighbourhood. -/
theorem eventually_pow_conj_mem :
    letI := T.topology
    ∀ (a : Fin B.length → F.Carrierˣ), B.IsStrictlyContracting_allFieldBZ T a →
      ∀ (C : Set (GeneralLinear n F.Carrier)), IsCompact C →
        ∀ U : Set (GeneralLinear n F.Carrier), U ∈ 𝓝 (1 : GeneralLinear n F.Carrier) →
          ∃ r : ℕ, ∀ s : ℕ, r ≤ s → ∀ u ∈ C, u ∈ B.unipotentSubgroup F.Carrier →
            B.blockScalar F.Carrier a ^ s * u * (B.blockScalar F.Carrier a ^ s)⁻¹ ∈ U := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro a ha C hC U hU
  obtain ⟨ε, hε, -, hc⟩ := B.uniformCompactBlockContraction_allFieldBZ T
    (C ∩ (B.unipotentSubgroup F.Carrier : Set (GeneralLinear n F.Carrier))) ∅
    (hC.inter_right (B.isClosed_unipotentSubgroup F.Carrier)) Set.inter_subset_right
    isCompact_empty (Set.empty_subset _) U hU
  obtain ⟨r, hr⟩ := B.strictPowersEventuallyDeep_allFieldBZ T a ha ε hε
  refine ⟨r, fun s hs u hu huN => ?_⟩
  have hpow : B.blockScalar F.Carrier (fun i => a i ^ s) = B.blockScalar F.Carrier a ^ s :=
    map_pow (B.blockScalar F.Carrier) a s
  rw [← hpow]
  exact (hc _ (hr s hs)).1 u ⟨hu, huN⟩

end Iwahori
section Standard
variable {n : ℕ} (B : BlockShape n)

/-- Stable pairing data for the standard parabolic of shape `B`, contracting by
the block scalar of a strictly contracting tuple. -/
def standardPairingData (a : Fin B.length → F.Carrierˣ) (ha : B.IsStrictlyContracting_allFieldBZ T a) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Jacquet.StablePairingData (GeneralLinear n F.Carrier) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact
    { N := B.unipotentSubgroup F.Carrier
      Nbar := B.oppositeUnipotentSubgroup F.Carrier
      M := B.leviSubgroup F.Carrier
      hMN := B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier
      hMNbar := B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier
      g := B.blockScalar F.Carrier a
      commute := fun m hm => blockScalar_commute_of_mem_leviSubgroup F B a hm
      Good := fun K => IsCompact (K : Set (GeneralLinear n F.Carrier)) ∧
        B.HasBlockIwahoriFactorization_allFieldBZ T K
      isCompact := fun K hK => hK.1
      exists_good_subset := fun O hO h1 => by
        obtain ⟨K, hKc, hKO, hfac⟩ :=
          B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization_allFieldBZ T (hO.mem_nhds h1)
        exact ⟨K, ⟨hKc, hfac⟩, hKO⟩
      good_conj := fun m hm K hK =>
        ⟨Jacquet.isCompact_conjOpenSubgroup m K hK.1,
          hasBlockIwahoriFactorization_conj F T B hm hK.2⟩
      factor := fun K hK => HasBlockIwahoriFactorization.factor F T B hK.2
      lower_conj := fun K hK => HasBlockIwahoriFactorization.lower_conj F T B hK.2 ha.weak
      upper_conj := fun K hK => HasBlockIwahoriFactorization.upper_conj_pow F T B hK.2 ha.weak
      deep := fun K₀ K₁ hK₀ _ => by
        obtain ⟨r, hr⟩ := eventually_pow_conj_mem F T B a ha K₀ hK₀.1 K₁
          (K₁.isOpen.mem_nhds K₁.one_mem)
        exact ⟨r, fun u hu huN => hr r le_rfl u hu huN⟩ }

/-- Admissible representations satisfy the finiteness and canonical-lift
hypotheses of the standard pairing data. -/
theorem standardPairingData_admits (a : Fin B.length → F.Carrierˣ)
    (ha : B.IsStrictlyContracting_allFieldBZ T a) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsAdmissible ρ),
      (standardPairingData F T B a ha).Admits ρ hρ.1 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ
  have hcof : ∀ K : OpenSubgroup (GeneralLinear n F.Carrier),
      ∃ L : OpenSubgroup (GeneralLinear n F.Carrier),
        IsCompact (L : Set (GeneralLinear n F.Carrier)) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hL, hLK, -⟩ :=
      B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization_allFieldBZ T (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L, hL, hLK⟩
  have hρ' := isAdmissible_smoothContragredient_of_compact_cofinal hcof ρ hρ
  exact
    { duality := fun K _ =>
        Jacquet.compactCompression_stableEvaluationDuality ρ hρ.1 K _ _ (hρ.2 K)
      upper_surjective := fun K hK =>
        (Jacquet.blockStableImageJacquetBijective F T B (SmoothDual ρ)
          (smoothContragredient ρ) hρ' K hK.1 hK.2 a ha).2
      upper_kernel := fun K hK =>
        (Jacquet.blockPowerKernelJacquet F T B (SmoothDual ρ)
          (smoothContragredient ρ) hρ' K hK.1 hK.2 a ha).ge
      lower_surjective := fun K hK =>
        (Jacquet.blockOppositeStableImageJacquetBijective F T B V ρ hρ K hK.1 hK.2 a ha).2
      lower_kernel := fun K hK =>
        (Jacquet.blockOppositePowerKernelJacquet F T B V ρ hρ K hK.1 hK.2 a ha).ge }

/-- The upper normalized Levi action, transported to the ambient upper quotient,
is the inverse half modulus times the descended action of the embedded Levi. -/
theorem jacquetModuleEquiv_normalizedJacquet {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (l : B.Levi F.Carrier)
    (x : B.JacquetModule ρ) :
    B.jacquetModuleEquiv ρ (T.normalizedJacquet B ρ l x) =
      (Jacquet.inverseHalfCharacter (T.leviModulus B) l : ℂ) •
        Jacquet.action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
          (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
          (B.leviEquiv F.Carrier l) (B.jacquetModuleEquiv ρ x) := by
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
  rw [T.normalizedJacquet_mk, map_smul, B.jacquetModuleEquiv_mk, B.jacquetModuleEquiv_mk,
    Jacquet.inverseHalfCharacter_apply]
  rfl

/-- The upper normalized Jacquet map, transported to the ambient upper quotient,
is the coinvariant map. -/
theorem jacquetModuleEquiv_normalizedJacquetMap {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) W} (f : ρ.IntertwiningMap σ)
    (x : B.JacquetModule ρ) :
    B.jacquetModuleEquiv σ (T.normalizedJacquetMap B f x) =
      Jacquet.map (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier) f
        (B.jacquetModuleEquiv ρ x) := by
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
  rfl

/-- The opposite Levi action is the inverse-modulus twist of the descended
action of the embedded Levi. -/
theorem oppositeJacquet_ρ_apply (π : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (l : B.Levi F.Carrier)
    (y : Jacquet.Coinvariants π.ρ (B.oppositeUnipotentSubgroup F.Carrier)) :
    (CuspidalJacquetMultiplicity.oppositeJacquet T B π).ρ l y =
      (Jacquet.inverseHalfCharacter
          ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹
          (B.leviEquiv F.Carrier l) : ℂ) •
        Jacquet.action π.ρ (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
          (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
          (B.leviEquiv F.Carrier l) y := by
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective _ _ y
  rfl

end Standard
section Refined
variable {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

end Refined
/-- The standard clause: natural upper/opposite normalized Jacquet duality for
the standard parabolics of `GL_n`. -/
theorem standardNaturalJacquetDuality : StandardNaturalJacquetDualityClause.{uF, uV} := by
  intro F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : IsTopologicalRing F.Carrier := inferInstance
  intro n B
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  obtain ⟨a, ha⟩ := B.deepChamberNonempty_allFieldBZ T 1 zero_lt_one
  have has : B.IsStrictlyContracting_allFieldBZ T a := ha
  let δ := (T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom
  let χO : B.Levi F.Carrier →* ℂˣ :=
    (Jacquet.inverseHalfCharacter δ⁻¹).comp (B.leviEquiv F.Carrier).toMonoidHom
  have hχ : ∀ l, (Jacquet.inverseHalfCharacter (T.leviModulus B) l : ℂ) * (χO l : ℂ) = 1 := by
    intro l
    have e : Jacquet.inverseHalfCharacter δ⁻¹ (B.leviEquiv F.Carrier l) =
        Jacquet.inverseHalfCharacter (T.leviModulus B)⁻¹ l := by
      have hδ : δ⁻¹ (B.leviEquiv F.Carrier l) = (T.leviModulus B)⁻¹ l := by
        simp [δ]
      simp only [Jacquet.inverseHalfCharacter, Jacquet.complexCharacter,
        Jacquet.positiveHalfCharacter, MonoidHom.inv_apply, MonoidHom.comp_apply, hδ]
    change _ * (Jacquet.inverseHalfCharacter δ⁻¹ (B.leviEquiv F.Carrier l) : ℂ) = 1
    rw [e]
    exact inverseHalfCharacter_mul_inverseHalfCharacter_inv _ l
  have hχO : IsOpen (χO.ker : Set (B.Levi F.Carrier)) := by
    have hδ : IsOpen (δ.ker : Set (B.leviSubgroup F.Carrier)) :=
      (T.isOpen_ker_leviModulus B).preimage (B.leviEquivContinuous F.Carrier).symm.continuous
    have hδinv : IsOpen (δ⁻¹.ker : Set (B.leviSubgroup F.Carrier)) := by
      have heq : δ⁻¹.ker = δ.ker := by
        ext m
        simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
      rw [heq]
      exact hδ
    exact (Jacquet.isOpen_ker_inverseHalfCharacter δ⁻¹ hδinv).preimage
      (B.leviEquivContinuous F.Carrier).continuous
  have key : ∀ (π : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) (hπ : IsAdmissible π.ρ),
      ∃ b, (standardPairingData F T B a has).IsStablePairing π.ρ hπ.1 b ∧
        ∃ E : Representation.Equiv (T.normalizedJacquet B (smoothContragredient π.ρ))
            (smoothContragredient (CuspidalJacquetMultiplicity.oppositeJacquet T B π).ρ),
          ∀ x y, (E x).1 y = b (B.jacquetModuleEquiv (smoothContragredient π.ρ) x) y := by
    intro π hπ
    have hA := standardPairingData_admits F T B a has π.ρ hπ
    obtain ⟨b, hb⟩ := (standardPairingData F T B a has).exists_isStablePairing hA
    refine ⟨b, hb, ?_⟩
    refine hb.exists_equiv hA (B.leviEquivContinuous F.Carrier)
      (fun l => (Jacquet.inverseHalfCharacter (T.leviModulus B) l : ℂ)) χO hχ hχO
      (T.normalizedJacquet B (smoothContragredient π.ρ))
      (B.jacquetModuleEquiv (smoothContragredient π.ρ))
      (fun l x => jacquetModuleEquiv_normalizedJacquet F T B _ l x)
      (CuspidalJacquetMultiplicity.oppositeJacquet T B π).ρ
      (fun l y => oppositeJacquet_ρ_apply F T B π l y)
  choose b hb E hE using key
  refine ⟨E, ?_⟩
  intro π τ hπ hτ f x y
  refine (hE π hπ _ y).trans (Eq.trans ?_ (hE τ hτ x _).symm)
  refine (DFunLike.congr_fun (congrArg (b π hπ)
    (jacquetModuleEquiv_normalizedJacquetMap F T B (contragredientMap f) x)) y).trans ?_
  exact (hb π hπ).natural (standardPairingData_admits F T B a has π.ρ hπ) (hb τ hτ) f
    (B.jacquetModuleEquiv (smoothContragredient τ.ρ) x) y

end Langlands.AllFieldBZ.Parabolic
