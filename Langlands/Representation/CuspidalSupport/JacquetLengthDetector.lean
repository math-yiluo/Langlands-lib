import Langlands.Representation.Filtration.RepresentationLength
import Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof

/-!
# Summed Jacquet lengths as a count on subrepresentations

For a finite set `I` of block shapes, the summed composition length of the
actual normalized Jacquet modules over `I` is invariant under equivalences and
additive on short exact sequences with smooth middle term. Its natural-number
truncation is a count on subrepresentations of a smooth representation of
finite summed length: zero on `⊥`, additive across the kernel and range of an
intertwiner, and strictly monotone once every nonzero step quotient has positive
summed length.
-/

noncomputable section

open Representation

namespace Langlands.CuspidalSupport.JacquetLength

open GeneralLinear

universe uF uU uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  {U : Type uU} {V : Type uV} {W : Type uW}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- The actual normalized Jacquet equivalence induced by an equivalence of
representations of `GL_n`. -/
def normalizedJacquetEquiv (C : BlockShape n)
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) W} (e : ρ.Equiv σ) :
    (T.normalizedJacquet C ρ).Equiv (T.normalizedJacquet C σ) :=
  { T.normalizedJacquetMap C e.toIntertwiningMap with
    invFun := T.normalizedJacquetMap C e.symm.toIntertwiningMap
    left_inv := fun x => by
      obtain ⟨v, rfl⟩ := C.jacquetMk_surjective ρ x
      change C.jacquetMk ρ (e.symm (e v)) = C.jacquetMk ρ v
      rw [e.symm_apply_apply]
    right_inv := fun x => by
      obtain ⟨w, rfl⟩ := C.jacquetMk_surjective σ x
      change C.jacquetMk σ (e (e.symm w)) = C.jacquetMk σ w
      rw [e.apply_symm_apply] }

/-- The summed composition length of the normalized Jacquet modules over a
finite set of block shapes. -/
def jacquetLength (I : Finset (BlockShape n))
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) : ℕ∞ :=
  ∑ C ∈ I, repLength (T.normalizedJacquet C ρ)

variable (I : Finset (BlockShape n))

/-- Summed Jacquet length is invariant under actual equivalences. -/
theorem jacquetLength_congr {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) W} (e : ρ.Equiv σ) :
    jacquetLength T I ρ = jacquetLength T I σ :=
  Finset.sum_congr rfl fun C _ => repLength_congr (normalizedJacquetEquiv T C e)

/-- Summed Jacquet length is additive on a short exact sequence whose middle
term is smooth. -/
theorem jacquetLength_eq_add_of_exact
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) U}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear n F.Carrier) W}
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ) :
    letI := T.topology
    IsSmooth σ → Function.Injective i → Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    jacquetLength T I σ = jacquetLength T I ρ + jacquetLength T I τ := by
  let := T.topology
  intro hσ hi hq hex
  rw [jacquetLength, jacquetLength, jacquetLength, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun C _ => ?_
  obtain ⟨hi', hex', hq'⟩ := T.normalizedJacquetMap_exact C i q hσ hi hq hex
  exact repLength_eq_add_of_exact _ _ hi' hq' hex'

/-- A zero carrier has zero summed Jacquet length. -/
theorem jacquetLength_eq_zero_of_subsingleton
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) [Subsingleton V] :
    jacquetLength T I ρ = 0 := by
  refine Finset.sum_eq_zero fun C _ => ?_
  rw [repLength_eq_zero_iff]
  constructor
  intro x y
  obtain ⟨v, rfl⟩ := C.jacquetMk_surjective ρ x
  obtain ⟨w, rfl⟩ := C.jacquetMk_surjective ρ y
  rw [Subsingleton.elim v w]

section Counts

variable {π : Representation ℂ (GeneralLinear n F.Carrier) V}
  {π' : Representation ℂ (GeneralLinear n F.Carrier) W}

/-- The inclusion of an invariant subspace as an actual intertwiner. -/
def subtypeMap (S : Subrepresentation π) : S.toRepresentation.IntertwiningMap π where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' := fun _ => rfl

theorem subtypeMap_injective (S : Subrepresentation π) :
    Function.Injective (subtypeMap S) :=
  Submodule.injective_subtype _

/-- The whole invariant subspace is equivalent to the representation. -/
def topEquiv (π : Representation ℂ (GeneralLinear n F.Carrier) V) :
    (⊤ : Subrepresentation π).toRepresentation.Equiv π :=
  { subtypeMap (⊤ : Subrepresentation π) with
    invFun := fun v => ⟨v, trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The quotient of an upper invariant subspace by a lower one. -/
abbrev stepQuotient (S S' : Subrepresentation π) :
    Representation ℂ (GeneralLinear n F.Carrier)
      (S'.toSubmodule ⧸ S.toSubmodule.comap S'.toSubmodule.subtype) :=
  S'.toRepresentation.quotient (S.toSubmodule.comap S'.toSubmodule.subtype)
    (fun g _ hv => S.apply_mem_toSubmodule g hv)

/-- The count on subrepresentations: the natural-number value of the summed
Jacquet length. -/
def count (S : Subrepresentation π) : ℕ :=
  (jacquetLength T I S.toRepresentation).toNat

theorem count_bot : count T I (⊥ : Subrepresentation π) = 0 := by
  have : Subsingleton (⊥ : Subrepresentation π).toSubmodule := by
    constructor
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : a = 0 := ha
    have hb' : b = 0 := hb
    subst ha' hb'
    rfl
  rw [count, jacquetLength_eq_zero_of_subsingleton, ENat.toNat_zero]

theorem jacquetLength_top :
    jacquetLength T I (⊤ : Subrepresentation π).toRepresentation = jacquetLength T I π :=
  jacquetLength_congr T I (topEquiv π)

theorem count_top :
    count T I (⊤ : Subrepresentation π) = (jacquetLength T I π).toNat := by
  rw [count, jacquetLength_top]

/-- An upper invariant subspace has the length of a lower one plus that of
their step quotient. -/
theorem jacquetLength_step (hπ : letI := T.topology; IsSmooth π)
    {S S' : Subrepresentation π} (hSS' : S ≤ S') :
    jacquetLength T I S'.toRepresentation =
      jacquetLength T I S.toRepresentation + jacquetLength T I (stepQuotient S S') := by
  let := T.topology
  let i : S.toRepresentation.IntertwiningMap S'.toRepresentation :=
    { toLinearMap := Submodule.inclusion hSS'
      isIntertwining' := fun _ => rfl }
  let q : S'.toRepresentation.IntertwiningMap (stepQuotient S S') :=
    { toLinearMap := (S.toSubmodule.comap S'.toSubmodule.subtype).mkQ
      isIntertwining' := fun _ => rfl }
  have hS' : IsSmooth S'.toRepresentation :=
    isSmooth_of_injective (subtypeMap S') (subtypeMap_injective S') hπ
  refine jacquetLength_eq_add_of_exact T I i q hS' (Submodule.inclusion_injective hSS')
    (Submodule.mkQ_surjective _) ?_
  ext ⟨v, hv⟩
  constructor
  · rintro ⟨⟨w, hw⟩, hwv⟩
    have hvw : v = w := (congrArg Subtype.val hwv).symm
    subst hvw
    change Submodule.Quotient.mk _ = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hw
  · intro hq
    change Submodule.Quotient.mk _ = 0 at hq
    have hq' := (Submodule.Quotient.mk_eq_zero _).mp hq
    exact ⟨⟨v, hq'⟩, rfl⟩

/-- Every invariant subspace has at most the summed Jacquet length of the
ambient smooth representation. -/
theorem jacquetLength_le (hπ : letI := T.topology; IsSmooth π) (S : Subrepresentation π) :
    jacquetLength T I S.toRepresentation ≤ jacquetLength T I π := by
  have h := jacquetLength_step T I hπ (le_top : S ≤ ⊤)
  rw [jacquetLength_top] at h
  rw [h]
  exact le_self_add

/-- The count is additive across the kernel and the range of an intertwiner. -/
theorem count_top_eq_ker_add_range (hπ : letI := T.topology; IsSmooth π)
    (hfin : jacquetLength T I π ≠ ⊤) (A : π.IntertwiningMap π') :
    count T I (⊤ : Subrepresentation π) = count T I A.ker + count T I A.range := by
  let := T.topology
  let q : π.IntertwiningMap A.range.toRepresentation :=
    { toLinearMap := A.toLinearMap.rangeRestrict
      isIntertwining' := fun g => by
        ext v
        exact IntertwiningMap.isIntertwining _ _ A g v }
  have hq : Function.Surjective q := LinearMap.surjective_rangeRestrict _
  have hex : LinearMap.range (subtypeMap A.ker).toLinearMap = LinearMap.ker q.toLinearMap := by
    change LinearMap.range (LinearMap.ker A.toLinearMap).subtype =
      LinearMap.ker A.toLinearMap.rangeRestrict
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]
  have hsum := jacquetLength_eq_add_of_exact T I (subtypeMap A.ker) q hπ
    (subtypeMap_injective _) hq hex
  rw [hsum] at hfin
  rw [count_top, hsum, ENat.toNat_add (fun h => hfin (by rw [h, top_add]))
    (fun h => hfin (by rw [h, add_top])), count, count]

/-- The count is strictly monotone when the summed Jacquet length is finite and
every nonzero step quotient has positive summed Jacquet length. -/
theorem count_strictMono (hπ : letI := T.topology; IsSmooth π)
    (hfin : jacquetLength T I π ≠ ⊤)
    (hpos : ∀ S S' : Subrepresentation π, S ≤ S' →
      Nontrivial (S'.toSubmodule ⧸ S.toSubmodule.comap S'.toSubmodule.subtype) →
      1 ≤ jacquetLength T I (stepQuotient S S')) :
    StrictMono (count T I (π := π)) := by
  intro S S' hlt
  have hle := hlt.le
  have hstep := jacquetLength_step T I hπ hle
  have hfin' : jacquetLength T I S'.toRepresentation ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (jacquetLength_le T I hπ S')
  have hnt : Nontrivial (S'.toSubmodule ⧸ S.toSubmodule.comap S'.toSubmodule.subtype) := by
    obtain ⟨v, hvS', hvS⟩ := SetLike.exists_of_lt hlt
    refine ⟨⟨Submodule.Quotient.mk ⟨v, hvS'⟩, 0, fun h => hvS ?_⟩⟩
    exact (Submodule.Quotient.mk_eq_zero (S.toSubmodule.comap S'.toSubmodule.subtype)).mp h
  have h1 := hpos S S' hle hnt
  rw [hstep] at hfin'
  have ha : jacquetLength T I S.toRepresentation ≠ ⊤ := fun h => hfin' (by rw [h, top_add])
  have hb : jacquetLength T I (stepQuotient S S') ≠ ⊤ := fun h => hfin' (by rw [h, add_top])
  rw [count, count, hstep, ENat.toNat_add ha hb]
  have : 0 < (jacquetLength T I (stepQuotient S S')).toNat :=
    ENat.toNat_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one h1)) hb
  omega

end Counts

end Langlands.CuspidalSupport.JacquetLength
