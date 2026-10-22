import Langlands.Representation.Conductor.Definitions

/-!
# Principal congruence subgroups and newvector levels

Principal congruence means reduction of the entire matrix to the identity,
whereas the newvector subgroup only fixes the last row. The former is
contained in the latter. These are actual subgroups of the matrix general
linear group, including at rank one and level zero.
-/

noncomputable section

namespace Langlands.Conductor

universe uR uF uK uV

open Matrix

variable {R : Type uR} [CommRing R]

/-- The kernel of reduction on integral invertible matrices. -/
def integralPrincipalCongruence (n : ℕ) (I : Ideal R) :
    Subgroup (GeneralLinearGroup (Fin (n + 1)) R) :=
  (GeneralLinearGroup.map (n := Fin (n + 1)) (Ideal.Quotient.mk I)).ker

/-- Principal congruence is the identity congruence on every matrix entry. -/
theorem mem_integralPrincipalCongruence (n : ℕ) (I : Ideal R)
    (g : GeneralLinearGroup (Fin (n + 1)) R) :
    g ∈ integralPrincipalCongruence n I ↔
      ∀ i j, g i j -
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j ∈ I := by
  change GeneralLinearGroup.map (Ideal.Quotient.mk I) g = 1 ↔ _
  constructor
  · intro h i j
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1
    have he := congrArg (fun a : GeneralLinearGroup (Fin (n + 1)) (R ⧸ I) =>
      a i j) h
    simpa [GeneralLinearGroup.map_apply, Matrix.one_apply] using he
  · intro h
    apply GeneralLinearGroup.ext
    intro i j
    have he := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (h i j)
    simpa [GeneralLinearGroup.map_apply, Matrix.one_apply] using he

/-- Fixing every reduced row fixes the last reduced row. -/
theorem integralPrincipalCongruence_le_integralCongruence (n : ℕ) (I : Ideal R) :
    integralPrincipalCongruence n I ≤ integralCongruence n I := by
  intro g hg
  exact (mem_integralCongruence n I g).2
    ((mem_integralPrincipalCongruence n I g).1 hg (Fin.last n))

/-- Principal congruence imposes no condition modulo the unit ideal. -/
@[simp]
theorem integralPrincipalCongruence_top (n : ℕ) :
    integralPrincipalCongruence (R := R) n ⊤ = ⊤ := by
  ext g
  simp [mem_integralPrincipalCongruence]

/-- Increasing the ideal weakens principal congruence. -/
theorem integralPrincipalCongruence_mono (n : ℕ) {I J : Ideal R} (h : I ≤ J) :
    integralPrincipalCongruence n I ≤ integralPrincipalCongruence n J := by
  intro g hg
  exact (mem_integralPrincipalCongruence n J g).2 fun i j =>
    h ((mem_integralPrincipalCongruence n I g).1 hg i j)

/-- In rank one, principal and last-row congruence are the same condition. -/
theorem integralPrincipalCongruence_rankOne (I : Ideal R) :
    integralPrincipalCongruence 0 I = integralCongruence 0 I := by
  ext g
  simp [mem_integralPrincipalCongruence, mem_integralCongruence, Matrix.one_apply]

variable {F : Type uF} [Field F]

/-- The image of the integral reduction kernel inside the field group. -/
def principalCongruenceSubgroup (O : Subring F) (n : ℕ) (I : Ideal O) :
    Subgroup (GeneralLinearGroup (Fin (n + 1)) F) :=
  (integralPrincipalCongruence n I).map (GeneralLinearGroup.map O.subtype)

/-- The integral representative satisfies exactly the principal condition. -/
theorem map_mem_principalCongruenceSubgroup (O : Subring F) (n : ℕ) (I : Ideal O)
    (g : GeneralLinearGroup (Fin (n + 1)) O) :
    GeneralLinearGroup.map O.subtype g ∈ principalCongruenceSubgroup O n I ↔
      g ∈ integralPrincipalCongruence n I :=
  Subgroup.mem_map_iff_mem (integral_map_injective O n)

/-- The principal subgroup is contained in the newvector subgroup. -/
theorem principalCongruenceSubgroup_le_congruenceSubgroup
    (O : Subring F) (n : ℕ) (I : Ideal O) :
    principalCongruenceSubgroup O n I ≤ congruenceSubgroup O n I :=
  Subgroup.map_mono (integralPrincipalCongruence_le_integralCongruence n I)

@[simp]
theorem principalCongruenceSubgroup_top (O : Subring F) (n : ℕ) :
    principalCongruenceSubgroup O n ⊤ = integralSubgroup O n := by
  simp [principalCongruenceSubgroup, integralSubgroup, Subgroup.map_top]

/-- The principal subgroup at the power `a` of the maximal ideal.
At `a = 0` this is the full integral group. -/
def principalLevelSubgroup (F : Type uF) [Field F] [ValuativeRel F] (n a : ℕ) :
    Subgroup (GeneralLinearGroup (Fin (n + 1)) F) :=
  principalCongruenceSubgroup (ValuativeRel.valuation F).integer n
    (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ a)

@[simp]
theorem principalLevelSubgroup_zero (F : Type uF) [Field F] [ValuativeRel F] (n : ℕ) :
    principalLevelSubgroup F n 0 =
      integralSubgroup (ValuativeRel.valuation F).integer n := by
  simp [principalLevelSubgroup]

theorem principalLevelSubgroup_antitone (F : Type uF) [Field F] [ValuativeRel F]
    (n : ℕ) : Antitone (principalLevelSubgroup F n) := by
  intro a b hab
  exact Subgroup.map_mono
    (integralPrincipalCongruence_mono n (Ideal.pow_le_pow_right hab))

theorem principalLevelSubgroup_le_levelSubgroup
    (F : Type uF) [Field F] [ValuativeRel F] (n a : ℕ) :
    principalLevelSubgroup F n a ≤ levelSubgroup F n a :=
  principalCongruenceSubgroup_le_congruenceSubgroup _ _ _

/-- One principal subgroup works simultaneously for all smaller newvector levels. -/
theorem principalLevelSubgroup_le_levelSubgroup_of_le
    (F : Type uF) [Field F] [ValuativeRel F] (n : ℕ) {a b : ℕ} (h : a ≤ b) :
    principalLevelSubgroup F n b ≤ levelSubgroup F n a :=
  (principalLevelSubgroup_le_levelSubgroup F n b).trans
    (levelSubgroup_antitone F n h)

/-- Use a positive principal level even when the newvector level is zero. -/
theorem principalLevelSubgroup_max_one_le_levelSubgroup
    (F : Type uF) [Field F] [ValuativeRel F] (n a : ℕ) :
    principalLevelSubgroup F n (max 1 a) ≤ levelSubgroup F n a :=
  principalLevelSubgroup_le_levelSubgroup_of_le F n (le_max_right 1 a)

section Topology

open Topology

/-- An open ideal gives an open reduction kernel in the integral group. -/
theorem isOpen_integralPrincipalCongruence [TopologicalSpace R] [IsTopologicalRing R]
    (n : ℕ) (I : Ideal R) (hI : IsOpen (I : Set R)) :
    IsOpen (integralPrincipalCongruence n I :
      Set (GeneralLinearGroup (Fin (n + 1)) R)) := by
  have hset : (integralPrincipalCongruence n I :
      Set (GeneralLinearGroup (Fin (n + 1)) R)) =
      ⋂ i, ⋂ j, {g | g i j -
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j ∈ I} := by
    ext g
    simp only [SetLike.mem_coe, mem_integralPrincipalCongruence,
      Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun j => hI.preimage (by fun_prop)

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Principal congruence is open in the field group for an open subring and ideal. -/
theorem isOpen_principalCongruenceSubgroup (O : Subring F) (n : ℕ) (I : Ideal O)
    (hO : IsOpen (O : Set F)) (hI : IsOpen (I : Set O)) :
    IsOpen (principalCongruenceSubgroup O n I :
      Set (GeneralLinearGroup (Fin (n + 1)) F)) :=
  (isOpenEmbedding_integral_map O n hO).isOpenMap _
    (isOpen_integralPrincipalCongruence n I hI)

/-- Principal congruence is compact over a compact Hausdorff integer ring. -/
theorem isCompact_principalCongruenceSubgroup [T2Space F]
    (O : Subring F) [CompactSpace O] (n : ℕ) (I : Ideal O)
    (hI : IsOpen (I : Set O)) :
    IsCompact (principalCongruenceSubgroup O n I :
      Set (GeneralLinearGroup (Fin (n + 1)) F)) := by
  let : CompactSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) O) :=
    inferInstanceAs (CompactSpace (Fin (n + 1) → Fin (n + 1) → O))
  have hclosed := (integralPrincipalCongruence n I).isClosed_of_isOpen
    (isOpen_integralPrincipalCongruence n I hI)
  exact hclosed.isCompact.image (Continuous.generalLinearGroup_map continuous_subtype_val)

end Topology

section LocalField

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem principalLocalField_t2 : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

/-- The actual principal subgroup with its inherited open-subgroup certificate. -/
def principalLevelOpenSubgroup (n a : ℕ) :
    OpenSubgroup (GeneralLinearGroup (Fin (n + 1)) F) := by
  have := principalLocalField_t2 F
  exact
    { toSubgroup := principalLevelSubgroup F n a
      isOpen' := isOpen_principalCongruenceSubgroup _ _ _
        (Valuation.isOpen_integer (v := ValuativeRel.valuation F))
        (IsLocalRing.isOpen_maximalIdeal_pow (ValuativeRel.valuation F).integer a) }

/-- Principal levels are compact in the existing topology on the field group. -/
theorem isCompact_principalLevelOpenSubgroup (n a : ℕ) :
    IsCompact (principalLevelOpenSubgroup F n a :
      Set (GeneralLinearGroup (Fin (n + 1)) F)) := by
  have := principalLocalField_t2 F
  exact isCompact_principalCongruenceSubgroup _ _ _
    (IsLocalRing.isOpen_maximalIdeal_pow (ValuativeRel.valuation F).integer a)

end LocalField

section FixedVectors

variable {K : Type uK} [CommRing K] [ValuativeRel F]
variable {V : Type uV} [AddCommGroup V] [Module K V] {n : ℕ}

/-- Fixed vectors for the actual principal subgroup. -/
def principalLevelFixedVectors
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V) (a : ℕ) :
    Submodule K V :=
  Langlands.fixedVectors ρ (principalLevelSubgroup F n a)

/-- Last-row invariance at a bounded level gives invariance under one principal subgroup. -/
theorem levelFixedVectors_le_principalLevelFixedVectors
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    {a b : ℕ} (h : a ≤ b) :
    levelFixedVectors ρ a ≤ principalLevelFixedVectors ρ b := by
  intro v hv g
  exact (mem_levelFixedVectors ρ a v).1 hv g
    (principalLevelSubgroup_le_levelSubgroup_of_le F n h g.property)

/-- Nonvanishing transfers to the principal fixed space at any upper bound. -/
theorem principalLevelFixedVectors_ne_bot_of_levelFixedVectors
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    {a b : ℕ} (h : a ≤ b) (hv : levelFixedVectors ρ a ≠ ⊥) :
    principalLevelFixedVectors ρ b ≠ ⊥ := by
  intro he
  apply hv
  exact le_bot_iff.mp (he ▸ levelFixedVectors_le_principalLevelFixedVectors ρ h)

/-- A bounded finite newvector conductor supplies the principal invariant needed
for a separately proved bounded-level finiteness theorem. -/
theorem principalLevelFixedVectors_ne_bot_of_conductor_le
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    (hρ : HasNewvectorLevel ρ) (b : ℕ) (hb : newvectorConductor ρ hρ ≤ b) :
    principalLevelFixedVectors ρ (max 1 b) ≠ ⊥ :=
  principalLevelFixedVectors_ne_bot_of_levelFixedVectors ρ
    (hb.trans (le_max_right 1 b)) (newvectorConductor_spec ρ hρ).1

end FixedVectors

end Langlands.Conductor
