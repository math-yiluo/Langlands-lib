import Langlands.Correspondence.PadicSupercuspidalFinitenessProof
import Langlands.AllField.Representation.CuspidalSupport.CompactCoefficientFinitenessProof
import Langlands.AllField.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.AllField.Representation.CuspidalSupport.DeterminantUnitStructureProof
import Langlands.AllField.Representation.CuspidalSupport.LeviCompactPart
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Compact-open finiteness of supercuspidal classes over every local field

Bernstein–Zelevinsky (1976), Corollary 4.15, with the original arbitrary local-field
instances and independent field and representation-carrier universes.
-/

noncomputable section

namespace Langlands.Henniart.AllFieldCompactOpenFiniteness

open GeneralLinear
open Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport (IsLeviQuasicuspidal
  exists_twistIntertwiningMap_of_restrictedHom_nonzero twistEquivOfNonzeroIntertwiner
  isIrreducible_comp_of_surjective nontrivial_of_isIrreducible)
open CompactOpenFiniteness (IsConstituent isSmooth_subrepresentation
  exists_fixedVectors_ne_bot isCompl_toSubmodule exists_ne_zero_of_isConstituent
  finite_monoidHom_units)

universe uF uV uW

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The one-block shape of rank `n + 1`; its Levi subgroup is `GL_(n+1)`. -/
abbrev fullBlock (n : ℕ) : BlockShape (n + 1) :=
  CuspidalSupport.LeviAdmissibility.oneBlock (n + 1) (Nat.succ_pos n)

local instance finitenessLeviTopologicalGroup (n : ℕ) :
    IsTopologicalGroup ((fullBlock n).Levi F) :=
  (LocalFieldData.ofInstances F).leviTopologicalGroup (fullBlock n)

/-- BZ76's `G°` in the one-block Levi: determinant of normalized absolute value one. -/
abbrev unitGroup (n : ℕ) : Subgroup ((fullBlock n).Levi F) :=
  determinantUnitSubgroup (LocalFieldData.ofInstances F) (fullBlock n)

/-- The pullback of a representation of `GL_(n+1)` to the one-block Levi. -/
abbrev leviRep (n : ℕ) (ρ : Representation ℂ (GeneralLinear (n + 1) F) V) :
    Representation ℂ ((fullBlock n).Levi F) V :=
  ρ.comp ((fullBlock n).leviEmbedding F)

/-- The restriction of a representation of `GL_(n+1)` to `G°`. -/
abbrev unitRep (n : ℕ) (ρ : Representation ℂ (GeneralLinear (n + 1) F) V) :
    Representation ℂ (unitGroup F n) V :=
  determinantUnitRestriction (LocalFieldData.ofInstances F) (fullBlock n) (leviRep F n ρ)

/-- `G° Z` in the one-block Levi. -/
abbrev twistKernel (n : ℕ) : Subgroup ((fullBlock n).Levi F) :=
  unitGroup F n ⊔ Subgroup.center ((fullBlock n).Levi F)

/-- The finite abelian quotient `GL_(n+1) / G° Z` (BZ76 3.20). -/
abbrev twistQuotient (n : ℕ) := (fullBlock n).Levi F ⧸ twistKernel F n

theorem finite_twistQuotient (n : ℕ) : Finite (twistQuotient F n) := by
  have := determinantUnit_sup_center_finiteIndex (LocalFieldData.ofInstances F) (fullBlock n)
  infer_instance

/-- The compact open subgroup of `G°` cut out by an open subgroup of `GL_(n+1)`. -/
def unitLevel (n : ℕ) (N : OpenSubgroup (GeneralLinear (n + 1) F)) :
    OpenSubgroup (unitGroup F n) :=
  OpenSubgroup.comap (unitGroup F n).subtype continuous_subtype_val
    (OpenSubgroup.comap ((fullBlock n).leviEmbedding F)
      ((fullBlock n).leviEmbeddingContinuous F).continuous N)

theorem isCompact_unitLevel (n : ℕ) (N : OpenSubgroup (GeneralLinear (n + 1) F))
    (hN : IsCompact (N : Set (GeneralLinear (n + 1) F))) :
    IsCompact (unitLevel F n N : Set (unitGroup F n)) := by
  let := (LocalFieldData.ofInstances F).leviTopologicalGroup (fullBlock n)
  have hL : IsCompact (((fullBlock n).leviEmbedding F) ⁻¹'
      (N : Set (GeneralLinear (n + 1) F))) :=
    ((fullBlock n).singleBlockLeviEquivContinuous rfl F).toHomeomorph.isCompact_preimage.mpr
      hN
  have hclosed : IsClosed (unitGroup F n : Set ((fullBlock n).Levi F)) :=
    (determinantUnitOpenSubgroup (LocalFieldData.ofInstances F) (fullBlock n)).isClosed
  exact hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hL

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem isSmooth_leviRep (n : ℕ)
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F)) :
    IsSmooth (leviRep F n A.representation) :=
  isSmooth_comp _ ((fullBlock n).leviEmbeddingContinuous F).continuous A.isSmooth

theorem isSmooth_unitRep (n : ℕ)
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F)) :
    IsSmooth (unitRep F n A.representation) :=
  isSmooth_comp _ continuous_subtype_val (isSmooth_leviRep F n A)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem isIrreducible_leviRep (n : ℕ)
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F)) (hA : A.IsIrreducible) :
    (leviRep F n A.representation).IsIrreducible := by
  have := hA
  exact isIrreducible_comp_of_surjective A.representation _
    ((fullBlock n).singleBlock_leviEmbedding_surjective rfl F)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The one-block embedding maps the centre of the Levi into the centre of `GL_(n+1)`. -/
theorem leviEmbedding_mem_center (n : ℕ) {z : (fullBlock n).Levi F}
    (hz : z ∈ Subgroup.center ((fullBlock n).Levi F)) :
    (fullBlock n).leviEmbedding F z ∈
      Subgroup.center (GeneralLinear (n + 1) F) := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨y, rfl⟩ := (fullBlock n).singleBlock_leviEmbedding_surjective rfl F g
  rw [← map_mul, ← map_mul, hz y]

/-- A vector fixed by `N` is fixed by the corresponding subgroup of `G°`. -/
theorem fixedVectors_unitRep_ne_bot (n : ℕ)
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F))
    (N : OpenSubgroup (GeneralLinear (n + 1) F))
    (hfix : fixedVectors A.representation N.toSubgroup ≠ ⊥) :
    fixedVectors (unitRep F n A.representation) (unitLevel F n N).toSubgroup ≠ ⊥ := by
  intro hbot
  apply hfix
  rw [eq_bot_iff] at hbot ⊢
  intro v hv
  apply hbot
  rw [fixedVectors, Representation.mem_invariants] at hv ⊢
  intro h
  exact hv ⟨_, h.property⟩

/-- BZ76 3.21, 3.26 and the averaging argument: a supercuspidal representation with a
nonzero vector fixed by a compact open subgroup `L` of `G°` has a constituent class in
the `L`-fixed stratum. -/
theorem exists_isConstituent (n : ℕ)
    (χ : Subgroup.center (GeneralLinear (n + 1) F) →* ℂˣ)
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n + 1))
    (hχ : A.obj.HasCentralCharacter χ)
    (L : OpenSubgroup (unitGroup F n)) (hL : IsCompact (L : Set (unitGroup F n)))
    (hfix : fixedVectors (unitRep F n A.obj.representation) L.toSubgroup ≠ ⊥) :
    ∃ c ∈ CompactCoefficientClass.fixedStratum.{uF, uV} L.toSubgroup,
      IsConstituent (isSmooth_unitRep F n A.obj) c := by
  let := (LocalFieldData.ofInstances F).leviTopologicalGroup (fullBlock n)
  let D : SmoothRep.{0, uF, uV} ℂ ((fullBlock n).Levi F) :=
    SmoothRep.of (leviRep F n A.obj.representation) (isSmooth_leviRep F n A.obj)
  have hD : D.IsIrreducible := isIrreducible_leviRep F n A.obj A.property.1
  have hquasi : IsLeviQuasicuspidal (fullBlock n) D.representation := by
    have hvan := (isSupercuspidal_iff_standard A.obj.representation).mp A.property.2
    intro S hS
    have h := (Jacquet.coinvariantsMapEquiv A.obj.representation
      ((fullBlock n).leviEmbedding F)
      (Geometric.refinedUnipotent F (fullBlock n) S)).toEquiv.subsingleton_congr
    rw [(fullBlock n).singleBlock_refinedUnipotent_map rfl F S] at h
    exact h.mpr (hvan.2 ((fullBlock n).singleBlockRefinementEquiv rfl S)
      (((fullBlock n).singleBlock_refinedParabolic_ne_top_iff rfl F S).mp hS))
  have hcoef : HasCompactSmoothDualCoefficients (unitRep F n A.obj.representation) :=
    (leviHarishChandraTheorem F (LocalFieldData.ofInstances F) (n + 1) (fullBlock n) D).mp hquasi
  have := determinantUnit_sup_center_finiteIndex (LocalFieldData.ofInstances F) (fullBlock n)
  obtain ⟨hsemi, m, S, hS, hspan⟩ :=
    FiniteIndexRestriction.finite_irreducible_restriction D.representation (unitGroup F n) hD
      (fun z => ⟨(χ ⟨_, leviEmbedding_mem_center F n z.property⟩ : ℂ),
        fun v => hχ ⟨_, leviEmbedding_mem_center F n z.property⟩ v⟩)
  have hsm := isSmooth_unitRep F n A.obj
  obtain ⟨i, hi⟩ := exists_fixedVectors_ne_bot hsm L hL S hspan hfix
  have := hsemi
  obtain ⟨Q, hQ⟩ := exists_isCompl (S i)
  have hc : HasCompactSmoothDualCoefficients (S i).toRepresentation :=
    hasCompactSmoothDualCoefficients_subrepresentation
      (determinantUnitCompactOpenCofinal (LocalFieldData.ofInstances F) (fullBlock n))
      (SmoothRep.of _ hsm) hcoef (S i)
  exact ⟨CompactCoefficientClass.ofRep
      ⟨SmoothRep.of (S i).toRepresentation (isSmooth_subrepresentation hsm (S i)), hS i, hc⟩,
    hi, S i, Q, isCompl_toSubmodule hQ, hS i, hc, rfl⟩

/-- BZ76 3.29 with central characters: supercuspidal representations with the same
central character and a nonzero intertwiner between their restrictions to `G°` differ by
a twist by a character of `GL_(n+1) / G° Z`. -/
theorem exists_twist_equiv (n : ℕ)
    (χ : Subgroup.center (GeneralLinear (n + 1) F) →* ℂˣ)
    (A₁ A₂ : SupercuspidalRep.{uF, uV} (F := F) (n := n + 1))
    (h₁ : A₁.obj.HasCentralCharacter χ) (h₂ : A₂.obj.HasCentralCharacter χ)
    (f : (unitRep F n A₁.obj.representation).IntertwiningMap
      (unitRep F n A₂.obj.representation)) (hf : f ≠ 0) :
    ∃ φ : twistQuotient F n →* ℂˣ,
      Nonempty ((Langlands.twist (φ.comp (QuotientGroup.mk' (twistKernel F n)))
        (leviRep F n A₁.obj.representation)).Equiv (leviRep F n A₂.obj.representation)) := by
  have := determinantUnit_sup_center_finiteIndex (LocalFieldData.ofInstances F) (fullBlock n)
  have hcomm : commutator ((fullBlock n).Levi F) ≤ unitGroup F n :=
    Abelianization.commutator_subset_ker
      (leviDeterminantNorm (LocalFieldData.ofInstances F) (fullBlock n))
  have hz : ∀ (A : SupercuspidalRep.{uF, uV} (F := F) (n := n + 1)),
      A.obj.HasCentralCharacter χ → ∀ (z : (fullBlock n).Levi F)
        (hz : z ∈ Subgroup.center ((fullBlock n).Levi F)) (v : A.obj),
        leviRep F n A.obj.representation z v =
          (χ ⟨_, leviEmbedding_mem_center F n hz⟩ : ℂ) • v :=
    fun A hA z hz v => hA ⟨_, leviEmbedding_mem_center F n hz⟩ v
  obtain ⟨χ', hχ', t, ht⟩ := exists_twistIntertwiningMap_of_restrictedHom_nonzero
    (leviRep F n A₁.obj.representation) (leviRep F n A₂.obj.representation) (unitGroup F n)
    hcomm (fun z => ⟨_, hz A₁ h₁ z z.property⟩) (fun z => ⟨_, hz A₂ h₂ z z.property⟩) f hf
  let E := twistEquivOfNonzeroIntertwiner _ _ (isIrreducible_leviRep F n A₁.obj A₁.property.1)
    (isIrreducible_leviRep F n A₂.obj A₂.property.1) χ' t ht
  have hcenter : Subgroup.center ((fullBlock n).Levi F) ≤ χ'.ker := by
    intro z hz'
    rw [MonoidHom.mem_ker]
    have : Nontrivial A₁.obj :=
      nontrivial_of_isIrreducible A₁.obj.representation (hρ := A₁.property.1)
    obtain ⟨v, hv⟩ := exists_ne (0 : A₁.obj)
    have hEv : E v ≠ 0 := fun h => hv (E.injective (h.trans (map_zero E).symm))
    have key := Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap z v
    change E ((χ' z : ℂ) • leviRep F n A₁.obj.representation z v) =
      leviRep F n A₂.obj.representation z (E v) at key
    rw [hz A₁ h₁ z hz' v, hz A₂ h₂ z hz' (E v), map_smul, map_smul, smul_smul] at key
    have hmul := (smul_left_injective ℂ hEv key).trans (one_mul _).symm
    exact Units.ext (mul_right_cancel₀ (Units.ne_zero _) hmul)
  have hker : twistKernel F n ≤ χ'.ker := sup_le hχ' hcenter
  refine ⟨QuotientGroup.lift (twistKernel F n) χ' hker, ⟨?_⟩⟩
  have hφ : (QuotientGroup.lift (twistKernel F n) χ' hker).comp
      (QuotientGroup.mk' (twistKernel F n)) = χ' := by
    ext g
    rfl
  rw [hφ]
  exact E

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Two pullbacks of supercuspidal representations equivalent to the same twisted
representation of the one-block Levi have the same isomorphism class. -/
theorem isoClass_eq_of_twist_equiv (n : ℕ) {V₀ : Type uW} [AddCommGroup V₀] [Module ℂ V₀]
    (ρ₀ : Representation ℂ ((fullBlock n).Levi F) V₀)
    (φ : (fullBlock n).Levi F →* ℂˣ)
    (A₁ A₂ : SupercuspidalRep.{uF, uV} (F := F) (n := n + 1))
    (h₁ : Nonempty ((Langlands.twist φ ρ₀).Equiv (leviRep F n A₁.obj.representation)))
    (h₂ : Nonempty ((Langlands.twist φ ρ₀).Equiv (leviRep F n A₂.obj.representation))) :
    A₁.isoClass = A₂.isoClass := by
  obtain ⟨E₁⟩ := h₁
  obtain ⟨E₂⟩ := h₂
  let E := E₁.symm.trans E₂
  let E' : A₁.obj.representation.Equiv A₂.obj.representation :=
    Representation.Equiv.mk E.toLinearEquiv fun g => by
      obtain ⟨y, rfl⟩ := (fullBlock n).singleBlock_leviEmbedding_surjective rfl F g
      exact E.toIntertwiningMap.isIntertwining' y
  exact (SupercuspidalRep.isoClass_eq_iff A₁ A₂).mpr
    ⟨CategoryTheory.ObjectProperty.isoMk _ (SmoothRep.mkIso E')⟩

/-- Bernstein–Zelevinsky (1976), Corollary 4.15, over a nonarchimedean local field: fixing the central
character and a compact open subgroup leaves only finitely many supercuspidal classes
of `GL_(n+1)` with a nonzero fixed vector. -/
theorem centralFixedStratum_finite (n : ℕ)
    (χ : Subgroup.center (GeneralLinear (n + 1) F) →* ℂˣ)
    (N : OpenSubgroup (GeneralLinear (n + 1) F))
    (hN : IsCompact (N : Set (GeneralLinear (n + 1) F))) :
    (SupercuspidalClass.centralFixedStratum.{uF, uV} χ N.toSubgroup).Finite := by
  classical
  let s := SupercuspidalClass.centralFixedStratum.{uF, uV} χ N.toSubgroup
  rcases isEmpty_or_nonempty s with hs | hs
  · exact Set.toFinite s
  have hfin : (CompactCoefficientClass.fixedStratum.{uF, uV}
      (unitLevel F n N).toSubgroup).Finite :=
    compactCoefficientFixedLevelFiniteness.{uF, uV} F (LocalFieldData.ofInstances F) (n + 1)
      (Nat.succ_pos n) (fullBlock n) (unitLevel F n N) (isCompact_unitLevel F n N hN)
  have hrep : ∀ a : s, ∃ A : SupercuspidalRep.{uF, uV} (F := F) (n := n + 1),
      A.isoClass = a.val := fun a => Quotient.exists_rep a.val
  choose rep hrep using hrep
  have hmem : ∀ a : s, (rep a).obj.HasCentralCharacter χ ∧
      fixedVectors (rep a).obj.representation N.toSubgroup ≠ ⊥ := by
    intro a
    have h := a.property
    rw [← hrep a] at h
    exact h
  have hdata : ∀ a : s, ∃ c ∈ CompactCoefficientClass.fixedStratum.{uF, uV}
      (unitLevel F n N).toSubgroup, IsConstituent (isSmooth_unitRep F n (rep a).obj) c :=
    fun a => exists_isConstituent F n χ (rep a) (hmem a).1 (unitLevel F n N) (isCompact_unitLevel F n N hN)
      (fixedVectors_unitRep_ne_bot F n (rep a).obj N (hmem a).2)
  choose cl hcl hcon using hdata
  have htw : ∀ a : s, ∃ φ : twistQuotient F n →* ℂˣ,
      Nonempty ((Langlands.twist (φ.comp (QuotientGroup.mk' (twistKernel F n)))
        (leviRep F n (rep (Function.invFun cl (cl a))).obj.representation)).Equiv
          (leviRep F n (rep a).obj.representation)) := by
    intro a
    have hb : cl (Function.invFun cl (cl a)) = cl a := Function.invFun_eq ⟨a, rfl⟩
    have h₁ := hcon (Function.invFun cl (cl a))
    rw [hb] at h₁
    obtain ⟨f, hf⟩ := exists_ne_zero_of_isConstituent _ _ h₁ (hcon a)
    exact exists_twist_equiv F n χ _ _ (hmem _).1 (hmem a).1 f hf
  choose tw htw using htw
  let Φ : s → CompactCoefficientClass.fixedStratum.{uF, uV} (unitLevel F n N).toSubgroup ×
      (twistQuotient F n →* ℂˣ) := fun a => (⟨cl a, hcl a⟩, tw a)
  have hinj : Function.Injective Φ := by
    intro a a' h
    have h1 : cl a = cl a' := congrArg Subtype.val (congrArg Prod.fst h)
    have h2 : tw a = tw a' := congrArg Prod.snd h
    have k₁ := htw a
    have k₂ := htw a'
    rw [← h1, ← h2] at k₂
    have heq := isoClass_eq_of_twist_equiv F n _ _ _ _ k₁ k₂
    rw [hrep, hrep] at heq
    exact Subtype.ext heq
  have := hfin.to_subtype
  have := finite_twistQuotient F n
  have := finite_monoidHom_units (twistQuotient F n)
  have := Finite.of_injective Φ hinj
  exact Set.toFinite s

end Langlands.Henniart.AllFieldCompactOpenFiniteness

namespace Langlands.Henniart

universe uF uV

/-- Bernstein–Zelevinsky (1976), Corollary 4.15, at arbitrary independent field
and carrier universes, for every supplied nonarchimedean local-field structure. -/
theorem supercuspidalCompactOpenFiniteness :
    SupercuspidalCompactOpenFinitenessStatement.{uF, uV} :=
  fun F _ _ _ _ n χ N hN =>
    AllFieldCompactOpenFiniteness.centralFixedStratum_finite F n χ N hN

end Langlands.Henniart
