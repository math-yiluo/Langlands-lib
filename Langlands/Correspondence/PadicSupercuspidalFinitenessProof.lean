import Langlands.Correspondence.SupercuspidalFinitenessStatement
import Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessProof
import Langlands.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.Representation.CuspidalSupport.CuspidalityComparisonProof
import Langlands.Representation.CuspidalSupport.DeterminantUnitFiniteRestriction
import Langlands.Representation.CuspidalSupport.NormKernelTwistAlgebra
import Langlands.Representation.CuspidalSupport.NormKernelTwistElementary
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.CuspidalSupport.LeviCompactPart
import Langlands.Representation.CompactCoefficient.ConditionalProjection
import Langlands.Representation.Compact.CharZeroAverage
import Langlands.Group.GL.OneBlockShape

/-!
# Bernstein–Zelevinsky finiteness of supercuspidal classes over p-adic fields

Bernstein–Zelevinsky (1976), Corollary 4.15, for `GL_(n+1)` over a p-adic field: for a
fixed central character and a fixed compact open subgroup `N`, only finitely many
supercuspidal classes have a nonzero `N`-fixed vector.

The argument is BZ76 §§3.20–3.29 and 4.14–4.16. The restriction of a supercuspidal
representation to the determinant-unit subgroup `G°` is a finite sum of irreducible
representations with compact coefficients (3.21, 3.26); a nonzero `N`-fixed vector
lands, after averaging, in one of them; these lie in a finite set by 4.14. Two
supercuspidal representations sharing such a constituent are twists of each other by
a character of the finite group `GL_(n+1) / G° Z` (3.29 and the central character).
-/

noncomputable section

namespace Langlands.Henniart.CompactOpenFiniteness

open GeneralLinear CuspidalSupport

universe uG uK uV uW

section Generic

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The inclusion of an invariant subspace, as an intertwiner. -/
def inclusion {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    S.toRepresentation.IntertwiningMap ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

/-- The projection onto an invariant subspace along an invariant complement, with the
subspace as codomain. -/
def projectionOnto {ρ : Representation ℂ G V} (S Q : Subrepresentation ρ)
    (h : IsCompl S.toSubmodule Q.toSubmodule) :
    ρ.IntertwiningMap S.toRepresentation where
  toLinearMap := S.toSubmodule.projectionOnto Q.toSubmodule h
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining ρ ρ (equivariantProjection S Q h) g v

/-- Complements in the lattice of subrepresentations are complements of submodules. -/
theorem isCompl_toSubmodule {ρ : Representation ℂ G V} {S Q : Subrepresentation ρ}
    (h : IsCompl S Q) : IsCompl S.toSubmodule Q.toSubmodule :=
  ⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule (disjoint_iff.mp h.1)),
    codisjoint_iff.mpr (congrArg Subrepresentation.toSubmodule (codisjoint_iff.mp h.2))⟩

/-- A nonzero complemented invariant subspace of `ρ` equivalent to an invariant
subspace of `σ` gives a nonzero intertwiner from `ρ` to `σ`. -/
theorem exists_ne_zero_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (S Q : Subrepresentation ρ) (h : IsCompl S.toSubmodule Q.toSubmodule)
    (S' : Subrepresentation σ) (E : S.toRepresentation.Equiv S'.toRepresentation)
    [Nontrivial S.toSubmodule] : ∃ f : ρ.IntertwiningMap σ, f ≠ 0 := by
  refine ⟨(inclusion S').comp (E.toIntertwiningMap.comp (projectionOnto S Q h)), ?_⟩
  intro hf
  obtain ⟨w, hw⟩ := exists_ne (0 : S.toSubmodule)
  have hw' := congrArg (fun f : ρ.IntertwiningMap σ => f (w : V)) hf
  change ((E (S.toSubmodule.projectionOnto Q.toSubmodule h (w : V)) : S'.toSubmodule) : W) =
    0 at hw'
  rw [Submodule.projectionOnto_apply_left, ZeroMemClass.coe_eq_zero] at hw'
  exact hw (E.injective (hw'.trans (map_zero E).symm))

/-- A finite group has finitely many characters with values in `ℂˣ`. -/
theorem finite_monoidHom_units (Q : Type uG) [Group Q] [Finite Q] : Finite (Q →* ℂˣ) := by
  have : NeZero (Nat.card Q) := ⟨Nat.card_pos.ne'⟩
  let f : (Q →* ℂˣ) → (Q → rootsOfUnity (Nat.card Q) ℂ) := fun φ q =>
    ⟨φ q, by rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]⟩
  refine Finite.of_injective f ?_
  intro φ ψ h
  apply MonoidHom.ext
  intro q
  exact congrArg Subtype.val (congrFun h q)

variable [TopologicalSpace G]

/-- Invariant subspaces of smooth representations are smooth. -/
theorem isSmooth_subrepresentation {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (S : Subrepresentation ρ) : IsSmooth S.toRepresentation :=
  isSmooth_of_injective (inclusion S) Subtype.val_injective hρ

/-- If finitely many invariant subspaces span a smooth representation with a nonzero
vector fixed by a compact open subgroup, then one of them has such a vector: the
averaging projection would otherwise vanish on each of them. -/
theorem exists_fixedVectors_ne_bot [IsTopologicalGroup G] {ρ : Representation ℂ G V}
    (hρ : IsSmooth ρ) (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) {m : ℕ}
    (S : Fin m → Subrepresentation ρ) (hS : ⨆ i, (S i).toSubmodule = ⊤)
    (hfix : fixedVectors ρ L.toSubgroup ≠ ⊥) :
    ∃ i, fixedVectors (S i).toRepresentation L.toSubgroup ≠ ⊥ := by
  by_contra hne
  push Not at hne
  apply hfix
  let P := Compact.CharZero.averageMap ρ hρ L hL
  have hle : ∀ i, (S i).toSubmodule ≤ LinearMap.ker P := by
    intro i w hw
    have hsm := isSmooth_subrepresentation hρ (S i)
    have hc := LinearMap.congr_fun
      (Compact.CharZero.averageMap_commute _ ρ hsm hρ L hL (inclusion (S i))) ⟨w, hw⟩
    have hmem := Compact.CharZero.averageMap_mem_fixedVectors _ hsm L hL ⟨w, hw⟩
    rw [hne i, Submodule.mem_bot] at hmem
    rw [LinearMap.mem_ker]
    change ((Compact.CharZero.averageMap _ hsm L hL ⟨w, hw⟩ : (S i).toSubmodule) : V) =
      P w at hc
    rw [← hc, hmem]
    rfl
  have htop : (⊤ : Submodule ℂ V) ≤ LinearMap.ker P := by
    rw [← hS]
    exact iSup_le hle
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot, ← Compact.CharZero.averageMap_id ρ hρ L hL v hv]
  exact htop Submodule.mem_top

/-- `c` is the class of an irreducible invariant subspace of `ρ` with compact
coefficients and an invariant complement. -/
def IsConstituent {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (c : CompactCoefficientClass.{uG, uV} G) : Prop :=
  ∃ (S Q : Subrepresentation ρ) (_ : IsCompl S.toSubmodule Q.toSubmodule)
    (hirr : S.toRepresentation.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients S.toRepresentation),
    CompactCoefficientClass.ofRep
      ⟨SmoothRep.of S.toRepresentation (isSmooth_subrepresentation hρ S), hirr, hc⟩ = c

/-- Two smooth representations with a common constituent class admit a nonzero
intertwiner. -/
theorem exists_ne_zero_of_isConstituent {V' : Type uV} [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ G V} {σ : Representation ℂ G V'} (hρ : IsSmooth ρ)
    (hσ : IsSmooth σ) {c : CompactCoefficientClass.{uG, uV} G}
    (h₁ : IsConstituent hρ c) (h₂ : IsConstituent hσ c) :
    ∃ f : ρ.IntertwiningMap σ, f ≠ 0 := by
  obtain ⟨S, Q, hSQ, hirr, hc, rfl⟩ := h₁
  obtain ⟨S', -, -, hirr', hc', h⟩ := h₂
  obtain ⟨i⟩ := (CompactCoefficientClass.ofRep_eq_iff _ _).mp h.symm
  have := nontrivial_of_isIrreducible S.toRepresentation (hρ := hirr)
  exact exists_ne_zero_of_equiv S Q hSQ S'
    (SmoothRep.equivOfIso ((irreducibleCompactCoefficientProperty G).ι.mapIso i))

end Generic

section Padic

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

local instance padicFinitenessTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance padicFinitenessValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance padicFinitenessLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

/-- The one-block shape of rank `n + 1`; its Levi subgroup is `GL_(n+1)`. -/
abbrev fullBlock (n : ℕ) : BlockShape (n + 1) :=
  LeviAdmissibility.oneBlock (n + 1) (Nat.succ_pos n)

local instance padicFinitenessLeviTopologicalGroup (n : ℕ) :
    IsTopologicalGroup ((fullBlock n).Levi K.Carrier) :=
  K.canonicalTopologicalData.leviTopologicalGroup (fullBlock n)

/-- BZ76's `G°` in the one-block Levi: determinant of normalized absolute value one. -/
abbrev unitGroup (n : ℕ) : Subgroup ((fullBlock n).Levi K.Carrier) :=
  determinantUnitSubgroup K.canonicalTopologicalData (fullBlock n)

/-- The pullback of a representation of `GL_(n+1)` to the one-block Levi. -/
abbrev leviRep (n : ℕ) (ρ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) :
    Representation ℂ ((fullBlock n).Levi K.Carrier) V :=
  ρ.comp ((fullBlock n).leviEmbedding K.Carrier)

/-- The restriction of a representation of `GL_(n+1)` to `G°`. -/
abbrev unitRep (n : ℕ) (ρ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) :
    Representation ℂ (unitGroup K n) V :=
  determinantUnitRestriction K.canonicalTopologicalData (fullBlock n) (leviRep K n ρ)

/-- `G° Z` in the one-block Levi. -/
abbrev twistKernel (n : ℕ) : Subgroup ((fullBlock n).Levi K.Carrier) :=
  unitGroup K n ⊔ Subgroup.center ((fullBlock n).Levi K.Carrier)

/-- The finite abelian quotient `GL_(n+1) / G° Z` (BZ76 3.20). -/
abbrev twistQuotient (n : ℕ) := (fullBlock n).Levi K.Carrier ⧸ twistKernel K n

theorem finite_twistQuotient (n : ℕ) : Finite (twistQuotient K n) := by
  have := determinantUnit_sup_center_finiteIndex K.canonicalTopologicalData (fullBlock n)
  infer_instance

/-- The compact open subgroup of `G°` cut out by an open subgroup of `GL_(n+1)`. -/
def unitLevel (n : ℕ) (N : OpenSubgroup (GeneralLinear (n + 1) K.Carrier)) :
    OpenSubgroup (unitGroup K n) :=
  OpenSubgroup.comap (unitGroup K n).subtype continuous_subtype_val
    (OpenSubgroup.comap ((fullBlock n).leviEmbedding K.Carrier)
      ((fullBlock n).leviEmbeddingContinuous K.Carrier).continuous N)

theorem isCompact_unitLevel (n : ℕ) (N : OpenSubgroup (GeneralLinear (n + 1) K.Carrier))
    (hN : IsCompact (N : Set (GeneralLinear (n + 1) K.Carrier))) :
    IsCompact (unitLevel K n N : Set (unitGroup K n)) := by
  have hL : IsCompact (((fullBlock n).leviEmbedding K.Carrier) ⁻¹'
      (N : Set (GeneralLinear (n + 1) K.Carrier))) :=
    ((fullBlock n).singleBlockLeviEquivContinuous rfl K.Carrier).toHomeomorph.isCompact_preimage.mpr
      hN
  have hclosed : IsClosed (unitGroup K n : Set ((fullBlock n).Levi K.Carrier)) :=
    (determinantUnitOpenSubgroup K.canonicalTopologicalData (fullBlock n)).isClosed
  exact hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hL

theorem isSmooth_leviRep (n : ℕ)
    (A : SmoothRep.{0, uK, uV} ℂ (GeneralLinear (n + 1) K.Carrier)) :
    IsSmooth (leviRep K n A.representation) :=
  isSmooth_comp _ ((fullBlock n).leviEmbeddingContinuous K.Carrier).continuous A.isSmooth

theorem isSmooth_unitRep (n : ℕ)
    (A : SmoothRep.{0, uK, uV} ℂ (GeneralLinear (n + 1) K.Carrier)) :
    IsSmooth (unitRep K n A.representation) :=
  isSmooth_comp _ continuous_subtype_val (isSmooth_leviRep K n A)

theorem isIrreducible_leviRep (n : ℕ)
    (A : SmoothRep.{0, uK, uV} ℂ (GeneralLinear (n + 1) K.Carrier)) (hA : A.IsIrreducible) :
    (leviRep K n A.representation).IsIrreducible := by
  have := hA
  exact isIrreducible_comp_of_surjective A.representation _
    ((fullBlock n).singleBlock_leviEmbedding_surjective rfl K.Carrier)

/-- The one-block embedding maps the centre of the Levi into the centre of `GL_(n+1)`. -/
theorem leviEmbedding_mem_center (n : ℕ) {z : (fullBlock n).Levi K.Carrier}
    (hz : z ∈ Subgroup.center ((fullBlock n).Levi K.Carrier)) :
    (fullBlock n).leviEmbedding K.Carrier z ∈
      Subgroup.center (GeneralLinear (n + 1) K.Carrier) := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨y, rfl⟩ := (fullBlock n).singleBlock_leviEmbedding_surjective rfl K.Carrier g
  rw [← map_mul, ← map_mul, hz y]

/-- A vector fixed by `N` is fixed by the corresponding subgroup of `G°`. -/
theorem fixedVectors_unitRep_ne_bot (n : ℕ)
    (A : SmoothRep.{0, uK, uV} ℂ (GeneralLinear (n + 1) K.Carrier))
    (N : OpenSubgroup (GeneralLinear (n + 1) K.Carrier))
    (hfix : fixedVectors A.representation N.toSubgroup ≠ ⊥) :
    fixedVectors (unitRep K n A.representation) (unitLevel K n N).toSubgroup ≠ ⊥ := by
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
    (A : SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := n + 1))
    (L : OpenSubgroup (unitGroup K n)) (hL : IsCompact (L : Set (unitGroup K n)))
    (hfix : fixedVectors (unitRep K n A.obj.representation) L.toSubgroup ≠ ⊥) :
    ∃ c ∈ CompactCoefficientClass.fixedStratum.{uK, uV} L.toSubgroup,
      IsConstituent (isSmooth_unitRep K n A.obj) c := by
  let D : SmoothRep.{0, uK, uV} ℂ ((fullBlock n).Levi K.Carrier) :=
    SmoothRep.of (leviRep K n A.obj.representation) (isSmooth_leviRep K n A.obj)
  have hD : D.IsIrreducible := isIrreducible_leviRep K n A.obj A.property.1
  have hquasi : IsLeviQuasicuspidal (fullBlock n) D.representation :=
    ((singleBlockCuspidalityClause K.canonicalTopologicalData (n + 1) (fullBlock n) rfl _
      A.obj.representation).mpr A.property.2).2
  have hcoef : HasCompactSmoothDualCoefficients (unitRep K n A.obj.representation) :=
    (leviHarishChandraTheorem p K K.canonicalTopologicalData (n + 1) (fullBlock n) D).mp hquasi
  obtain ⟨hsemi, m, S, hS, hspan⟩ :=
    FiniteRestriction.leviFiniteRestriction K K.canonicalTopologicalData (fullBlock n) D hD
  have hsm := isSmooth_unitRep K n A.obj
  obtain ⟨i, hi⟩ := exists_fixedVectors_ne_bot hsm L hL S hspan hfix
  have := hsemi
  obtain ⟨Q, hQ⟩ := exists_isCompl (S i)
  have hc : HasCompactSmoothDualCoefficients (S i).toRepresentation :=
    hasCompactSmoothDualCoefficients_subrepresentation
      (determinantUnitCompactOpenCofinal K.canonicalTopologicalData (fullBlock n))
      (SmoothRep.of _ hsm) hcoef (S i)
  exact ⟨CompactCoefficientClass.ofRep
      ⟨SmoothRep.of (S i).toRepresentation (isSmooth_subrepresentation hsm (S i)), hS i, hc⟩,
    hi, S i, Q, isCompl_toSubmodule hQ, hS i, hc, rfl⟩

/-- BZ76 3.29 with central characters: supercuspidal representations with the same
central character and a nonzero intertwiner between their restrictions to `G°` differ by
a twist by a character of `GL_(n+1) / G° Z`. -/
theorem exists_twist_equiv (n : ℕ)
    (χ : Subgroup.center (GeneralLinear (n + 1) K.Carrier) →* ℂˣ)
    (A₁ A₂ : SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := n + 1))
    (h₁ : A₁.obj.HasCentralCharacter χ) (h₂ : A₂.obj.HasCentralCharacter χ)
    (f : (unitRep K n A₁.obj.representation).IntertwiningMap
      (unitRep K n A₂.obj.representation)) (hf : f ≠ 0) :
    ∃ φ : twistQuotient K n →* ℂˣ,
      Nonempty ((Langlands.twist (φ.comp (QuotientGroup.mk' (twistKernel K n)))
        (leviRep K n A₁.obj.representation)).Equiv (leviRep K n A₂.obj.representation)) := by
  have := determinantUnit_sup_center_finiteIndex K.canonicalTopologicalData (fullBlock n)
  have hcomm : commutator ((fullBlock n).Levi K.Carrier) ≤ unitGroup K n :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      ⟨⟨determinantUnitQuotient_mul_comm K.canonicalTopologicalData (fullBlock n)⟩⟩
  have hz : ∀ (A : SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := n + 1)),
      A.obj.HasCentralCharacter χ → ∀ (z : (fullBlock n).Levi K.Carrier)
        (hz : z ∈ Subgroup.center ((fullBlock n).Levi K.Carrier)) (v : A.obj),
        leviRep K n A.obj.representation z v =
          (χ ⟨_, leviEmbedding_mem_center K n hz⟩ : ℂ) • v :=
    fun A hA z hz v => hA ⟨_, leviEmbedding_mem_center K n hz⟩ v
  obtain ⟨χ', hχ', t, ht⟩ := exists_twistIntertwiningMap_of_restrictedHom_nonzero
    (leviRep K n A₁.obj.representation) (leviRep K n A₂.obj.representation) (unitGroup K n)
    hcomm (fun z => ⟨_, hz A₁ h₁ z z.property⟩) (fun z => ⟨_, hz A₂ h₂ z z.property⟩) f hf
  let E := twistEquivOfNonzeroIntertwiner _ _ (isIrreducible_leviRep K n A₁.obj A₁.property.1)
    (isIrreducible_leviRep K n A₂.obj A₂.property.1) χ' t ht
  have hcenter : Subgroup.center ((fullBlock n).Levi K.Carrier) ≤ χ'.ker := by
    intro z hz'
    rw [MonoidHom.mem_ker]
    have : Nontrivial A₁.obj :=
      nontrivial_of_isIrreducible A₁.obj.representation (hρ := A₁.property.1)
    obtain ⟨v, hv⟩ := exists_ne (0 : A₁.obj)
    have hEv : E v ≠ 0 := fun h => hv (E.injective (h.trans (map_zero E).symm))
    have key := Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap z v
    change E ((χ' z : ℂ) • leviRep K n A₁.obj.representation z v) =
      leviRep K n A₂.obj.representation z (E v) at key
    rw [hz A₁ h₁ z hz' v, hz A₂ h₂ z hz' (E v), map_smul, map_smul, smul_smul] at key
    have hmul := (smul_left_injective ℂ hEv key).trans (one_mul _).symm
    exact Units.ext (mul_right_cancel₀ (Units.ne_zero _) hmul)
  have hker : twistKernel K n ≤ χ'.ker := sup_le hχ' hcenter
  refine ⟨QuotientGroup.lift (twistKernel K n) χ' hker, ⟨?_⟩⟩
  have hφ : (QuotientGroup.lift (twistKernel K n) χ' hker).comp
      (QuotientGroup.mk' (twistKernel K n)) = χ' := by
    ext g
    rfl
  rw [hφ]
  exact E

/-- Two pullbacks of supercuspidal representations equivalent to the same twisted
representation of the one-block Levi have the same isomorphism class. -/
theorem isoClass_eq_of_twist_equiv (n : ℕ) {V₀ : Type uW} [AddCommGroup V₀] [Module ℂ V₀]
    (ρ₀ : Representation ℂ ((fullBlock n).Levi K.Carrier) V₀)
    (φ : (fullBlock n).Levi K.Carrier →* ℂˣ)
    (A₁ A₂ : SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := n + 1))
    (h₁ : Nonempty ((Langlands.twist φ ρ₀).Equiv (leviRep K n A₁.obj.representation)))
    (h₂ : Nonempty ((Langlands.twist φ ρ₀).Equiv (leviRep K n A₂.obj.representation))) :
    A₁.isoClass = A₂.isoClass := by
  obtain ⟨E₁⟩ := h₁
  obtain ⟨E₂⟩ := h₂
  let E := E₁.symm.trans E₂
  let E' : A₁.obj.representation.Equiv A₂.obj.representation :=
    Representation.Equiv.mk E.toLinearEquiv fun g => by
      obtain ⟨y, rfl⟩ := (fullBlock n).singleBlock_leviEmbedding_surjective rfl K.Carrier g
      exact E.toIntertwiningMap.isIntertwining' y
  exact (SupercuspidalRep.isoClass_eq_iff A₁ A₂).mpr
    ⟨CategoryTheory.ObjectProperty.isoMk _ (SmoothRep.mkIso E')⟩

/-- Bernstein–Zelevinsky (1976), Corollary 4.15, over a p-adic field: fixing the central
character and a compact open subgroup leaves only finitely many supercuspidal classes
of `GL_(n+1)` with a nonzero fixed vector. -/
theorem centralFixedStratum_finite (n : ℕ)
    (χ : Subgroup.center (GeneralLinear (n + 1) K.Carrier) →* ℂˣ)
    (N : OpenSubgroup (GeneralLinear (n + 1) K.Carrier))
    (hN : IsCompact (N : Set (GeneralLinear (n + 1) K.Carrier))) :
    (SupercuspidalClass.centralFixedStratum.{uK, uV} χ N.toSubgroup).Finite := by
  classical
  let s := SupercuspidalClass.centralFixedStratum.{uK, uV} χ N.toSubgroup
  rcases isEmpty_or_nonempty s with hs | hs
  · exact Set.toFinite s
  have hfin : (CompactCoefficientClass.fixedStratum.{uK, uV}
      (unitLevel K n N).toSubgroup).Finite :=
    compactCoefficientFixedLevelFiniteness.{uK, uV} p K K.canonicalTopologicalData (n + 1)
      (Nat.succ_pos n) (fullBlock n) (unitLevel K n N) (isCompact_unitLevel K n N hN)
  have hrep : ∀ a : s, ∃ A : SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := n + 1),
      A.isoClass = a.val := fun a => Quotient.exists_rep a.val
  choose rep hrep using hrep
  have hmem : ∀ a : s, (rep a).obj.HasCentralCharacter χ ∧
      fixedVectors (rep a).obj.representation N.toSubgroup ≠ ⊥ := by
    intro a
    have h := a.property
    rw [← hrep a] at h
    exact h
  have hdata : ∀ a : s, ∃ c ∈ CompactCoefficientClass.fixedStratum.{uK, uV}
      (unitLevel K n N).toSubgroup, IsConstituent (isSmooth_unitRep K n (rep a).obj) c :=
    fun a => exists_isConstituent K n (rep a) (unitLevel K n N) (isCompact_unitLevel K n N hN)
      (fixedVectors_unitRep_ne_bot K n (rep a).obj N (hmem a).2)
  choose cl hcl hcon using hdata
  have htw : ∀ a : s, ∃ φ : twistQuotient K n →* ℂˣ,
      Nonempty ((Langlands.twist (φ.comp (QuotientGroup.mk' (twistKernel K n)))
        (leviRep K n (rep (Function.invFun cl (cl a))).obj.representation)).Equiv
          (leviRep K n (rep a).obj.representation)) := by
    intro a
    have hb : cl (Function.invFun cl (cl a)) = cl a := Function.invFun_eq ⟨a, rfl⟩
    have h₁ := hcon (Function.invFun cl (cl a))
    rw [hb] at h₁
    obtain ⟨f, hf⟩ := exists_ne_zero_of_isConstituent _ _ h₁ (hcon a)
    exact exists_twist_equiv K n χ _ _ (hmem _).1 (hmem a).1 f hf
  choose tw htw using htw
  let Φ : s → CompactCoefficientClass.fixedStratum.{uK, uV} (unitLevel K n N).toSubgroup ×
      (twistQuotient K n →* ℂˣ) := fun a => (⟨cl a, hcl a⟩, tw a)
  have hinj : Function.Injective Φ := by
    intro a a' h
    have h1 : cl a = cl a' := congrArg Subtype.val (congrArg Prod.fst h)
    have h2 : tw a = tw a' := congrArg Prod.snd h
    have k₁ := htw a
    have k₂ := htw a'
    rw [← h1, ← h2] at k₂
    have heq := isoClass_eq_of_twist_equiv K n _ _ _ _ k₁ k₂
    rw [hrep, hrep] at heq
    exact Subtype.ext heq
  have := hfin.to_subtype
  have := finite_twistQuotient K n
  have := finite_monoidHom_units (twistQuotient K n)
  have := Finite.of_injective Φ hinj
  exact Set.toFinite s

/-- The bounded-level form: fixing the central character and bounding the first level
with nonzero fixed vectors leaves only finitely many supercuspidal classes. -/
theorem centralLevelStratum_finite (n : ℕ)
    (χ : Subgroup.center (GeneralLinear (n + 1) K.Carrier) →* ℂˣ) (b : ℕ) :
    (SupercuspidalClass.centralLevelStratum.{uK, uV} χ b).Finite := by
  rw [SupercuspidalClass.centralLevelStratum_eq χ b]
  exact centralFixedStratum_finite K n χ (Conductor.levelOpenSubgroup K.Carrier n b)
    (Conductor.isCompact_levelOpenSubgroup K.Carrier n b)

end Padic

/-- Bernstein–Zelevinsky (1976), Corollary 4.15, for `GL_(n+1)` over every p-adic field
with its canonical topology: fixing the central character and a compact open subgroup
leaves only finitely many supercuspidal classes with a nonzero fixed vector. -/
def PadicSupercuspidalCompactOpenFinitenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p),
    letI := K.canonicalTopologicalData.topology
    letI := K.canonicalTopologicalData.valuativeRel
    letI := K.canonicalTopologicalData.localField
    ∀ (n : ℕ) (χ : Subgroup.center (GeneralLinear (n + 1) K.Carrier) →* ℂˣ)
      (N : OpenSubgroup (GeneralLinear (n + 1) K.Carrier)),
      IsCompact (N : Set (GeneralLinear (n + 1) K.Carrier)) →
        (SupercuspidalClass.centralFixedStratum.{uK, uV} χ N.toSubgroup).Finite

/-- Proof of `PadicSupercuspidalCompactOpenFinitenessStatement`. -/
theorem padicSupercuspidalCompactOpenFiniteness :
    PadicSupercuspidalCompactOpenFinitenessStatement.{uK, uV} :=
  fun _ _ K n χ N hN => centralFixedStratum_finite K n χ N hN

end Langlands.Henniart.CompactOpenFiniteness
