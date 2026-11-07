import Langlands.Shimura.DefiniteFormsTensor
import Langlands.Representation.Smooth.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients.Filtration

/-!
# Harris's tower of congruence subgroups `K_ℓ(n)`

Harris (1999, p.308) fixes "a lattice of normal congruence subgroups `K_ℓ(n) ⊂ K_ℓ`" with
`⋯ ⊃ K_ℓ(n) ⊃ K_ℓ(n+1) ⊃ ⋯` and `⋂_n K_ℓ(n) = {1}`, sets `K(n) = K_ℓ(n) × K^ℓ`, and takes a free
`𝒪/ℓ^m𝒪`-module `𝓛` of finite order with a continuous action of `K_ℓ` that factors through
`K_{ℓ,n} = K_ℓ/K_ℓ(n)`. This module records the tower and the facts about it used with (3.8).

## Main definitions and results

* `Langlands.CongruenceTower G`: a decreasing sequence of open normal subgroups of a topological
  group `G` with trivial intersection, extending the published
  `AntitoneNormalSubgroupFiltration`; `CongruenceTower.openLevel` is a member as an
  `OpenNormalSubgroup`.
* `CongruenceTower.exists_lower_subset`, `CongruenceTower.exists_lower_le`: in a compact group every
  open neighbourhood of `1`, in particular every open subgroup, contains some `K_ℓ(n)`.
* `CongruenceTower.isSmoothVector_iff`, `CongruenceTower.isSmooth_iff_iSup`: in a compact group the
  smooth vectors are those fixed by some `K_ℓ(n)`.
* `CongruenceTower.exists_lower_le_ker`, `CongruenceTower.isSmooth_iff_exists_lower_le_ker`: a
  representation of a compact group on a finitely generated module is smooth exactly when it is
  trivial on some `K_ℓ(n)`; `CongruenceTower.factorRep` is then the representation of
  `G ⧸ K_ℓ(n)`.
* In `Langlands.Shimura.DefiniteForms`: `isCompact_localLevel` (`K_ℓ` is compact for compact `K`),
  `isOpen_congruenceLevel`, `isCompact_congruenceLevel`, `antitone_congruenceLevel` and
  `iInf_congruenceLevel` (the levels `K(n)` are open, compact, decreasing, with intersection `K^ℓ`),
  `exists_lower_le_ker` (a smooth action of `K_ℓ` on a finitely generated module factors through
  some `K_{ℓ,n}`) and `smoothTensorEquiv` (Harris's (3.8) for such an action).
-/

noncomputable section

namespace Langlands

open Langlands.NYLL.RamificationTheory.DiscreteValuationField

universe uG uR uV

/-- Harris's tower `⋯ ⊃ K_ℓ(n) ⊃ K_ℓ(n+1) ⊃ ⋯` of open normal subgroups of a topological group
with trivial intersection: the published antitone filtration by normal subgroups, with open
members and `⋂_n K_ℓ(n) = {1}`. -/
structure CongruenceTower (G : Type uG) [Group G] [TopologicalSpace G]
    extends AntitoneNormalSubgroupFiltration G where
  /-- Every member of the tower is open. -/
  isOpen_lower : ∀ n : ℕ, IsOpen (lower n : Set G)
  /-- The members of the tower intersect in the trivial subgroup. -/
  iInf_lower : ⨅ n, lower n = ⊥

namespace CongruenceTower

variable {G : Type uG} [Group G] [TopologicalSpace G] (T : CongruenceTower G)

/-- `K_ℓ(n)` as an open normal subgroup. -/
def openLevel (n : ℕ) : OpenNormalSubgroup G where
  toSubgroup := T.lower n
  isOpen' := T.isOpen_lower n
  isNormal' := T.lower_normal n

@[simp]
lemma openLevel_toSubgroup (n : ℕ) : (T.openLevel n).toSubgroup = T.lower n :=
  rfl

lemma antitone_lower : Antitone T.lower :=
  fun _ _ h => T.antitone h

/-- An element lying in every `K_ℓ(n)` is trivial. -/
lemma eq_one_of_forall_mem {g : G} (hg : ∀ n, g ∈ T.lower n) : g = 1 := by
  have : g ∈ ⨅ n, T.lower n := Subgroup.mem_iInf.2 hg
  rwa [T.iInf_lower, Subgroup.mem_bot] at this

section Compact

variable [SeparatelyContinuousMul G] [CompactSpace G]

/-- In a compact group, every open neighbourhood of `1` contains some `K_ℓ(n)`. -/
theorem exists_lower_subset {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ n, (T.lower n : Set G) ⊆ U := by
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_family_closed
    (fun n => (T.lower n : Set G) ∩ Uᶜ)
    (fun n => ((T.lower n).isClosed_of_isOpen (T.isOpen_lower n)).inter hU.isClosed_compl)
    (by
      rw [Set.disjoint_iff]
      rintro g ⟨-, hg⟩
      simp only [Set.mem_iInter, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_compl_iff] at hg
      exact (hg 0).2 ((T.eq_one_of_forall_mem fun n => (hg n).1) ▸ h1))
    (fun m n => ⟨max m n,
      Set.inter_subset_inter_left _ (SetLike.coe_subset_coe.2 (T.antitone (le_max_left m n))),
      Set.inter_subset_inter_left _ (SetLike.coe_subset_coe.2 (T.antitone (le_max_right m n)))⟩)
  refine ⟨n, fun g hg => ?_⟩
  by_contra hgU
  exact Set.disjoint_left.1 hn (Set.mem_univ g) ⟨hg, hgU⟩

/-- In a compact group, every open subgroup contains some `K_ℓ(n)`. -/
theorem exists_lower_le (H : OpenSubgroup G) : ∃ n, T.lower n ≤ H.toSubgroup :=
  T.exists_lower_subset H.isOpen H.one_mem

end Compact

section Representation

variable {R : Type uR} {V : Type uV} [CommRing R] [AddCommGroup V] [Module R V]

/-- The vectors fixed by `K_ℓ(n)` increase with `n`. -/
lemma fixedVectors_mono (ρ : Representation R G V) :
    Monotone fun n => fixedVectors ρ (T.lower n) := by
  intro m n h v hv
  exact (Representation.mem_invariants _ v).2 fun g =>
    (Representation.mem_invariants _ v).1 hv ⟨g, T.antitone h g.2⟩

variable [SeparatelyContinuousMul G] [CompactSpace G]

/-- In a compact group, a vector is smooth exactly when it is fixed by some `K_ℓ(n)`. -/
theorem isSmoothVector_iff (ρ : Representation R G V) (v : V) :
    IsSmoothVector ρ v ↔ ∃ n, v ∈ fixedVectors ρ (T.lower n) := by
  constructor
  · rintro ⟨H, hv⟩
    obtain ⟨n, hn⟩ := T.exists_lower_le H
    exact ⟨n, (Representation.mem_invariants _ v).2 fun g =>
      (Representation.mem_invariants _ v).1 hv ⟨g, hn g.2⟩⟩
  · rintro ⟨n, hv⟩
    exact ⟨(T.openLevel n).toOpenSubgroup, hv⟩

/-- In a compact group, a representation is smooth exactly when it is the union of the vectors
fixed by the `K_ℓ(n)`. -/
theorem isSmooth_iff_iSup (ρ : Representation R G V) :
    IsSmooth ρ ↔ ⨆ n, fixedVectors ρ (T.lower n) = ⊤ := by
  rw [eq_top_iff]
  constructor
  · intro hρ v _
    obtain ⟨n, hn⟩ := (T.isSmoothVector_iff ρ v).1 (hρ v)
    exact Submodule.mem_iSup_of_mem n hn
  · intro h v
    have hv := h (Submodule.mem_top (x := v))
    rw [Submodule.mem_iSup_of_directed _ (T.fixedVectors_mono ρ).directed_le] at hv
    exact (T.isSmoothVector_iff ρ v).2 hv

/-- A smooth representation of a compact group on a finitely generated module is trivial on
some `K_ℓ(n)`: Harris's assumption that the action on `𝓛` factors through `K_ℓ ⧸ K_ℓ(n)` is
automatic. -/
theorem exists_lower_le_ker [Module.Finite R V] {ρ : Representation R G V} (hρ : IsSmooth ρ) :
    ∃ n, T.lower n ≤ ρ.ker := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := V)
  choose N hN using fun v => (T.isSmoothVector_iff ρ v).1 (hρ v)
  have htop : fixedVectors ρ (T.lower (s.sup N)) = ⊤ := by
    rw [eq_top_iff, ← hs, Submodule.span_le]
    intro v hv
    exact T.fixedVectors_mono ρ (Finset.le_sup hv) (hN v)
  refine ⟨s.sup N, fun g hg => MonoidHom.mem_ker.2 (LinearMap.ext fun v => ?_)⟩
  have hv : v ∈ fixedVectors ρ (T.lower (s.sup N)) := htop ▸ Submodule.mem_top
  exact (Representation.mem_invariants _ v).1 hv ⟨g, hg⟩

end Representation

section Factor

variable {R : Type uR} {V : Type uV} [CommRing R] [AddCommGroup V] [Module R V]
  {ρ : Representation R G V} {n : ℕ}

/-- A representation trivial on `K_ℓ(n)`, as a representation of `K_ℓ ⧸ K_ℓ(n)` (Harris's
`K_{ℓ,n}`). -/
def factorRep (hn : T.lower n ≤ ρ.ker) : Representation R (G ⧸ T.lower n) V :=
  QuotientGroup.lift (T.lower n) ρ hn

@[simp]
lemma factorRep_mk (hn : T.lower n ≤ ρ.ker) (g : G) :
    T.factorRep hn (g : G ⧸ T.lower n) = ρ g :=
  rfl

lemma factorRep_comp_mk' (hn : T.lower n ≤ ρ.ker) :
    (T.factorRep hn).comp (QuotientGroup.mk' (T.lower n)) = ρ :=
  QuotientGroup.lift_comp_mk' _ _ _

/-- A representation of `K_ℓ ⧸ K_ℓ(n)` inflated to `K_ℓ` is smooth. -/
theorem isSmooth_comp_mk' (n : ℕ) (ρ' : Representation R (G ⧸ T.lower n) V) :
    IsSmooth (ρ'.comp (QuotientGroup.mk' (T.lower n))) := fun v =>
  ⟨(T.openLevel n).toOpenSubgroup, (Representation.mem_invariants _ v).2 fun g => by
    have hg : (QuotientGroup.mk g.1 : G ⧸ T.lower n) = 1 := (QuotientGroup.eq_one_iff g.1).2 g.2
    exact (congrArg (fun q => ρ' q v) hg).trans (LinearMap.congr_fun (map_one ρ') v)⟩

/-- On a finitely generated module over a compact group, the smooth representations are those
that factor through some `K_ℓ ⧸ K_ℓ(n)`. -/
theorem isSmooth_iff_exists_lower_le_ker [SeparatelyContinuousMul G] [CompactSpace G]
    [Module.Finite R V] : IsSmooth ρ ↔ ∃ n, T.lower n ≤ ρ.ker := by
  refine ⟨T.exists_lower_le_ker, fun ⟨n, hn⟩ => ?_⟩
  rw [← T.factorRep_comp_mk' hn]
  exact T.isSmooth_comp_mk' n _

end Factor

end CongruenceTower

end Langlands

namespace Langlands.Shimura.DefiniteForms

open Langlands.Global Langlands.Shimura.EquivariantForms

universe v t uR

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (ℓ : FinitePlace ℚ) (K : Subgroup σ.FiniteAdelicPoints)

/-- The `ℓ`-component map `K → K_ℓ` is continuous. -/
lemma continuous_localLevelMap : Continuous (localLevelMap σ ℓ K) :=
  continuous_induced_rng.2 ((σ.finiteLocalMap ℓ).continuous.comp continuous_subtype_val)

/-- For compact `K`, the local level `K_ℓ` is compact. -/
lemma isCompact_localLevel (hK : IsCompact (K : Set σ.FiniteAdelicPoints)) :
    IsCompact (localLevel σ ℓ K : Set (σ.Points (FiniteCompletion ℚ ℓ))) := by
  rw [localLevel, Subgroup.coe_map]
  exact hK.image (σ.finiteLocalMap ℓ).continuous

lemma compactSpace_localLevel (hK : IsCompact (K : Set σ.FiniteAdelicPoints)) :
    CompactSpace (localLevel σ ℓ K) :=
  isCompact_iff_compactSpace.1 (isCompact_localLevel σ ℓ K hK)

variable {K}

/-- `K(n)` decreases with `K_ℓ(n)`. -/
lemma congruenceLevel_mono {H H' : Subgroup (localLevel σ ℓ K)} (h : H ≤ H') :
    congruenceLevel σ ℓ K H ≤ congruenceLevel σ ℓ K H' :=
  inf_le_inf_left _ (Subgroup.comap_mono (Subgroup.map_mono h))

/-- `K(n)` is the image in `GJ(𝔸^f)` of its trace on `K`. -/
lemma coe_congruenceLevel (H : Subgroup (localLevel σ ℓ K)) :
    (congruenceLevel σ ℓ K H : Set σ.FiniteAdelicPoints) =
      Subtype.val '' (((congruenceLevel σ ℓ K H).subgroupOf K : Subgroup K) : Set K) := by
  ext g
  constructor
  · intro hg
    exact ⟨⟨g, congruenceLevel_le σ ℓ K H hg⟩, hg, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact hk

/-- For an open subgroup `K` and an open subgroup `H` of `K_ℓ`, `K(n)` is open. -/
lemma isOpen_congruenceLevel (hK : IsOpen (K : Set σ.FiniteAdelicPoints))
    {H : Subgroup (localLevel σ ℓ K)} (hH : IsOpen (H : Set (localLevel σ ℓ K))) :
    IsOpen (congruenceLevel σ ℓ K H : Set σ.FiniteAdelicPoints) := by
  have h1 : IsOpen (((congruenceLevel σ ℓ K H).subgroupOf K : Subgroup K) : Set K) := by
    rw [congruenceLevel_subgroupOf]
    exact hH.preimage (continuous_localLevelMap σ ℓ K)
  rw [coe_congruenceLevel]
  exact hK.isOpenMap_subtype_val _ h1

/-- For a compact subgroup `K` and an open subgroup `H` of `K_ℓ`, `K(n)` is compact. -/
lemma isCompact_congruenceLevel (hK : IsCompact (K : Set σ.FiniteAdelicPoints))
    {H : Subgroup (localLevel σ ℓ K)} (hH : IsOpen (H : Set (localLevel σ ℓ K))) :
    IsCompact (congruenceLevel σ ℓ K H : Set σ.FiniteAdelicPoints) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have h1 : IsClosed (((congruenceLevel σ ℓ K H).subgroupOf K : Subgroup K) : Set K) := by
    rw [congruenceLevel_subgroupOf]
    exact (H.isClosed_of_isOpen hH).preimage (continuous_localLevelMap σ ℓ K)
  rw [coe_congruenceLevel]
  exact h1.isCompact.image continuous_subtype_val

variable (T : CongruenceTower (localLevel σ ℓ K))

/-- The levels `K(n)` decrease. -/
lemma antitone_congruenceLevel : Antitone fun n => congruenceLevel σ ℓ K (T.lower n) :=
  fun _ _ h => congruenceLevel_mono σ ℓ (T.antitone h)

/-- The levels `K(n)` intersect in `K^ℓ`. -/
lemma iInf_congruenceLevel : ⨅ n, congruenceLevel σ ℓ K (T.lower n) = primeToLevel σ ℓ K := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_iInf] at hg
    have hgK : g ∈ K := congruenceLevel_le σ ℓ K _ (hg 0)
    have hk : ∀ n, localLevelMap σ ℓ K ⟨g, hgK⟩ ∈ T.lower n := fun n => by
      have := (Subgroup.mem_subgroupOf (h := (⟨g, hgK⟩ : K))).2 (hg n)
      rw [congruenceLevel_subgroupOf] at this
      exact this
    exact ⟨hgK, congrArg Subtype.val (T.eq_one_of_forall_mem hk)⟩
  · exact le_iInf fun n => primeToLevel_le_congruenceLevel σ ℓ K _

variable {R : Type uR} [CommRing R] {V : Type t} [AddCommGroup V] [Module R V]
  {ρ : Representation R (localLevel σ ℓ K) V}

/-- For compact `K`, a smooth action of `K_ℓ` on a finitely generated module factors through
some `K_{ℓ,n} = K_ℓ ⧸ K_ℓ(n)`. -/
theorem exists_lower_le_ker (hK : IsCompact (K : Set σ.FiniteAdelicPoints)) [Module.Finite R V]
    (hρ : IsSmooth ρ) : ∃ n, T.lower n ≤ ρ.ker :=
  have := compactSpace_localLevel σ ℓ K hK
  T.exists_lower_le_ker hρ

/-- Harris's (3.8) for a finite free `𝓛` whose action of `K_ℓ` is trivial on `K_ℓ(n)`:
`[𝒜_ℓ(GJ, R, K(n)) ⊗ 𝓛]^{K_{ℓ,n}} ≃ 𝒜_ℓ(GJ, 𝓛, K)`, the published `congruenceTensorEquiv` for
the factored representation `factorRep`. -/
def smoothTensorEquiv [Module.Free R V] [Module.Finite R V] {n : ℕ} (hn : T.lower n ≤ ρ.ker) :
    Representation.invariants (k := R) (G := localLevel σ ℓ K ⧸ T.lower n)
      (V := congruenceTensorSpace σ ℓ K (T.lower n) (R := R) (V := V))
      (congruenceTensorAction σ ℓ K (T.lower n) (T.factorRep hn)) ≃ₗ[R]
      ellModuleForms σ ℓ K ρ :=
  congruenceTensorEquiv σ ℓ K (T.lower n) (T.factorRep hn)

end Langlands.Shimura.DefiniteForms
