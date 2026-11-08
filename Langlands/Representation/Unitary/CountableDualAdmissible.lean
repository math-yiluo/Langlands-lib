import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.FiniteVectors
import Langlands.Representation.Unitary.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Dimension.ErdosKaplansky
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Cardinality

/-! # Irreducible admissible subrepresentations from a countable smooth dual -/

noncomputable section

universe uG uK uV

set_option autoImplicit false

namespace Langlands.CountableDual

open scoped MonoidAlgebra
open Module Langlands.FiniteVectors Cardinal

section Form

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V)

theorem inner_add_right (x y z : V) : c.inner x (y + z) = c.inner x y + c.inner x z := by
  have h := congrArg (starRingEnd ℂ) (c.add_left y z x)
  rwa [map_add, c.conj_inner_symm, c.conj_inner_symm, c.conj_inner_symm] at h

theorem inner_smul_right (x y : V) (r : ℂ) : c.inner x (r • y) = r * c.inner x y := by
  have h := congrArg (starRingEnd ℂ) (c.smul_left y x r)
  rwa [map_mul, Complex.conj_conj, c.conj_inner_symm, c.conj_inner_symm] at h

/-- Pairing against a fixed left vector, which is complex linear in the right variable. -/
def rightFunctional (y : V) : V →ₗ[ℂ] ℂ where
  toFun := c.inner y
  map_add' := inner_add_right c y
  map_smul' r x := inner_smul_right c y x r

@[simp] theorem rightFunctional_apply (y x : V) : rightFunctional c y x = c.inner y x := rfl

theorem inner_zero_right (x : V) : c.inner x 0 = 0 := (rightFunctional c x).map_zero

theorem inner_eq_zero_symm (x y : V) (h : c.inner y x = 0) : c.inner x y = 0 := by
  rw [← c.conj_inner_symm, h, map_zero]

/-- The right orthogonal of a complex subspace. -/
def orth (q : Submodule ℂ V) : Submodule ℂ V where
  carrier := {x | ∀ y ∈ q, c.inner y x = 0}
  add_mem' {x x'} hx hx' y hy := by
    change c.inner y (x + x') = 0
    rw [inner_add_right, hx y hy, hx' y hy, add_zero]
  zero_mem' y _ := inner_zero_right c y
  smul_mem' r x hx y hy := by
    change c.inner y (r • x) = 0
    rw [inner_smul_right, hx y hy, mul_zero]

theorem mem_orth {q : Submodule ℂ V} {x : V} :
    x ∈ orth c q ↔ ∀ y ∈ q, c.inner y x = 0 := Iff.rfl

theorem inf_orth (q : Submodule ℂ V) : q ⊓ orth c q = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hq, ho⟩
  exact (Submodule.mem_bot ℂ).mpr (c.definite x (ho x hq))

/-- Orthogonality to a basis gives orthogonality to its span. -/
theorem mem_orth_of_basis (q : Submodule ℂ V) {ι : Type*} (bq : Basis ι ℂ q) (x : V)
    (hx : ∀ j, c.inner (bq j : V) x = 0) : x ∈ orth c q := by
  intro y hy
  apply inner_eq_zero_symm
  have h0 : (rightFunctional c x).comp q.subtype = 0 := bq.ext fun j => by
    simpa using inner_eq_zero_symm c x (bq j : V) (hx j)
  exact LinearMap.congr_fun h0 ⟨y, hy⟩

/-- A finite-dimensional subspace and its right orthogonal span the whole space. -/
theorem sup_orth (q : Submodule ℂ V) [FiniteDimensional ℂ q] : q ⊔ orth c q = ⊤ := by
  let bq := Module.finBasis ℂ q
  let T : V →ₗ[ℂ] (Fin (finrank ℂ q) → ℂ) := LinearMap.pi fun j => rightFunctional c (bq j : V)
  have hinj : Function.Injective (T ∘ₗ q.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hyo : (y : V) ∈ orth c q := mem_orth_of_basis c q bq y fun j => congrFun hy j
    rw [Submodule.mem_bot]
    exact Subtype.ext (c.definite _ (hyo y y.2))
  have hsurj : Function.Surjective (T ∘ₗ q.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ := hsurj (T x)
  have hxy : x - (y : V) ∈ orth c q := by
    apply mem_orth_of_basis c q bq
    intro j
    have hj : rightFunctional c (bq j : V) (y : V) = rightFunctional c (bq j : V) x :=
      congrFun hy j
    change rightFunctional c (bq j : V) (x - y) = 0
    rw [map_sub, hj, sub_self]
  have hx : x = (y : V) + (x - y) := by abel
  rw [hx]
  exact Submodule.add_mem_sup y.2 hxy

end Form

section CompactSide

variable {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (κ : Representation ℂ K V) (c : InnerProductSpace.Core ℂ V)

theorem orth_stable (hc : ∀ k x y, c.inner (κ k x) (κ k y) = c.inner x y)
    (q : Submodule ℂ V) (hq : ∀ k, ∀ v ∈ q, κ k v ∈ q) :
    ∀ k, ∀ v ∈ orth c q, κ k v ∈ orth c q := by
  intro k v hv y hy
  have h := hc k (κ k⁻¹ y) v
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  rw [h]
  exact hv _ (hq k⁻¹ y hy)

/-- The group-algebra module structure on the original carrier. -/
abbrev algModule : Module ℂ[K] V := inferInstanceAs (Module ℂ[K] κ.asModule)

variable [Module ℂ[K] V] [IsScalarTower ℂ ℂ[K] V]
  (hmod : ∀ k v, MonoidAlgebra.of ℂ K k • v = κ k v)

include hmod in
theorem single_smul (k : K) (a : ℂ) (v : V) :
    MonoidAlgebra.single k a • v = a • κ k v := by
  have h : MonoidAlgebra.single k a = a • MonoidAlgebra.of ℂ K k := by
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single]
  rw [h, smul_assoc, hmod]

/-- A subspace stable under the group as a group-algebra submodule. -/
def toAlg (p : Submodule ℂ V) (hp : ∀ k, ∀ v ∈ p, κ k v ∈ p) : Submodule ℂ[K] V where
  carrier := p
  add_mem' := p.add_mem
  zero_mem' := p.zero_mem
  smul_mem' r v hv := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => rw [zero_smul]; exact p.zero_mem
    | add r s hr hs => rw [add_smul]; exact p.add_mem hr hs
    | single k a => rw [single_smul κ hmod]; exact p.smul_mem a (hp k v hv)

@[simp] theorem mem_toAlg (p : Submodule ℂ V) (hp : ∀ k, ∀ v ∈ p, κ k v ∈ p) (v : V) :
    v ∈ toAlg κ hmod p hp ↔ v ∈ p := Iff.rfl

include hmod in
theorem alg_stable (N : Submodule ℂ[K] V) :
    ∀ k, ∀ v ∈ N.restrictScalars ℂ, κ k v ∈ N.restrictScalars ℂ := fun k v hv => by
  rw [← hmod]
  exact N.smul_mem _ hv

include hmod in
/-- A finite group-stable vector-wise representation with an invariant positive form is a
semisimple group-algebra module. -/
theorem isSemisimpleModule (hc : ∀ k x y, c.inner (κ k x) (κ k y) = c.inner x y)
    (hfin : ∀ v : V, IsFiniteVector κ v) : IsSemisimpleModule ℂ[K] V := by
  let p : V → Submodule ℂ[K] V := fun v => toAlg κ hmod (orbitSpan κ v)
    (fun k w hw => (orbitSubrepresentation κ v).apply_mem_toSubmodule k hw)
  apply isSemisimpleModule_of_isSemisimpleModule_submodule' (p := p)
  · intro v
    have hv : FiniteDimensional ℂ (orbitSpan κ v) := hfin v
    rw [isSemisimpleModule_iff, (p v).mapIic.complementedLattice_iff]
    refine ⟨fun a => ?_⟩
    obtain ⟨a, ha⟩ := a
    have hale : a.restrictScalars ℂ ≤ orbitSpan κ v := ha
    have : FiniteDimensional ℂ (a.restrictScalars ℂ) := Submodule.finiteDimensional_of_le hale
    let o := toAlg κ hmod (orth c (a.restrictScalars ℂ))
      (orth_stable κ c hc _ (alg_stable κ hmod a))
    refine ⟨⟨o ⊓ p v, Set.mem_Iic.mpr inf_le_right⟩, ?_, ?_⟩
    · rw [disjoint_iff]
      apply Subtype.ext
      change a ⊓ (o ⊓ p v) = ⊥
      rw [eq_bot_iff]
      rintro x ⟨hxa, hxo, _⟩
      have hx : x ∈ a.restrictScalars ℂ ⊓ orth c (a.restrictScalars ℂ) := ⟨hxa, hxo⟩
      rw [inf_orth] at hx
      exact (Submodule.mem_bot ℂ).mp hx ▸ Submodule.zero_mem _
    · rw [codisjoint_iff]
      apply Subtype.ext
      change a ⊔ (o ⊓ p v) = p v
      have htop : a ⊔ o = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : x ∈ a.restrictScalars ℂ ⊔ orth c (a.restrictScalars ℂ) := by
          rw [sup_orth]; trivial
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
        exact Submodule.add_mem_sup hy hz
      rw [← sup_inf_assoc_of_le o (show a ≤ p v from ha), htop, top_inf_eq]
  · rw [eq_top_iff]
    intro v _
    exact Submodule.mem_iSup_of_mem v (self_mem_orbitSpan κ v)

end CompactSide

section Averaging

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem orbit_apply_eq (U : Subgroup G) (u : U) (v : V) :
    Compact.orbit (ρ.comp U.subtype) (ρ u v) = Compact.orbit (ρ.comp U.subtype) v := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w * u, by simp [map_mul]⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w * u⁻¹, by simp [map_mul]⟩

/-- Averaging over a compact open subgroup does not see translations by that subgroup. -/
theorem averageMap_apply_rep (U : OpenSubgroup G) (hU : IsCompact (U : Set G))
    (u : U.toSubgroup) (v : V) :
    Compact.averageMap ρ hρ U hU (ρ u v) = Compact.averageMap ρ hρ U hU v := by
  change Compact.orbitMean _ (ρ u v) = Compact.orbitMean _ v
  unfold Compact.orbitMean
  rw [orbit_apply_eq]

/-- Averaging preserves every invariant subspace. -/
theorem averageMap_mem (B : Submodule ℂ V) (hB : ∀ g, ∀ v ∈ B, ρ g v ∈ B)
    (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) {x : V} (hx : x ∈ B) :
    Compact.averageMap ρ hρ U hU x ∈ B := by
  classical
  have := Compact.finite_orbit_of_smooth ρ hρ U hU x
  let := Fintype.ofFinite (Compact.orbit (ρ.comp U.toSubgroup.subtype) x)
  change Compact.orbitMean _ x ∈ B
  rw [Compact.orbitMean_eq_finiteMean]
  apply B.smul_mem
  apply B.sum_mem
  rintro ⟨_, ⟨u, rfl⟩⟩ _
  exact hB u x hx

/-- Averaging is invisible to the Hermitian pairing against a fixed vector. -/
theorem inner_averageMap (b : InvariantPositiveForm ρ) (U : OpenSubgroup G)
    (hU : IsCompact (U : Set G)) (y : V) (hy : y ∈ fixedVectors ρ U.toSubgroup) (x : V) :
    b.inner y (Compact.averageMap ρ hρ U hU x) = b.inner y x := by
  classical
  have := Compact.finite_orbit_of_smooth ρ hρ U hU x
  let := Fintype.ofFinite (Compact.orbit (ρ.comp U.toSubgroup.subtype) x)
  change rightFunctional b.toInnerProductCore y (Compact.orbitMean _ x) = _
  rw [Compact.orbitMean_eq_finiteMean]
  unfold Compact.finiteMean
  rw [map_smul, map_sum]
  have hterm : ∀ z : Compact.orbit (ρ.comp U.toSubgroup.subtype) x,
      rightFunctional b.toInnerProductCore y z.val = b.inner y x := by
    rintro ⟨_, ⟨u, rfl⟩⟩
    have hyu : ρ u y = y := hy u
    change b.inner y (ρ u x) = _
    conv_lhs => rw [← hyu]
    exact b.invariant u y x
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  have hcard : (Fintype.card (Compact.orbit (ρ.comp U.toSubgroup.subtype) x) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end Averaging

section Irreducible

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)

/-- A nonzero subrepresentation without proper nonzero subrepresentations of the ambient
representation is irreducible as a representation. -/
theorem isIrreducible_of_forall {A : Subrepresentation ρ} (hne : A ≠ ⊥)
    (key : ∀ C : Subrepresentation ρ, C ≤ A → C = ⊥ ∨ C = A) :
    A.toRepresentation.IsIrreducible := by
  let up : Subrepresentation A.toRepresentation → Subrepresentation ρ := fun D =>
    ⟨D.toSubmodule.map A.toSubmodule.subtype, by
      rintro g _ ⟨x, hx, rfl⟩
      exact ⟨A.toRepresentation g x, D.apply_mem_toSubmodule g hx, rfl⟩⟩
  have hup : ∀ D, up D ≤ A := by
    rintro D _ ⟨x, _, rfl⟩
    exact x.2
  have hbot : ∀ D : Subrepresentation A.toRepresentation, up D = ⊥ → D = ⊥ := by
    intro D h
    apply Subrepresentation.ext
    change D.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : V) ∈ (up D).toSubmodule := ⟨x, hx, rfl⟩
    rw [h] at hx'
    exact (Submodule.mem_bot ℂ).mpr (Subtype.ext ((Submodule.mem_bot ℂ).mp hx'))
  have htop : ∀ D : Subrepresentation A.toRepresentation, up D = A → D = ⊤ := by
    intro D h
    apply Subrepresentation.ext
    change D.toSubmodule = ⊤
    rw [eq_top_iff]
    intro x _
    have hx' : (x : V) ∈ (up D).toSubmodule := by rw [h]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [← Subtype.ext hyx]
    exact hy
  have hnt : Nontrivial (Subrepresentation A.toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    apply Subrepresentation.ext
    change A.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro v hv
    have hmem : (⟨v, hv⟩ : A.toSubmodule) ∈
        (⊤ : Subrepresentation A.toRepresentation).toSubmodule :=
      Submodule.mem_top
    rw [← h] at hmem
    exact (Submodule.mem_bot ℂ).mpr (congrArg Subtype.val ((Submodule.mem_bot ℂ).mp hmem))
  refine ⟨fun D => ?_⟩
  · rcases key (up D) (hup D) with h | h
    · exact Or.inl (hbot D h)
    · exact Or.inr (htop D h)

/-- An actual equivalence transports irreducibility. -/
theorem isIrreducible_of_equiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (e : ρ.Equiv σ) (h : ρ.IsIrreducible) : σ.IsIrreducible := by
  have hnt : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    apply Subrepresentation.ext
    change (⊥ : Submodule ℂ V) = ⊤
    exact Subsingleton.elim _ _
  have hW : Nontrivial W := e.toLinearEquiv.injective.nontrivial
  have hntσ : Nontrivial (Subrepresentation σ) := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    refine ⟨⊥, ⊤, fun hbt => hw ?_⟩
    have hmem : w ∈ (⊤ : Subrepresentation σ).toSubmodule := Submodule.mem_top
    rw [← hbt] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  let down : Subrepresentation σ → Subrepresentation ρ := fun D =>
    ⟨D.toSubmodule.comap e.toLinearEquiv.toLinearMap, fun g v hv => by
      have hint := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
      change e.toIntertwiningMap (ρ g v) ∈ D.toSubmodule
      rw [hint]
      exact D.apply_mem_toSubmodule g hv⟩
  refine ⟨fun D => ?_⟩
  rcases h.eq_bot_or_eq_top (down D) with hD | hD
  · left
    apply Subrepresentation.ext
    change D.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
    have hv : v ∈ (down D).toSubmodule := hw
    rw [hD] at hv
    rw [(Submodule.mem_bot ℂ).mp hv, map_zero]
    exact Submodule.zero_mem _
  · right
    apply Subrepresentation.ext
    change D.toSubmodule = ⊤
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
    have hv : v ∈ (down D).toSubmodule := by rw [hD]; exact Submodule.mem_top
    exact hv

end Irreducible

section Minimal

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

include hρ in
/-- Inside a unitary subrepresentation whose fixed vectors under compact open subgroups are
finite-dimensional, a subrepresentation with fixed vectors of minimal positive dimension
generates an irreducible admissible subrepresentation. -/
theorem exists_irreducible_admissible_le (b : InvariantPositiveForm ρ)
    (hcpt : ∀ U : OpenSubgroup G, ∃ U' : OpenSubgroup G, U' ≤ U ∧ IsCompact (U' : Set G))
    (A : Subrepresentation ρ) (hA : A ≠ ⊥)
    (hfin : ∀ U : OpenSubgroup G, IsCompact (U : Set G) →
      FiniteDimensional ℂ ↥(A.toSubmodule ⊓ fixedVectors ρ U.toSubgroup)) :
    ∃ A₀ : Subrepresentation ρ, A₀ ≤ A ∧ A₀ ≠ ⊥ ∧ A₀.toRepresentation.IsIrreducible ∧
      IsAdmissible A₀.toRepresentation := by
  classical
  obtain ⟨a, haA, ha0⟩ : ∃ a ∈ A.toSubmodule, a ≠ 0 := by
    by_contra! h
    apply hA
    apply Subrepresentation.ext
    change A.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro v hv
    exact (Submodule.mem_bot ℂ).mpr (h v hv)
  obtain ⟨U₁, hU₁⟩ := hρ a
  obtain ⟨U₀, hU₀le, hU₀⟩ := hcpt U₁
  have haU₀ : a ∈ fixedVectors ρ U₀.toSubgroup := fun u => hU₁ ⟨u.1, hU₀le u.2⟩
  let fx : Subrepresentation ρ → Submodule ℂ V := fun B =>
    B.toSubmodule ⊓ fixedVectors ρ U₀.toSubgroup
  have hfA := hfin U₀ hU₀
  have hfx : ∀ B : Subrepresentation ρ, B ≤ A → FiniteDimensional ℂ (fx B) := fun B hB =>
    Submodule.finiteDimensional_of_le (inf_le_inf_right _ hB)
  let P : ℕ → Prop := fun n => ∃ B : Subrepresentation ρ, B ≤ A ∧ fx B ≠ ⊥ ∧
    finrank ℂ (fx B) = n
  have hP : ∃ n, P n := by
    refine ⟨_, A, le_rfl, fun h => ha0 ?_, rfl⟩
    have hmem : a ∈ fx A := ⟨haA, haU₀⟩
    rw [h] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  obtain ⟨B₀, hB₀A, hB₀ne, hB₀rank⟩ := Nat.find_spec hP
  have hfB₀ := hfx B₀ hB₀A
  let gen : Submodule ℂ V := Submodule.span ℂ (Set.range fun p : G × fx B₀ => ρ p.1 (p.2 : V))
  have hgen : ∀ g, ∀ v ∈ gen, ρ g v ∈ gen := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨h, x⟩, rfl⟩ := hw
      apply Submodule.subset_span
      exact ⟨(g * h, x), by simp [map_mul]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact gen.add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact gen.smul_mem r hx
  let A₀ : Subrepresentation ρ := ⟨gen, hgen⟩
  have hA₀B₀ : A₀ ≤ B₀ := by
    change gen ≤ B₀.toSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨⟨g, x⟩, rfl⟩
    exact B₀.apply_mem_toSubmodule g x.2.1
  have hgenfx : fx B₀ ≤ gen := fun x hx =>
    Submodule.subset_span ⟨(1, ⟨x, hx⟩), by simp⟩
  have hfxA₀ : fx A₀ = fx B₀ :=
    le_antisymm (inf_le_inf_right _ hA₀B₀) (le_inf hgenfx inf_le_right)
  have hA₀A : A₀ ≤ A := hA₀B₀.trans hB₀A
  have hA₀ne : A₀ ≠ ⊥ := by
    intro h
    apply hB₀ne
    rw [← hfxA₀, eq_bot_iff]
    rintro x ⟨hx, -⟩
    have hx' : x ∈ (A₀ : Subrepresentation ρ).toSubmodule := hx
    rw [h] at hx'
    exact hx'
  have key : ∀ C : Subrepresentation ρ, C ≤ A₀ → C = ⊥ ∨ C = A₀ := by
    intro C hC
    by_cases hCfx : fx C = ⊥
    · left
      have hzero : ∀ c ∈ C.toSubmodule, Compact.averageMap ρ hρ U₀ hU₀ c = 0 := by
        intro c hc
        have hmem : Compact.averageMap ρ hρ U₀ hU₀ c ∈ fx C :=
          ⟨averageMap_mem ρ hρ C.toSubmodule (fun g v hv => C.apply_mem_toSubmodule g hv)
            U₀ hU₀ hc, Compact.averageMap_mem_fixedVectors ρ hρ U₀ hU₀ c⟩
        rw [hCfx] at hmem
        exact (Submodule.mem_bot ℂ).mp hmem
      apply Subrepresentation.ext
      change C.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro c hc
      have horth : ∀ y ∈ gen, b.inner c y = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨⟨g, x⟩, rfl⟩ := hw
          have hc' : ρ g⁻¹ c ∈ C.toSubmodule := C.apply_mem_toSubmodule g⁻¹ hc
          have h1 : b.inner c (ρ g x) = b.inner (ρ g⁻¹ c) x := by
            have := b.invariant g (ρ g⁻¹ c) x
            rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
              Module.End.one_apply] at this
          rw [h1]
          apply inner_eq_zero_symm
          rw [← inner_averageMap ρ hρ b U₀ hU₀ x x.2.2, hzero _ hc']
          exact inner_zero_right _ _
        | zero => exact inner_zero_right _ _
        | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
        | smul r x _ hx => rw [inner_smul_right, hx, mul_zero]
      exact (Submodule.mem_bot ℂ).mpr (b.definite c (horth c (hC hc)))
    · right
      apply le_antisymm hC
      have hle : fx C ≤ fx B₀ := hfxA₀ ▸ inf_le_inf_right _ hC
      have hmin : Nat.find hP ≤ finrank ℂ (fx C) :=
        Nat.find_min' hP ⟨C, hC.trans hA₀A, hCfx, rfl⟩
      have heq : fx C = fx B₀ := Submodule.eq_of_le_of_finrank_le hle (hB₀rank ▸ hmin)
      change gen ≤ C.toSubmodule
      rw [Submodule.span_le]
      rintro _ ⟨⟨g, x⟩, rfl⟩
      have hx : (x : V) ∈ fx C := by rw [heq]; exact x.2
      exact C.apply_mem_toSubmodule g hx.1
  refine ⟨A₀, hA₀A, hA₀ne, isIrreducible_of_forall ρ hA₀ne key, ?_, ?_⟩
  · intro x
    obtain ⟨U, hU⟩ := hρ x.val
    exact ⟨U, fun u => Subtype.ext (hU u)⟩
  · intro U
    obtain ⟨U', hU'le, hU'⟩ := hcpt U
    have := hfin U' hU'
    let f : fixedVectors A₀.toRepresentation U.toSubgroup →ₗ[ℂ]
        ↥(A.toSubmodule ⊓ fixedVectors ρ U'.toSubgroup) :=
      { toFun := fun x => ⟨x.1.1, hA₀A x.1.2, fun u =>
          congrArg Subtype.val (x.2 ⟨u.1, hU'le u.2⟩)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Module.Finite.of_injective f ?_
    intro x y h
    have h' := congrArg (fun z : ↥(A.toSubmodule ⊓ fixedVectors ρ U'.toSubgroup) => (z : V)) h
    exact Subtype.ext (Subtype.ext h')

end Minimal

section Multiplicity

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (κ : Representation ℂ K V)
  (hcomm : ∀ g k v, ρ g (κ k v) = κ k (ρ g v))
  [Module ℂ[K] V] [IsScalarTower ℂ ℂ[K] V]
  (hmod : ∀ k v, MonoidAlgebra.of ℂ K k • v = κ k v)

include hcomm hmod in
/-- Each operator of the commuting action is group-algebra linear. -/
def algRep (g : G) : V →ₗ[ℂ[K]] V where
  toFun := ρ g
  map_add' := map_add _
  map_smul' r v := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs =>
      simp only [RingHom.id_apply] at hr hs ⊢
      rw [add_smul, map_add, hr, hs, add_smul]
    | single k a => simp only [RingHom.id_apply, single_smul κ hmod, map_smul, hcomm]

include hρ hcomm hmod in
/-- A countable-dimensional space of smooth compact-finite functionals forces finite
dimension of the fixed vectors in each compact-type isotypic component. -/
theorem finiteDimensional_isotypic_fixed (c : InnerProductSpace.Core ℂ V)
    (hc : ∀ k x y, c.inner (κ k x) (κ k y) = c.inner x y)
    (hfin : ∀ v : V, IsFiniteVector κ v)
    (hdual : ∀ L : Submodule ℂ (Module.Dual ℂ V),
      (∀ l ∈ L, IsSmoothVector ρ.dual l ∧ IsFiniteVector κ.dual l) → Module.rank ℂ L ≤ ℵ₀)
    (S : Submodule ℂ[K] V) [IsSimpleModule ℂ[K] S] [FiniteDimensional ℂ S]
    (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    FiniteDimensional ℂ ↥((isotypicComponent ℂ[K] V S).restrictScalars ℂ ⊓
      fixedVectors ρ U.toSubgroup) := by
  classical
  have := isSemisimpleModule κ c hmod hc hfin
  let A := isotypicComponent ℂ[K] V S
  have hNstable : ∀ k, ∀ v ∈ fixedVectors ρ U.toSubgroup,
      κ k v ∈ fixedVectors ρ U.toSubgroup := by
    intro k v hv u
    change ρ u (κ k v) = κ k v
    rw [hcomm, show ρ u v = v from hv u]
  let N := toAlg κ hmod (fixedVectors ρ U.toSubgroup) hNstable
  let C := A ⊓ N
  suffices hC : FiniteDimensional ℂ C by exact hC
  have hCA : C ≤ A := inf_le_left
  have hiso : IsIsotypicOfType ℂ[K] C S :=
    (IsIsotypicOfType.isotypicComponent ℂ[K] V S).of_injective (Submodule.inclusion hCA)
      (Submodule.inclusion_injective hCA)
  obtain ⟨ι, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
  rcases finite_or_infinite ι with hι | hι
  · exact Module.Finite.equiv (e.symm.restrictScalars ℂ)
  exfalso
  have : Nonempty ι := Infinite.nonempty ι
  have : Nontrivial S := IsSimpleModule.nontrivial ℂ[K] S
  obtain ⟨D, hCD⟩ := exists_isCompl C
  let π : V →ₗ[ℂ[K]] C := C.projectionOnto D hCD
  let eU : V →ₗ[ℂ] V := Compact.averageMap ρ hρ U hU
  let Q : V →ₗ[ℂ] (ι →₀ S) :=
    (e.toLinearMap.restrictScalars ℂ) ∘ₗ (π.restrictScalars ℂ) ∘ₗ eU
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual ℂ S, ℓ s₀ ≠ 0 := by
    by_contra! h
    exact hs₀ ((Module.forall_dual_apply_eq_zero_iff ℂ s₀).mp h)
  let Φ : (ι → ℂ) →ₗ[ℂ] Module.Dual ℂ S →ₗ[ℂ] Module.Dual ℂ (ι →₀ S) :=
    LinearMap.mk₂ ℂ (fun μ ℓ' => Finsupp.lsum ℂ (fun i => μ i • ℓ'))
      (fun μ ν ℓ' => by ext i s; simp [add_smul])
      (fun r μ ℓ' => by ext i s; simp [mul_smul])
      (fun μ ℓ' ℓ'' => by ext i s; simp [smul_add])
      (fun r μ ℓ' => by
        ext i s
        simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
          Finsupp.lsum_single, LinearMap.smul_apply, smul_eq_mul]
        ring)
  have hΦ : ∀ (μ : ι → ℂ) (ℓ' : Module.Dual ℂ S) (i : ι) (s : S),
      Φ μ ℓ' (Finsupp.single i s) = μ i * ℓ' s := by
    intro μ ℓ' i s
    simp [Φ, Finsupp.lsum_single]
  have hΦsmul : ∀ (μ : ι → ℂ) (ℓ' : Module.Dual ℂ S) (r : ℂ[K]) (x : ι →₀ S),
      Φ μ ℓ' (r • x) = Φ μ (ℓ' ∘ₗ DistribSMul.toLinearMap ℂ S r) x := by
    intro μ ℓ' r x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]
    | single i s => rw [Finsupp.smul_single, hΦ, hΦ]; rfl
  let L : (ι → ℂ) →ₗ[ℂ] Module.Dual ℂ V := Q.dualMap ∘ₗ Φ.flip ℓ
  have hL : ∀ μ v, L μ v = Φ μ ℓ (Q v) := fun _ _ => rfl
  have hQsingle : ∀ i, ∃ v : V, Q v = Finsupp.single i s₀ := by
    intro i
    let x : C := e.symm (Finsupp.single i s₀)
    refine ⟨(x : V), ?_⟩
    have hfix : (x : V) ∈ fixedVectors ρ U.toSubgroup := x.2.2
    have h1 : eU x = x := Compact.averageMap_id ρ hρ U hU _ hfix
    change e (π (eU x)) = _
    rw [h1]
    change e (C.projectionOnto D hCD (x : V)) = _
    rw [Submodule.projectionOnto_apply_left]
    exact e.apply_symm_apply _
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro μ hμ
    rw [LinearMap.mem_ker] at hμ
    rw [Submodule.mem_bot]
    funext i
    obtain ⟨v, hv⟩ := hQsingle i
    have h0 := LinearMap.congr_fun hμ v
    rw [hL, hv, hΦ] at h0
    exact (mul_eq_zero.mp h0).resolve_right hℓ
  have hsmooth : ∀ μ, IsSmoothVector ρ.dual (L μ) := by
    intro μ
    refine ⟨U, ?_⟩
    rw [fixedVectors, Representation.mem_invariants]
    intro u
    apply LinearMap.ext
    intro v
    change L μ (ρ ((u⁻¹ : U.toSubgroup) : G) v) = L μ v
    rw [hL, hL]
    congr 1
    change e (π (eU (ρ ((u⁻¹ : U.toSubgroup) : G) v))) = e (π (eU v))
    rw [show eU (ρ ((u⁻¹ : U.toSubgroup) : G) v) = eU v from
      averageMap_apply_rep ρ hρ U hU u⁻¹ v]
  have hfinite : ∀ μ, IsFiniteVector κ.dual (L μ) := by
    intro μ
    let Λ : Module.Dual ℂ S →ₗ[ℂ] Module.Dual ℂ V := Q.dualMap ∘ₗ Φ μ
    have hact : ∀ k, κ.dual k (L μ) =
        Λ (ℓ ∘ₗ DistribSMul.toLinearMap ℂ S (MonoidAlgebra.of ℂ K k⁻¹)) := by
      intro k
      apply LinearMap.ext
      intro v
      change L μ (κ k⁻¹ v) = Φ μ _ (Q v)
      have hQ : Q (κ k⁻¹ v) = MonoidAlgebra.of ℂ K k⁻¹ • Q v := by
        let f : ρ.IntertwiningMap ρ :=
          LinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ (κ k⁻¹)
            (fun g w => (hcomm g k⁻¹ w).symm)
        have hc : eU (κ k⁻¹ v) = κ k⁻¹ (eU v) :=
          (LinearMap.congr_fun (Compact.averageMap_commute ρ ρ hρ hρ U hU f) v).symm
        change e (π (eU (κ k⁻¹ v))) = MonoidAlgebra.of ℂ K k⁻¹ • e (π (eU v))
        rw [hc, ← hmod, map_smul, map_smul]
      rw [hL, hQ, hΦsmul]
    have hle : orbitSpan κ.dual (L μ) ≤ LinearMap.range Λ := by
      rw [orbitSpan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨_, (hact k).symm⟩
    exact Submodule.finiteDimensional_of_le hle
  have hrank := hdual (LinearMap.range L) (by
    rintro _ ⟨μ, rfl⟩
    exact ⟨hsmooth μ, hfinite μ⟩)
  rw [rank_range_of_injective L hinj, rank_fun_infinite] at hrank
  have hlt : ℵ₀ < #(ι → ℂ) := by
    have h1 : Cardinal.lift.{uV} #ℂ ≤ Cardinal.lift.{0} #(ι → ℂ) :=
      Cardinal.lift_mk_le_lift_mk_of_injective (f := fun z : ℂ => fun _ : ι => z)
        (fun z w h => congrFun h (Classical.arbitrary ι))
    rw [Cardinal.mk_complex, Cardinal.lift_uzero] at h1
    calc ℵ₀ = Cardinal.lift.{uV} ℵ₀ := Cardinal.lift_aleph0.symm
      _ < Cardinal.lift.{uV} 𝔠 := Cardinal.lift_lt.mpr Cardinal.aleph0_lt_continuum
      _ ≤ _ := h1
  exact absurd hrank (not_le.mpr hlt)

end Multiplicity

section Main

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- **Irreducible admissible subrepresentations from a countable smooth dual.**
Let `ρ` be a smooth representation commuting with a representation `κ` all of whose vectors
are finite, with a positive definite Hermitian form invariant under both. Suppose every
open subgroup contains a compact open one, and every space of functionals that are smooth
for `ρ` and finite for `κ` has countable dimension. Then `ρ` has a nonzero irreducible
admissible subrepresentation. -/
theorem exists_irreducible_admissible [Nontrivial V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (κ : Representation ℂ K V)
    (hcomm : ∀ g k v, ρ g (κ k v) = κ k (ρ g v))
    (b : InvariantPositiveForm ρ) (hb : ∀ k x y, b.inner (κ k x) (κ k y) = b.inner x y)
    (hfin : ∀ v : V, IsFiniteVector κ v)
    (hcpt : ∀ U : OpenSubgroup G, ∃ U' : OpenSubgroup G, U' ≤ U ∧ IsCompact (U' : Set G))
    (hdual : ∀ L : Submodule ℂ (Module.Dual ℂ V),
      (∀ l ∈ L, IsSmoothVector ρ.dual l ∧ IsFiniteVector κ.dual l) → Module.rank ℂ L ≤ ℵ₀) :
    ∃ A : Subrepresentation ρ, A ≠ ⊥ ∧ A.toRepresentation.IsIrreducible ∧
      IsAdmissible A.toRepresentation := by
  classical
  let := algModule κ
  have : IsScalarTower ℂ ℂ[K] V := inferInstanceAs (IsScalarTower ℂ ℂ[K] κ.asModule)
  have hmod : ∀ k v, MonoidAlgebra.of ℂ K k • v = κ k v := by
    intro k v
    change κ.asAlgebraHom (MonoidAlgebra.of ℂ K k) v = κ k v
    simp
  have := isSemisimpleModule κ b.toInnerProductCore hmod hb hfin
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let p := toAlg κ hmod (orbitSpan κ v)
    (fun k w hw => (orbitSubrepresentation κ v).apply_mem_toSubmodule k hw)
  have hpfin : FiniteDimensional ℂ (orbitSpan κ v) := hfin v
  rcases IsSemisimpleModule.eq_bot_or_exists_simple_le p with hp | ⟨S, hSp, hS⟩
  · exfalso
    have hvp : v ∈ p := self_mem_orbitSpan κ v
    rw [hp] at hvp
    exact hv ((Submodule.mem_bot _).mp hvp)
  have := hS
  have hSle : S.restrictScalars ℂ ≤ orbitSpan κ v := hSp
  have hSfin : FiniteDimensional ℂ (S.restrictScalars ℂ) :=
    Submodule.finiteDimensional_of_le hSle
  have : FiniteDimensional ℂ S := hSfin
  let Aalg := isotypicComponent ℂ[K] V S
  let A : Subrepresentation ρ := ⟨Aalg.restrictScalars ℂ, fun g w hw =>
    (Submodule.IsFullyInvariant.isotypicComponent ℂ[K] V S) (algRep ρ κ hcomm hmod g) hw⟩
  have hA : A ≠ ⊥ := by
    intro h
    have hSA : S ≤ Aalg := Submodule.le_isotypicComponent S
    have hSbot : S = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ A.toSubmodule := hSA hx
      rw [h] at hx'
      exact (Submodule.mem_bot _).mpr ((Submodule.mem_bot ℂ).mp hx')
    exact (isSimpleModule_iff_isAtom.mp hS).1 hSbot
  obtain ⟨A₀, -, hne, hirr, hadm⟩ := exists_irreducible_admissible_le ρ hρ b hcpt A hA
    (fun U hU => finiteDimensional_isotypic_fixed ρ hρ κ hcomm hmod b.toInnerProductCore hb hfin
      hdual S U hU)
  exact ⟨A₀, hne, hirr, hadm⟩

end Main

section Transfer

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Pairing against a left vector, as a conjugate-linear map into the algebraic dual. -/
def conjFunctional (c : InnerProductSpace.Core ℂ V) : V →ₛₗ[starRingEnd ℂ] Module.Dual ℂ V where
  toFun := rightFunctional c
  map_add' h h' := LinearMap.ext fun y => c.add_left h h' y
  map_smul' a h := LinearMap.ext fun y => c.smul_left h y a

@[simp] theorem conjFunctional_apply (c : InnerProductSpace.Core ℂ V) (h y : V) :
    conjFunctional c h y = c.inner h y := rfl

theorem conjFunctional_injective (c : InnerProductSpace.Core ℂ V) :
    Function.Injective (conjFunctional c) := by
  intro h h' hh
  have hsub : conjFunctional c (h - h') = 0 := by rw [map_sub, hh, sub_self]
  have h0 : c.inner (h - h') (h - h') = 0 := LinearMap.congr_fun hsub (h - h')
  exact sub_eq_zero.mp (c.definite _ h0)

omit [TopologicalSpace G] in
/-- The conjugate-linear pairing map intertwines the action with its algebraic dual. -/
theorem conjFunctional_apply_rep (ρ : Representation ℂ G V) (b : InvariantPositiveForm ρ)
    (g : G) (h : V) :
    conjFunctional b.toInnerProductCore (ρ g h) =
      ρ.dual g (conjFunctional b.toInnerProductCore h) := by
  apply LinearMap.ext
  intro y
  change b.inner (ρ g h) y = b.inner h (ρ g⁻¹ y)
  have := b.invariant g h (ρ g⁻¹ y)
  rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    at this

omit [TopologicalSpace G] in
theorem forall_of_isIrreducible (ρ : Representation ℂ G V) {A : Subrepresentation ρ}
    (hirr : A.toRepresentation.IsIrreducible) :
    ∀ C : Subrepresentation ρ, C ≤ A → C = ⊥ ∨ C = A := by
  intro C hC
  let D : Subrepresentation A.toRepresentation :=
    ⟨C.toSubmodule.comap A.toSubmodule.subtype, fun g x hx => C.apply_mem_toSubmodule g hx⟩
  rcases hirr.eq_bot_or_eq_top D with h | h
  · left
    apply Subrepresentation.ext
    change C.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro c hc
    have hD : (⟨c, hC hc⟩ : A.toSubmodule) ∈ D.toSubmodule := hc
    rw [h] at hD
    exact (Submodule.mem_bot ℂ).mpr (congrArg Subtype.val ((Submodule.mem_bot ℂ).mp hD))
  · right
    apply le_antisymm hC
    intro a ha
    have hD : (⟨a, ha⟩ : A.toSubmodule) ∈ D.toSubmodule := by
      rw [h]; exact Submodule.mem_top
    exact hD

variable {W : Type uV} [AddCommGroup W] [Module ℂ W]

/-- **Transfer to a dual realization.** If every pairing functional of an invariant positive
form is represented by a vector of a realization embedded equivariantly in the algebraic
dual, then every irreducible admissible subrepresentation of the first realization has a
conjugate-linear copy in the second, again irreducible and admissible. -/
theorem exists_dual_subrepresentation (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hσ : IsSmooth σ) (b : InvariantPositiveForm ρ) (β : W →ₗ[ℂ] Module.Dual ℂ V)
    (hβinj : Function.Injective β) (hβ : ∀ g x, β (σ g x) = ρ.dual g (β x))
    (hR : ∀ h : V, ∃ x : W, β x = conjFunctional b.toInnerProductCore h)
    (A : Subrepresentation ρ) (hA : A ≠ ⊥) (hirr : A.toRepresentation.IsIrreducible)
    (hadm : IsAdmissible A.toRepresentation) :
    ∃ A' : Subrepresentation σ, A' ≠ ⊥ ∧ A'.toRepresentation.IsIrreducible ∧
      IsAdmissible A'.toRepresentation := by
  classical
  let R := conjFunctional b.toInnerProductCore
  choose Φf hΦf using hR
  let Φ : V →ₛₗ[starRingEnd ℂ] W :=
    { toFun := Φf
      map_add' := fun h h' => hβinj (by rw [map_add, hΦf, hΦf, hΦf, map_add])
      map_smul' := fun a h => hβinj (by
        rw [hΦf, map_smulₛₗ (conjFunctional b.toInnerProductCore), map_smul β, hΦf]) }
  have hΦ : ∀ h, β (Φ h) = R h := hΦf
  have hΦinj : Function.Injective Φ := fun h h' hh =>
    conjFunctional_injective b.toInnerProductCore (by rw [← hΦ, ← hΦ, hh])
  have hΦeq : ∀ g h, Φ (ρ g h) = σ g (Φ h) := fun g h => hβinj (by
    rw [hΦ, hβ, hΦ]
    exact conjFunctional_apply_rep ρ b g h)
  let A' : Subrepresentation σ := ⟨A.toSubmodule.map Φ, by
    rintro g _ ⟨h, hh, rfl⟩
    exact ⟨ρ g h, A.apply_mem_toSubmodule g hh, hΦeq g h⟩⟩
  have hA'ne : A' ≠ ⊥ := by
    intro hbot
    apply hA
    apply Subrepresentation.ext
    change A.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro h hh
    have hx : Φ h ∈ A'.toSubmodule := ⟨h, hh, rfl⟩
    rw [hbot] at hx
    have h0 : Φ h = Φ 0 := by rw [map_zero]; exact (Submodule.mem_bot ℂ).mp hx
    exact (Submodule.mem_bot ℂ).mpr (hΦinj h0)
  have hkey := forall_of_isIrreducible ρ hirr
  have key : ∀ C' : Subrepresentation σ, C' ≤ A' → C' = ⊥ ∨ C' = A' := by
    intro C' hC'
    let C : Subrepresentation ρ := ⟨C'.toSubmodule.comap Φ ⊓ A.toSubmodule, by
      rintro g h ⟨h1, h2⟩
      refine ⟨?_, A.apply_mem_toSubmodule g h2⟩
      change Φ (ρ g h) ∈ C'.toSubmodule
      rw [hΦeq]
      exact C'.apply_mem_toSubmodule g h1⟩
    rcases hkey C (fun x hx => hx.2) with hC | hC
    · left
      apply Subrepresentation.ext
      change C'.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨h, hh, rfl⟩ := hC' hx
      have hmem : h ∈ C.toSubmodule := ⟨hx, hh⟩
      rw [hC] at hmem
      rw [(Submodule.mem_bot ℂ).mp hmem, map_zero]
      exact Submodule.zero_mem _
    · right
      apply le_antisymm hC'
      rintro _ ⟨h, hh, rfl⟩
      have hmem : h ∈ C.toSubmodule := by rw [hC]; exact hh
      exact hmem.1
  refine ⟨A', hA'ne, isIrreducible_of_forall σ hA'ne key, ?_, ?_⟩
  · intro x
    obtain ⟨U, hU⟩ := hσ x.val
    exact ⟨U, fun u => Subtype.ext (hU u)⟩
  · intro U
    let FA : Submodule ℂ V := A.toSubmodule ⊓ fixedVectors ρ U.toSubgroup
    have hFA : Module.Finite ℂ FA := by
      have := hadm.2 U
      let f : FA →ₗ[ℂ] fixedVectors A.toRepresentation U.toSubgroup :=
        { toFun := fun h => ⟨⟨h.1, h.2.1⟩, fun u => Subtype.ext (h.2.2 u)⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      refine Module.Finite.of_injective f ?_
      intro x y hxy
      have h' := congrArg (fun z : fixedVectors A.toRepresentation U.toSubgroup =>
        ((z : A.toSubmodule) : V)) hxy
      exact Subtype.ext h'
    have hFG : (FA.map Φ).FG := (Module.Finite.iff_fg.mp hFA).map Φ
    have : Module.Finite ℂ (FA.map Φ) := Module.Finite.iff_fg.mpr hFG
    let f : fixedVectors A'.toRepresentation U.toSubgroup →ₗ[ℂ] FA.map Φ :=
      { toFun := fun x => ⟨x.1.1, by
          obtain ⟨h, hh, hx⟩ := x.1.2
          refine ⟨h, ⟨hh, fun u => hΦinj ?_⟩, hx⟩
          change Φ (ρ u h) = Φ h
          rw [hΦeq, hx]
          exact congrArg Subtype.val (x.2 u)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Module.Finite.of_injective f ?_
    intro x y hxy
    have h' := congrArg (fun z : FA.map Φ => (z : W)) hxy
    exact Subtype.ext (Subtype.ext h')

end Transfer

end Langlands.CountableDual
