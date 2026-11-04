import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Order.CompactlyGenerated.Basic
import Langlands.Group.LieKolchin.DerivedConnected

/-! # Common eigenvectors of connected solvable groups

The abstract Lie–Kolchin argument: a representation `ρ : G →* Module.End k V` of a connected
solvable group on a nonzero finite-dimensional vector space over an algebraically closed
field has a common eigenvector, provided every linear condition `Λ (ρ g) = c` cuts out a closed
subset of `G` and left translations, inversion and the maps `y ↦ ⁅a, y⁆` are continuous. -/

open scoped commutatorElement

universe v

namespace Langlands.LieKolchin

section CommonEigenvector

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Strong induction on the dimension for `exists_common_eigenvector`. -/
theorem exists_common_eigenvector_aux {ι : Type*} (d : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module k M] [FiniteDimensional k M] [Nontrivial M]
      (f : ι → Module.End k M), (∀ i j, Commute (f i) (f j)) →
      Module.finrank k M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, ∃ c : k, f i v = c • v := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ _ f hc hd
  by_cases hall : ∀ i, ∃ c : k, ∀ x, f i x = c • x
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    refine ⟨v, hv, fun i => ?_⟩
    obtain ⟨c, hc'⟩ := hall i
    exact ⟨c, hc' v⟩
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f i)
  let W : Submodule k M := (f i).eigenspace μ
  have hW : ∀ j, ∀ w ∈ W, f j w ∈ W := by
    intro j w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    calc f i (f j w) = (f i * f j) w := rfl
      _ = (f j * f i) w := by rw [(hc i j).eq]
      _ = f j (μ • w) := by rw [Module.End.mul_apply, hw]
      _ = μ • f j w := map_smul _ _ _
  have hWbot : W ≠ ⊥ := hμ
  have hWtop : W ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := hi μ
    have hxW : x ∈ W := h ▸ Submodule.mem_top
    exact hx ((Module.End.mem_eigenspace_iff).mp hxW)
  have hlt : Module.finrank k W < d :=
    hd ▸ Submodule.finrank_lt hWtop
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWbot
  let g : ι → Module.End k W := fun j => (f j).restrict (hW j)
  have hcg : ∀ j l, Commute (g j) (g l) := by
    intro j l
    refine LinearMap.ext fun w => Subtype.ext ?_
    change f j (f l w) = f l (f j w)
    exact LinearMap.congr_fun (hc j l).eq (w : M)
  obtain ⟨w, hw0, hw⟩ := ih _ hlt W g hcg rfl
  refine ⟨w, fun h => hw0 (Subtype.ext h), fun j => ?_⟩
  obtain ⟨c, hcw⟩ := hw j
  exact ⟨c, congrArg Subtype.val hcw⟩

/-- A commuting family of endomorphisms of a nonzero finite-dimensional vector space over an
algebraically closed field has a common eigenvector. -/
theorem exists_common_eigenvector {ι : Type*} {M : Type v} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] [Nontrivial M] (f : ι → Module.End k M)
    (hc : ∀ i j, Commute (f i) (f j)) :
    ∃ v : M, v ≠ 0 ∧ ∀ i, ∃ c : k, f i v = c • v :=
  exists_common_eigenvector_aux _ M f hc rfl

end CommonEigenvector

section Weights

variable {k V A : Type*} [Field k] [AddCommGroup V] [Module k V] [Monoid A]

/-- The simultaneous eigenspace of a representation `ρ` for an eigenvalue function `χ`. -/
def weightSpace (ρ : A →* Module.End k V) (χ : A → k) : Submodule k V :=
  ⨅ a, (ρ a).eigenspace (χ a)

theorem mem_weightSpace {ρ : A →* Module.End k V} {χ : A → k} {w : V} :
    w ∈ weightSpace ρ χ ↔ ∀ a, ρ a w = χ a • w := by
  simp [weightSpace]

theorem disjoint_weightSpace (ρ : A →* Module.End k V) {χ ψ : A → k} (h : χ ≠ ψ) :
    Disjoint (weightSpace ρ χ) (weightSpace ρ ψ) := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp h
  rw [Submodule.disjoint_def]
  intro w hχ hψ
  have h' : (χ a - ψ a) • w = 0 := by
    rw [sub_smul, ← mem_weightSpace.1 hχ a, ← mem_weightSpace.1 hψ a, sub_self]
  exact (smul_eq_zero.1 h').resolve_left (sub_ne_zero.2 ha)

/-- Simultaneous eigenspaces for distinct eigenvalue functions are independent. -/
theorem iSupIndep_weightSpace (ρ : A →* Module.End k V) :
    iSupIndep fun χ : A → k => weightSpace ρ χ := by
  classical
  suffices h : ∀ (χ : A → k) (s : Finset (A → k)), χ ∉ s →
      Disjoint (weightSpace ρ χ) (s.sup fun ψ => weightSpace ρ ψ) by
    rw [iSupIndep_iff_supIndep]
    intro s
    rw [Finset.supIndep_iff_disjoint_erase]
    intro χ _
    exact h _ _ (s.notMem_erase χ)
  intro χ s
  induction s using Finset.induction_on with
  | empty => simp
  | insert ψ s _ ih =>
    intro hχ
    rw [Finset.mem_insert, not_or] at hχ
    obtain ⟨hχψ, hχs⟩ := hχ
    specialize ih hχs
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hχψ
    let T : Module.End k V := ρ a - ψ a • 1
    have hT : ∀ (φ : A → k), ∀ w ∈ weightSpace ρ φ, T w = (φ a - ψ a) • w := by
      intro φ w hw
      simp only [T, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        mem_weightSpace.1 hw a, sub_smul]
    have hle : (s.sup fun φ => weightSpace ρ φ) ≤
        (s.sup fun φ => weightSpace ρ φ).comap T := by
      refine Finset.sup_le fun φ hφ w hw => ?_
      rw [Submodule.mem_comap, hT φ w hw]
      exact Finset.le_sup (f := fun φ => weightSpace ρ φ) hφ
        ((weightSpace ρ φ).smul_mem _ hw)
    rw [Finset.sup_insert, disjoint_iff, Submodule.eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
    have hmem : (χ a - ψ a) • (y + z) ∈
        weightSpace ρ χ ⊓ s.sup fun φ => weightSpace ρ φ := by
      refine ⟨(weightSpace ρ χ).smul_mem _ hx, ?_⟩
      rw [← hT χ _ hx, map_add, hT ψ y hy, sub_self, zero_smul, zero_add]
      exact hle hz
    rw [ih.eq_bot, Submodule.mem_bot] at hmem
    exact (smul_eq_zero.1 hmem).resolve_left (sub_ne_zero.2 ha)

end Weights

section Closed

variable {k V G : Type*} [Field k] [AddCommGroup V] [Module k V] [Group G]
  [TopologicalSpace G] {ρ : G →* Module.End k V}

/-- If every scalar linear condition on `ρ` is closed, so is every vector-valued one. -/
theorem isClosed_linear_eq
    (hR : ∀ (Λ : Module.End k V →ₗ[k] k) (c : k), IsClosed {g : G | Λ (ρ g) = c})
    {M : Type*} [AddCommGroup M] [Module k M] (L : Module.End k V →ₗ[k] M) (m : M) :
    IsClosed {g : G | L (ρ g) = m} := by
  let b := Module.Basis.ofVectorSpace k M
  have h : {g : G | L (ρ g) = m} =
      ⋂ i, {g : G | (b.coord i ∘ₗ L) (ρ g) = b.coord i m} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, LinearMap.comp_apply,
      Module.Basis.coord_apply]
    exact b.ext_elem_iff
  rw [h]
  exact isClosed_iInter fun i => hR _ _

/-- The set of `g` such that `ρ g` maps `W` into `U` is closed. -/
theorem isClosed_mapsTo
    (hR : ∀ (Λ : Module.End k V →ₗ[k] k) (c : k), IsClosed {g : G | Λ (ρ g) = c})
    (W U : Submodule k V) : IsClosed {g : G | ∀ w ∈ W, ρ g w ∈ U} := by
  have h : {g : G | ∀ w ∈ W, ρ g w ∈ U} =
      ⋂ w : W, {g : G | (U.mkQ ∘ₗ LinearMap.applyₗ (w : V)) (ρ g) = 0} := by
    ext g
    simp [Submodule.Quotient.mk_eq_zero]
  rw [h]
  exact isClosed_iInter fun w => isClosed_linear_eq hR _ _

/-- The set of `g` such that `v` is a `c`-eigenvector of `ρ g` is closed. -/
theorem isClosed_eigen
    (hR : ∀ (Λ : Module.End k V →ₗ[k] k) (c : k), IsClosed {g : G | Λ (ρ g) = c})
    (v : V) (c : k) : IsClosed {g : G | ρ g v = c • v} :=
  isClosed_linear_eq hR (LinearMap.applyₗ v) (c • v)

end Closed

section Restrict

variable {k V G : Type*} [Field k] [AddCommGroup V] [Module k V] [Group G]

/-- The restriction of `ρ` to a subgroup `Γ` acting on an invariant subspace `W`. -/
noncomputable def restrictHom (ρ : G →* Module.End k V) (Γ : Subgroup G) (W : Submodule k V)
    (hW : ∀ g ∈ Γ, ∀ w ∈ W, ρ g w ∈ W) : Γ →* Module.End k W where
  toFun g := (ρ g).restrict (hW g g.2)
  map_one' := by
    ext w
    simp
  map_mul' g h := by
    ext w
    simp

theorem restrictHom_apply_coe (ρ : G →* Module.End k V) (Γ : Subgroup G) (W : Submodule k V)
    (hW : ∀ g ∈ Γ, ∀ w ∈ W, ρ g w ∈ W) (g : Γ) (w : W) :
    ((restrictHom ρ Γ W hW g w : W) : V) = ρ g w :=
  rfl

end Restrict

section LieKolchin

variable {k : Type*} {V : Type v} {G : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V]
  [Module k V] [FiniteDimensional k V] [Group G] [TopologicalSpace G]

/-- The inductive step of Lie–Kolchin, indexed by the remaining length `m` of the derived
series: the `i`-th derived subgroup has a common eigenvector whenever the `(i + m)`-th one is
trivial. -/
theorem exists_common_eigenvector_derivedSeries [PreconnectedSpace G]
    (hmul : ∀ a : G, Continuous fun x => a * x) (hinv : Continuous fun x : G => x⁻¹)
    (hcomm : ∀ a : G, Continuous fun x : G => ⁅a, x⁆)
    (ρ : G →* Module.End k V)
    (hR : ∀ (Λ : Module.End k V →ₗ[k] k) (c : k), IsClosed {g : G | Λ (ρ g) = c})
    [Nontrivial V] (m : ℕ) :
    ∀ i, derivedSeries G (i + m) = ⊥ →
      ∃ v : V, v ≠ 0 ∧ ∀ g ∈ derivedSeries G i, ∃ c : k, ρ g v = c • v := by
  induction m with
  | zero =>
    intro i hi
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨v, hv, fun g hg => ⟨1, ?_⟩⟩
    rw [Nat.add_zero] at hi
    rw [hi, Subgroup.mem_bot] at hg
    subst hg
    simp
  | succ m ih =>
    intro i hi
    have hi' : derivedSeries G (i + 1 + m) = ⊥ := by
      rw [show i + 1 + m = i + (m + 1) by omega]
      exact hi
    obtain ⟨v, hv0, hv⟩ := ih (i + 1) hi'
    have hnormal : (derivedSeries G (i + 1)).Normal := derivedSeries_normal G (i + 1)
    have hle : derivedSeries G (i + 1) ≤ derivedSeries G i :=
      derivedSeries_antitone G (Nat.le_succ i)
    have hconj : ∀ (g : G) (a : derivedSeries G (i + 1)),
        g⁻¹ * (a : G) * g ∈ derivedSeries G (i + 1) := by
      intro g a
      simpa using hnormal.conj_mem a a.2 g⁻¹
    have hinj : ∀ (g : G) (w : V), ρ g w = 0 → w = 0 := by
      intro g w h
      have e : ρ g⁻¹ (ρ g w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [← e, h, map_zero]
    let ρ' : derivedSeries G (i + 1) →* Module.End k V := ρ.comp (derivedSeries G (i + 1)).subtype
    choose χ hχ using fun a : derivedSeries G (i + 1) => hv a a.2
    set W := weightSpace ρ' χ with hWdef
    have hvW : v ∈ W := mem_weightSpace.2 hχ
    have hW0 : W ≠ ⊥ := fun h => hv0 (by rw [h] at hvW; exact (Submodule.mem_bot k).1 hvW)
    -- finitely many weights
    set T : Set (derivedSeries G (i + 1) → k) := {ψ | weightSpace ρ' ψ ≠ ⊥} with hTdef
    have hT : T.Finite := by
      have := (iSupIndep_weightSpace ρ').fintypeNeBotOfFiniteDimensional
      exact Set.finite_coe_iff.1 (Finite.of_fintype {ψ // weightSpace ρ' ψ ≠ ⊥})
    -- `ρ g` maps `W` into the weight space of the conjugate weight
    have hmaps : ∀ (g : G), ∀ w ∈ W,
        ρ g w ∈ weightSpace ρ' (fun a => χ ⟨g⁻¹ * a * g, hconj g a⟩) := by
      intro g w hw
      rw [mem_weightSpace] at hw ⊢
      intro a
      have h1 := hw ⟨g⁻¹ * a * g, hconj g a⟩
      change ρ (g⁻¹ * a * g) w = _ at h1
      change ρ (a : G) (ρ g w) = _
      have e : (a : G) * g = g * (g⁻¹ * a * g) := by group
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h1, map_smul]
    let S : (derivedSeries G (i + 1) → k) → Set G :=
      fun ψ => {g | ∀ w ∈ W, ρ g w ∈ weightSpace ρ' ψ}
    have hΓW : (derivedSeries G i : Set G) ⊆ S χ := by
      refine subset_of_finite_closed_cover
        (isConnected_derivedSeries hmul hinv hcomm i).isPreconnected hT S
        (fun ψ _ => isClosed_mapsTo hR W _) ?_ ?_ (hW0 : χ ∈ T) (derivedSeries G i).one_mem ?_
      · intro g _
        refine Set.mem_iUnion₂.2 ⟨_, ?_, hmaps g⟩
        intro h
        exact hv0 (hinj g v (by
          have := hmaps g v hvW
          rw [h] at this
          exact (Submodule.mem_bot k).1 this))
      · intro ψ _ ψ' _ hψψ' g _ hg hg'
        have h1 := hg v hvW
        have h2 := hg' v hvW
        exact hv0 (hinj g v (Submodule.disjoint_def.1 (disjoint_weightSpace ρ' hψψ') _ h1 h2))
      · intro w hw
        rw [map_one, Module.End.one_apply]
        exact hw
    -- the restriction of `ρ` to `W`
    let r := restrictHom ρ (derivedSeries G i) W fun g hg => hΓW hg
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
    have hr_scalar : ∀ a : derivedSeries G (i + 1), r ⟨a, hle a.2⟩ = χ a • 1 := by
      intro a
      refine LinearMap.ext fun w => Subtype.ext ?_
      rw [restrictHom_apply_coe]
      exact mem_weightSpace.1 w.2 a
    -- the determinant of `r` kills the commutator subgroup
    let D : derivedSeries G i →* kˣ := (LinearMap.det.comp r).toHomUnits
    have hker : derivedSeries G (i + 1) ≤ D.ker.map (derivedSeries G i).subtype := by
      rw [derivedSeries_succ, Subgroup.commutator_le]
      intro x hx y hy
      refine Subgroup.mem_map.2 ⟨⁅(⟨x, hx⟩ : derivedSeries G i), ⟨y, hy⟩⁆, ?_, rfl⟩
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
        mul_comm]
    have hroot : ∀ a : derivedSeries G (i + 1),
        χ a ^ Module.finrank k W = 1 := by
      intro a
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.1 (hker a.2)
      have hb' : b = ⟨a, hle a.2⟩ := Subtype.ext hba
      have h1 : LinearMap.det (r b) = 1 := congrArg Units.val ((MonoidHom.mem_ker).1 hb)
      rw [hb', hr_scalar, LinearMap.det_smul, map_one, mul_one] at h1
      exact h1
    have hd : 0 < Module.finrank k W := Module.finrank_pos
    -- the weight `χ` is trivial, by connectedness of the commutator subgroup
    have htriv : (derivedSeries G (i + 1) : Set G) ⊆ {g | ρ g v = (1 : k) • v} := by
      refine subset_of_finite_closed_cover
        (isConnected_derivedSeries hmul hinv hcomm (i + 1)).isPreconnected
        (Polynomial.nthRootsFinset (Module.finrank k W) (1 : k)).finite_toSet
        (fun ζ => {g : G | ρ g v = ζ • v}) (fun ζ _ => isClosed_eigen hR v ζ) ?_ ?_
        (by simp [Polynomial.mem_nthRootsFinset hd]) (derivedSeries G (i + 1)).one_mem
        (by simp)
      · intro a ha
        refine Set.mem_iUnion₂.2 ⟨χ ⟨a, ha⟩, ?_, hχ ⟨a, ha⟩⟩
        simpa [Polynomial.mem_nthRootsFinset hd] using hroot ⟨a, ha⟩
      · intro ζ _ ζ' _ hζ g _ h1 h2
        have h1' : ρ g v = ζ • v := h1
        have h2' : ρ g v = ζ' • v := h2
        have h3 : (ζ - ζ') • v = 0 := by
          rw [sub_smul, ← h1', ← h2', sub_self]
        exact hζ (sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hv0))
    have hχ1 : ∀ a : derivedSeries G (i + 1), χ a = 1 := by
      intro a
      have h1 : ρ a v = (1 : k) • v := htriv a.2
      rw [hχ a] at h1
      exact smul_left_injective k hv0 h1
    have hr_one : ∀ a : derivedSeries G (i + 1), r ⟨a, hle a.2⟩ = 1 := by
      intro a
      rw [hr_scalar, hχ1, one_smul]
    -- hence the restricted operators commute
    have hcommute : ∀ x y : derivedSeries G i, Commute (r x) (r y) := by
      intro x y
      have hxy : ((⁅x, y⁆ : derivedSeries G i) : G) ∈ derivedSeries G (i + 1) := by
        rw [derivedSeries_succ]
        exact Subgroup.commutator_mem_commutator x.2 y.2
      have h1 : r ⁅x, y⁆ = 1 := hr_one ⟨_, hxy⟩
      have h2 : x * y = ⁅x, y⁆ * (y * x) := by
        rw [commutatorElement_def]
        group
      change r x * r y = r y * r x
      rw [← map_mul, ← map_mul, h2, map_mul, h1, one_mul]
    obtain ⟨w, hw0, hw⟩ := exists_common_eigenvector (fun x => r x) hcommute
    refine ⟨w, fun h => hw0 (Subtype.ext h), fun g hg => ?_⟩
    obtain ⟨c, hc⟩ := hw ⟨g, hg⟩
    exact ⟨c, congrArg Subtype.val hc⟩

/-- **Lie–Kolchin, abstract form.** A representation of a connected solvable group with
separately continuous group laws on a nonzero finite-dimensional vector space over an
algebraically closed field has a common eigenvector, provided every linear condition on the
representation is closed. -/
theorem exists_common_eigenvector_of_isSolvable [PreconnectedSpace G] [Group.IsSolvable G]
    [Nontrivial V]
    (hmul : ∀ a : G, Continuous fun x => a * x) (hinv : Continuous fun x : G => x⁻¹)
    (hcomm : ∀ a : G, Continuous fun x : G => ⁅a, x⁆)
    (ρ : G →* Module.End k V)
    (hR : ∀ (Λ : Module.End k V →ₗ[k] k) (c : k), IsClosed {g : G | Λ (ρ g) = c}) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ∃ c : k, ρ g v = c • v := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  obtain ⟨v, hv0, hv⟩ :=
    exists_common_eigenvector_derivedSeries hmul hinv hcomm ρ hR n 0 (by rwa [Nat.zero_add])
  exact ⟨v, hv0, fun g => hv g (by rw [derivedSeries_zero]; exact Subgroup.mem_top g)⟩

end LieKolchin

end Langlands.LieKolchin
