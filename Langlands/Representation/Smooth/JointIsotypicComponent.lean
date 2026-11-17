import Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof
import Langlands.Representation.FiniteVectors
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# An isotypic component of a smooth representation inside a jointly irreducible action

Let `σ` be a smooth complex representation of a topological group `G` on `V`, and let `C`
be a set of linear operators on `V` commuting with every `σ g`. Suppose that `σ` and `C`
together act irreducibly: every subspace stable under all `σ g` and all `c ∈ C` is `0`
or `V`.

* `iSup_range_eq_top`: for every nonzero subrepresentation `U` of `σ`, the images of the
  `G`-intertwining maps `U → V` span `V`.
* `exists_irreducible_admissible_isotypic`: if moreover every open subgroup of `G` contains
  a compact open subgroup and some `σ`-stable subspace `N ≠ 0` has finite-dimensional
  intersection with the fixed vectors of every compact open subgroup, then `σ` has an
  irreducible admissible subrepresentation `U ≤ N`, and `V` is `U`-isotypic.
* `typeSpan`, `finiteDimensional_fixedVectors_inf_typeSpan`: a supply of such `N`. For a
  representation `κ` of a group `K` commuting with `σ`, a representation `τ` of `K` on a
  finite-dimensional space and a `σ`-stable subspace `P`, `typeSpan κ τ P` is the span of
  the images of the `K`-equivariant maps `τ → V` with values in `P`. Its intersection
  with the fixed vectors of a compact open `L` is finite-dimensional as soon as the
  space of such maps with values in `P ⊓ V^L` is.

The arguments generalize the proof of Flath's two-factor theorem in
`Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof`, where `C` is
the action of the second factor.
-/

noncomputable section

namespace Langlands.JointIsotypic

open Representation FiniteVectors TwoFactorExistence
open scoped TensorProduct

universe uG uK uV uE

section Algebra

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- `σ` and the operators in `C` act irreducibly together: a subspace stable under every
`σ g` and every `c ∈ C` is `0` or everything. -/
def IsJointlyIrreducible (σ : Representation ℂ G V) (C : Set (Module.End ℂ V)) : Prop :=
  ∀ P : Submodule ℂ V, (∀ (g : G), ∀ x ∈ P, σ g x ∈ P) → (∀ c ∈ C, ∀ x ∈ P, c x ∈ P) →
    P = ⊥ ∨ P = ⊤

/-- Every operator in `C` commutes with every `σ g`. -/
def CommutesWith (σ : Representation ℂ G V) (C : Set (Module.End ℂ V)) : Prop :=
  ∀ c ∈ C, ∀ (g : G) (x : V), c (σ g x) = σ g (c x)

variable {σ : Representation ℂ G V} {C : Set (Module.End ℂ V)}

/-- An operator commuting with `σ`, as an intertwining map from `σ` to itself. -/
def commutingHom (c : Module.End ℂ V) (hc : ∀ (g : G) (x : V), c (σ g x) = σ g (c x)) :
    σ.IntertwiningMap σ where
  toLinearMap := c
  isIntertwining' g := LinearMap.ext fun x => hc g x

theorem commutingHom_apply (c : Module.End ℂ V) (hc : ∀ (g : G) (x : V), c (σ g x) = σ g (c x))
    (x : V) : commutingHom c hc x = c x := rfl

/-- **Isotypy.** If `C` commutes with `σ` and `σ` and `C` act irreducibly together, then the
images of the intertwining maps from a nonzero subrepresentation `U` of `σ` span `V`. -/
theorem iSup_range_eq_top (hC : CommutesWith σ C) (hirr : IsJointlyIrreducible σ C)
    (U : Subrepresentation σ) (hU : U ≠ ⊥) :
    ⨆ f : U.toRepresentation.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤ := by
  let T : Submodule ℂ V :=
    ⨆ f : U.toRepresentation.IntertwiningMap σ, LinearMap.range f.toLinearMap
  have hσ : ∀ (g : G), ∀ x ∈ T, σ g x ∈ T := by
    intro g x hx
    refine Submodule.iSup_induction _ (motive := fun x => σ g x ∈ T) hx ?_ ?_ ?_
    · rintro f _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem f
        ⟨U.toRepresentation g u, LinearMap.congr_fun (f.isIntertwining' g) u⟩
    · rw [map_zero]
      exact T.zero_mem
    · intro x y hx hy
      rw [map_add]
      exact T.add_mem hx hy
  have hCT : ∀ c ∈ C, ∀ x ∈ T, c x ∈ T := by
    intro c hc x hx
    refine Submodule.iSup_induction _ (motive := fun x => c x ∈ T) hx ?_ ?_ ?_
    · rintro f _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem ((commutingHom c (hC c hc)).comp f) ⟨u, rfl⟩
    · rw [map_zero]
      exact T.zero_mem
    · intro x y hx hy
      rw [map_add]
      exact T.add_mem hx hy
  rcases hirr T hσ hCT with h | h
  · exfalso
    obtain ⟨u, hu, hu0⟩ := exists_ne_zero_of_ne_bot hU
    have hT : u ∈ T := Submodule.mem_iSup_of_mem (subtypeHom U) ⟨⟨u, hu⟩, rfl⟩
    rw [h] at hT
    exact hu0 ((Submodule.mem_bot ℂ).mp hT)
  · exact h

/-- A vector `y` that lies in the orbit span of every nonzero vector of its own orbit span
generates an irreducible subrepresentation. -/
theorem isIrreducible_orbitSubrepresentation {y : V} (hy : y ≠ 0)
    (hcyc : ∀ u ∈ orbitSpan σ y, u ≠ 0 → y ∈ orbitSpan σ u) :
    (orbitSubrepresentation σ y).toRepresentation.IsIrreducible := by
  let U := orbitSubrepresentation σ y
  have key : ∀ P : Subrepresentation U.toRepresentation, P ≠ ⊥ →
      ∀ w : U.toSubmodule, w ∈ P := by
    intro P hP w
    obtain ⟨p, hp, hp0⟩ := exists_ne_zero_of_ne_bot hP
    let R : Subrepresentation σ :=
      { toSubmodule := P.toSubmodule.map U.toSubmodule.subtype
        apply_mem_toSubmodule := by
          rintro g _ ⟨v, hv, rfl⟩
          exact ⟨U.toRepresentation g v, P.apply_mem_toSubmodule g hv, rfl⟩ }
    have hpR : (p : V) ∈ R.toSubmodule := ⟨p, hp, rfl⟩
    have hp0' : (p : V) ≠ 0 := fun h => hp0 (Subtype.ext h)
    have hyR : y ∈ R.toSubmodule := orbitSpan_le σ _ R hpR (hcyc p p.2 hp0')
    have hwR : (w : V) ∈ R.toSubmodule := orbitSpan_le σ y R hyR w.2
    obtain ⟨v, hv, hvw⟩ := Submodule.mem_map.mp hwR
    have hvw' : v = w := Subtype.ext hvw
    rw [← hvw']
    exact hv
  have hy' : (⟨y, self_mem_orbitSpan σ y⟩ : U.toSubmodule) ≠ 0 :=
    fun h => hy (congrArg Subtype.val h)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hy' ?_⟩, eq_bot_or_eq_top := fun P => ?_ }
  · have h1 := mem_top (σ := U.toRepresentation) ⟨y, self_mem_orbitSpan σ y⟩
    rw [← h] at h1
    exact mem_bot_iff.mp h1
  · by_cases hP : P = ⊥
    · exact Or.inl hP
    · exact Or.inr (eq_top_of_forall P (key P hP))

theorem orbitSubrepresentation_ne_bot {y : V} (hy : y ≠ 0) : orbitSubrepresentation σ y ≠ ⊥ := by
  intro h
  have h1 : y ∈ (orbitSubrepresentation σ y).toSubmodule := self_mem_orbitSpan σ y
  rw [h] at h1
  exact hy ((Submodule.mem_bot ℂ).mp h1)

end Algebra

section Topology

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {σ : Representation ℂ G V} {C : Set (Module.End ℂ V)}

/-- If `σ` and `C` act irreducibly together and a nonzero vector is fixed by a compact open
subgroup `K`, then every nonzero subrepresentation of `σ` contains a nonzero `K`-fixed
vector. -/
theorem exists_fixed_of_ne_bot (hC : CommutesWith σ C) (hirr : IsJointlyIrreducible σ C)
    (hs : IsSmooth σ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {x : V} (hx0 : x ≠ 0)
    (hx : x ∈ fixedVectors σ K.toSubgroup) {N : Subrepresentation σ} (hN : N ≠ ⊥) :
    ∃ n ∈ N, n ≠ 0 ∧ n ∈ fixedVectors σ K.toSubgroup := by
  by_contra hcon
  let e := Compact.averageMap σ hs K hK
  have hcomm : ∀ c ∈ C, ∀ v, e (c v) = c (e v) := fun c hc v =>
    (LinearMap.congr_fun
      (Compact.averageMap_commute σ σ hs hs K hK (commutingHom c (hC c hc))) v).symm
  have hN0 : ∀ n ∈ N, e n = 0 := by
    intro n hn
    have hsN := isSmooth_toRepresentation hs N
    have h : ((Compact.averageMap N.toRepresentation hsN K hK ⟨n, hn⟩ : N.toSubmodule) : V) =
        e n :=
      LinearMap.congr_fun
        (Compact.averageMap_commute N.toRepresentation σ hsN hs K hK (subtypeHom N)) ⟨n, hn⟩
    have hmem : e n ∈ N := by
      rw [← h]
      exact Subtype.prop _
    by_contra hne
    exact hcon ⟨_, hmem, hne, Compact.averageMap_mem_fixedVectors _ _ _ _ n⟩
  let Z : Submodule ℂ V := ⨅ g : G, LinearMap.ker (e ∘ₗ σ g)
  have hmemZ : ∀ v, v ∈ Z ↔ ∀ g : G, e (σ g v) = 0 := by
    intro v
    simp only [Z, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
  have hZσ : ∀ (h : G), ∀ v ∈ Z, σ h v ∈ Z := by
    intro h v hv
    rw [hmemZ] at hv ⊢
    intro g
    have h' := hv (g * h)
    rwa [map_mul, Module.End.mul_apply] at h'
  have hZC : ∀ c ∈ C, ∀ v ∈ Z, c v ∈ Z := by
    intro c hc v hv
    rw [hmemZ] at hv ⊢
    intro g
    rw [← hC c hc, hcomm c hc, hv g, map_zero]
  have hNZ : ∀ n ∈ N, n ∈ Z := by
    intro n hn
    rw [hmemZ]
    intro g
    exact hN0 _ (N.apply_mem_toSubmodule g hn)
  have hxZ : x ∉ Z := by
    intro h
    rw [hmemZ] at h
    have h2 := h 1
    rw [map_one, Module.End.one_apply, Compact.averageMap_id _ _ _ _ x hx] at h2
    exact hx0 h2
  rcases hirr Z hZσ hZC with hZ | hZ
  · refine hN (eq_bot_of_forall N fun n hn => ?_)
    have h := hNZ n hn
    rw [hZ] at h
    exact (Submodule.mem_bot ℂ).mp h
  · apply hxZ
    rw [hZ]
    exact Submodule.mem_top

/-- Choice of a nonzero `y ∈ N` lying in the orbit span of every nonzero vector of its own
orbit span: `y` minimizes the dimension of the part of its orbit span fixed by a compact
open subgroup and lying in `N`. -/
theorem exists_cyclic (hC : CommutesWith σ C) (hirr : IsJointlyIrreducible σ C)
    (hs : IsSmooth σ)
    (hcpt : ∀ W : OpenSubgroup G, ∃ K : OpenSubgroup G, K ≤ W ∧ IsCompact (K : Set G))
    (N : Subrepresentation σ)
    (hfin : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      FiniteDimensional ℂ ↥(fixedVectors σ K.toSubgroup ⊓ N.toSubmodule))
    {x : V} (hxN : x ∈ N.toSubmodule) (hx : x ≠ 0) :
    ∃ y ∈ N.toSubmodule, y ≠ 0 ∧ ∀ u ∈ orbitSpan σ y, u ≠ 0 → y ∈ orbitSpan σ u := by
  classical
  obtain ⟨W, hW⟩ := hs x
  obtain ⟨K, hKW, hK⟩ := hcpt W
  let M : Submodule ℂ V := fixedVectors σ K.toSubgroup ⊓ N.toSubmodule
  have hMfin : FiniteDimensional ℂ M := hfin K hK
  have hxM : x ∈ M := Submodule.mem_inf.mpr
    ⟨mem_fixedVectors_iff.mpr fun k hk => (mem_fixedVectors_iff.mp hW) k (hKW hk), hxN⟩
  let S : V → Submodule ℂ V := fun z => orbitSpan σ z ⊓ M
  have hex : ∃ d, ∃ z ∈ M, z ≠ 0 ∧ Module.finrank ℂ (S z) = d := ⟨_, x, hxM, hx, rfl⟩
  obtain ⟨y, hyM, hy0, hyd⟩ := Nat.find_spec hex
  have hmin : ∀ z ∈ M, z ≠ 0 → Module.finrank ℂ (S y) ≤ Module.finrank ℂ (S z) := by
    intro z hz hz0
    rw [hyd]
    exact Nat.find_min' hex ⟨z, hz, hz0, rfl⟩
  obtain ⟨hy₁, hyN⟩ := Submodule.mem_inf.mp hyM
  refine ⟨y, hyN, hy0, fun u hu hu0 => ?_⟩
  obtain ⟨n, hn, hn0, hn₁⟩ :=
    exists_fixed_of_ne_bot hC hirr hs K hK hy0 hy₁ (orbitSubrepresentation_ne_bot hu0)
  have hn' : n ∈ orbitSpan σ u := hn
  have hny : n ∈ orbitSpan σ y := orbitSpan_le σ u (orbitSubrepresentation σ y) hu hn'
  have hnN : n ∈ N.toSubmodule := orbitSpan_le σ y N hyN hny
  have hle : S n ≤ S y := inf_le_inf_right M (orbitSpan_le σ n (orbitSubrepresentation σ y) hny)
  have hfy : FiniteDimensional ℂ (S y) := Submodule.finiteDimensional_of_le inf_le_right
  have heq : S n = S y :=
    Submodule.eq_of_le_of_finrank_le hle (hmin n (Submodule.mem_inf.mpr ⟨hn₁, hnN⟩) hn0)
  have hyS : y ∈ S y := Submodule.mem_inf.mpr ⟨self_mem_orbitSpan σ y, hyM⟩
  rw [← heq] at hyS
  exact orbitSpan_le σ n (orbitSubrepresentation σ u) hn' (Submodule.mem_inf.mp hyS).1

omit [IsTopologicalGroup G] in
/-- A subrepresentation contained in `N` is admissible when `N` meets the fixed vectors of
every compact open subgroup in a finite-dimensional space and every open subgroup contains
a compact open one. -/
theorem isAdmissible_of_le (hs : IsSmooth σ)
    (hcpt : ∀ W : OpenSubgroup G, ∃ K : OpenSubgroup G, K ≤ W ∧ IsCompact (K : Set G))
    (N : Subrepresentation σ)
    (hfin : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      FiniteDimensional ℂ ↥(fixedVectors σ K.toSubgroup ⊓ N.toSubmodule))
    (U : Subrepresentation σ) (hUN : U.toSubmodule ≤ N.toSubmodule) :
    IsAdmissible U.toRepresentation := by
  refine ⟨isSmooth_toRepresentation hs U, fun L => ?_⟩
  obtain ⟨K, hKL, hK⟩ := hcpt L
  have hKfin := hfin K hK
  have hmap : ∀ w : fixedVectors U.toRepresentation L.toSubgroup,
      ((w : U.toSubmodule) : V) ∈ fixedVectors σ K.toSubgroup ⊓ N.toSubmodule := by
    intro w
    refine Submodule.mem_inf.mpr ⟨mem_fixedVectors_iff.mpr fun k hk => ?_,
      hUN (w : U.toSubmodule).2⟩
    exact congrArg Subtype.val ((mem_fixedVectors_iff.mp w.2) k (hKL hk))
  let f : fixedVectors U.toRepresentation L.toSubgroup →ₗ[ℂ]
      ↥(fixedVectors σ K.toSubgroup ⊓ N.toSubmodule) :=
    LinearMap.codRestrict _
      (U.toSubmodule.subtype ∘ₗ (fixedVectors U.toRepresentation L.toSubgroup).subtype) hmap
  refine Module.Finite.of_injective f fun a b hab => ?_
  have h := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext h)

/-- **Existence of an isotypic component.** Let `σ` be smooth, `C` commute with `σ`, and
`σ` and `C` act irreducibly together. Suppose that every open subgroup of `G` contains a
compact open subgroup and that a nonzero `σ`-stable subspace `N` meets the fixed vectors
of every compact open subgroup in a finite-dimensional space. Then `σ` has an irreducible
admissible subrepresentation `U` such that the images of the intertwining maps `U → V`
span `V`. -/
theorem exists_irreducible_admissible_isotypic (hC : CommutesWith σ C)
    (hirr : IsJointlyIrreducible σ C) (hs : IsSmooth σ)
    (hcpt : ∀ W : OpenSubgroup G, ∃ K : OpenSubgroup G, K ≤ W ∧ IsCompact (K : Set G))
    (N : Subrepresentation σ)
    (hfin : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      FiniteDimensional ℂ ↥(fixedVectors σ K.toSubgroup ⊓ N.toSubmodule))
    {x : V} (hxN : x ∈ N.toSubmodule) (hx : x ≠ 0) :
    ∃ U : Subrepresentation σ, U.toRepresentation.IsIrreducible ∧
      IsAdmissible U.toRepresentation ∧
      ⨆ f : U.toRepresentation.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤ := by
  obtain ⟨y, hyN, hy0, hcyc⟩ := exists_cyclic hC hirr hs hcpt N hfin hxN hx
  exact ⟨orbitSubrepresentation σ y, isIrreducible_orbitSubrepresentation hy0 hcyc,
    isAdmissible_of_le hs hcpt N hfin _ (orbitSpan_le σ y N hyN),
    iSup_range_eq_top hC hirr _ (orbitSubrepresentation_ne_bot hy0)⟩

end Topology

section TypeSpan

variable {G : Type uG} [Group G] {K : Type uK} [Group K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {E : Type uE} [AddCommGroup E] [Module ℂ E]

/-- The `K`-equivariant linear maps from `τ` to `κ` with values in the subspace `P`. -/
def equivariantInto (κ : Representation ℂ K V) (τ : Representation ℂ K E)
    (P : Submodule ℂ V) : Submodule ℂ (E →ₗ[ℂ] V) where
  carrier := {φ | (∀ w, φ w ∈ P) ∧ ∀ (k : K) (w : E), φ (τ k w) = κ k (φ w)}
  add_mem' := by
    rintro φ ψ ⟨hφ, hφ'⟩ ⟨hψ, hψ'⟩
    refine ⟨fun w => P.add_mem (hφ w) (hψ w), fun k w => ?_⟩
    simp only [LinearMap.add_apply, map_add, hφ', hψ']
  zero_mem' := ⟨fun _ => P.zero_mem, fun k w => by simp⟩
  smul_mem' := by
    rintro a φ ⟨hφ, hφ'⟩
    refine ⟨fun w => P.smul_mem a (hφ w), fun k w => ?_⟩
    simp only [LinearMap.smul_apply, map_smul, hφ']

theorem mem_equivariantInto (κ : Representation ℂ K V) (τ : Representation ℂ K E)
    (P : Submodule ℂ V) (φ : E →ₗ[ℂ] V) :
    φ ∈ equivariantInto κ τ P ↔ (∀ w, φ w ∈ P) ∧ ∀ (k : K) (w : E), φ (τ k w) = κ k (φ w) :=
  Iff.rfl

theorem equivariantInto_mono (κ : Representation ℂ K V) (τ : Representation ℂ K E)
    {P P' : Submodule ℂ V} (h : P ≤ P') : equivariantInto κ τ P ≤ equivariantInto κ τ P' :=
  fun _ hφ => ⟨fun w => h (hφ.1 w), hφ.2⟩

/-- The span of the images of the `K`-equivariant maps from `τ` with values in `P`. -/
def typeSpan (κ : Representation ℂ K V) (τ : Representation ℂ K E) (P : Submodule ℂ V) :
    Submodule ℂ V :=
  ⨆ φ : equivariantInto κ τ P, LinearMap.range (φ : E →ₗ[ℂ] V)

theorem apply_mem_typeSpan {κ : Representation ℂ K V} {τ : Representation ℂ K E}
    {P : Submodule ℂ V} {φ : E →ₗ[ℂ] V} (hφ : φ ∈ equivariantInto κ τ P) (w : E) :
    φ w ∈ typeSpan κ τ P :=
  Submodule.mem_iSup_of_mem (⟨φ, hφ⟩ : equivariantInto κ τ P) ⟨w, rfl⟩

variable {σ : Representation ℂ G V} {κ : Representation ℂ K V} {τ : Representation ℂ K E}

/-- If `κ` commutes with `σ` and `P` is `σ`-stable, the type span is `σ`-stable. -/
theorem typeSpan_stable (hκ : ∀ (k : K) (g : G) (x : V), κ k (σ g x) = σ g (κ k x))
    (P : Subrepresentation σ) (g : G) {x : V} (hx : x ∈ typeSpan κ τ P.toSubmodule) :
    σ g x ∈ typeSpan κ τ P.toSubmodule := by
  refine Submodule.iSup_induction _
    (motive := fun x => σ g x ∈ typeSpan κ τ P.toSubmodule) hx ?_ ?_ ?_
  · rintro ⟨φ, hφ, hφ'⟩ _ ⟨w, rfl⟩
    have hψ : σ g ∘ₗ φ ∈ equivariantInto κ τ P.toSubmodule :=
      ⟨fun w => P.apply_mem_toSubmodule g (hφ w), fun k w => by
        simp only [LinearMap.comp_apply, hφ', hκ]⟩
    exact apply_mem_typeSpan hψ w
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- The type span as a subrepresentation of `σ`. -/
def typeSpanSubrepresentation (hκ : ∀ (k : K) (g : G) (x : V), κ k (σ g x) = σ g (κ k x))
    (τ : Representation ℂ K E) (P : Subrepresentation σ) : Subrepresentation σ where
  toSubmodule := typeSpan κ τ P.toSubmodule
  apply_mem_toSubmodule g _ hx := typeSpan_stable hκ P g hx

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The fixed vectors of a compact open `L` in the type span lie in the span of the images
of the equivariant maps with values in `P ⊓ V^L`; hence they form a finite-dimensional
space when those maps do and `E` is finite-dimensional. -/
theorem finiteDimensional_fixedVectors_inf_typeSpan [FiniteDimensional ℂ E] (hs : IsSmooth σ)
    (hκ : ∀ (k : K) (g : G) (x : V), κ k (σ g x) = σ g (κ k x)) (P : Subrepresentation σ)
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G))
    (hJ : FiniteDimensional ℂ
      (equivariantInto κ τ (P.toSubmodule ⊓ fixedVectors σ L.toSubgroup))) :
    FiniteDimensional ℂ ↥(fixedVectors σ L.toSubgroup ⊓ typeSpan κ τ P.toSubmodule) := by
  let J := equivariantInto κ τ (P.toSubmodule ⊓ fixedVectors σ L.toSubgroup)
  have hJ' : Module.Finite ℂ J := hJ
  have hJE : Module.Finite ℂ (J ⊗[ℂ] E) := Module.Finite.tensorProduct ℂ J E
  let T : J ⊗[ℂ] E →ₗ[ℂ] V := TensorProduct.lift J.subtype
  let R : Submodule ℂ V := LinearMap.range T
  have hR : FiniteDimensional ℂ R := Module.Finite.range T
  let e := Compact.averageMap σ hs L hL
  have heκ : ∀ (k : K) (v : V), e (κ k v) = κ k (e v) := fun k v =>
    (LinearMap.congr_fun (Compact.averageMap_commute σ σ hs hs L hL
      (commutingHom (κ k) (fun g x => hκ k g x))) v).symm
  have heP : ∀ v ∈ P.toSubmodule, e v ∈ P.toSubmodule := by
    intro v hv
    have hsP := isSmooth_toRepresentation hs P
    have h : ((Compact.averageMap P.toRepresentation hsP L hL ⟨v, hv⟩ : P.toSubmodule) : V) =
        e v :=
      LinearMap.congr_fun
        (Compact.averageMap_commute P.toRepresentation σ hsP hs L hL (subtypeHom P)) ⟨v, hv⟩
    rw [← h]
    exact Subtype.prop _
  have key : ∀ y ∈ typeSpan κ τ P.toSubmodule, e y ∈ R := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y => e y ∈ R) hy ?_ ?_ ?_
    · rintro ⟨φ, hφ, hφ'⟩ _ ⟨w, rfl⟩
      have hψ : e ∘ₗ φ ∈ J :=
        ⟨fun w => Submodule.mem_inf.mpr ⟨heP _ (hφ w),
          Compact.averageMap_mem_fixedVectors σ hs L hL _⟩, fun k w => by
          simp only [LinearMap.comp_apply, hφ', heκ]⟩
      exact ⟨(⟨e ∘ₗ φ, hψ⟩ : J) ⊗ₜ w, TensorProduct.lift.tmul _ _⟩
    · rw [map_zero]
      exact R.zero_mem
    · intro x y hx hy
      rw [map_add]
      exact R.add_mem hx hy
  have hle : fixedVectors σ L.toSubgroup ⊓ typeSpan κ τ P.toSubmodule ≤ R := by
    intro x hx
    obtain ⟨hxL, hxT⟩ := Submodule.mem_inf.mp hx
    have h := key x hxT
    rwa [Compact.averageMap_id σ hs L hL x hxL] at h
  exact Submodule.finiteDimensional_of_le hle

/-- **Existence of an isotypic component, multiplicity form.** As
`exists_irreducible_admissible_isotypic`, with `N` the type span of `τ` in a `σ`-stable
`P`: it suffices that some equivariant map into `P` is nonzero and that for every compact
open `L` the equivariant maps with values in `P ⊓ V^L` form a finite-dimensional space. -/
theorem exists_irreducible_admissible_isotypic_of_typeSpan [FiniteDimensional ℂ E]
    {C : Set (Module.End ℂ V)} (hC : CommutesWith σ C) (hirr : IsJointlyIrreducible σ C)
    (hs : IsSmooth σ)
    (hcpt : ∀ W : OpenSubgroup G, ∃ K : OpenSubgroup G, K ≤ W ∧ IsCompact (K : Set G))
    (hκ : ∀ (k : K) (g : G) (x : V), κ k (σ g x) = σ g (κ k x)) (P : Subrepresentation σ)
    (hJ : ∀ L : OpenSubgroup G, IsCompact (L : Set G) → FiniteDimensional ℂ
      (equivariantInto κ τ (P.toSubmodule ⊓ fixedVectors σ L.toSubgroup)))
    {φ : E →ₗ[ℂ] V} (hφ : φ ∈ equivariantInto κ τ P.toSubmodule) {w : E} (hw : φ w ≠ 0) :
    ∃ U : Subrepresentation σ, U.toRepresentation.IsIrreducible ∧
      IsAdmissible U.toRepresentation ∧
      ⨆ f : U.toRepresentation.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤ :=
  exists_irreducible_admissible_isotypic hC hirr hs hcpt (typeSpanSubrepresentation hκ τ P)
    (fun L hL => finiteDimensional_fixedVectors_inf_typeSpan hs hκ P L hL (hJ L hL))
    (apply_mem_typeSpan hφ w) hw

end TypeSpan

end Langlands.JointIsotypic
