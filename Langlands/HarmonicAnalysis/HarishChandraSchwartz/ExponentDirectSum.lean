import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDecomposition
import Langlands.Representation.Smooth.FixedVectors.OrderProof
import Mathlib.Algebra.DirectSum.Module

/-!
# The decomposition `V = ⊕_{χ ∈ 𝓔xp(π)} V_χ` (Waldspurger I.3)

For a commutative group `A` acting on a space `Y` so that every vector lies in a
finite-dimensional stable subspace, `Y` is the internal direct sum of the simultaneous
generalized eigenspaces `Y_χ`; if moreover `Y` is generated, under operators commuting with `A`,
by a finite-dimensional stable subspace, only finitely many `Y_χ` are nonzero. For an admissible
representation of `G` and a central `A` this gives `V = ⊕_{χ ∈ 𝓔xp(π)} V_χ`, with `𝓔xp(π)`
finite when `π` is finitely generated.
-/

namespace Langlands.HarishChandraSchwartz

section Abstract

variable {A : Type*} [CommGroup A] {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

/-- The exponents of `T`: the functions `χ : A → ℂ` whose simultaneous generalized eigenspace
`Y_χ` is nonzero (Waldspurger's `𝓔xp(π)` for `T = π|_{A_G}`). -/
def exponentSet (T : A →* Module.End ℂ Y) : Set (A → ℂ) :=
  {χ | jointGenEigenspace T χ ≠ ⊥}

/-- The spaces `Y_χ` are independent. -/
theorem iSupIndep_jointGenEigenspace (T : A →* Module.End ℂ Y) :
    iSupIndep (jointGenEigenspace T) :=
  Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (f := fun a => T a)
    fun a b φ => Module.End.mapsTo_maxGenEigenspace_of_comm (commute_jointFamily T b a) φ

/-- An endomorphism commuting with every `T a` preserves every `Y_χ`. -/
theorem mapsTo_jointGenEigenspace_of_commute (T : A →* Module.End ℂ Y) {g : Module.End ℂ Y}
    (hg : ∀ a, Commute (T a) g) (χ : A → ℂ) {y : Y} (hy : y ∈ jointGenEigenspace T χ) :
    g y ∈ jointGenEigenspace T χ := by
  change g y ∈ ⨅ a, (T a).maxGenEigenspace (χ a)
  change y ∈ ⨅ a, (T a).maxGenEigenspace (χ a) at hy
  rw [Submodule.mem_iInf] at hy ⊢
  exact fun a => Module.End.mapsTo_maxGenEigenspace_of_comm (hg a) (χ a) (hy a)

/-- On a finite-dimensional `T`-stable subspace the exponent in the definition of `Y_χ` can be
chosen independently of `a` (the source's `∃ d, ∀ a`). -/
theorem mem_jointGenEigenspace_iff_exists_pow (T : A →* Module.End ℂ Y) (W : Submodule ℂ Y)
    [FiniteDimensional ℂ W] (hW : ∀ a, ∀ x ∈ W, T a x ∈ W) {χ : A → ℂ} {y : Y} (hy : y ∈ W) :
    y ∈ jointGenEigenspace T χ ↔ ∃ d : ℕ, ∀ a, ((T a - χ a • 1) ^ d) y = 0 := by
  constructor
  · intro h
    refine ⟨Module.finrank ℂ W, fun a => ?_⟩
    obtain ⟨k, hk⟩ := mem_jointGenEigenspace.1 h a
    have hmaps : ∀ x ∈ W, (T a - χ a • 1) x ∈ W := fun x hx => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact W.sub_mem (hW a x hx) (W.smul_mem _ hx)
    let f := (T a - χ a • 1).restrict hmaps
    have hpow : ∀ n, ((f ^ n) ⟨y, hy⟩ : Y) = ((T a - χ a • 1) ^ n) y := fun n => by
      rw [Module.End.pow_restrict]; rfl
    have hk' : (⟨y, hy⟩ : W) ∈ LinearMap.ker (f ^ k) := by
      rw [LinearMap.mem_ker]; ext; rw [hpow, hk]; rfl
    have h' := Module.End.ker_pow_le_ker_pow_finrank f k hk'
    rw [LinearMap.mem_ker] at h'
    rw [← hpow, h']; rfl
  · rintro ⟨d, hd⟩
    exact mem_jointGenEigenspace.2 fun a => ⟨d, hd a⟩

/-- If every vector lies in a finite-dimensional `T`-stable subspace, the `Y_χ` span `Y`. -/
theorem iSup_jointGenEigenspace_eq_top (T : A →* Module.End ℂ Y)
    (hloc : ∀ y : Y, ∃ W : Submodule ℂ Y, FiniteDimensional ℂ W ∧
      (∀ a, ∀ x ∈ W, T a x ∈ W) ∧ y ∈ W) :
    ⨆ χ, jointGenEigenspace T χ = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨W, hW, hWT, hy⟩ := hloc y
  obtain ⟨c, hc, rfl⟩ := exists_sum_mem_jointGenEigenspace T W hWT hy
  rw [Finsupp.sum]
  exact Submodule.sum_mem _ fun χ _ => Submodule.mem_iSup_of_mem χ (hc χ).2

open scoped Classical in
/-- Waldspurger I.3: `Y = ⊕_χ Y_χ` (internal direct sum) when every vector lies in a
finite-dimensional `T`-stable subspace. -/
theorem isInternal_jointGenEigenspace (T : A →* Module.End ℂ Y)
    (hloc : ∀ y : Y, ∃ W : Submodule ℂ Y, FiniteDimensional ℂ W ∧
      (∀ a, ∀ x ∈ W, T a x ∈ W) ∧ y ∈ W) :
    DirectSum.IsInternal (jointGenEigenspace T) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_jointGenEigenspace T, iSup_jointGenEigenspace_eq_top T hloc⟩

/-- The direct sum runs over the exponents: `⨆_{χ ∈ 𝓔xp} Y_χ = ⨆_χ Y_χ`. -/
theorem biSup_exponentSet_eq_iSup (T : A →* Module.End ℂ Y) :
    ⨆ χ ∈ exponentSet T, jointGenEigenspace T χ = ⨆ χ, jointGenEigenspace T χ := by
  refine le_antisymm (iSup₂_le fun χ _ => le_iSup (jointGenEigenspace T) χ) (iSup_le fun χ => ?_)
  by_cases h : jointGenEigenspace T χ = ⊥
  · rw [h]; exact bot_le
  · exact le_iSup₂ (f := fun χ (_ : χ ∈ exponentSet T) => jointGenEigenspace T χ) χ h

/-- Every exponent is a character: `χ 1 = 1` and `χ (a b) = χ a χ b`. -/
theorem map_one_and_map_mul_of_mem_exponentSet (T : A →* Module.End ℂ Y) {χ : A → ℂ}
    (hχ : χ ∈ exponentSet T) : χ 1 = 1 ∧ ∀ a b, χ (a * b) = χ a * χ b := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  exact ⟨map_one_of_mem_jointGenEigenspace T hx0 hx,
    fun a b => map_mul_of_mem_jointGenEigenspace T hx0 hx a b⟩

/-- Finiteness of the exponents: if `Y` is spanned by the images of a finite-dimensional
`T`-stable subspace `W` under a set `𝒢` of endomorphisms commuting with `T`, only finitely many
`Y_χ` are nonzero. -/
theorem exponentSet_finite (T : A →* Module.End ℂ Y) (W : Submodule ℂ Y)
    [FiniteDimensional ℂ W] (hW : ∀ a, ∀ x ∈ W, T a x ∈ W) (𝒢 : Set (Module.End ℂ Y))
    (h𝒢 : ∀ g ∈ 𝒢, ∀ a, Commute (T a) g)
    (hgen : Submodule.span ℂ (⋃ g ∈ 𝒢, g '' (W : Set Y)) = ⊤) :
    (exponentSet T).Finite := by
  classical
  obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional W).2 inferInstance
  have hSW : ∀ s ∈ S, s ∈ W := fun s hs => hS ▸ Submodule.subset_span hs
  choose c hc hsum using fun s : S => exists_sum_mem_jointGenEigenspace T W hW (hSW s s.2)
  let X : Finset (A → ℂ) := Finset.univ.biUnion fun s : S => (c s).support
  let Z : Submodule ℂ Y := ⨆ χ ∈ X, jointGenEigenspace T χ
  have hWZ : W ≤ Z := by
    rw [← hS, Submodule.span_le]
    intro s hs
    have h : ((c ⟨s, hs⟩).sum fun _ x => x) = s := hsum ⟨s, hs⟩
    rw [← h, Finsupp.sum]
    refine Submodule.sum_mem _ fun χ hχ => ?_
    refine Submodule.mem_iSup_of_mem χ (Submodule.mem_iSup_of_mem ?_ (hc ⟨s, hs⟩ χ).2)
    exact Finset.mem_biUnion.2 ⟨⟨s, hs⟩, Finset.mem_univ _, hχ⟩
  have hZg : ∀ g ∈ 𝒢, ∀ z ∈ Z, g z ∈ Z := by
    intro g hg z hz
    have : Submodule.map g Z ≤ Z := by
      simp only [Z, Submodule.map_iSup]
      exact iSup₂_mono fun χ _ => Submodule.map_le_iff_le_comap.2 fun x hx =>
        mapsTo_jointGenEigenspace_of_commute T (h𝒢 g hg) χ hx
    exact this (Submodule.mem_map_of_mem hz)
  have hZ : Z = ⊤ := by
    refine eq_top_iff.2 (hgen ▸ Submodule.span_le.2 ?_)
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_image] at hy
    obtain ⟨g, hg, x, hx, rfl⟩ := hy
    exact hZg g hg x (hWZ hx)
  refine (X.finite_toSet).subset fun χ hχ => ?_
  by_contra hχX
  have hdisj := (iSupIndep_jointGenEigenspace T).disjoint_biSup (y := (X : Set (A → ℂ))) hχX
  have : jointGenEigenspace T χ ≤ ⨆ i ∈ (X : Set (A → ℂ)), jointGenEigenspace T i := by
    have hZ' : (⨆ i ∈ (X : Set (A → ℂ)), jointGenEigenspace T i) = ⊤ := by
      simpa [Z] using hZ
    rw [hZ']; exact le_top
  exact hχ (hdisj.eq_bot_of_le this)

end Abstract

section Admissible

variable {G : Type*} [Group G] [TopologicalSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {A : Type*} [CommGroup A]

omit [TopologicalSpace G] in
/-- For a central `j : A →* G`, every operator `ρ (j a)` preserves the vectors fixed by a
subgroup. -/
theorem apply_mem_fixedVectors_of_central (ρ : Representation ℂ G V) (j : A →* G)
    (hj : ∀ a g, j a * g = g * j a) (K : Subgroup G) (a : A) {x : V}
    (hx : x ∈ fixedVectors ρ K) : ρ (j a) x ∈ fixedVectors ρ K := by
  change ∀ k : K, ρ (k : G) (ρ (j a) x) = ρ (j a) x
  intro k
  have hk : ρ (k : G) x = x := hx k
  rw [← Module.End.mul_apply, ← map_mul, ← hj, map_mul, Module.End.mul_apply, hk]

/-- For an admissible `ρ` and a central `j`, `V_χ` is the source's
`{v ; ∃ d, ∀ a, (π(a) − χ(a))^d v = 0}`. -/
theorem mem_jointGenEigenspace_iff_exists_pow_of_isAdmissible {ρ : Representation ℂ G V}
    (hρ : IsAdmissible ρ) (j : A →* G) (hj : ∀ a g, j a * g = g * j a) {χ : A → ℂ} {v : V} :
    v ∈ jointGenEigenspace (ρ.comp j) χ ↔
      ∃ d : ℕ, ∀ a, ((ρ (j a) - χ a • 1) ^ d) v = 0 := by
  obtain ⟨K, hK⟩ := hρ.1 v
  have : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  exact mem_jointGenEigenspace_iff_exists_pow (ρ.comp j) (fixedVectors ρ K.toSubgroup)
    (fun a x hx => apply_mem_fixedVectors_of_central ρ j hj K.toSubgroup a hx) hK

/-- Waldspurger I.3: for an admissible representation `ρ` of `G` and a central
`j : A →* G`, `V = ⊕_χ V_χ` for the action of `A` (internal direct sum). -/
theorem isInternal_jointGenEigenspace_of_isAdmissible [DecidableEq (A → ℂ)]
    {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ) (j : A →* G)
    (hj : ∀ a g, j a * g = g * j a) :
    DirectSum.IsInternal (jointGenEigenspace (ρ.comp j)) := by
  have hloc : ∀ y : V, ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧
      (∀ a, ∀ x ∈ W, ρ.comp j a x ∈ W) ∧ y ∈ W := by
    intro y
    obtain ⟨K, hK⟩ := hρ.1 y
    exact ⟨fixedVectors ρ K.toSubgroup, hρ.2 K,
      fun a x hx => apply_mem_fixedVectors_of_central ρ j hj K.toSubgroup a hx, hK⟩
  have := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_jointGenEigenspace (ρ.comp j), iSup_jointGenEigenspace_eq_top (ρ.comp j) hloc⟩
  convert this

/-- The exponents of a finitely generated admissible representation for a central `A` form a
finite set. -/
theorem exponentSet_finite_of_isAdmissible {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
    (j : A →* G) (hj : ∀ a g, j a * g = g * j a) (S : Finset V)
    (hS : Submodule.span ℂ (⋃ g : G, ρ g '' (S : Set V)) = ⊤) :
    (exponentSet (ρ.comp j)).Finite := by
  classical
  choose K hK using fun v : V => hρ.1 v
  let K₀ : OpenSubgroup G := S.inf K
  have hSK : ∀ s ∈ S, s ∈ fixedVectors ρ K₀.toSubgroup := fun s hs =>
    fixedVectors_antitone ρ (OpenSubgroup.toSubgroup_le.2 (Finset.inf_le hs : K₀ ≤ K s)) (hK s)
  have : FiniteDimensional ℂ (fixedVectors ρ K₀.toSubgroup) := hρ.2 K₀
  refine exponentSet_finite (ρ.comp j) (fixedVectors ρ K₀.toSubgroup)
    (fun a x hx => apply_mem_fixedVectors_of_central ρ j hj K₀.toSubgroup a hx)
    (Set.range fun g : G => (ρ g : Module.End ℂ V)) ?_ ?_
  · rintro _ ⟨g, rfl⟩ a
    change ρ (j a) * ρ g = ρ g * ρ (j a)
    rw [← map_mul, ← map_mul, hj]
  · refine eq_top_iff.2 (hS ▸ Submodule.span_mono ?_)
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_image] at hy ⊢
    obtain ⟨g, s, hs, rfl⟩ := hy
    exact ⟨_, ⟨g, rfl⟩, s, hSK s hs, rfl⟩

end Admissible

end Langlands.HarishChandraSchwartz
