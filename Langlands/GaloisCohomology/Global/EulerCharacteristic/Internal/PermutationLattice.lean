import Langlands.GaloisCohomology.Local.EulerCharacteristic.Additive
import Langlands.Cohomology.HerbrandLattice
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke

/-!
# Permutation modules with the same character

Let `Γ` be a finite group and `X`, `X'` finite `Γ`-sets with `#X^γ = #X'^γ` for every `γ ∈ Γ` (the
permutation characters agree). Then:

* over a field of characteristic `0`, two finite-dimensional representations with the same
  character are isomorphic (`nonempty_equiv_of_character_eq`, by Maschke's theorem and induction on
  the dimension), so the permutation representations `k^X` and `k^{X'}` are isomorphic;
* the permutation lattices `ℤ^X`, `ℤ^{X'}` are then related by an injective intertwining map with
  finite cokernel (`exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq`), obtained from the
  real isomorphism by `Langlands.Cohomology.Herbrand.exists_intMatrix_det_ne_zero`;
* an additive function `d` on finite `𝔽_ℓ[Γ]`-modules takes the same value on `𝔽_ℓ^X` and `𝔽_ℓ^{X'}`
  (`AdditiveFunction.toFun_funPermRep_eq_of_card_fixedBy_eq`): `d(𝔽_ℓ^X) = g(ℤ^X)` for the
  associated function `g(A) = d(A/ℓA) - d(A[ℓ])` (`AdditiveFunction.g_funPermAction`), which is
  unchanged by an injective map with finite cokernel.

This is the lattice argument in Tate's proof of the global Euler characteristic formula; here it
serves the reduction to cyclic subgroups (Artin's induction theorem) in
`Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.Artin`.
-/

namespace Langlands.GaloisCohomology

open Module Representation
open scoped TensorProduct

universe u v

noncomputable section

section Defs

variable (k Γ : Type*) [CommSemiring k] [Group Γ] (X : Type*) [MulAction Γ X]

/-- The permutation representation of `Γ` on the functions `X → k`: `(γ f)(x) = f(γ⁻¹ x)`. -/
def funPermRep : Representation k Γ (X → k) where
  toFun γ := LinearMap.funLeft k k (fun x => γ⁻¹ • x)
  map_one' := by
    ext f x
    simp
  map_mul' γ δ := by
    ext f x
    simp [mul_smul]

variable {k Γ X} in
@[simp]
theorem funPermRep_apply (γ : Γ) (f : X → k) (x : X) : funPermRep k Γ X γ f x = f (γ⁻¹ • x) :=
  rfl

/-- The action `(γ f)(x) = f(γ⁻¹ x)` of `Γ` on functions `X → A`, as a distributive action. -/
abbrev funPermAction (A : Type*) [AddCommGroup A] : DistribMulAction Γ (X → A) where
  smul γ f x := f (γ⁻¹ • x)
  one_smul f := funext fun x => show f ((1 : Γ)⁻¹ • x) = f x by rw [inv_one, one_smul]
  mul_smul γ δ f := funext fun x =>
    show f ((γ * δ)⁻¹ • x) = f (δ⁻¹ • γ⁻¹ • x) by rw [mul_inv_rev, mul_smul]
  smul_zero γ := rfl
  smul_add γ f f' := rfl

end Defs

section Character

universe uk uG uU uV uW

variable {k : Type uk} {G : Type uG} [Field k] [Group G]

theorem character_prod {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) (g : G) :
    (ρ.prod σ).character g = ρ.character g + σ.character g :=
  LinearMap.trace_prodMap' (ρ g) (σ g)

/-- `τ × ρ ≅ τ × σ` from `ρ ≅ σ`. -/
def equivProdRight {U : Type uU} {V : Type uV} {W : Type uW} [AddCommGroup U]
    [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (τ : Representation k G U) {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : (τ.prod ρ).Equiv (τ.prod σ) :=
  Representation.Equiv.mk ((LinearEquiv.refl k U).prodCongr e.toLinearEquiv) fun g =>
    LinearMap.ext fun x => Prod.ext rfl
      (LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x.2)

/-- Over a field in which the order of the finite group `G` is invertible, an injective intertwining
map `τ → σ` has a complement: `σ ≅ τ × Z`. -/
theorem exists_equiv_prod_of_injective [Finite G] [NeZero (Nat.card G : k)] {U : Type uU}
    {W : Type uW} [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    {τ : Representation k G U} {σ : Representation k G W} (f : IntertwiningMap τ σ)
    (hf : Function.Injective f) :
    ∃ Z : Subrepresentation σ, Nonempty ((τ.prod Z.toRepresentation).Equiv σ) := by
  obtain ⟨Z, hZ⟩ := exists_isCompl f.range
  have hZ' : IsCompl (LinearMap.range f.toLinearMap) Z.toSubmodule :=
    ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hZ.disjoint)),
      codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hZ.codisjoint))⟩
  let e : (U × Z.toSubmodule) ≃ₗ[k] W :=
    ((LinearEquiv.ofInjective f.toLinearMap hf).prodCongr (LinearEquiv.refl k Z.toSubmodule)).trans
      (Submodule.prodEquivOfIsCompl _ _ hZ')
  have he : ∀ u z, e (u, z) = f u + z := fun u z => by
    simp [e, Submodule.coe_prodEquivOfIsCompl']
  refine ⟨Z, ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun x => ?_⟩⟩
  obtain ⟨u, z⟩ := x
  have h1 : f (τ g u) = σ g (f u) := LinearMap.congr_fun (f.isIntertwining' g) u
  change e (τ g u, Z.toRepresentation g z) = σ g (e (u, z))
  rw [he, he, map_add, h1]
  rfl

/-- Over a field of characteristic `0`, two finite-dimensional representations of a finite group with
the same character are isomorphic. -/
theorem nonempty_equiv_of_character_eq [CharZero k] [Finite G] {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W)
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  suffices H : ∀ n : ℕ, ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (ρ : Representation k G V) (σ : Representation k G W), finrank k V = n →
      ρ.character = σ.character → Nonempty (ρ.Equiv σ) from H _ ρ σ rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V W _ _ _ _ _ _ ρ σ hn h
  have : Fintype G := Fintype.ofFinite G
  have hG : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : NeZero (Nat.card G : k) := ⟨hG⟩
  have : Invertible (Nat.card G : k) := invertibleOfNonzero hG
  have hdim : finrank k W = finrank k V := by
    have h1 := congrFun h 1
    rw [Representation.char_one, Representation.char_one] at h1
    exact_mod_cast h1.symm
  by_cases hV : finrank k V = 0
  · have : Subsingleton W := Module.finrank_zero_iff.1 (hdim.trans hV)
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofFinrankEq V W hdim.symm) fun g =>
      LinearMap.ext fun _ => Subsingleton.elim _ _⟩
  have hex : ∃ m, ∃ Y : Subrepresentation ρ, Y ≠ ⊥ ∧ finrank k Y.toSubmodule = m := by
    refine ⟨finrank k V, ⊤, fun h0 => hV ?_, finrank_top k V⟩
    have h1 : (⊤ : Submodule k V) = ⊥ := congrArg Subrepresentation.toSubmodule h0
    rw [← finrank_top k V, h1, finrank_bot]
  classical
  obtain ⟨Y, hY0, hYm⟩ := Nat.find_spec hex
  have hmin : ∀ Y' : Subrepresentation ρ, Y' ≠ ⊥ →
      finrank k Y.toSubmodule ≤ finrank k Y'.toSubmodule := fun Y' hY' => by
    rw [hYm]
    exact Nat.find_min' hex ⟨Y', hY', rfl⟩
  have hYsub : Y.toSubmodule ≠ ⊥ := fun h0 => hY0 (Subrepresentation.toSubmodule_injective h0)
  let ι : IntertwiningMap Y.toRepresentation ρ :=
    ⟨Y.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  have hιinj : Function.Injective ι := Subtype.val_injective
  have hι0 : ι ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := Submodule.ne_bot_iff _ |>.1 hYsub
    intro h0
    exact hy0 (congrArg (fun φ : IntertwiningMap Y.toRepresentation ρ => φ ⟨y, hy⟩) h0)
  have hHom : finrank k (IntertwiningMap Y.toRepresentation σ) =
      finrank k (IntertwiningMap Y.toRepresentation ρ) := by
    have h1 := card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation ρ
    have h2 := card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation σ
    rw [h] at h1
    exact_mod_cast h2.symm.trans h1
  have hpos : 0 < finrank k (IntertwiningMap Y.toRepresentation σ) :=
    hHom ▸ Module.finrank_pos_iff_exists_ne_zero.2 ⟨ι, hι0⟩
  obtain ⟨f, hf0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hfinj : Function.Injective f := by
    let K : Submodule k Y.toSubmodule := LinearMap.ker f.toLinearMap
    by_cases hK : K = ⊥
    · exact LinearMap.ker_eq_bot.1 hK
    exfalso
    let K' : Subrepresentation ρ := ⟨K.map Y.toSubmodule.subtype, by
      rintro g _ ⟨y, hy, rfl⟩
      refine ⟨Y.toRepresentation g y, ?_, rfl⟩
      have h1 := LinearMap.congr_fun (f.isIntertwining' g) y
      have hy' : f.toLinearMap y = 0 := hy
      change f.toLinearMap (Y.toRepresentation g y) = 0
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
      rw [h1, hy', map_zero]⟩
    have hK'dim : finrank k K'.toSubmodule = finrank k K := Submodule.finrank_map_subtype_eq _ _
    have hKpos : finrank k K ≠ 0 := fun h0 => hK (Submodule.finrank_eq_zero.1 h0)
    have hK'0 : K' ≠ ⊥ := by
      intro h0
      have h1 : K'.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h0
      rw [h1, finrank_bot] at hK'dim
      exact hKpos hK'dim.symm
    have h1 := hmin K' hK'0
    have h2 : finrank k K = finrank k Y.toSubmodule :=
      le_antisymm (Submodule.finrank_le K) (hK'dim ▸ h1)
    have hKtop : K = ⊤ := Submodule.eq_top_of_finrank_eq h2
    exact hf0 (IntertwiningMap.ext (LinearMap.ker_eq_top.1 hKtop))
  obtain ⟨V', ⟨eV⟩⟩ := exists_equiv_prod_of_injective ι hιinj
  obtain ⟨W', ⟨eW⟩⟩ := exists_equiv_prod_of_injective f hfinj
  have hchar : V'.toRepresentation.character = W'.toRepresentation.character := by
    funext g
    have h1 := congrFun (char_iso eV) g
    have h2 := congrFun (char_iso eW) g
    have h3 := congrFun h g
    rw [character_prod] at h1 h2
    linear_combination h1 - h2 + h3
  have hYpos : 0 < finrank k Y.toSubmodule :=
    Nat.pos_of_ne_zero fun h0 => hYsub (Submodule.finrank_eq_zero.1 h0)
  have hlt : finrank k V'.toSubmodule < n := by
    have h1 := eV.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at h1
    omega
  obtain ⟨e'⟩ := ih _ hlt V'.toRepresentation W'.toRepresentation rfl hchar
  exact ⟨eV.symm.trans ((equivProdRight Y.toRepresentation e').trans eW)⟩

/-- The character of a permutation representation counts fixed points. -/
theorem character_funPermRep {Γ : Type*} [Group Γ] (X : Type*) [MulAction Γ X] [Finite X] (γ : Γ) :
    (funPermRep k Γ X).character γ = Nat.card (MulAction.fixedBy X γ) := by
  classical
  have := Fintype.ofFinite X
  rw [Representation.character, LinearMap.trace_eq_matrix_trace k (Pi.basisFun k X), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    funPermRep_apply, Pi.single_apply]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulAction.mem_fixedBy]
  rw [inv_smul_eq_iff, eq_comm]

theorem nonempty_equiv_funPermRep_of_card_fixedBy_eq [CharZero k] {Γ : Type*} [Group Γ] [Finite Γ]
    {X X' : Type*} [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    Nonempty ((funPermRep k Γ X).Equiv (funPermRep k Γ X')) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite X'
  exact nonempty_equiv_of_character_eq _ _ (funext fun γ => by
    rw [character_funPermRep, character_funPermRep, h])

end Character

section Lattice

variable {Γ : Type*} [Group Γ]

/-- The matrix of a permutation representation, over any ring. -/
theorem toMatrix'_funPermRep {R : Type*} [CommRing R] (X : Type*) [MulAction Γ X] [Fintype X]
    [DecidableEq X] (γ : Γ) (i j : X) :
    LinearMap.toMatrix' (funPermRep R Γ X γ) i j = if γ⁻¹ • i = j then 1 else 0 := by
  rw [LinearMap.toMatrix'_apply, funPermRep_apply, Pi.single_apply]

/-- **Permutation lattices with the same character.** There is an injective intertwining map
`ℤ^X → ℤ^{X'}` whose image contains `n · ℤ^{X'}` for some `n ≠ 0`. -/
theorem exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq [Finite Γ] {X X' : Type*}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    ∃ φ : (X → ℤ) →ₗ[ℤ] (X' → ℤ), Function.Injective φ ∧
      (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ γ x, φ (funPermRep ℤ Γ X γ x) = funPermRep ℤ Γ X' γ (φ x) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite X'
  obtain ⟨E⟩ := nonempty_equiv_funPermRep_of_card_fixedBy_eq (k := ℝ) h
  -- a bijection `X ≃ X'`: the two sets have the same size
  have hcard : Fintype.card X = Fintype.card X' := by
    have h1 := h 1
    simp only [MulAction.fixedBy, one_smul, Set.ofPred_true] at h1
    rw [Nat.card_univ, Nat.card_univ, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h1
    exact h1
  let τ : X ≃ X' := Fintype.equivOfCardEq hcard
  -- everything as endomorphisms of `X → R` through `τ`
  let tr : ∀ (R : Type) [CommRing R], (X' → R) ≃ₗ[R] (X → R) := fun R _ =>
    LinearEquiv.funCongrLeft R R τ
  let P : Γ → Matrix X X ℤ := fun γ => LinearMap.toMatrix' (funPermRep ℤ Γ X γ)
  let Q : Γ → Matrix X X ℤ := fun γ => LinearMap.toMatrix'
    ((tr ℤ).toLinearMap ∘ₗ funPermRep ℤ Γ X' γ ∘ₗ (tr ℤ).symm.toLinearMap)
  let Eℝ : (X → ℝ) →ₗ[ℝ] (X → ℝ) := (tr ℝ).toLinearMap ∘ₗ E.toLinearMap
  let C : Matrix X X ℝ := LinearMap.toMatrix' Eℝ
  have hPmap : ∀ γ, (P γ).map (Int.castRingHom ℝ) = LinearMap.toMatrix' (funPermRep ℝ Γ X γ) := by
    intro γ
    ext i j
    simp only [Matrix.map_apply, P, toMatrix'_funPermRep]
    split_ifs <;> simp
  have hQmap : ∀ γ, (Q γ).map (Int.castRingHom ℝ) = LinearMap.toMatrix'
      ((tr ℝ).toLinearMap ∘ₗ funPermRep ℝ Γ X' γ ∘ₗ (tr ℝ).symm.toLinearMap) := by
    intro γ
    ext i j
    simp only [Matrix.map_apply, Q, LinearMap.toMatrix'_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, tr, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, funPermRep_apply]
    rw [LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have hCdet : C.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' ((E.toLinearEquiv).trans (tr ℝ))).ne_zero
  have hrel : ∀ γ, (Q γ).map (Int.castRingHom ℝ) * C = C * (P γ).map (Int.castRingHom ℝ) := by
    intro γ
    rw [hPmap, hQmap, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun f => ?_
    simp only [Eℝ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    exact congrArg (tr ℝ) (LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' γ) f).symm
  obtain ⟨M, hMdet, hM⟩ := Langlands.Cohomology.Herbrand.exists_intMatrix_det_ne_zero P Q C hCdet hrel
  let φ₀ : (X → ℤ) →ₗ[ℤ] (X → ℤ) := Matrix.toLin' M
  let ψ₀ : (X → ℤ) →ₗ[ℤ] (X → ℤ) := Matrix.toLin' M.adjugate
  have hφψ : ∀ y, φ₀ (ψ₀ y) = M.det • y := fun y => by
    rw [← Matrix.toLin'_mul_apply, Matrix.mul_adjugate, map_smul, Matrix.toLin'_one]
    rfl
  have hψφ : ∀ x, ψ₀ (φ₀ x) = M.det • x := fun x => by
    rw [← Matrix.toLin'_mul_apply, Matrix.adjugate_mul, map_smul, Matrix.toLin'_one]
    rfl
  refine ⟨(tr ℤ).symm.toLinearMap ∘ₗ φ₀, fun x y hxy => ?_, ⟨M.det, hMdet, fun y => ?_⟩,
    fun γ x => ?_⟩
  · have h1 : φ₀ x = φ₀ y := (tr ℤ).symm.injective hxy
    have h2 : M.det • x = M.det • y := by rw [← hψφ, ← hψφ, h1]
    funext i
    have h3 := congrFun h2 i
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    exact mul_left_cancel₀ hMdet h3
  · refine ⟨ψ₀ (tr ℤ y), ?_⟩
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hφψ, map_zsmul,
      LinearEquiv.symm_apply_apply]
  · have hc : φ₀ ∘ₗ funPermRep ℤ Γ X γ =
        ((tr ℤ).toLinearMap ∘ₗ funPermRep ℤ Γ X' γ ∘ₗ (tr ℤ).symm.toLinearMap) ∘ₗ φ₀ := by
      apply LinearMap.toMatrix'.injective
      rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
      exact (hM γ).symm
    have := LinearMap.congr_fun hc x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at this ⊢
    rw [this, LinearEquiv.symm_apply_apply]

end Lattice

namespace Local.AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

omit [Group Γ] in
/-- `ℤ^X / ℓ` is finite for a finite set `X`. -/
theorem finite_modN_fun (l : ℕ) [NeZero l] (X : Type*) [Finite X] : Finite (ModN (X → ℤ) l) := by
  have : Module.Finite ℤ (X → ℤ) := Module.Finite.pi
  set R := LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) (l : ℤ))
  have : Module.Finite ℤ ((X → ℤ) ⧸ R) :=
    Module.Finite.of_surjective R.mkQ (Submodule.mkQ_surjective R)
  change Finite ((X → ℤ) ⧸ R)
  apply Module.finite_of_fg_torsion
  intro z
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective R z
  refine ⟨⟨(l : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast NeZero.ne l)⟩, ?_⟩
  change (l : ℤ) • R.mkQ y = 0
  rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨y, rfl⟩

/-- For a finite `Γ`-set `X`, `g(ℤ^X) = d(𝔽_ℓ^X)`. -/
theorem g_funPermAction [NeZero l] (X : Type u) [MulAction Γ X] [Finite X] :
    letI := funPermAction Γ X ℤ
    d.g (X → ℤ) = d.toFun (X → ZMod l) (funPermRep (ZMod l) Γ X) := by
  let _ := funPermAction Γ X ℤ
  have hl : (l : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne l
  have htors : ∀ f : X → ℤ, l • f = 0 → f = 0 := fun f hf => funext fun x => by
    have h1 := congrFun hf x
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hl
  let c : (X → ℤ) →ₗ[ℤ] (X → ZMod l) :=
    LinearMap.pi fun x => (Int.castAddHom (ZMod l)).toIntLinearMap ∘ₗ LinearMap.proj x
  have hc : ∀ f x, c f x = (f x : ZMod l) := fun _ _ => rfl
  have hker : LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) (l : ℤ)) ≤ LinearMap.ker c := by
    rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    funext x
    simp [hc]
  let ψ := (LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) (l : ℤ))).liftQ c hker
  have hψ : Function.Bijective (ψ.toAddMonoidHom.toZModLinearMap l) := by
    refine ⟨?_, fun y => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 : ∀ y, (l : ℤ) ∣ f y := fun y => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact congrFun hx y
      choose a ha using h1
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨a, funext fun y => by simp [ha y]⟩
    · refine ⟨Submodule.Quotient.mk (fun x => ((y x).val : ℤ)), funext fun x => ?_⟩
      change c _ x = y x
      rw [hc, Int.cast_natCast, ZMod.natCast_zmod_val]
  let E : ModN (X → ℤ) l ≃ₗ[ZMod l] (X → ZMod l) := LinearEquiv.ofBijective _ hψ
  have : Finite (ModN (X → ℤ) l) := Finite.of_equiv _ E.symm.toEquiv
  rw [d.g_eq_of_torsion_trivial _ htors]
  refine d.toFun_congr _ _ E fun γ x => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [modNRep_mk]
  rfl

/-- **Additive functions on permutation modules depend only on the permutation character.** -/
theorem toFun_funPermRep_eq_of_card_fixedBy_eq [NeZero l] [Finite Γ] {X X' : Type u}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    d.toFun (X → ZMod l) (funPermRep (ZMod l) Γ X) =
      d.toFun (X' → ZMod l) (funPermRep (ZMod l) Γ X') := by
  obtain ⟨φ, hφ, ⟨n, hn, hrange⟩, hcomm⟩ :=
    exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq h
  let _ := funPermAction Γ X ℤ
  let _ := funPermAction Γ X' ℤ
  have : Module.Finite ℤ (X' → ℤ) := Module.Finite.pi
  have : Finite ((X' → ℤ) ⧸ φ.toAddMonoidHom.range) := by
    let R := LinearMap.range φ
    have : Module.Finite ℤ ((X' → ℤ) ⧸ R) :=
      Module.Finite.of_surjective R.mkQ (Submodule.mkQ_surjective R)
    have hfin : Finite ((X' → ℤ) ⧸ R) := by
      apply Module.finite_of_fg_torsion
      intro z
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective R z
      refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
      change n • R.mkQ y = 0
      rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      obtain ⟨x, hx⟩ := hrange y
      exact ⟨x, hx⟩
    have heq : R.toAddSubgroup = φ.toAddMonoidHom.range := by
      ext y
      simp [R, LinearMap.mem_range]
    have : Finite ((X' → ℤ) ⧸ R.toAddSubgroup) := hfin
    exact Finite.of_equiv _ (QuotientAddGroup.quotientAddEquivOfEq heq).toEquiv
  have hl : (l : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne l
  have : Subsingleton (TorsN (X → ℤ) l) := ⟨fun a b => Subtype.ext (by
    have key : ∀ t : TorsN (X → ℤ) l, (t : X → ℤ) = 0 := fun t => funext fun x => by
      have h1 := congrFun ((mem_ker_lsmul_iff l (t : X → ℤ)).1 t.2) x
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left hl
    rw [key a, key b])⟩
  have : Finite (TorsN (X → ℤ) l) := Finite.of_subsingleton
  have hmod : Finite (ModN (X → ℤ) l) := finite_modN_fun l X
  have hg := d.g_eq_of_finite_cokernel φ.toAddMonoidHom (fun γ b => hcomm γ b) hφ
  rw [← d.g_funPermAction X, ← d.g_funPermAction X', hg]

end Local.AdditiveFunction

end

end Langlands.GaloisCohomology
