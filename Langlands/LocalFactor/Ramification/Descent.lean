import Langlands.LocalFactor.Ramification.Galois

/-!
# Maps and fixed spaces for an explicitly supplied finite inertia quotient

The quotient, its surjectivity, and the kernel condition remain explicit.
No existence or independence of the finite quotient is asserted.
-/

noncomputable section

namespace Langlands.Ramification.Local

universe u₀ uK uL uk uJ uV uW uU

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
    {L : Type uL} [Field L] [Algebra K₀ L]
    (T : LocalField.TopologicalData K₀ L) (K : Type uK) [Field K] [Algebra K₀ K]
    [Algebra K L] [IsScalarTower K₀ K L]
    {k : Type uk} [Field k] {J : Type uJ} [Group J]
    (π : J →* inertia T K) (hπ : Function.Surjective π)
    {V : Type uV} [AddCommGroup V] [Module k V]
    {W : Type uW} [AddCommGroup W] [Module k W]
    {U : Type uU} [AddCommGroup U] [Module k U]
    {ρ : Representation k J V} {σ : Representation k J W}
    {τ : Representation k J U}

/-- An intertwiner descends with its underlying linear map unchanged. -/
def descendInertiaMap (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker)
    (f : ρ.IntertwiningMap σ) :
    (descendInertiaRepresentation T K π hπ ρ hρ).IntertwiningMap
      (descendInertiaRepresentation T K π hπ σ hσ) where
  toLinearMap := f.toLinearMap
  isIntertwining' i := by
    obtain ⟨j, rfl⟩ := hπ i
    simpa only [descendInertiaRepresentation_apply] using f.isIntertwining' j

@[simp]
theorem descendInertiaMap_apply (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker)
    (f : ρ.IntertwiningMap σ) (v : V) :
    descendInertiaMap T K π hπ hρ hσ f v = f v := rfl

@[simp]
theorem descendInertiaMap_id (hρ : π.ker ≤ ρ.ker) :
    descendInertiaMap T K π hπ hρ hρ (.id ρ) =
      .id (descendInertiaRepresentation T K π hπ ρ hρ) := by
  ext v
  rfl

@[simp]
theorem descendInertiaMap_comp
    (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker) (hτ : π.ker ≤ τ.ker)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    descendInertiaMap T K π hπ hρ hτ (g.comp f) =
      (descendInertiaMap T K π hπ hσ hτ g).comp
        (descendInertiaMap T K π hπ hρ hσ f) := by
  ext v
  rfl

/-- The kernel condition is invariant under an actual representation equivalence. -/
theorem kernel_le_of_equiv (hρ : π.ker ≤ ρ.ker) (e : ρ.Equiv σ) :
    π.ker ≤ σ.ker := by
  intro j hj
  apply MonoidHom.mem_ker.mpr
  ext w
  obtain ⟨v, rfl⟩ := e.surjective w
  change σ j (e v) = e v
  have he := LinearMap.congr_fun (e.isIntertwining' j) v
  change e (ρ j v) = σ j (e v) at he
  have hjρ : ρ j = 1 := hρ hj
  rw [hjρ] at he
  exact he.symm

theorem kernel_le_iff_of_equiv (e : ρ.Equiv σ) :
    π.ker ≤ ρ.ker ↔ π.ker ≤ σ.ker :=
  ⟨fun h => kernel_le_of_equiv T K π h e,
    fun h => kernel_le_of_equiv T K π h e.symm⟩

/-- A genuine equivalence descends, including for independent carrier universes. -/
def descendInertiaEquiv (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker)
    (e : ρ.Equiv σ) :
    (descendInertiaRepresentation T K π hπ ρ hρ).Equiv
      (descendInertiaRepresentation T K π hπ σ hσ) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' := (descendInertiaMap T K π hπ hρ hσ e.toIntertwiningMap).isIntertwining'

/-- The fixed subspace of every finite subgroup is the fixed subspace of its
actual inverse image under the supplied quotient map. -/
theorem fixedVectors_descend_eq (hρ : π.ker ≤ ρ.ker) (H : Subgroup (inertia T K)) :
    fixedVectors (descendInertiaRepresentation T K π hπ ρ hρ) H =
      fixedVectors ρ (H.comap π) := by
  ext v
  constructor
  · intro hv j
    have hi := hv ⟨π j.val, j.property⟩
    change descendInertiaRepresentation T K π hπ ρ hρ (π j.val) v = v at hi
    change ρ j.val v = v
    simpa only [descendInertiaRepresentation_apply] using hi
  · intro hv i
    obtain ⟨j, hj⟩ := hπ i.val
    have hjH : j ∈ H.comap π := by
      change π j ∈ H
      rw [hj]
      exact i.property
    change descendInertiaRepresentation T K π hπ ρ hρ i.val v = v
    rw [← hj, descendInertiaRepresentation_apply]
    exact hv ⟨j, hjH⟩

private theorem fixedVectors_top_eq_invariants (ρ : Representation k J V) :
    fixedVectors ρ ⊤ = Representation.invariants ρ := by
  ext v
  exact ⟨fun h j => h ⟨j, Subgroup.mem_top j⟩, fun h j => h j.val⟩

/-- In particular, descent does not change the full invariant subspace. -/
theorem fixedVectors_descend_top_eq (hρ : π.ker ≤ ρ.ker) :
    fixedVectors (descendInertiaRepresentation T K π hπ ρ hρ) ⊤ =
      Representation.invariants ρ := by
  rw [fixedVectors_descend_eq, Subgroup.comap_top, fixedVectors_top_eq_invariants]

variable [FiniteDimensional k V] [FiniteDimensional k W]

theorem fixedCodimension_descend_eq
    (hρ : π.ker ≤ ρ.ker) (H : Subgroup (inertia T K)) :
    fixedCodimension (inertia T K)
      (descendInertiaRepresentation T K π hπ ρ hρ) H =
        fixedCodimension J ρ (H.comap π) := by
  unfold fixedCodimension
  rw [fixedVectors_descend_eq]

variable [FiniteDimensional K₀ L]

/-- The tame term of the actual finite-inertia sum is the codimension of the
original full invariant space. This is not quotient independence. -/
theorem artinConductorOfQuotient_eq_tame_add_swan (hρ : π.ker ≤ ρ.ker) :
    artinConductorOfQuotient T K π hπ ρ hρ =
      ((Module.finrank k V - Module.finrank k (Representation.invariants ρ) : ℕ) : ℚ) +
        swanConductorOfQuotient T K π hπ ρ hρ := by
  unfold artinConductorOfQuotient swanConductorOfQuotient
  rw [inertiaArtinConductor_eq_tame_add_swan]
  unfold fixedCodimension
  rw [fixedVectors_descend_top_eq]

/-- Artin expressions at one fixed finite quotient are invariant under
representation equivalence. -/
theorem artinConductorOfQuotient_equiv
    (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker) (e : ρ.Equiv σ) :
    artinConductorOfQuotient T K π hπ ρ hρ =
      artinConductorOfQuotient T K π hπ σ hσ :=
  inertiaArtinConductor_equiv T K (descendInertiaEquiv T K π hπ hρ hσ e)

/-- Swan expressions at one fixed finite quotient are invariant under
representation equivalence. -/
theorem swanConductorOfQuotient_equiv
    (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker) (e : ρ.Equiv σ) :
    swanConductorOfQuotient T K π hπ ρ hρ =
      swanConductorOfQuotient T K π hπ σ hσ :=
  inertiaSwanConductor_equiv T K (descendInertiaEquiv T K π hπ hρ hσ e)

end Langlands.Ramification.Local

namespace Langlands.Ramification.Padic

universe uK uL uk uJ uV uW uU

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {k : Type uk} [Field k] {J : Type uJ} [Group J]
    (π : J →* inertia T K) (hπ : Function.Surjective π)
    {V : Type uV} [AddCommGroup V] [Module k V]
    {W : Type uW} [AddCommGroup W] [Module k W]
    {U : Type uU} [AddCommGroup U] [Module k U]
    {ρ : Representation k J V} {σ : Representation k J W}
    {τ : Representation k J U}

@[inherit_doc Local.descendInertiaMap]
def descendInertiaMap (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker)
    (f : ρ.IntertwiningMap σ) :
    (descendInertiaRepresentation T K π hπ ρ hρ).IntertwiningMap
      (descendInertiaRepresentation T K π hπ σ hσ) :=
  Local.descendInertiaMap T.toLocalData K π hπ hρ hσ f

@[simp]
theorem descendInertiaMap_apply (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker)
    (f : ρ.IntertwiningMap σ) (v : V) :
    descendInertiaMap T K π hπ hρ hσ f v = f v :=
  Local.descendInertiaMap_apply T.toLocalData K π hπ hρ hσ f v

@[simp]
theorem descendInertiaMap_id (hρ : π.ker ≤ ρ.ker) :
    descendInertiaMap T K π hπ hρ hρ (.id ρ) =
      .id (descendInertiaRepresentation T K π hπ ρ hρ) :=
  Local.descendInertiaMap_id T.toLocalData K π hπ hρ

@[simp]
theorem descendInertiaMap_comp
    (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker) (hτ : π.ker ≤ τ.ker)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    descendInertiaMap T K π hπ hρ hτ (g.comp f) =
      (descendInertiaMap T K π hπ hσ hτ g).comp
        (descendInertiaMap T K π hπ hρ hσ f) :=
  Local.descendInertiaMap_comp T.toLocalData K π hπ hρ hσ hτ f g

@[inherit_doc Local.kernel_le_of_equiv]
theorem kernel_le_of_equiv (hρ : π.ker ≤ ρ.ker) (e : ρ.Equiv σ) :
    π.ker ≤ σ.ker :=
  Local.kernel_le_of_equiv T.toLocalData K π hρ e

theorem kernel_le_iff_of_equiv (e : ρ.Equiv σ) :
    π.ker ≤ ρ.ker ↔ π.ker ≤ σ.ker :=
  Local.kernel_le_iff_of_equiv T.toLocalData K π e

@[inherit_doc Local.descendInertiaEquiv]
def descendInertiaEquiv (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker)
    (e : ρ.Equiv σ) :
    (descendInertiaRepresentation T K π hπ ρ hρ).Equiv
      (descendInertiaRepresentation T K π hπ σ hσ) :=
  Local.descendInertiaEquiv T.toLocalData K π hπ hρ hσ e

@[inherit_doc Local.fixedVectors_descend_eq]
theorem fixedVectors_descend_eq (hρ : π.ker ≤ ρ.ker) (H : Subgroup (inertia T K)) :
    fixedVectors (descendInertiaRepresentation T K π hπ ρ hρ) H =
      fixedVectors ρ (H.comap π) :=
  Local.fixedVectors_descend_eq T.toLocalData K π hπ hρ H

@[inherit_doc Local.fixedVectors_descend_top_eq]
theorem fixedVectors_descend_top_eq (hρ : π.ker ≤ ρ.ker) :
    fixedVectors (descendInertiaRepresentation T K π hπ ρ hρ) ⊤ =
      Representation.invariants ρ :=
  Local.fixedVectors_descend_top_eq T.toLocalData K π hπ hρ

variable [FiniteDimensional k V] [FiniteDimensional k W]

theorem fixedCodimension_descend_eq
    (hρ : π.ker ≤ ρ.ker) (H : Subgroup (inertia T K)) :
    fixedCodimension (inertia T K)
      (descendInertiaRepresentation T K π hπ ρ hρ) H =
        fixedCodimension J ρ (H.comap π) :=
  Local.fixedCodimension_descend_eq T.toLocalData K π hπ hρ H

@[inherit_doc Local.artinConductorOfQuotient_eq_tame_add_swan]
theorem artinConductorOfQuotient_eq_tame_add_swan (hρ : π.ker ≤ ρ.ker) :
    artinConductorOfQuotient T K π hπ ρ hρ =
      ((Module.finrank k V - Module.finrank k (Representation.invariants ρ) : ℕ) : ℚ) +
        swanConductorOfQuotient T K π hπ ρ hρ :=
  Local.artinConductorOfQuotient_eq_tame_add_swan T.toLocalData K π hπ hρ

@[inherit_doc Local.artinConductorOfQuotient_equiv]
theorem artinConductorOfQuotient_equiv
    (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker) (e : ρ.Equiv σ) :
    artinConductorOfQuotient T K π hπ ρ hρ =
      artinConductorOfQuotient T K π hπ σ hσ :=
  Local.artinConductorOfQuotient_equiv T.toLocalData K π hπ hρ hσ e

@[inherit_doc Local.swanConductorOfQuotient_equiv]
theorem swanConductorOfQuotient_equiv
    (hρ : π.ker ≤ ρ.ker) (hσ : π.ker ≤ σ.ker) (e : ρ.Equiv σ) :
    swanConductorOfQuotient T K π hπ ρ hρ =
      swanConductorOfQuotient T K π hπ σ hσ :=
  Local.swanConductorOfQuotient_equiv T.toLocalData K π hπ hρ hσ e

end Langlands.Ramification.Padic
