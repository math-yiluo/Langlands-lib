import Langlands.LocalFactor.Ramification.Galois

/-!
# Maps and fixed spaces for an explicitly supplied finite inertia quotient

The quotient, its surjectivity, and the kernel condition remain explicit.
No existence or independence of the finite quotient is asserted.
-/

noncomputable section

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

end Langlands.Ramification.Padic
