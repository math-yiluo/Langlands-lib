import Langlands.Correspondence.HenniartUnramified.Extension

/-! # Uniqueness up to unramified twist -/

noncomputable section

namespace Langlands.FiniteRepresentation.SplitDegree

open Representation LinearMap

universe uG uH uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Irreducible representations with a nonzero intertwiner between their inertia restrictions differ
by an unramified twist. -/
theorem twist_equiv_of_inertia_ne_zero (D : SplitDegree G)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V')
    (hρ : ρ.IsIrreducible) (hρ' : ρ'.IsIrreducible)
    (T : Representation.IntertwiningMap (ρ.comp D.inertia.subtype) (ρ'.comp D.inertia.subtype))
    (hT : T ≠ 0) :
    ∃ z : ℂˣ, Nonempty (Representation.Equiv
      (Langlands.twist (Weil.Local.unramifiedCharacter D.degree z).toMonoidHom ρ) ρ') := by
  obtain ⟨z, f, hf⟩ := D.exists_twisted_intertwiner ρ ρ' ⟨T, hT⟩
  exact ⟨z, nonempty_equiv_of_ne_zero _ _ (isIrreducible_twist _ _ hρ) hρ' f hf⟩

variable {H : Type uH} [Group H] [TopologicalSpace H]
variable {D : SplitDegree G} {E : SplitDegree H} {m : ℕ}

namespace Stage

variable (S : Stage D E (m + 1))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V)

theorem comp_inertia_eq_block : τ.comp E.inertia.subtype = (S.block τ 0).comp S.ιJ := by
  ext h : 1
  simp only [MonoidHom.comp_apply, block_apply, cj_zero]
  rw [← coe_κJ, κJ_ιJ]
  rfl

theorem block_eq_comp (k : ℕ) : S.block τ k = (S.block τ 0).comp (D.cj k) := by
  ext n : 1
  simp [cj_zero]

/-- The coordinate projection exhibits the first block as a quotient of the coinduction on
inertia. -/
def proj0 : Representation.IntertwiningMap ((S.coind τ).comp D.inertia.subtype) (S.block τ 0) :=
  ⟨LinearMap.proj (0 : Fin (m + 1)), fun n => by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      LinearMap.coe_proj, Function.eval, coind_inertia, inertiaRep_apply]
    rfl⟩

theorem proj0_ne_zero [Nontrivial V] : S.proj0 τ ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : V)
  apply ha
  have := congrArg (fun F => F (Pi.single 0 a)) h
  simpa [proj0] using this

variable [FiniteDimensional ℂ V]

/-- Any irreducible representation of `G` whose inertia restriction maps onto the first block is
an unramified twist of the coinduction. -/
theorem twist_equiv_coind_of_occurs [Nontrivial V]
    (hirr : ∀ k : Fin (m + 1), (S.block τ k).IsIrreducible)
    (hdist : ∀ j k : Fin (m + 1), j ≠ k →
      ∀ T : (S.block τ j).IntertwiningMap (S.block τ k), T = 0)
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    (σ' : Representation ℂ G V') (hσ' : σ'.IsIrreducible)
    (P : Representation.IntertwiningMap (σ'.comp D.inertia.subtype) (S.block τ 0)) (hP : P ≠ 0) :
    ∃ u : ℂˣ, Nonempty (Representation.Equiv
      (Langlands.twist (Weil.Local.unramifiedCharacter D.degree u).toMonoidHom σ') (S.coind τ)) := by
  let P' : Representation.IntertwiningMap ((σ'.comp S.ι).comp E.inertia.subtype)
      (τ.comp E.inertia.subtype) :=
    ⟨P.toLinearMap, fun h => by
      rw [S.comp_inertia_eq_block τ]
      exact P.isIntertwining' (S.ιJ h)⟩
  have hP' : P' ≠ 0 := by
    intro h0
    have h1 := congrArg IntertwiningMap.toLinearMap h0
    exact hP (IntertwiningMap.ext h1)
  obtain ⟨z, F, hF⟩ := E.exists_twisted_intertwiner (σ'.comp S.ι) τ ⟨P', hP'⟩
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) (Nat.succ_pos m)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero m)] at hw
    exact z.ne_zero hw.symm
  let u : ℂˣ := Units.mk0 w hw0
  have hu : u ^ (m + 1) = z := Units.ext (by simpa [u] using hw)
  let σ'' := Langlands.twist (Weil.Local.unramifiedCharacter D.degree u).toMonoidHom σ'
  have hF' : ∀ h : H, F.toLinearMap ∘ₗ σ'' (S.ι h) = τ h ∘ₗ F.toLinearMap := by
    intro h
    have := F.isIntertwining' h
    change F.toLinearMap ∘ₗ ((Weil.Local.unramifiedCharacter E.degree z h : ℂ) • σ' (S.ι h)) =
      τ h ∘ₗ F.toLinearMap at this
    change F.toLinearMap ∘ₗ ((Weil.Local.unramifiedCharacter D.degree u (S.ι h) : ℂ) •
      σ' (S.ι h)) = τ h ∘ₗ F.toLinearMap
    rw [S.unramifiedCharacter_ι, hu]
    exact this
  have hF0 : F.toLinearMap ≠ 0 := fun h0 => hF (IntertwiningMap.ext h0)
  let Q : Representation.IntertwiningMap σ'' (S.coind τ) :=
    ⟨recip D m σ'' F.toLinearMap, S.recip_intertwines τ σ'' F.toLinearMap hF'⟩
  have hQ : Q ≠ 0 := fun h0 => recip_ne_zero D m σ'' F.toLinearMap hF0
    (congrArg IntertwiningMap.toLinearMap h0)
  exact ⟨u, nonempty_equiv_of_ne_zero _ _ (isIrreducible_twist _ _ hσ')
    (S.coind_isIrreducible τ hirr hdist) Q hQ⟩

end Stage

end Langlands.FiniteRepresentation.SplitDegree
