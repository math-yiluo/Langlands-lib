import Langlands.Representation.Smooth.CompactCompletion
import Langlands.Representation.Jacquet.StablePairingProof

/-!
# The group action on the compact-open completion

Conjugation of normalized compact averages shows that translation preserves
compatible families. The translations therefore define a representation on the
completion, with the previously defined subgroup-fixed space as its invariants.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz.CompactOpenSubgroup

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[simp]
theorem mem_conj (K : CompactOpenSubgroup G) (g x : G) :
    x ∈ (K.conj g).1 ↔ g⁻¹ * x * g ∈ K.1 := by
  change (MulAut.conj g).symm x ∈ K.1 ↔ _
  rw [MulAut.conj_symm_apply]

@[simp]
theorem conj_one (K : CompactOpenSubgroup G) : K.conj 1 = K := by
  apply Subtype.ext
  ext x
  simp

theorem conj_mul (K : CompactOpenSubgroup G) (g h : G) :
    (K.conj h).conj g = K.conj (g * h) := by
  apply Subtype.ext
  ext x
  simp [mul_inv_rev, mul_assoc]

theorem conj_mono (g : G) {K L : CompactOpenSubgroup G} (hKL : K.1 ≤ L.1) :
    (K.conj g).1 ≤ (L.conj g).1 := by
  intro x hx
  rw [mem_conj] at hx ⊢
  exact hKL hx

/-- Agreement of the two published conjugate-open-subgroup constructions. -/
theorem conj_eq_conjOpenSubgroup (K : CompactOpenSubgroup G) (g : G) :
    (K.conj g).1 = Jacquet.conjOpenSubgroup g K.1 := by
  ext x
  rw [mem_conj, Jacquet.mem_conjOpenSubgroup]

end Langlands.HarishChandraSchwartz.CompactOpenSubgroup

namespace Langlands.CompactCompletion

open Langlands.HarishChandraSchwartz

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- Compact averaging commutes with translation and conjugation of the index. -/
theorem averageMap_translate (g : G) (K : CompactOpenSubgroup G) (v : V) :
    Compact.averageMap ρ hρ K.1 K.2 (ρ g v) =
      ρ g (Compact.averageMap ρ hρ (K.conj g⁻¹).1 (K.conj g⁻¹).2 v) := by
  have hK : Jacquet.conjOpenSubgroup g (K.conj g⁻¹).1 = K.1 := by
    rw [← CompactOpenSubgroup.conj_eq_conjOpenSubgroup,
      CompactOpenSubgroup.conj_mul]
    simp
  have hc := Jacquet.averageMap_conj ρ hρ g (K.conj g⁻¹).1 (K.conj g⁻¹).2
    (hK.symm ▸ K.2) v
  simpa only [hK] using hc

/-- Translation preserves the compatibility equations defining completion. -/
theorem translate_mem (g : G) (v : completion ρ hρ) :
    translate ρ g v.1 ∈ completion ρ hρ := by
  intro K L hLK
  change Compact.averageMap ρ hρ K.1 K.2 (ρ g (v.1 (L.conj g⁻¹))) =
    ρ g (v.1 (K.conj g⁻¹))
  rw [averageMap_translate]
  exact congrArg (ρ g) (v.property _ _ (CompactOpenSubgroup.conj_mono g⁻¹ hLK))

@[simp]
theorem translate_one (v : CompactOpenSubgroup G → V) : translate ρ 1 v = v := by
  funext K
  simp [translate]

theorem translate_mul (g h : G) (v : CompactOpenSubgroup G → V) :
    translate ρ (g * h) v = translate ρ g (translate ρ h v) := by
  funext K
  simp only [translate, mul_inv_rev, CompactOpenSubgroup.conj_mul, map_mul,
    Module.End.mul_apply]

/-- The linear translation operator on completion families. -/
def action (g : G) : Module.End ℂ (completion ρ hρ) where
  toFun v := ⟨translate ρ g v.1, translate_mem ρ hρ g v⟩
  map_add' v w := by
    apply Subtype.ext
    funext K
    exact (ρ g).map_add _ _
  map_smul' c v := by
    apply Subtype.ext
    funext K
    exact (ρ g).map_smul c _

@[simp]
theorem action_apply (g : G) (v : completion ρ hρ) (K : CompactOpenSubgroup G) :
    (action ρ hρ g v).1 K = ρ g (v.1 (K.conj g⁻¹)) :=
  rfl

@[simp]
theorem action_one : action ρ hρ 1 = 1 := by
  ext v
  exact congrFun (translate_one ρ v.1) _

theorem action_mul (g h : G) : action ρ hρ (g * h) = action ρ hρ g * action ρ hρ h := by
  ext v
  exact congrFun (translate_mul ρ g h v.1) _

/-- The group representation on the completion; smoothness is not asserted. -/
def representation : Representation ℂ G (completion ρ hρ) where
  toFun := action ρ hρ
  map_one' := action_one ρ hρ
  map_mul' := action_mul ρ hρ

@[simp]
theorem representation_apply (g : G) (v : completion ρ hρ)
    (K : CompactOpenSubgroup G) :
    (representation ρ hρ g v).1 K = ρ g (v.1 (K.conj g⁻¹)) :=
  rfl

/-- Each translation is a linear automorphism, with inverse translation by `g⁻¹`. -/
def actionEquiv (g : G) : completion ρ hρ ≃ₗ[ℂ] completion ρ hρ :=
  LinearMap.GeneralLinearGroup.toLinearEquiv ((representation ρ hρ).asGroupHom g)

@[simp]
theorem actionEquiv_apply (g : G) (v : completion ρ hρ)
    (K : CompactOpenSubgroup G) :
    (actionEquiv ρ hρ g v).1 K = ρ g (v.1 (K.conj g⁻¹)) :=
  rfl

@[simp]
theorem actionEquiv_symm_apply (g : G) (v : completion ρ hρ)
    (K : CompactOpenSubgroup G) :
    ((actionEquiv ρ hρ g).symm v).1 K = ρ g⁻¹ (v.1 (K.conj g)) := by
  change ρ g⁻¹ (v.1 (K.conj g⁻¹⁻¹)) = _
  rw [inv_inv]

/-- The existing completion-fixed subspace is precisely the fixed-vector space
of the completion representation. -/
theorem completionFixed_eq_fixedVectors (H : Subgroup G) :
    completionFixed ρ hρ H = fixedVectors (representation ρ hρ) H := by
  ext v
  constructor
  · intro hv h
    exact Subtype.ext (hv h h.property)
  · intro hv h hh
    exact congrArg Subtype.val (hv ⟨h, hh⟩)

end Langlands.CompactCompletion
