import Langlands.Representation.Compact.ProjectionProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations

/-!
# The completion of a smooth representation

Renard 2026, I.1.4 and VI.9.7 (printed p.205/PDF p.211): the completion `V̄` of a smooth
representation `(π, V)` of a locally profinite group `G` is the projective limit of the
spaces `e · V` over the idempotents `e` of the Hecke algebra. The normalized averages `e_K`
over compact open subgroups `K` form a cofinal filtering system of idempotents, and
`e_K · V = V^K`; Renard writes `V̄ = lim_K V^K` in the proof of VI.9.7. This file realizes
that limit concretely, without the Hecke algebra:

* `completion ρ hρ` is the space of families `(v_K)` indexed by the compact open subgroups,
  with `e_K v_L = v_K` whenever `L ≤ K`; here `e_K` is the published normalized compact
  average `Compact.averageMap`.
* `translate ρ g v` is the family `K ↦ π(g) v_{g⁻¹ K g}`, the action of `g` on `V̄`.
* `completionFixed ρ hρ H` is the subspace `V̄^H` of the completion fixed by a subgroup `H`.
-/

noncomputable section

namespace Langlands.CompactCompletion

open Langlands.HarishChandraSchwartz

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The completion `V̄ = lim_K e_K · V` of a smooth representation: families `(v_K)` indexed
by the compact open subgroups, with `e_K v_L = v_K` whenever `L ≤ K`. Taking `L = K` shows
`v_K ∈ V^K`. -/
def completion (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) :
    Submodule ℂ (CompactOpenSubgroup G → V) where
  carrier := {v | ∀ K L : CompactOpenSubgroup G, L.1 ≤ K.1 →
    Compact.averageMap ρ hρ K.1 K.2 (v L) = v K}
  zero_mem' := by
    intro K L _
    simp
  add_mem' := by
    intro a b ha hb K L hLK
    simp only [Pi.add_apply, map_add, ha K L hLK, hb K L hLK]
  smul_mem' := by
    intro c a ha K L hLK
    simp only [Pi.smul_apply, map_smul, ha K L hLK]

/-- The action of `g` on families: `(g · v)_K = π(g) v_{g⁻¹ K g}`. -/
def translate (ρ : Representation ℂ G V) (g : G) (v : CompactOpenSubgroup G → V) :
    CompactOpenSubgroup G → V :=
  fun K => ρ g (v (K.conj g⁻¹))

/-- The subspace `V̄^H` of the completion fixed by every element of a subgroup `H`. -/
def completionFixed (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (H : Subgroup G) :
    Submodule ℂ (completion ρ hρ) where
  carrier := {v | ∀ h ∈ H, translate ρ h v.1 = v.1}
  zero_mem' := by
    intro h _
    funext K
    simp [translate]
  add_mem' := by
    intro a b ha hb h hh
    funext K
    have ha' := congrFun (ha h hh) K
    have hb' := congrFun (hb h hh) K
    simp only [translate] at ha' hb' ⊢
    simp only [Submodule.coe_add, Pi.add_apply, map_add, ha', hb']
  smul_mem' := by
    intro c a ha h hh
    funext K
    have ha' := congrFun (ha h hh) K
    simp only [translate] at ha' ⊢
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, ha']

end Langlands.CompactCompletion
