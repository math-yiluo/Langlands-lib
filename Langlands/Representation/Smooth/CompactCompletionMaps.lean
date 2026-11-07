import Langlands.Representation.Smooth.CompactCompletion

/-!
# Componentwise maps of compact-open completions

The completion of an intertwiner applies it to each component. Naturality of
compact averaging makes the resulting family compatible. Intertwining with
translations also gives a map on the subspaces fixed by any subgroup.
-/

noncomputable section

namespace Langlands.CompactCompletion

open Langlands.HarishChandraSchwartz

universe uG uV uW uX

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {X : Type uX} [AddCommGroup X] [Module ℂ X]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
variable {τ : Representation ℂ G X}

/-- An intertwiner acts on a completion by applying it to each component. -/
def map (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (f : ρ.IntertwiningMap σ) :
    completion ρ hρ →ₗ[ℂ] completion σ hσ where
  toFun v := ⟨fun K => f (v.1 K), by
    intro K L hLK
    calc
      Compact.averageMap σ hσ K.1 K.2 (f (v.1 L)) =
          f (Compact.averageMap ρ hρ K.1 K.2 (v.1 L)) :=
        (LinearMap.congr_fun (Compact.averageMap_commute ρ σ hρ hσ K.1 K.2 f)
          (v.1 L)).symm
      _ = f (v.1 K) := congrArg f (v.property K L hLK)⟩
  map_add' _ _ := by
    apply Subtype.ext
    funext K
    exact f.map_add _ _
  map_smul' _ _ := by
    apply Subtype.ext
    funext K
    exact f.map_smul _ _

@[simp]
theorem map_apply (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (f : ρ.IntertwiningMap σ)
    (v : completion ρ hρ) (K : CompactOpenSubgroup G) :
    (map hρ hσ f v).1 K = f (v.1 K) :=
  rfl

@[simp]
theorem map_id (hρ : IsSmooth ρ) :
    map hρ hρ (Representation.IntertwiningMap.id ρ) = LinearMap.id := by
  ext v
  rfl

@[simp]
theorem map_comp (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (hτ : IsSmooth τ)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    map hρ hτ (g.comp f) = (map hσ hτ g).comp (map hρ hσ f) := by
  ext v
  rfl

/-- The componentwise map commutes with translation of families. -/
theorem map_translate (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (f : ρ.IntertwiningMap σ)
    (g : G) (v : completion ρ hρ) :
    (fun K => f (translate ρ g v.1 K)) = translate σ g (map hρ hσ f v).1 := by
  funext K
  exact f.isIntertwining ρ σ g (v.1 (K.conj g⁻¹))

/-- The completion of an intertwiner restricts to the subspaces fixed by `H`. -/
def mapFixed (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (H : Subgroup G)
    (f : ρ.IntertwiningMap σ) :
    completionFixed ρ hρ H →ₗ[ℂ] completionFixed σ hσ H where
  toFun v := ⟨map hρ hσ f v.1, by
    intro h hh
    rw [← map_translate]
    exact congrArg (fun w : CompactOpenSubgroup G → V => fun K => f (w K))
      (v.property h hh)⟩
  map_add' v w := by
    apply Subtype.ext
    exact (map hρ hσ f).map_add v.1 w.1
  map_smul' c v := by
    apply Subtype.ext
    exact (map hρ hσ f).map_smul c v.1

@[simp]
theorem mapFixed_apply (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (H : Subgroup G)
    (f : ρ.IntertwiningMap σ) (v : completionFixed ρ hρ H)
    (K : CompactOpenSubgroup G) :
    (mapFixed hρ hσ H f v).1.1 K = f (v.1.1 K) :=
  rfl

@[simp]
theorem mapFixed_id (hρ : IsSmooth ρ) (H : Subgroup G) :
    mapFixed hρ hρ H (Representation.IntertwiningMap.id ρ) = LinearMap.id := by
  ext v
  rfl

@[simp]
theorem mapFixed_comp (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (hτ : IsSmooth τ)
    (H : Subgroup G) (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    mapFixed hρ hτ H (g.comp f) =
      (mapFixed hσ hτ H g).comp (mapFixed hρ hσ H f) := by
  ext v
  rfl

end Langlands.CompactCompletion
