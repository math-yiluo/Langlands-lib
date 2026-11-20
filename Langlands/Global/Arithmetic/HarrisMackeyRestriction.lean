import Langlands.Global.Arithmetic.GeneralPositionStatement
import Langlands.VirtualRepresentation.ExactMackey
import Langlands.Representation.Filtration.CentralEigenspaceSplitting

/-! # Restriction to a stage that meets every inducing coset -/

noncomputable section

universe uG uV

namespace Langlands.Global.GeneralPosition

open FiniteRepresentation

variable {G U : Type uG} [Group G] [Group U]

private theorem irreducible_of_restrict (ι : U →* G)
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (h : (restrict ι A).IsIrreducible) :
    A.IsIrreducible := by
  let f (S : Subrepresentation A.representation) :
      Subrepresentation (restrict ι A).representation :=
    ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ι g) hv⟩
  have hf : Function.Injective f := fun S T hST =>
    Subrepresentation.toSubmodule_injective
      (congrArg (fun R : Subrepresentation (restrict ι A).representation => R.toSubmodule) hST)
  have hbot : f ⊥ = ⊥ := rfl
  have htop : f ⊤ = ⊤ := rfl
  let : Nontrivial (Subrepresentation A.representation) :=
    ⟨⊥, ⊤, fun he => h.bot_ne_top (hbot.symm.trans ((congrArg f he).trans htop))⟩
  refine ⟨?_⟩
  intro S
  rcases h.eq_bot_or_eq_top (f S) with hs | hs
  · exact Or.inl (hf (hs.trans hbot.symm))
  · exact Or.inr (hf (hs.trans htop.symm))

/-- If the image of `ι` meets every inducing coset, Mackey restriction has only
one term. Irreducibility of that term implies irreducibility before restriction. -/
theorem induce_irreducible_of_one_coset (H : Subgroup G) (ι : U →* G)
    (S : Subgroup U) (κ : S →* H) [H.FiniteIndex] [S.FiniteIndex]
    (hκ : ∀ s : S, (κ s : G) = ι s)
    (hS : ∀ u : U, ι u ∈ H → u ∈ S)
    (hcover : ∀ g : G, ∃ (h : H) (u : U), g = h * ι u)
    (A : FiniteRepresentation.{0, uG, uV} ℂ H)
    (hirr : (induce S (restrict κ A)).IsIrreducible) :
    (induce H A).IsIrreducible := by
  let x : Unit → G := fun _ => 1
  have hc : ∀ _ : Unit, ∀ s : S, (κ s : G) = 1 * ι s * (1 : G)⁻¹ :=
    fun _ s => by simpa only [inv_one, one_mul, mul_one] using hκ s
  let e := mackeyEquiv H ι x (fun _ => S) (fun _ => κ) hc
    (fun _ u hu => hS u (by simpa only [x, inv_one, one_mul, mul_one] using hu))
    (fun g => by obtain ⟨h, u, rfl⟩ := hcover g; exact ⟨h, (), u, by simp only [x, one_mul]⟩)
    (fun _ _ _ _ _ _ _ => Subsingleton.elim _ _) A
  let E : FiniteRepresentation.Equiv (restrict ι (induce H A)) (induce S (restrict κ A)) :=
    { toLinearEquiv := e.trans
        (LinearEquiv.funUnique Unit ℂ (induce S (restrict κ A)).obj)
      isIntertwining' := fun u => LinearMap.ext fun f => by
        change e ((restrict ι (induce H A)).representation u f) () =
          (induce S (restrict κ A)).representation u (e f ())
        exact mackeyMap_intertwines H ι x (fun _ => S) (fun _ => κ) hc A u f () }
  exact irreducible_of_restrict ι _
    ((CentralEigenspaceSplitting.isIrreducible_iff_of_equiv E).mpr hirr)

end Langlands.Global.GeneralPosition
