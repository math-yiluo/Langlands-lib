import Langlands.Cohomology.GaloisCovering
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Section trace for a finite Galois covering of a site -/

noncomputable section

open CategoryTheory Opposite

universe u v w r

namespace Langlands.Cohomology.GaloisCovering

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Γ : Type w} [Group Γ] [Fintype Γ] {V' V : C}
  (G : GaloisCovering J Γ V' V) {R : Type r} [CommRing R]
  (F : Sheaf J (ModuleCat.{r} R))

private def deckSum : F.obj.obj (op V') →ₗ[R] F.obj.obj (op V') :=
  ∑ γ : Γ, (F.obj.map (G.deck γ).op).hom

private theorem deckSum_apply (s : F.obj.obj (op V')) :
    G.deckSum F s = ∑ γ : Γ, F.obj.map (G.deck γ).op s := by
  simp only [deckSum, LinearMap.sum_apply]

private theorem deckSum_mem_range (s : F.obj.obj (op V')) :
    G.deckSum F s ∈ LinearMap.range (F.obj.map G.p.op).hom := by
  apply G.exists_map_p_eq F
  intro δ
  rw [deckSum_apply, map_sum]
  calc
    ∑ γ : Γ, F.obj.map (G.deck δ).op (F.obj.map (G.deck γ).op s) =
        ∑ γ : Γ, F.obj.map (G.deck (γ * δ)).op s := by
      simp only [map_map_apply, G.deck_mul]
    _ = ∑ γ : Γ, F.obj.map (G.deck γ).op s :=
      Equiv.sum_comp (Equiv.mulRight δ) (fun γ => F.obj.map (G.deck γ).op s)

/-- Trace descends the unnormalized sum of the deck restrictions to a section on the base. -/
def traceSections : F.obj.obj (op V') →ₗ[R] F.obj.obj (op V) :=
  (LinearEquiv.ofInjective (F.obj.map G.p.op).hom (G.map_p_injective F)).symm.toLinearMap.comp
    ((G.deckSum F).codRestrict _ (G.deckSum_mem_range F))

/-- Restricting the trace back to the cover gives the deck sum. -/
theorem restrict_traceSections (s : F.obj.obj (op V')) :
    F.obj.map G.p.op (G.traceSections F s) = ∑ γ : Γ, F.obj.map (G.deck γ).op s := by
  let e := LinearEquiv.ofInjective (F.obj.map G.p.op).hom (G.map_p_injective F)
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨G.deckSum F s, G.deckSum_mem_range F s⟩)
  exact h.trans (G.deckSum_apply F s)

/-- Tracing the restriction of a section multiplies it by the order of the deck group. -/
theorem traceSections_restrict (s : F.obj.obj (op V)) :
    G.traceSections F (F.obj.map G.p.op s) = Fintype.card Γ • s := by
  apply G.map_p_injective F
  rw [G.restrict_traceSections, map_nsmul]
  simp only [map_map_apply, G.deck_comp, Finset.sum_const, Finset.card_univ]

/-- The section trace commutes with a morphism of coefficient sheaves. -/
theorem traceSections_naturality {F' : Sheaf J (ModuleCat.{r} R)} (f : F ⟶ F')
    (s : F.obj.obj (op V')) :
    f.hom.app (op V) (G.traceSections F s) =
      G.traceSections F' (f.hom.app (op V') s) := by
  apply G.map_p_injective F'
  rw [← ModuleCat.comp_apply, ← f.hom.naturality, ModuleCat.comp_apply,
    G.restrict_traceSections, G.restrict_traceSections, map_sum]
  apply Finset.sum_congr rfl
  intro γ _
  exact ConcreteCategory.congr_hom (f.hom.naturality (G.deck γ).op) s

/-- Restriction commutes with trace in a deck-equivariant square of covers with the same group. -/
theorem traceSections_map {B' B : C} (H : GaloisCovering J Γ B' B)
    {a : B' ⟶ V'} {b : B ⟶ V} (h : a ≫ G.p = H.p ≫ b)
    (hDeck : ∀ γ, H.deck γ ≫ a = a ≫ G.deck γ) (s : F.obj.obj (op V')) :
    F.obj.map b.op (G.traceSections F s) = H.traceSections F (F.obj.map a.op s) := by
  apply H.map_p_injective F
  rw [map_map_apply, ← h, ← map_map_apply, G.restrict_traceSections,
    H.restrict_traceSections, map_sum]
  simp only [map_map_apply, hDeck]

end Langlands.Cohomology.GaloisCovering
