import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.InfiniteAdelicGroupProduct
import Langlands.Global.InfinitePlaceMaximalCompactConjugacy

/-! # Conjugacy of maximal compact subgroups of the infinite adelic group -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.CompactIwasawa

section Pi

variable {I : Type u} {H : I → Type v} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]

private theorem isCompact_map_eval {K : Subgroup (∀ i, H i)}
    (hK : IsCompact (K : Set (∀ i, H i))) (i : I) :
    IsCompact (K.map (Pi.evalMonoidHom H i) : Set (H i)) := by
  rw [Subgroup.coe_map]
  exact hK.image (continuous_apply i)

/-- A product-group maximal compact is the product of its coordinate images. -/
theorem IsMaximalCompact.eq_pi_map_eval {K : Subgroup (∀ i, H i)}
    (hK : IsMaximalCompact K) :
    K = Subgroup.pi Set.univ (fun i => K.map (Pi.evalMonoidHom H i)) := by
  refine (hK.2 _ (isCompact_univ_pi fun i => isCompact_map_eval hK.1 i) ?_).symm
  intro x hx
  rw [Subgroup.mem_pi]
  exact fun i _ => ⟨x, hx, rfl⟩

/-- Each coordinate image of a product-group maximal compact is maximal compact. -/
theorem IsMaximalCompact.map_eval {K : Subgroup (∀ i, H i)}
    (hK : IsMaximalCompact K) (i : I) :
    IsMaximalCompact (K.map (Pi.evalMonoidHom H i)) := by
  classical
  refine ⟨isCompact_map_eval hK.1 i, fun L hL hle => le_antisymm ?_ hle⟩
  let C (j : I) := Function.update (fun k => K.map (Pi.evalMonoidHom H k)) i L j
  have hC (j : I) : IsCompact (C j : Set (H j)) := by
    by_cases h : j = i
    · subst j
      simpa only [C, Function.update_self] using hL
    · simpa only [C, Function.update_of_ne h] using isCompact_map_eval hK.1 j
  have hKC : K ≤ Subgroup.pi Set.univ C := by
    intro x hx
    rw [Subgroup.mem_pi]
    intro j _
    have hxj : x j ∈ K.map (Pi.evalMonoidHom H j) := ⟨x, hx, rfl⟩
    by_cases h : j = i
    · subst j
      simpa only [C, Function.update_self] using hle hxj
    · simpa only [C, Function.update_of_ne h] using hxj
  have heq := hK.2 (Subgroup.pi Set.univ C) (isCompact_univ_pi hC) hKC
  intro x hx
  let y := Function.update (1 : ∀ i, H i) i x
  refine ⟨y, heq ▸ (show y ∈ Subgroup.pi Set.univ C from ?_), ?_⟩
  · rw [Subgroup.mem_pi]
    intro j _
    by_cases h : j = i
    · subst j
      simpa only [y, C, Function.update_self] using hx
    · rw [show y j = 1 by simp only [y, Function.update_of_ne h, Pi.one_apply]]
      exact (C j).one_mem
  · change y i = x
    simp only [y, Function.update_self]

end Pi

end Langlands.CompactIwasawa

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.CompactIwasawa

/-- Any two maximal compact subgroups of the actual infinite adelic group of
a connected reductive group are conjugate by an infinite adelic point. -/
def InfiniteAdelicMaximalCompactConjugacyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (K L : Subgroup (InfiniteAdelicGroupPoints F G)),
      IsConnectedReductive G → IsMaximalCompact K → IsMaximalCompact L →
      ∃ t : InfiniteAdelicGroupPoints F G, K.map (MulAut.conj t).toMonoidHom = L

theorem infiniteAdelicMaximalCompactConjugacy :
    InfiniteAdelicMaximalCompactConjugacyStatement.{u} := by
  intro F _ _ G _ K L hG hK hL
  let e := completions F G
  let H := K.map e.toMonoidHom
  let I := L.map e.toMonoidHom
  have hH : IsMaximalCompact H := hK.map e
  have hI : IsMaximalCompact I := hL.map e
  choose t ht using fun w => InfinitePlaceGroupPoints.infinitePlaceMaximalCompactConjugacy F G w
    _ _ hG (hH.map_eval w) (hI.map_eval w)
  have hconj : H.map (MulAut.conj t).toMonoidHom = I := by
    rw [hH.eq_pi_map_eval, hI.eq_pi_map_eval]
    ext x
    simp only [Subgroup.mem_map_equiv, Subgroup.mem_pi, Set.mem_univ, true_implies]
    refine forall_congr' fun w => ?_
    rw [← ht w, Subgroup.mem_map_equiv]
    rfl
  refine ⟨e.symm t, Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_⟩
  change (K.map (MulAut.conj (e.symm t)).toMonoidHom).map e.toMonoidHom = I
  rw [← hconj, Subgroup.map_map]
  change K.map (e.toMonoidHom.comp (MulAut.conj (e.symm t)).toMonoidHom) =
    (K.map e.toMonoidHom).map (MulAut.conj t).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change e (e.symm t * x * (e.symm t)⁻¹) = t * e x * t⁻¹
  simp only [map_mul, map_inv, e.apply_symm_apply]

end Langlands.Global.InfiniteAdelicGroupPoints
