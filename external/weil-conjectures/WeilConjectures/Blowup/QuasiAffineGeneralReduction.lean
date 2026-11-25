/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.DisjointnessBlowup
public import WeilConjectures.Compactification.FiniteTypeDirected
public import WeilConjectures.Compactification.IdealSheafPower
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties

/-!

# The disjointness reduction in Conrad's Theorem 2.4, Case 3

This file contains the first of the two opening reductions of Conrad's proof of Case 3 of
Theorem 2.4 in *Deligne's notes on Nagata compactifications* (blueprint:
`lemma:nagata-conrad-case3-disjointness-reduction`).

The data is a qcqs scheme `X` with quasi-compact opens `U ≤ V`, a morphism `p : Y ⟶ X`
from a qcqs scheme and a section `f : U ⟶ Y` of `p` over `U` whose image is closed in
`p ⁻¹ V`. After one `V`-admissible blow-up of `X` the closure of the image of (the base
change of) `f` no longer meets the part lying over the closure of `V ∖ U`.

The blow-up is produced by Deligne's disjointness lemma
(`AlgebraicGeometry.disjoint_closure_range_of_blowupMap_sup`, blueprint
`lemma:nagata-conrad-disjointness-blowup`) applied to the two centres

* `I₁`, a finite-type quasi-coherent subideal of the vanishing ideal of the reduced closed
  subscheme `closure (V ∖ U)`, and
* `I₂ = I₁ * I₁ ⊔ K ^ n`, where `K` is a finite-type ideal sheaf cutting out `X ∖ V` and
  `n` is large enough that `K ^ n` pulls back into `I₁ ^ 2 · 𝒪_Y + I_{closure f(U)}`.

The exponent `n` comes from `Scheme.IdealSheafData.exists_pow_le`, and the passage from
the vanishing ideal of `closure (V ∖ U)`, which need not be of finite type, to the
finite-type subideal `I₁` is the compactness of a finite-type ideal sheaf against the
directed supremum of the finite-type subideals
(`Scheme.IdealSheafData.exists_le_of_ofFiniteType_le_iSup`).

## Main results

- `AlgebraicGeometry.exists_isAdmissible_disjoint_closure_range_of_le`: the disjointness
  blow-up (blueprint: `lemma:nagata-conrad-case3-disjointness-reduction`).

-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Conrad's Theorem 2.4, Case 3, Step 1**: the disjointness blow-up.

Let `X` be qcqs, let `U ≤ V` be quasi-compact opens of `X`, let `p : Y ⟶ X` be a morphism
from a qcqs scheme and let `f : U ⟶ Y` be a section of `p` over `U` whose image is closed
in `p ⁻¹ V`. There is a `V`-admissible blow-up of `X` after which the closure of the image
of the base change of `f` is disjoint from the part lying over the closure of `V ∖ U`.

The base change is left flexible: `Z'` is an arbitrary scheme over `Y` and over
`(I₁ ⊔ I₂).blowup`, and `Y'` an arbitrary scheme over `U` and over `Z'`, fitting into the two
commuting squares, exactly as in `AlgebraicGeometry.disjoint_closure_range_of_blowupMap_sup`.
(Blueprint: `lemma:nagata-conrad-case3-disjointness-reduction`.) -/
theorem exists_isAdmissible_disjoint_closure_range_of_le
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {p : Y ⟶ X}
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (hfc : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ B : IsAdmissible X V,
      ∀ {Z' Y' : Scheme.{u}} {r : Z' ⟶ Y} {p' : Z' ⟶ B.I.blowup}
        (_ : r ≫ p = p' ≫ B.I.blowupMap)
        {fY : Y' ⟶ U.toScheme} {f' : Y' ⟶ Z'} [QuasiCompact f']
        (_ : f' ≫ r = fY ≫ f),
        Disjoint (closure (Set.range f'))
          (p' ⁻¹' closure (B.I.blowupMap ⁻¹' ((V : Set X) \ (U : Set X)))) := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  -- `V ∖ U` is closed in `V`, so its closure misses `U`
  have hcl : closure ((V : Set X) \ (U : Set X)) ⊆ (U : Set X)ᶜ :=
    closure_minimal (fun _ hx ↦ hx.2) U.isOpen.isClosed_compl
  -- the reduced structure on `closure (V ∖ U)`
  set H : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨_, isClosed_closure (s := (V : Set X) \ (U : Set X))⟩
    with hHdef
  have hHsupp : (H.support : Set X) = closure ((V : Set X) \ (U : Set X)) := by
    rw [hHdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  -- a finite-type closed subscheme structure on `X ∖ V`
  obtain ⟨K, hKft, hKsupp⟩ := X.exists_finiteType_ideal_coe_support_eq_compl V hV
  -- the graph lies over `U`
  have hYU : Set.range (f ≫ p) ⊆ (U : Set X) := by
    rw [hf, Scheme.Opens.range_ι]
  -- the graph is closed in `p ⁻¹ V`, so the closure of the graph meets `p ⁻¹ V` in it
  have hgraph : closure (Set.range f) ∩ ((p ⁻¹ᵁ V : Y.Opens) : Set Y) ⊆ Set.range f := by
    rintro y ⟨hy, hyV⟩
    obtain ⟨z, rfl⟩ : ∃ z, (p ⁻¹ᵁ V).ι z = y := by
      rwa [← Scheme.Opens.range_ι] at hyV
    have hz : z ∈ closure ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f) :=
      (p ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage hy
    rwa [hfc.closure_eq] at hz
  -- the set-theoretic containment feeding `exists_pow_le`:
  -- `p (p ⁻¹ (V (I₁ ^ 2)) ∩ closure (f (U))) ⊆ X ∖ V`
  have hsupp : (((H * H).comap p ⊔ f.ker).support : Set Y) ⊆ ((K.comap p).support : Set Y) := by
    intro y hy
    rw [Scheme.IdealSheafData.coe_support_sup] at hy
    obtain ⟨hy₁, hy₂⟩ := hy
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup, Set.union_self,
      hHsupp, Set.mem_preimage] at hy₁
    rw [Scheme.Hom.support_ker] at hy₂
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hKsupp,
      Set.mem_preimage, Set.mem_compl_iff]
    intro hyV
    obtain ⟨u, rfl⟩ := hgraph ⟨hy₂, hyV⟩
    have hu : (f ≫ p) u ∈ (U : Set X) := hYU (Set.mem_range_self u)
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hu
    exact hcl hy₁ hu
  obtain ⟨n, hn⟩ := Scheme.IdealSheafData.exists_pow_le (hKft.comap p) hsupp
  -- the directed family of the finite-type quasi-coherent subideals of `H`
  set S : Set X.IdealSheafData := {J : X.IdealSheafData | J ≤ H ∧ J.ofFiniteType}
  have hSdir : DirectedOn (· ≤ ·) S := Scheme.IdealSheafData.directedOn_ofFiniteType_le H
  have hSsup : sSup S = H := Scheme.IdealSheafData.sSup_ofFiniteType_le_eq H
  have : Nonempty S := ⟨⟨⊥, bot_le, Scheme.IdealSheafData.ofFiniteType_bot⟩⟩
  -- the square of `H` is the supremum of the squares of the members of the family
  have hsq : H * H ≤ ⨆ J : S, (J.1 * J.1) := by
    conv_lhs => rw [← hSsup, sSup_eq_iSup']
    rw [Scheme.IdealSheafData.iSup_mul]
    refine iSup_le fun i ↦ ?_
    rw [mul_comm, Scheme.IdealSheafData.iSup_mul]
    refine iSup_le fun j ↦ ?_
    obtain ⟨k, hk, hik, hjk⟩ := hSdir i.1 i.2 j.1 j.2
    exact (Scheme.IdealSheafData.mul_mono hjk hik).trans
      (le_iSup (fun l : S ↦ l.1 * l.1) ⟨k, hk⟩)
  -- the family is directed after pulling back to `Y` and adding the ideal of the graph
  have hBdir : Directed (· ≤ ·) (fun J : S ↦ (J.1 * J.1).comap p ⊔ f.ker) := by
    intro i j
    obtain ⟨k, hk, hik, hjk⟩ := hSdir i.1 i.2 j.1 j.2
    exact ⟨⟨k, hk⟩, sup_le_sup_right (Scheme.IdealSheafData.comap_mono p
        (Scheme.IdealSheafData.mul_mono hik hik)) _,
      sup_le_sup_right (Scheme.IdealSheafData.comap_mono p
        (Scheme.IdealSheafData.mul_mono hjk hjk)) _⟩
  -- `K ^ n` pulls back into the supremum, hence into one member: this is the large `α`
  have hAle : (K.comap p) ^ n ≤ ⨆ J : S, ((J.1 * J.1).comap p ⊔ f.ker) := by
    refine hn.trans (sup_le ?_ (le_trans le_sup_right
      (le_iSup (fun J : S ↦ (J.1 * J.1).comap p ⊔ f.ker) (Classical.arbitrary S))))
    refine le_trans ?_ (iSup_mono fun J : S ↦ (le_sup_left :
      (J.1 * J.1).comap p ≤ (J.1 * J.1).comap p ⊔ f.ker))
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
    refine hsq.trans (iSup_le fun J ↦ ?_)
    rw [Scheme.IdealSheafData.le_map_iff_comap_le]
    exact le_iSup (fun J : S ↦ (J.1 * J.1).comap p) J
  obtain ⟨i, hi⟩ := Scheme.IdealSheafData.exists_le_of_ofFiniteType_le_iSup
    ((hKft.comap p).pow n) hBdir hAle
  obtain ⟨hJle, hJft⟩ : i.1 ≤ H ∧ i.1.ofFiniteType := i.2
  set J : X.IdealSheafData := i.1
  -- the second centre `I₂ = I₁ ^ 2 ⊓ (X ∖ V)`
  have hI₂V : ((J * J ⊔ K ^ n : X.IdealSheafData).support : Set X) ⊆ (V : Set X)ᶜ := by
    rw [Scheme.IdealSheafData.coe_support_sup]
    refine Set.inter_subset_right.trans ?_
    rw [← hKsupp]
    exact fun x hx ↦ Scheme.IdealSheafData.support_pow_le n hx
  have hVU : (V : Set X) \ (U : Set X) ⊆ (J.support : Set X) := by
    have hle : (H.support : Set X) ⊆ (J.support : Set X) :=
      Scheme.IdealSheafData.support_antitone hJle
    rw [hHsupp] at hle
    exact fun x hx ↦ hle (subset_closure hx)
  have hfac : (J * J ⊔ K ^ n : X.IdealSheafData).comap p ≤ (J * J).comap p ⊔ f.ker := by
    rw [Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_pow]
    exact sup_le le_sup_left hi
  refine ⟨⟨J ⊔ (J * J ⊔ K ^ n), hJft.sup ((hJft.mul hJft).sup (hKft.pow n)), ?_⟩, ?_⟩
  · rw [Scheme.IdealSheafData.coe_support_sup]
    exact Set.disjoint_left.mpr fun x hxV hx ↦ hI₂V hx.2 hxV
  · intro Z' Y' r p' hw fY f' hqc hcomm
    have := hqc
    exact disjoint_closure_range_of_blowupMap_sup hUV hI₂V hVU hYU hfac hw hcomm

end AlgebraicGeometry
