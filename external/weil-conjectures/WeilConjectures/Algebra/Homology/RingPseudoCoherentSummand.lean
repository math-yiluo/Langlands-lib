/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts

public import WeilConjectures.RingTheory.MPseudoCoherent
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentIffAllM

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-!
# Direct summands of pseudo-coherent complexes

Source: literature/stacks-project/more-algebra.tex, Tags 064X and 064U
(blueprint: lem-pc-ring-pseudo-coherent-summand).
-/

private theorem mPseudoCoherent_of_homology_map {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] (m : ℤ)
    {C D : DerivedCategory (ModuleCat.{v} R)} (g : C ⟶ D)
    (hg : ∀ i : ℤ, m < i → IsIso ((homologyFunctor (ModuleCat.{v} R) i).map g))
    [Epi ((homologyFunctor (ModuleCat.{v} R) m).map g)]
    (h : IsMPseudoCoherent m C) : IsMPseudoCoherent m D := by
  obtain ⟨E, a, b, ha, hb, hfree, f, hf, hepi⟩ := h
  refine ⟨E, a, b, ha, hb, hfree, f ≫ g, ?_, ?_⟩
  · intro i hi
    have := hf i hi
    have := hg i hi
    rw [Functor.map_comp]
    infer_instance
  · have := hepi
    rw [Functor.map_comp]
    infer_instance

private theorem mPseudoCoherent_mono {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] {m n : ℤ} (hmn : m ≤ n)
    {C : DerivedCategory (ModuleCat.{v} R)} (h : IsMPseudoCoherent m C) :
    IsMPseudoCoherent n C := by
  obtain ⟨E, a, b, ha, hb, hfree, f, hf, hepi⟩ := h
  refine ⟨E, a, b, ha, hb, hfree, f, fun i hi => hf i (lt_of_le_of_lt hmn hi), ?_⟩
  by_cases hmn' : m = n
  · subst n
    exact hepi
  · have := hf n (lt_of_le_of_ne hmn hmn')
    infer_instance

private theorem pseudoCoherent_iff_all {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] (C : DerivedCategory (ModuleCat.{v} R)) :
    IsPseudoCoherent C ↔ ∀ m : ℤ, IsMPseudoCoherent m C := by
  classical
  let E := Q.objPreimage C
  let e : Q.obj E ≅ C := Q.objObjPreimageIso C
  have hpc : IsPseudoCoherent C ↔ IsPseudoCoherent (Q.obj E) := by
    constructor
    · rintro ⟨F, b, hb, hfree, ⟨f⟩⟩
      exact ⟨F, b, hb, hfree, ⟨f ≪≫ e.symm⟩⟩
    · rintro ⟨F, b, hb, hfree, ⟨f⟩⟩
      exact ⟨F, b, hb, hfree, ⟨f ≪≫ e⟩⟩
  rw [hpc, isPseudoCoherent_iff_forall_isMPseudoCoherent R E]
  exact ⟨fun h m => mPseudoCoherent_of_homology_map m e.hom (fun _ _ ↦ inferInstance) (h m),
    fun h m => mPseudoCoherent_of_homology_map m e.inv (fun _ _ ↦ inferInstance) (h m)⟩

/-- A direct summand of an `m`-pseudo-coherent complex is `m`-pseudo-coherent.
Proof: the bounded witness gives a common upper cohomology bound. Cohomology of each
summand is a quotient of that of `K ⊞ L`, hence vanishes above this bound. The zero
witness makes both summands `B`-pseudo-coherent for a sufficiently large `B`.
Descend simultaneously from `B` to `m`: if both summands are `(n + 1)`-pseudo-coherent,
the split triangles `K → K ⊞ L → L` and `L → L ⊞ K → K`, together with clause one of
`isMPseudoCoherent_of_distinguished_triangle`, make both `n`-pseudo-coherent.
The original witness gives `n`-pseudo-coherence of the middle terms whenever `m ≤ n`.
This is a simultaneous degree descent in place of the shift descent of Tag 064X.
Source: Stacks Project, More on Algebra, Tag 064X.
(blueprint: lem-pc-ring-pseudo-coherent-summand) -/
theorem mPseudoCoherent_summand {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] (m : ℤ)
    (K L : DerivedCategory (ModuleCat.{v} R))
    (h : IsMPseudoCoherent m (K ⊞ L)) :
    IsMPseudoCoherent m K ∧ IsMPseudoCoherent m L := by
  open CategoryTheory.Pretriangulated in
  have step (n : ℤ) (hn : m ≤ n)
      (hK : IsMPseudoCoherent (n + 1) K) (hL : IsMPseudoCoherent (n + 1) L) :
      IsMPseudoCoherent n K ∧ IsMPseudoCoherent n L := by
    have hsum := mPseudoCoherent_mono hn h
    have hswap := mPseudoCoherent_of_homology_map n (biprod.braiding K L).hom
      (fun _ _ ↦ inferInstance) hsum
    exact ⟨(isMPseudoCoherent_of_distinguished_triangle R n
        (binaryBiproductTriangle L K) (binaryBiproductTriangle_distinguished L K)).1
        hL hswap,
      (isMPseudoCoherent_of_distinguished_triangle R n
        (binaryBiproductTriangle K L) (binaryBiproductTriangle_distinguished K L)).1
        hK hsum⟩
  obtain ⟨E, a, b, ha, hb, hfree, f, hf, hepi⟩ := h
  have : E.IsStrictlyLE b := hb
  let B : ℤ := max m b + 1
  have hvan (i : ℤ) (hi : B ≤ i) :
      IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj (K ⊞ L)) := by
    have := hf i (by dsimp [B] at hi; omega)
    exact (isZero_of_isLE (Q.obj E) b i (by dsimp [B] at hi; omega)).of_iso
      (asIso ((homologyFunctor (ModuleCat.{v} R) i).map f)).symm
  have hbase : IsMPseudoCoherent B K ∧ IsMPseudoCoherent B L := by
    constructor
    · apply isMPseudoCoherent_of_homology_vanishes
      intro i hi
      exact (hvan i hi).of_epi ((homologyFunctor (ModuleCat.{v} R) i).map biprod.fst)
    · apply isMPseudoCoherent_of_homology_vanishes
      intro i hi
      exact (hvan i hi).of_epi ((homologyFunctor (ModuleCat.{v} R) i).map biprod.snd)
  have descend (k : ℕ) : m ≤ B - k →
      IsMPseudoCoherent (B - k) K ∧ IsMPseudoCoherent (B - k) L := by
    induction k with
    | zero => simpa using fun (_ : m ≤ B) => hbase
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have he : B - ((k + 1 : ℕ) : ℤ) + 1 = B - (k : ℤ) := by omega
      exact step (B - (k + 1 : ℕ)) hk
        (by rw [he]; exact hprev.1) (by rw [he]; exact hprev.2)
  have hBm : m ≤ B := by dsimp [B]; omega
  have heq : B - ((B - m).toNat : ℤ) = m := by omega
  simpa only [heq] using descend (B - m).toNat (by omega)

/-- If `K ⊞ L` is quasi-isomorphic to a bounded-above complex of finite free modules
(pseudo-coherent), then so are `K` and `L`.
Proof (node): stupid truncations of a bounded-above finite free model show `K ⊞ L` is
`m`-pseudo-coherent for every `m`, hence so are `K` and `L` by the first clause, and an
object that is `m`-pseudo-coherent for every `m` has a bounded-above finite free model,
built downward degree by degree (Stacks, Tag 064U).
Source: Stacks Project, More on Algebra, Tags 064X and 064U.
(blueprint: lem-pc-ring-pseudo-coherent-summand) -/
theorem pseudoCoherent_summand {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (K L : DerivedCategory (ModuleCat.{v} R))
    (h : IsPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent K ∧ IsPseudoCoherent L := by
  have hall := (pseudoCoherent_iff_all (K ⊞ L)).mp h
  exact ⟨(pseudoCoherent_iff_all K).mpr (fun m => (mPseudoCoherent_summand m K L (hall m)).1),
    (pseudoCoherent_iff_all L).mpr (fun m => (mPseudoCoherent_summand m K L (hall m)).2)⟩

end DerivedCategory
