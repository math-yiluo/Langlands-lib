/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Length
import WeilConjectures.RingTheory.SimpleFiltration
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Length-one filtrations of ideals in Artinian rings

Source: literature/stacks-project/algebra.tex, Algebra, proof of Lemma Tag 02HT
(blueprint: lem-weil-pbc-artinian-ideal-length-one-filtration).
-/

@[expose] public section

universe u

namespace RingTheory

/--
For an Artinian commutative ring, every ideal admits a finite filtration by ideals
whose successive quotients have module length one.

Source: literature/stacks-project/algebra.tex, Algebra, proof of Lemma Tag 02HT
(blueprint: lem-weil-pbc-artinian-ideal-length-one-filtration). The proof uses
`lem-weil-pbc-artinian-ring-self-finite-length` and
`theorem-finite-etale-covers-proper-henselian--2`. Regard `B` as a module over
itself and use the Artinian-ring finite-length lemma to bound strict submodule
chains. The ideal `J` is a submodule of `B`, so it has finite length. Apply the
finite-length simple-filtration lemma to `J`; its submodules are precisely the
ideals contained in `J`, and its successive module quotients are the displayed
quotients. The zero ideal is handled by taking `r = 0`.
-/
theorem exists_ideal_filtration_length_one (B : Type u) [CommRing B]
    [IsArtinianRing B] (J : Ideal B) :
    ∃ (r : ℕ) (F : Fin (r + 1) → Ideal B),
      F 0 = ⊥ ∧ F (Fin.last r) = J ∧
        (∀ i : Fin r, F (Fin.castSucc i) ≤ F i.succ) ∧
        (∀ i : Fin r,
          Module.length B
              (↥(F i.succ) ⧸
                Submodule.comap (F i.succ).subtype (F (Fin.castSucc i))) = 1) := by
  have hfin : Module.length B J < ⊤ := by
    rw [lt_top_iff_ne_top, Module.length_ne_top_iff]
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨r, F, h0, htop, hlt, hs⟩ :=
    Module.exists_simple_filtration_of_length_lt_top B J hfin
  let G : Fin (r + 1) → Ideal B := fun i => (F i).map J.subtype
  refine ⟨r, G, ?_, ?_, ?_, ?_⟩
  · simp [G, h0]
  · simp [G, htop]
  · intro i
    exact Submodule.map_mono (hlt i).le
  · intro i
    let p : Submodule B (↥(F i.succ)) :=
      Submodule.comap (F i.succ).subtype (F i.castSucc)
    let q : Submodule B (↥(G i.succ)) :=
      Submodule.comap (G i.succ).subtype (G i.castSucc)
    let f : (↥(F i.succ)) →ₗ[B] (↥(G i.succ)) :=
      (J.subtype.comp (F i.succ).subtype).codRestrict (G i.succ) (by
        intro x
        exact ⟨x, x.2, by simp⟩)
    have hf : Function.Bijective f := by
      constructor
      · intro x y h
        apply Subtype.ext
        simpa [f] using congr_arg Subtype.val h
      · intro y
        rcases y.2 with ⟨x, hx, hxy⟩
        refine ⟨⟨x, hx⟩, ?_⟩
        apply Subtype.ext
        simpa [f] using hxy
    let e : (↥(F i.succ)) ≃ₗ[B] (↥(G i.succ)) := LinearEquiv.ofBijective f hf
    have he : p.map (e : (↥(F i.succ)) →ₗ[B] (↥(G i.succ))) = q := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change (J.subtype y.1) ∈ Submodule.map J.subtype (F i.castSucc)
        exact Submodule.mem_map.mpr ⟨y.1, (Submodule.mem_comap.mp hy), rfl⟩
      · intro hx
        have hx' : x.1 ∈ G i.castSucc := Submodule.mem_comap.mp hx
        obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx'
        have hy' : y ∈ F i.succ := (hlt i).le hy
        refine Submodule.mem_map.mpr ⟨⟨y, hy'⟩, ?_, ?_⟩
        · exact Submodule.mem_comap.mpr hy
        · apply Subtype.ext
          change J.subtype y = x.1
          exact hxy
    have es := Submodule.Quotient.equiv p q e he
    exact (Module.length_eq_one_iff).2 ((es.isSimpleModule_iff).mp (hs i))
end RingTheory
