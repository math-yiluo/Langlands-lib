/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Shrink

/-!
# Ext one of a direct sum is the product of Ext one

Source: literature/stacks-project/more-algebra.tex, proof of Lemma Tag 05EG,
lines 24504--24516 (blueprint: theorem-finite-etale-covers-proper-henselian--2).

Short exactness of `0 → N → E → Q → 0` is expressed, as in the landed sibling
`LinearMap.extension_descends_of_summands` (lem-weil-pbc-direct-sum-extension-assembly),
by injectivity, `Function.Exact` and surjectivity, the module interpretation of
`CategoryTheory.ShortComplex.ShortExact`. The extension-theoretic `Ext¹` set is not
packaged as a quotient: bijectivity of the pullback map `Φ_A` is stated as its
surjectivity clause and its injectivity clause, with classes compared by endpoint-fixed
linear isomorphisms. The pullback `E ×_P C_j` is the submodule
`{(e, c) | v e = ι_j c}` of `E × C_j`, with the maps `n ↦ (u n, 0)` and `(e, c) ↦ c`.
-/

@[expose] public section

universe u w x y z z'

open DirectSum

namespace LinearMap

-- A morphism of short exact sequences fixing both endpoints is an isomorphism.
private theorem shortFive
    {R : Type u} [CommRing R]
    {N : Type w} [AddCommGroup N] [Module R N]
    {P : Type x} [AddCommGroup P] [Module R P]
    {F : Type y} [AddCommGroup F] [Module R F]
    {G : Type z} [AddCommGroup G] [Module R G]
    (a : N →ₗ[R] F) (b : F →ₗ[R] P) (a' : N →ₗ[R] G) (b' : G →ₗ[R] P)
    (ha' : Function.Injective a') (hab : Function.Exact a b)
    (hab' : Function.Exact a' b') (hb : Function.Surjective b)
    (f : F →ₗ[R] G) (hfa : f.comp a = a') (hbf : b'.comp f = b) :
    Function.Bijective f := by
  have hfa' (n : N) : f (a n) = a' n := congrArg (fun k : N →ₗ[R] G ↦ k n) hfa
  have hbf' (e : F) : b' (f e) = b e := congrArg (fun k : F →ₗ[R] P ↦ k e) hbf
  constructor
  · apply (injective_iff_map_eq_zero f).2
    intro e he
    have be : b e = 0 := by rw [← hbf', he, map_zero]
    obtain ⟨n, rfl⟩ := (hab e).1 be
    have hn : n = 0 := ha' (by simpa [hfa'] using he)
    simp [hn]
  · intro g
    obtain ⟨e, he⟩ := hb (b' g)
    have hz : b' (g - f e) = 0 := by simp [map_sub, hbf', he]
    obtain ⟨n, hn⟩ := (hab' _).1 hz
    refine ⟨e + a n, ?_⟩
    rw [map_add, hfa', hn]
    abel

-- Exactness of the componentwise map follows from Mathlib's range/kernel formulas.
private theorem sumExact
    {R : Type u} [CommRing R] {J : Type x}
    {N : Type w} [AddCommGroup N] [Module R N]
    {E : J → Type z} [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
    {C : J → Type y} [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    (a : ∀ j, N →ₗ[R] E j) (b : ∀ j, E j →ₗ[R] C j)
    (h : ∀ j, Function.Exact (a j) (b j)) :
    Function.Exact (DirectSum.lmap a) (DirectSum.lmap b) := by
  apply LinearMap.exact_iff.mpr
  symm
  change LinearMap.range (DFinsupp.mapRange.linearMap a) =
    LinearMap.ker (DFinsupp.mapRange.linearMap b)
  rw [DFinsupp.range_mapRangeLinearMap, DFinsupp.ker_mapRangeLinearMap]
  congr 2
  funext j
  exact (LinearMap.exact_iff.mp (h j)).symm

-- Explicit pushout of the direct sum of extensions along the sum map on N.
-- Its universal property will also identify extensions with equivalent pullbacks.
private theorem assemble
    {R : Type u} [CommRing R] {N : Type w} [AddCommGroup N] [Module R N]
    {J : Type x} [DecidableEq J] (C : J → Type y)
    [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    (E : J → Type z) [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
    (a : ∀ j, N →ₗ[R] E j) (b : ∀ j, E j →ₗ[R] C j)
    (h : ∀ j, Function.Injective (a j) ∧ Function.Exact (a j) (b j) ∧
      Function.Surjective (b j)) :
    ∃ (F : Type (max w x z)) (_ : AddCommGroup F) (_ : Module R F)
      (a' : N →ₗ[R] F) (b' : F →ₗ[R] (⨁ j, C j)) (t : ∀ j, E j →ₗ[R] F),
      Function.Injective a' ∧ Function.Exact a' b' ∧ Function.Surjective b' ∧
      (∀ j, (t j).comp (a j) = a') ∧
      (∀ j, b'.comp (t j) = (lof R J C j).comp (b j)) ∧
      (∀ f g : F →ₗ[R] (⨁ j, C j), f.comp a' = g.comp a' →
        (∀ j, f.comp (t j) = g.comp (t j)) → f = g) ∧
      (∀ (G : Type z') [AddCommGroup G] [Module R G]
        (c : N →ₗ[R] G) (d : ∀ j, E j →ₗ[R] G),
        (∀ j, (d j).comp (a j) = c) →
        ∃ f : F →ₗ[R] G, f.comp a' = c ∧ ∀ j, f.comp (t j) = d j) := by
  classical
  let s : (⨁ _ : J, N) →ₗ[R] N := toModule R J N (fun _ ↦ LinearMap.id)
  let i := DirectSum.lmap a
  let p := DirectSum.lmap b
  let r : (⨁ _ : J, N) →ₗ[R] N × (⨁ j, E j) := s.prod (-i)
  let K := LinearMap.range r
  let q := K.mkQ
  have hp : Function.Exact i p := sumExact a b (fun j ↦ (h j).2.1)
  have hi : Function.Injective i := (DirectSum.lmap_injective a).mpr (fun j ↦ (h j).1)
  have hr : K ≤ LinearMap.ker (p.comp (LinearMap.snd R N (⨁ j, E j))) := by
    rintro _ ⟨d, rfl⟩
    change p (-i d) = 0
    rw [map_neg, hp.apply_apply_eq_zero, neg_zero]
  let a' := q.comp (LinearMap.inl R N (⨁ j, E j))
  let b' := K.liftQ (p.comp (LinearMap.snd R N (⨁ j, E j))) hr
  let t (j : J) := q.comp ((LinearMap.inr R N (⨁ j, E j)).comp (lof R J E j))
  have ha' : Function.Injective a' := by
    apply (injective_iff_map_eq_zero a').2
    intro n hn
    have hm : (n, (0 : ⨁ j, E j)) ∈ K := (Submodule.Quotient.mk_eq_zero K).1 hn
    obtain ⟨d, hd⟩ := hm
    have hid : i d = 0 := by
      have := congrArg Prod.snd hd
      simpa [r] using this
    have hd0 : d = 0 := hi (by simpa using hid)
    have := congrArg Prod.fst hd
    simpa [r, hd0] using this.symm
  have hab' : Function.Exact a' b' := by
    intro e
    obtain ⟨⟨n, d⟩, rfl⟩ := K.mkQ_surjective e
    change p d = 0 ↔ ∃ n', q (n', 0) = q (n, d)
    constructor
    · intro hd
      obtain ⟨k, hk⟩ := (hp d).1 hd
      refine ⟨n + s k, (Submodule.Quotient.eq K).2 ?_⟩
      exact ⟨k, by simp [r, hk]⟩
    · rintro ⟨n', hn'⟩
      have hh := congrArg b' hn'
      change p 0 = p d at hh
      simpa using hh.symm
  have hb' : Function.Surjective b' := by
    intro c
    obtain ⟨d, hd⟩ := ((DirectSum.lmap_surjective b).mpr (fun j ↦ (h j).2.2)) c
    exact ⟨q (0, d), hd⟩
  have ht (j : J) : (t j).comp (a j) = a' := by
    ext n
    apply (Submodule.Quotient.eq K).2
    refine ⟨-lof R J (fun _ ↦ N) j n, ?_⟩
    simp [r, s, i]
  refine ⟨_, inferInstance, inferInstance, a', b', t, ha', hab', hb', ht, ?_, ?_, ?_⟩
  · intro j
    ext e
    simp [b', t, q, p]
  · intro f g h₁ h₂
    have hh : f.comp q = g.comp q := by
      apply LinearMap.prod_ext
      · simpa [a', LinearMap.comp_assoc] using h₁
      · apply DirectSum.linearMap_ext
        intro j
        simpa [t, LinearMap.comp_assoc] using h₂ j
    apply LinearMap.ext
    intro e
    obtain ⟨e, rfl⟩ := K.mkQ_surjective e
    exact congrArg (fun k : N × (⨁ j, E j) →ₗ[R] (⨁ j, C j) ↦ k e) hh
  · intro G _ _ c d hd
    let f₀ : N × (⨁ j, E j) →ₗ[R] G := c.coprod (toModule R J G d)
    have hf₀ : K ≤ LinearMap.ker f₀ := by
      rintro _ ⟨k, rfl⟩
      change c (s k) + toModule R J G d (-i k) = 0
      have hh : (toModule R J G d).comp i = c.comp s := by
        apply DirectSum.linearMap_ext
        intro j
        ext n
        simpa [i, s] using congrArg (fun f : N →ₗ[R] G ↦ f n) (hd j)
      have hh' := congrArg (fun f : (⨁ _ : J, N) →ₗ[R] G ↦ f k) hh
      change toModule R J G d (i k) = c (s k) at hh'
      rw [map_neg, hh', add_neg_cancel]
    refine ⟨K.liftQ f₀ hf₀, ?_, ?_⟩
    · ext n
      simp [a', q, f₀]
    · intro j
      ext e
      simp [t, q, f₀]

private abbrev PB
    {R : Type u} [CommRing R]
    {J : Type x} [DecidableEq J] {C : J → Type y}
    [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    {F : Type z} [AddCommGroup F] [Module R F]
    (b : F →ₗ[R] (⨁ j, C j)) (j : J) :=
  LinearMap.ker (b.comp (LinearMap.fst R F (C j)) -
    (lof R J C j).comp (LinearMap.snd R F (C j)))

private def pbIn
    {R : Type u} [CommRing R]
    {J : Type x} [DecidableEq J] {C : J → Type y}
    [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    {F : Type z} [AddCommGroup F] [Module R F]
    {N : Type w} [AddCommGroup N] [Module R N]
    (a : N →ₗ[R] F) (b : F →ₗ[R] (⨁ j, C j))
    (hab : Function.Exact a b) (j : J) : N →ₗ[R] PB b j :=
  (a.prod 0).codRestrict (PB b j) (by
    intro n
    simp [hab.apply_apply_eq_zero])

private def pbOut
    {R : Type u} [CommRing R]
    {J : Type x} [DecidableEq J] {C : J → Type y}
    [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    {F : Type z} [AddCommGroup F] [Module R F]
    (b : F →ₗ[R] (⨁ j, C j)) (j : J) : PB b j →ₗ[R] C j :=
  (LinearMap.snd R F (C j)).comp (PB b j).subtype

private theorem pb_eq
    {R : Type u} [CommRing R]
    {J : Type x} [DecidableEq J] {C : J → Type y}
    [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    {F : Type z} [AddCommGroup F] [Module R F]
    (b : F →ₗ[R] (⨁ j, C j)) (j : J) (e : PB b j) :
    b e.val.1 = lof R J C j e.val.2 := by
  have := e.property
  exact sub_eq_zero.mp this

private theorem pbExact
    {R : Type u} [CommRing R]
    {J : Type x} [DecidableEq J] {C : J → Type y}
    [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    {F : Type z} [AddCommGroup F] [Module R F]
    {N : Type w} [AddCommGroup N] [Module R N]
    (a : N →ₗ[R] F) (b : F →ₗ[R] (⨁ j, C j))
    (ha : Function.Injective a) (hab : Function.Exact a b)
    (hb : Function.Surjective b) (j : J) :
    Function.Injective (pbIn a b hab j) ∧
    Function.Exact (pbIn a b hab j) (pbOut b j) ∧
    Function.Surjective (pbOut b j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n m h
    apply ha
    exact congrArg (fun e : PB b j ↦ e.val.1) h
  · intro e
    constructor
    · intro he
      have he' : e.val.2 = 0 := he
      have hh : b e.val.1 = 0 := by rw [pb_eq b j e, he', map_zero]
      obtain ⟨n, hn⟩ := (hab _).1 hh
      refine ⟨n, ?_⟩
      apply Subtype.ext
      exact Prod.ext hn he'.symm
    · rintro ⟨n, rfl⟩
      rfl
  · intro c
    obtain ⟨e, he⟩ := hb (lof R J C j c)
    refine ⟨⟨(e, c), ?_⟩, rfl⟩
    exact sub_eq_zero.mpr he

private theorem pullbackEquiv
    {R : Type u} [CommRing R]
    {J : Type x} [DecidableEq J] {C : J → Type y}
    [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    {F : Type z} [AddCommGroup F] [Module R F]
    {N : Type w} [AddCommGroup N] [Module R N]
    (j : J)
    {E : Type z'} [AddCommGroup E] [Module R E]
    (a : N →ₗ[R] E) (b : E →ₗ[R] C j)
    (hab : Function.Exact a b) (hb : Function.Surjective b)
    (a' : N →ₗ[R] F) (b' : F →ₗ[R] (⨁ j, C j))
    (ha' : Function.Injective a') (hab' : Function.Exact a' b')
    (hb' : Function.Surjective b') (t : E →ₗ[R] F)
    (hta : t.comp a = a') (hbt : b'.comp t = (lof R J C j).comp b) :
    ∃ h : PB b' j ≃ₗ[R] E,
      (∀ n hn, h ⟨(a' n, 0), hn⟩ = a n) ∧
      ∀ p, b (h p) = p.val.2 := by
  let l : E →ₗ[R] PB b' j := (t.prod b).codRestrict (PB b' j) (by
    intro e
    apply sub_eq_zero.mpr
    exact congrArg (fun k : E →ₗ[R] (⨁ j, C j) ↦ k e) hbt)
  have hla : l.comp a = pbIn a' b' hab' j := by
    ext n
    · exact congrArg (fun k : N →ₗ[R] F ↦ k n) hta
    · exact hab.apply_apply_eq_zero n
  have hlb : (pbOut b' j).comp l = b := rfl
  have hh := pbExact a' b' ha' hab' hb' j
  let e := LinearEquiv.ofBijective l (shortFive a b (pbIn a' b' hab' j)
    (pbOut b' j) hh.1 hab hh.2.1 hb l hla hlb)
  refine ⟨e.symm, ?_, ?_⟩
  · intro n hn
    apply e.injective
    rw [e.apply_symm_apply]
    exact (congrArg (fun k : N →ₗ[R] PB b' j ↦ k n) hla).symm
  · intro p
    have hh := congrArg (fun q : PB b' j ↦ q.val.2) (e.apply_symm_apply p)
    exact hh

-- A set-theoretic section gives a surjection N × P → F; it need not be linear.
private theorem small_middle
    {R : Type u} [CommRing R]
    {N : Type w} [AddCommGroup N] [Module R N]
    {P : Type x} [AddCommGroup P] [Module R P]
    {F : Type z} [AddCommGroup F] [Module R F]
    (a : N →ₗ[R] F) (b : F →ₗ[R] P)
    (hab : Function.Exact a b) (hb : Function.Surjective b) :
    Small.{max w x} F := by
  classical
  let s : P → F := fun p ↦ (hb p).choose
  have hs (p : P) : b (s p) = p := (hb p).choose_spec
  apply small_of_surjective (f := fun e : N × P ↦ a e.1 + s e.2)
  intro e
  have hz : b (e - s (b e)) = 0 := by simp [map_sub, hs]
  obtain ⟨n, hn⟩ := (hab _).1 hz
  refine ⟨(n, b e), ?_⟩
  simp only [hn]
  abel


/-- Ext one of a direct sum is the product of the Ext one sets of its summands.

Source: literature/stacks-project/more-algebra.tex, proof of Lemma Tag 05EG,
lines 24504--24516 (the direct-sum compatibility step).
(blueprint: theorem-finite-etale-covers-proper-henselian--2)

First clause: surjectivity of `Φ_A` (every family of extensions of the `C j` by `N` is,
up to endpoint-fixed isomorphism, the family of pullbacks along `ι_j` of one extension
of `⨁ j, C j`). Second clause: injectivity of `Φ_A` (two extensions of `⨁ j, C j` whose
pullbacks along every `ι_j` are equivalent are equivalent).

Proof (following the node). For an extension `0 → N → E → P → 0` the pullback
`E ×_P C_j = {(e, c) | v e = ι_j c}` with its evident maps is an extension of `C_j`, and an
equivalence of extensions induces one of the pullbacks, so `Φ_A` is well-defined.
Surjectivity: choose representatives `0 → N → E_j → C_j → 0`; the sum map
`⨁ E_j → P` is surjective with kernel `⨁ u_j(N)` by finite support. Form
`E = (N ⊕ ⨁ E_j)/R`, `R` the image of `n ↦ (Σ n, -⨁ u_j(n_j))`; `N → E` is injective,
`E → P` surjective, and kernel equals image, so `E` is an extension of `P`. For each `j`
the map `E_j → E ×_P C_j`, `e ↦ ([0, ι_j e], v_j e)` is an isomorphism fixing `N` and
`C_j`. Injectivity: every `e ∈ E` lies in `u(N) + Σ_j im(E ×_P C_j → E)` by writing
`v e` as a finite sum; define `q : N ⊕ ⨁ (E ×_P C_j) → E` and `q'` through the `h_j`;
the kernel of `q` is killed by `q'` because the direct sum has unique components and
each `h_j` fixes `N`, so `q'` factors through `h : E → E'`; the inverses `h_j⁻¹` give its
inverse, and `h` fixes `N` and commutes with the maps to `P`. Being surjective and
injective, `Φ_A` is a bijection. -/
theorem extOne_directSum_bijective
    {R : Type u} [CommRing R] {N : Type w} [AddCommGroup N] [Module R N]
    {J : Type x} [DecidableEq J] (C : J → Type y)
    [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)] :
    (∀ (E : J → Type z) [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
        (u : ∀ j, N →ₗ[R] E j) (v : ∀ j, E j →ₗ[R] C j),
        (∀ j, Function.Injective (u j) ∧ Function.Exact (u j) (v j) ∧
          Function.Surjective (v j)) →
        ∃ (F : Type (max w x y)) (_ : AddCommGroup F) (_ : Module R F)
          (u' : N →ₗ[R] F) (v' : F →ₗ[R] (⨁ j, C j)),
          Function.Injective u' ∧ Function.Exact u' v' ∧ Function.Surjective v' ∧
          ∀ j, ∃ h : LinearMap.ker (v' ∘ₗ LinearMap.fst R F (C j) -
                (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F (C j)) ≃ₗ[R] E j,
            (∀ (n : N) (hn : ((u' n, 0) : F × C j) ∈ LinearMap.ker
                (v' ∘ₗ LinearMap.fst R F (C j) -
                  (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F (C j))),
              h ⟨(u' n, 0), hn⟩ = u j n) ∧
            ∀ p, v j (h p) = (p : F × C j).2) ∧
    (∀ (F : Type z) [AddCommGroup F] [Module R F] (F' : Type z') [AddCommGroup F']
        [Module R F'] (u : N →ₗ[R] F) (v : F →ₗ[R] (⨁ j, C j))
        (u' : N →ₗ[R] F') (v' : F' →ₗ[R] (⨁ j, C j)),
        Function.Injective u → Function.Exact u v → Function.Surjective v →
        Function.Injective u' → Function.Exact u' v' → Function.Surjective v' →
        (∀ j, ∃ h : LinearMap.ker (v ∘ₗ LinearMap.fst R F (C j) -
                (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F (C j)) ≃ₗ[R]
              LinearMap.ker (v' ∘ₗ LinearMap.fst R F' (C j) -
                (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F' (C j)),
            (∀ (n : N) (hn : ((u n, 0) : F × C j) ∈ LinearMap.ker
                (v ∘ₗ LinearMap.fst R F (C j) -
                  (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F (C j)))
              (hn' : ((u' n, 0) : F' × C j) ∈ LinearMap.ker
                (v' ∘ₗ LinearMap.fst R F' (C j) -
                  (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F' (C j))),
              h ⟨(u n, 0), hn⟩ = ⟨(u' n, 0), hn'⟩) ∧
            ∀ p, ((h p : F' × C j)).2 = (p : F × C j).2) →
        ∃ g : F ≃ₗ[R] F', g.toLinearMap ∘ₗ u = u' ∧ v' ∘ₗ g.toLinearMap = v) := by
  classical
  constructor
  · intro E _ _ a b h
    obtain ⟨F, _, _, a', b', t, ha', hab', hb', ht, hbt, _, _⟩ :=
      assemble.{u, w, x, y, z, 0} C E a b h
    have : Small.{max w x y} F := small_middle a' b' hab' hb'
    -- Transport the constructed quotient to the universe of its endpoints.
    let e : Shrink.{max w x y} F ≃ₗ[R] F := Shrink.linearEquiv R F
    let a'' := e.symm.toLinearMap.comp a'
    let b'' := b'.comp e.toLinearMap
    have hab'' : Function.Exact a'' b'' :=
      (LinearEquiv.conj_symm_exact_iff_exact a' b' e).mpr hab'
    refine ⟨Shrink.{max w x y} F, inferInstance, inferInstance, a'', b'',
      e.symm.injective.comp ha', hab'', hb'.comp e.surjective, ?_⟩
    intro j
    apply pullbackEquiv j (a j) (b j) (h j).2.1 (h j).2.2 a'' b''
      (e.symm.injective.comp ha') hab'' (hb'.comp e.surjective)
      (e.symm.toLinearMap.comp (t j))
    · simp only [a'', LinearMap.comp_assoc, ht]
    · simp [b'', LinearMap.comp_assoc, hbt]
  · intro F _ _ F' _ _ a b a' b' ha hab hb ha' hab' hb' h
    choose h hhN hhC using h
    -- Assemble the pullbacks once and compare this presentation to both extensions.
    let E (j : J) : Type (max z y) := PB b j
    let i (j : J) := pbIn a b hab j
    let p (j : J) := pbOut b j
    obtain ⟨G, _, _, c, d, t, hc, hcd, hd, ht, hdt, hgen, huniv⟩ :=
      assemble.{u, w, x, y, max z y, max z z'} C E i p (pbExact a b ha hab hb)
    let l (j : J) : E j →ₗ[R] F :=
      (LinearMap.fst R F (C j)).comp (PB b j).subtype
    let l' (j : J) : E j →ₗ[R] F' :=
      ((LinearMap.fst R F' (C j)).comp (PB b' j).subtype).comp (h j).toLinearMap
    obtain ⟨f₀, hf₀⟩ := huniv (F × F') (a.prod a') (fun j ↦ (l j).prod (l' j)) (by
      intro j
      ext n
      · rfl
      · exact congrArg (fun q : PB b' j ↦ q.val.1)
          (hhN j n (i j n).property (pbIn a' b' hab' j n).property))
    let f : G →ₗ[R] F := (LinearMap.fst R F F').comp f₀
    let f' : G →ₗ[R] F' := (LinearMap.snd R F F').comp f₀
    have hfc : f.comp c = a := by
      ext n
      exact congrArg Prod.fst (congrArg (fun k : N →ₗ[R] F × F' ↦ k n) hf₀.1)
    have hfc' : f'.comp c = a' := by
      ext n
      exact congrArg Prod.snd (congrArg (fun k : N →ₗ[R] F × F' ↦ k n) hf₀.1)
    have hft (j : J) : f.comp (t j) = l j := by
      ext e
      exact congrArg Prod.fst (congrArg (fun k : E j →ₗ[R] F × F' ↦ k e) (hf₀.2 j))
    have hft' (j : J) : f'.comp (t j) = l' j := by
      ext e
      exact congrArg Prod.snd (congrArg (fun k : E j →ₗ[R] F × F' ↦ k e) (hf₀.2 j))
    have hbf : b.comp f = d := by
      apply hgen
      · rw [LinearMap.comp_assoc, hfc, hab.linearMap_comp_eq_zero,
          hcd.linearMap_comp_eq_zero]
      · intro j
        rw [LinearMap.comp_assoc, hft, hdt]
        apply LinearMap.ext
        intro e
        exact pb_eq b j e
    have hbf' : b'.comp f' = d := by
      apply hgen
      · rw [LinearMap.comp_assoc, hfc', hab'.linearMap_comp_eq_zero,
          hcd.linearMap_comp_eq_zero]
      · intro j
        rw [LinearMap.comp_assoc, hft', hdt]
        apply LinearMap.ext
        intro e
        exact (pb_eq b' j (h j e)).trans (congrArg (lof R J C j) (hhC j e))
    let e := LinearEquiv.ofBijective f (shortFive c d a b ha hcd hab hd f hfc hbf)
    let e' := LinearEquiv.ofBijective f' (shortFive c d a' b' ha' hcd hab' hd f' hfc' hbf')
    refine ⟨e.symm.trans e', ?_, ?_⟩
    · ext n
      have hn : e.symm (a n) = c n := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact (congrArg (fun k : N →ₗ[R] F ↦ k n) hfc).symm
      change f' (e.symm (a n)) = a' n
      rw [hn]
      exact congrArg (fun k : N →ₗ[R] F' ↦ k n) hfc'
    · apply LinearMap.ext
      intro x
      change b' (f' (e.symm x)) = b x
      calc
        b' (f' (e.symm x)) = d (e.symm x) :=
          congrArg (fun k : G →ₗ[R] (⨁ j, C j) ↦ k (e.symm x)) hbf'
        _ = b (f (e.symm x)) :=
          (congrArg (fun k : G →ₗ[R] (⨁ j, C j) ↦ k (e.symm x)) hbf).symm
        _ = b x := congrArg b (e.apply_symm_apply x)

end LinearMap
