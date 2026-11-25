/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Basic
import WeilConjectures.AlgebraicGeometry.SmoothAtPrimeArtinianLiftingForward
import WeilConjectures.AlgebraicGeometry.SmoothAtPrimeArtinianLiftingReverse

/-!
# Smoothness near a prime and lifting along Artinian small extensions

Source: Stacks Project, Algebra, Lemma 02HT, (1) iff (3), and Definition 02HS
(blueprint: lem-weil-pbc-smooth-at-prime-artinian-lifting).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, Lemma 02HT, (1) iff (3); Definition 02HS.
(blueprint: lem-weil-pbc-smooth-at-prime-artinian-lifting).

A finite type ring map over a Noetherian ring is smooth on an open neighbourhood of `q`
exactly when every compatible diagram at `q` lifts along every Artinian small extension.
The small-extension conditions are spelled out using module length, not square-zero alone.

Proof (the twelve steps of the blueprint node):
1. Principal opens form a basis of Spec A (def-weil-affine-spectrum). The localization
   map identifies Spec A_g with D(g) (lem-weil-pbc-principal-localization-open-immersion,
   def-weil-open-immersion). Smoothness is unchanged by that isomorphism and by restriction
   (lem-weil-pbc-smooth-restrict-open-subschemes,
   lem-weil-pbc-morphism-factors-through-open-subscheme). Thus an open smooth neighbourhood
   exists iff some g outside q makes R -> A_g smooth
   (lem-weil-pbc-smooth-ring-map-iff-smooth-affine, def-weil-pbc-smooth-ring-map).
2. The kernel I of a small extension is a simple module. Its annihilator is the unique
   maximal ideal m' of B', so m'I = 0. Since B is nonzero, I is proper and contained in m',
   hence I squared is zero. Surjectivity also gives preimage(m_B) = m' and B'/I = B.
3. Given a smooth A_g and a diagram, a(g) is a unit because its preimage maximal ideal is q.
   Factor a through A_g; square-zero lifting for this smooth algebra gives a map to B'
   (lem-weil-pbc-smooth-ring-map-square-zero-lifting). Compose with A -> A_g to get a'.
4. Finite type over Noetherian gives a finite presentation A = P/I with P a finite polynomial
   ring (lem-weil-pbc-finite-type-noetherian-finite-presentation). Differentials of P are free
   on the coordinate differentials (lem-weil-pbc-polynomial-ring-kahler-basis,
   def-weil-pbc-kahler-differentials), and its first cotangent homology vanishes
   (lem-weil-pbc-polynomial-ring-h1-cotangent-vanishing). Jacobi-Zariski gives the exact
   sequence from first cotangent homology through I/I squared and the free differential
   module to Omega A/R (lem-weil-pbc-jacobi-zariski-quotient-smooth).
5. If the conormal map splits at q, exactness gives vanishing first cotangent homology there
   and makes the differentials a finite flat direct summand of a finite free module.
   Finite flat over local is free (lem-weil-pbc-finite-flat-local-free), so the criterion
   lem-weil-pbc-smooth-at-prime-naive-cotangent-criterion and step 1 give smoothness near q.
6. Localize P at the preimage q' of q, obtaining C with maximal ideal m and ideal J = IC.
   Noetherianity follows from lem-weil-pbc-finite-type-algebra-noetherian and
   lem-weil-pbc-localization-noetherian. Exact localization identifies C/J with A_q and
   J/J squared with the localized conormal module. Differential localization identifies
   the target with A_q tensor Omega C/R (lem-weil-pbc-kahler-differentials-localization).
7. For N >= 1 take B'_N = C/(J squared + m^N), B_N = C/(J + m^N), and their quotient map.
   Both are Artinian local with maximal ideals having N-th power zero
   (lem-weil-pbc-noetherian-local-quotient-artinian-local). The kernel has square zero.
   The natural maps from R and A give a compatible diagram with preimage maximal ideal q.
8. Filter the kernel by length-one factors (lem-weil-pbc-artinian-ideal-length-one-filtration).
   All intermediate quotients remain Artinian local by the quotient lemma in step 7.
   Apply the lifting hypothesis successively to these small extensions. At each step the
   preimage maximal ideal stays q by step 2. This produces s_N : A -> B'_N over R.
9. Elements outside q map to units, so s_N factors through A_q. The N-th power of q maps
   to zero, so it factors further through B_N. The resulting R-algebra map sigma_N is a
   section of B'_N -> B_N, by the universal properties of localization and quotient.
10. The square-zero conormal retraction lemma
    (lem-weil-pbc-square-zero-section-conormal-retraction) applied to this section makes
    the conormal map of B'_N -> B_N a split injection.
11. Artin-Rees (lem-weil-pbc-artin-rees) supplies c >= 1 such that m^N intersect J is
    contained in m^(N-c) J. Put k = N-c >= 1. Tensor step 10 with A_q/q^k. The modular law
    identifies its source with (J/J squared)/q^k. Apply the differential power-ideal lemma first to
    C and J with n = 1, then to C/J squared and its maximal ideal with n = N-1. This identifies the
    target with (A_q tensor Omega C/R)/q^k. Both maps send x to dx, so the localized conormal map
    modulo q^k is split for every k >= 1; tensoring preserves the given left inverse.
12. The source and target of the localized conormal map are finitely generated over the
    Noetherian local ring A_q. Its maximal ideal is its Jacobson radical. Apply
    lem-weil-pbc-split-injection-after-completion to the split maps modulo q^k from step 11.
    The conormal map itself splits, and step 5 finishes the reverse implication.
-/
theorem smooth_on_open_iff_artinian_lifting
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R]
    (φ₀ : R →+* A) (hfinite : φ₀.FiniteType) (q : Ideal A) [q.IsPrime] :
    (∃ W : (Spec (CommRingCat.of A)).Opens,
      (⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ W ∧
        Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom φ₀))) ↔
    (∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp φ₀ = φ.comp ρ → Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp φ₀ = ρ) := by
  constructor
  · exact smooth_on_open_artinian_lifting_forward φ₀ hfinite q
  · exact artinian_lifting_smooth_on_open_reverse φ₀ hfinite q

end AlgebraicGeometry
