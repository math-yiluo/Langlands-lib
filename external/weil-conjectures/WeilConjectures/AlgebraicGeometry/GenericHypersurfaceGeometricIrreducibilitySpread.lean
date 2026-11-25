/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.RingTheory.MvPolynomial.Basic
import WeilConjectures.AlgebraicGeometry.HypersurfaceGeometricFibrePrimeCriterion
import WeilConjectures.RingTheory.AbsoluteIrreducibilitySpecialization

/-! # Spreading geometric integrality for a hypersurface

Source: Stacks Project, Tag 0557, lemma-irreducible-polynomial.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

private theorem evaluation_generic_injective
    {S : Scheme.{u}} [IsIntegral S] (η : S)
    (hη : IsGenericPoint η Set.univ) : Function.Injective (S.Γevaluation η).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hnot : η ∉ S.basicOpen a :=
    (S.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) η trivial a).mp ha
  have hempty : ¬ (S.basicOpen a : Set S).Nonempty := by
    intro hn
    apply hnot
    apply (hη.mem_open_set_iff (S.basicOpen a).isOpen).mpr
    simpa only [Set.univ_inter] using hn
  exact (basicOpen_eq_bot_iff a).mp
    ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp hempty)

/-- A hypersurface with geometrically integral generic fibre has geometrically
irreducible fibres on a neighbourhood of the generic point.

Source: Stacks Project, Tag 0557, lemma-irreducible-polynomial.
Proof: put A = Gamma(S, top), a domain, and K = Frac(A). Identify the generic
fibre ring with K[t_1,...,t_n]/(P_K). If P_K is zero, all coefficients of P vanish
by injectivity of A into K, so P is zero; all fibres are affine spaces and the
whole base works. Otherwise geometric reducedness and irreducibility say that
over an algebraic closure of K the principal ideal (P_K) is prime. Thus P_K is
absolutely irreducible up to a nonzero scalar. A nonzero constant is excluded by
the nonemptiness of the generic fibre. A triangular substitution by sufficiently
separated powers of the last variable makes the leading coefficient a nonzero
element of A. Invert it and divide by it to make the polynomial monic in the
last variable of positive degree d. This coordinate change commutes with every
field specialization. Bound factor degrees in each of the remaining variables
by the corresponding degree of P. For each positive pair e_1 + e_2 = d, form
the finite type coefficient algebra of two monic factors with these bounds,
quotienting by all coefficient equations of P = Q_1 Q_2. Absolute irreducibility
excludes points over the algebraic closure of K. Nullstellensatz says the generic
coefficient algebra is zero. Consequently 1 is killed by some nonzero base
element, and localizing at this element kills the whole coefficient algebra.
Invert the finite product of these elements and the leading coefficient. No
specialization into any algebraically closed residue field can then factor P.
The monic polynomial retains positive degree, so each hypersurface is nonempty
and integral over that field. For an arbitrary field extension of a residue
field, pass to its algebraic closure and descend irreducibility and nonemptiness
along the surjective field-extension base change. This gives exactly geometric
irreducibility of the fibre morphism. The resulting principal base open contains
eta. If d = 1 the product of factor obstructions is empty and equals 1. If n = 0,
the generic hypotheses force P = 0, handled in the first case.

(blueprint: lem-sbc-generic-hypersurface-geometric-irreducibility-spread) -/
theorem exists_open_generic_hypersurface_geometric_irreducibility
    {S : Scheme.{u}} [IsAffine S] [IsIntegral S]
    (n : ℕ) (P : MvPolynomial (Fin n) Γ(S, ⊤))
    (η : S) (hη : IsGenericPoint η Set.univ) :
    let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
    let g : H ⟶ S := Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
    GeometricallyIrreducible (g.fiberToSpecResidueField η) →
      GeometricallyReduced (g.fiberToSpecResidueField η) →
      ∃ U : S.Opens, η ∈ U ∧
        ∀ s, s ∈ U → GeometricallyIrreducible (g.fiberToSpecResidueField s) := by
  dsimp only
  intro hgeom hred
  have hgeneric := (hypersurface_geometric_fibre_prime_criterion n P η).mp ⟨hgeom, hred⟩
  by_cases hP : P = 0
  · refine ⟨⊤, trivial, ?_⟩
    intro s _
    apply ((hypersurface_geometric_fibre_prime_criterion n P s).mpr ?_).1
    intro K _ φ
    simpa only [hP, map_zero, Ideal.span_singleton_zero] using
      (Ideal.isPrime_bot : (⊥ : Ideal (MvPolynomial (Fin n) K)).IsPrime)
  · let ι := (S.Γevaluation η).hom
    have hι : Function.Injective ι := evaluation_generic_injective η hη
    let j := (algebraMap (S.residueField η) (AlgebraicClosure (S.residueField η))).comp ι
    have hj : Function.Injective j :=
      (RingHom.injective (algebraMap (S.residueField η) _)).comp hι
    have hmap : MvPolynomial.map j P ≠ 0 := by
      intro hz
      apply hP
      exact MvPolynomial.map_injective j hj (hz.trans (map_zero _).symm)
    have hirred : Irreducible (MvPolynomial.map j P) :=
      ((Ideal.span_singleton_prime hmap).mp
        (hgeneric (AlgebraicClosure (S.residueField η)) (algebraMap _ _))).irreducible
    obtain ⟨a, ha, hspecial⟩ :=
      MvPolynomial.exists_nonzero_irreducible_specializations n P ι hι hirred
    refine ⟨S.basicOpen a, ?_, ?_⟩
    · apply (hη.mem_open_set_iff (S.basicOpen a).isOpen).mpr
      rw [Set.univ_inter]
      by_contra hn
      exact ha ((basicOpen_eq_bot_iff a).mp
        ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp hn))
    · intro s hs
      apply ((hypersurface_geometric_fibre_prime_criterion n P s).mpr ?_).1
      intro K _ φ
      apply Ideal.isPrime_span_singleton_of_prime
      apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
      apply hspecial K (φ.comp (S.Γevaluation s).hom)
      exact (map_ne_zero_iff φ φ.injective).mpr
        ((S.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) s trivial a).mpr hs)

end AlgebraicGeometry
