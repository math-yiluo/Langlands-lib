/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# A global complete intersection has the expected dimension at every point

Source: literature/stacks-project/algebra.tex, Algebra, Section 00S8
(blueprint: lem-weil-pbc-global-complete-intersection-equidimensional).
-/

@[expose] public section


universe u

namespace AlgebraicGeometry

/-- A nonzero quotient of a polynomial ring over a field by `t` equations whose
spectrum has dimension `m - t` has that local dimension at every prime.

Source: literature/stacks-project/algebra.tex, Algebra, Section 00S8, the paragraph
following Definition 00S9 (lines 35834--35849), using Lemma 00OT.
(blueprint: lem-weil-pbc-global-complete-intersection-equidimensional)

The conjunct `t ≤ m` in `hDim` expresses the nonnegativity forced by the
integer equality `dim T = m - t` for a nonzero ring; it prevents natural
subtraction from admitting presentations with more equations than variables.

Proof (the five blueprint steps):
1. Put `J = Ideal.span (Set.range f)`, `T = Q / J`, and `X = Spec T`.
   The quotient is finite type over `k` (`def-weil-pbc-finite-type-algebra`),
   and `Q` is Noetherian (`lem-weil-pbc-finite-type-algebra-noetherian`).
   Nontriviality gives a maximal ideal, so `X` is nonempty and its dimension
   is nonnegative (`def-kun-topological-krull-dimension`).
2. The whole spectrum is an open neighbourhood of any prime `p`. The infimum
   defining `topologicalKrullDimAt` (`def-kun-topological-dimension-at-point`)
   therefore gives the upper bound `dim_p X ≤ dim X = m - t`.
3. Write an open neighbourhood `U` of `p` as the complement of `V(I)`
   (`lem-weil-pbc-spec-irreducible-closed-subsets-primes`), and choose
   `g ∈ I` outside `p`. The Jacobson property of the finite-type algebra
   (`lem-weil-pbc-finite-type-over-field-prime-intersection-maximal`)
   supplies a maximal ideal `M` containing `p` and avoiding `g`, hence in `U`.
4. Pull `M` back to a maximal ideal `M'` of `Q`. Its localization has dimension
   `m` (`lem-weil-pbc-polynomial-ring-maximal-localization-dimension`).
   Localization dimensions are heights
   (`lem-weil-pbc-localization-dimension-chains-below-prime`), and the
   Noetherian height bound for the `t` generators of `J`
   (`lem-weil-pbc-noetherian-height-quotient-bound`) gives
   `m ≤ dim T_M + t`, thus `dim T_M ≥ m - t`.
5. Since `M ∈ U`, `dim U ≥ dim_M X`. The dimension at a closed point equals
   that of its local ring (`lem-weil-pbc-closed-point-dimension-local-ring`),
   so step 4 gives `dim U ≥ m - t`. Taking the infimum over all `U` gives
   the lower bound at `p`; combine it with step 2.
-/
/- Lower bound on local dimensions for a nonzero polynomial quotient by equations.

Source: literature/stacks-project/algebra.tex, Algebra, Section 00S8, the paragraph
following Definition 00S9 (lines 35834--35849), via the Jacobson closed-point argument
and the height bound for the generators.
(blueprint: lem-weil-pbc-global-complete-intersection-equidimensional-lower-bound)
-/
theorem topologicalKrullDimAt_spec_quotient_mvPolynomial_lower_bound
    (k : Type u) [Field k] (m t : ℕ)
    (f : Fin t → MvPolynomial (Fin m) k)
    (hT : Nontrivial (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))
    (htm : t ≤ m) :
    ∀ p : PrimeSpectrum (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)),
      ((m - t : ℕ) : WithBot ℕ∞) ≤
        topologicalKrullDimAt
          (⟨p, inferInstance⟩ :
            Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) := by
  intro p
  classical
  let _ := hT
  let P := MvPolynomial (Fin m) k
  let J : Ideal P := Ideal.span (Set.range f)
  let T := P ⧸ J
  let q : Ideal P := p.asIdeal.comap (Ideal.Quotient.mk J)
  obtain ⟨d, d', hd, hd', hdd, hdm, hdim⟩ :=
    topologicalKrullDimAt_polynomial_quotient_eq_height_difference m J p.asIdeal
  have hsubset : Set.range f ⊆ q := by
    rintro _ ⟨i, rfl⟩
    change Ideal.Quotient.mk J (f i) ∈ p.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i))]
    exact p.asIdeal.zero_mem
  have hheight := Ideal.height_le_height_add_encard_of_subset (Set.range f) hsubset
  have hmap : q.map (Ideal.Quotient.mk J) = p.asIdeal :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  have hcard : (Set.range f).encard ≤ (t : ℕ∞) := by
    simpa only [Set.image_univ, Set.encard_univ, ENat.card_eq_coe_fintype_card,
      Fintype.card_fin] using Set.encard_image_le f Set.univ
  rw [hmap, hd, hd'] at hheight
  have hbound : (d' : ℕ∞) ≤ (d : ℕ∞) + t :=
    hheight.trans (add_le_add_right hcard _)
  have hnat : d' ≤ d + t := by exact_mod_cast hbound
  rw [hdim]
  apply WithBot.coe_le_coe.mpr
  have harith : m - t ≤ m - d' + d := by omega
  exact_mod_cast harith

/-- (blueprint: lem-weil-pbc-global-complete-intersection-equidimensional) -/
theorem topologicalKrullDimAt_spec_quotient_mvPolynomial_of_eq
    (k : Type u) [Field k] (m t : ℕ)
    (f : Fin t → MvPolynomial (Fin m) k)
    (hT : Nontrivial (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))
    (hDim : t ≤ m ∧
      topologicalKrullDim
          (Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) =
        ((m - t : ℕ) : WithBot ℕ∞)) :
    ∀ p : PrimeSpectrum (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)),
      topologicalKrullDimAt
          (⟨p, inferInstance⟩ :
            Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) =
        ((m - t : ℕ) : WithBot ℕ∞) := by
  intro p
  let X := Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))
  let x : X := ⟨p, inferInstance⟩
  apply le_antisymm
  · have hupper : topologicalKrullDimAt x ≤ topologicalKrullDim X := by
      unfold topologicalKrullDimAt
      have h : (⨅ U : TopologicalSpace.Opens X, ⨅ (_ : x ∈ U), topologicalKrullDim U) ≤
        topologicalKrullDim (⊤ : TopologicalSpace.Opens X) :=
      iInf₂_le (α := WithBot ℕ∞) ⊤ trivial
      have he := IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
        (Homeomorph.Set.univ X).isHomeomorph
      rw [← he]
      exact h
    change topologicalKrullDimAt x ≤ _
    exact hupper.trans_eq hDim.2
  · exact topologicalKrullDimAt_spec_quotient_mvPolynomial_lower_bound
      k m t f hT hDim.1 p

end AlgebraicGeometry
