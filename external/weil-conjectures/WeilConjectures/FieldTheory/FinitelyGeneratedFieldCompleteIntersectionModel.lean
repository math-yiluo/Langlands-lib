/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.FieldTheory.TriangularFieldModelPresentation
import WeilConjectures.FieldTheory.TriangularFieldModelWeakRegularity
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Complete-intersection models of finitely generated fields

Source: Stacks Project, Algebra, proof of Tag 07BV, and More on Algebra, proof of Tag 07E1
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v

namespace FieldTheory

/-- A finitely generated extension with a transcendence basis of size `d` is the fraction
field of a quotient of a polynomial ring in `n` variables by a regular sequence of length
`c`, with `n - c = d`. Source: Stacks Project, proof of Tag 07BV, as used in Tag 07E1
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof:
1. `exists_triangularFieldModel_presentation` carries out the tower-of-minimal-polynomials
   construction, clearing denominators and presenting the embedded subalgebra by the
   explicit equations `h T - 1` followed by triangular monic equations. It also proves
   that every element of `K` is a fraction of elements of this quotient.
2. `triangularFieldModelEquations_isWeaklyRegular` proves successive injectivity of
   multiplication by these equations. The quotient admits a unital map to the nonzero
   field `K`, so its defining ideal is proper. Thus the sequence is regular.
3. The explicit list has length `r + 1`; set `n = d + 1 + r` and `c = r + 1`.
4. Pull back the domain structure along the injective map. Mathlib's fraction-ring lift
   is an injective algebra homomorphism. The fraction representations prove it surjective,
   and its formula on localization constructors gives the stated algebra equivalence. -/
theorem exists_completeIntersection_fractionField_model
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (hfg : ∃ (m : ℕ) (b : Fin m → K), IntermediateField.adjoin k (Set.range b) = ⊤)
    (d : ℕ) (x : Fin d → K) (hx : IsTranscendenceBasis k x) :
    ∃ (n c : ℕ) (f : List (MvPolynomial (Fin n) k)),
      c ≤ n ∧ n - c = d ∧ f.length = c ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) f ∧
      let A := MvPolynomial (Fin n) k ⧸ Ideal.ofList f
      ∃ (ι : A →ₐ[k] K),
        Function.Injective ι ∧
        (∀ z : K, ∃ a s : A, s ≠ 0 ∧ z = ι a * (ι s)⁻¹) ∧
        IsDomain A ∧
        ∃ e : FractionRing A ≃ₐ[k] K,
          ∀ (a : A) (s : nonZeroDivisors A),
            e (LocalizedModule.mk a s) = ι a * (ι s)⁻¹ := by
  obtain ⟨r, h, p, hh, hp, ι, hι, hfrac⟩ :=
    exists_triangularFieldModel_presentation k K hfg d x hx
  let f := triangularFieldModelEquations k d r h p
  let R := MvPolynomial (Fin (d + 1 + r)) k
  let A := R ⧸ Ideal.ofList f
  have hweak : RingTheory.Sequence.IsWeaklyRegular R f :=
    triangularFieldModelEquations_isWeaklyRegular k d r h p hh hp
  have hreg : RingTheory.Sequence.IsRegular R f :=
    { toIsWeaklyRegular := hweak
      top_ne_smul := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
        intro htop
        have hmem : (1 : R) ∈ Ideal.ofList f := by
          rw [← htop]
          exact Submodule.mem_top
        have h10 : (1 : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
        exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrArg ι h10) }
  have hdomain : IsDomain A := Function.Injective.isDomain ι hι
  let g : FractionRing A →ₐ[k] K := IsFractionRing.liftAlgHom hι
  have hmk (a : A) (s : nonZeroDivisors A) :
      g (LocalizedModule.mk a s) = ι a * (ι s)⁻¹ := by
    change IsFractionRing.lift hι (Localization.mk a s) = _
    rw [Localization.mk_eq_mk'_apply, IsFractionRing.lift_mk', div_eq_mul_inv]
    rfl
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨a, s, hs, hz⟩ := hfrac z
    let s' : nonZeroDivisors A := ⟨s, mem_nonZeroDivisors_iff_ne_zero.mpr hs⟩
    exact ⟨LocalizedModule.mk a s', (hmk a s').trans hz.symm⟩
  refine ⟨d + 1 + r, r + 1, f, by omega, by omega, ?_, hreg,
    ι, hι, hfrac, hdomain, AlgEquiv.ofBijective g ⟨g.injective, hsurj⟩, ?_⟩
  · exact triangularFieldModelEquations_length k d r h p
  · exact hmk

end FieldTheory
