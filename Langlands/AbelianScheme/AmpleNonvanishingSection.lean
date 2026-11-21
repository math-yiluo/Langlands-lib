import Langlands.AlgebraicGeometry.Picard.SmoothProperLineBundleEulerPolynomialProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldEulerInverseSymmetryProof
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse
import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof
import Langlands.AlgebraicGeometry.Picard.TranslationInvariantH0VanishingProof
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingProof
import Langlands.AbelianScheme.SeparatingLineBundle.RationalPoints
import Langlands.AbelianScheme.Tate.TwoPowerTorsionDensityReduction

/-! # An ample line bundle on an abelian variety has a section that is nonzero at a
rational point

Over an algebraically closed field, the Euler characteristic of an ample line bundle `L`
on an abelian variety is nonzero: otherwise `χ(L^k)^2 = k^(2g) χ(L)^2` would make the Euler
polynomial of `L` vanish at every positive integer, although its leading coefficient is
positive. Since the higher cohomology of `L` vanishes, `χ(L) = dim H⁰(L)`, so `L` has a
nonzero global section, and a nonzero section of a line bundle on a reduced irreducible
scheme of finite type over `K` is nonzero at some rational point. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.SchemeModule Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard
  Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- Every line bundle on an abelian scheme over a field has finite cohomology. -/
theorem lineBundle_hasFiniteCohomology (L : LineBundle A.X.left) :
    HasFiniteCohomology A.X.hom L.obj :=
  hasFiniteCohomology_of_iso A.X.hom (tensorPowOneIso L.obj)
    (lineBundleTensorPow_hasFiniteCohomology A.X.hom L 1)

/-- The tensor power `L^k` as a line bundle. -/
abbrev powLB (L : LineBundle A.X.left) (k : ℕ) : LineBundle A.X.left :=
  ⟨tensorPow L.obj k, tensorPow_isLocallyFreeRankOne _ L k⟩

variable [IsAlgClosed K]

/-- `χ(L^k)^2 = k^(2g) χ(L)^2` for an ample line bundle `L` on an abelian variety of
dimension `g` over an algebraically closed field and `k ≥ 1`. -/
theorem eulerCharacteristic_tensorPow_sq (g : ℕ) (hg : A.HasRelativeDimension g)
    (L : LineBundle A.X.left) (hL : L.IsAmple) (k : ℕ) (hk : 1 ≤ k)
    (h : HasFiniteCohomology A.X.hom L.obj)
    (hpow : HasFiniteCohomology A.X.hom (tensorPow L.obj k)) :
    eulerCharacteristic A.X.hom (tensorPow L.obj k) hpow ^ 2 =
      (k : ℤ) ^ (2 * g) * eulerCharacteristic A.X.hom L.obj h ^ 2 := by
  let N := L.inverse
  let Nk := (powLB A L k).inverse
  have hN := lineBundle_hasFiniteCohomology A N
  have hNk := lineBundle_hasFiniteCohomology A Nk
  have e1 := algClosedFieldAmpleEulerInverseScaling K A g hg L N hL
    ⟨L.tensorInverseIso⟩ k hk Nk ⟨(powLB A L k).tensorInverseIso⟩ h hN hpow hNk
  have e2 := algClosedFieldEulerInverseSymmetry K A g hg L N ⟨L.tensorInverseIso⟩ h hN
  have e3 := algClosedFieldEulerInverseSymmetry K A g hg (powLB A L k) Nk
    ⟨(powLB A L k).tensorInverseIso⟩ hpow hNk
  rw [e2, e3] at e1
  have hsgn : ((-1 : ℤ) ^ g) ≠ 0 := pow_ne_zero _ (by norm_num)
  have : (-1 : ℤ) ^ g * eulerCharacteristic A.X.hom (tensorPow L.obj k) hpow ^ 2 =
      (-1 : ℤ) ^ g * ((k : ℤ) ^ (2 * g) * eulerCharacteristic A.X.hom L.obj h ^ 2) := by
    linear_combination e1
  exact mul_left_cancel₀ hsgn this

/-- The Euler characteristic of an ample line bundle on an abelian variety over an
algebraically closed field is nonzero. -/
theorem eulerCharacteristic_ne_zero_of_isAmple (L : LineBundle A.X.left) (hL : L.IsAmple)
    (h : HasFiniteCohomology A.X.hom L.obj) :
    eulerCharacteristic A.X.hom L.obj h ≠ 0 := by
  intro h0
  obtain ⟨g, hg⟩ := Tate.exists_hasRelativeDimension A
  obtain ⟨hpow, P, hP, -, hamp⟩ := smoothProperLineBundleEulerPolynomial K A.X g hg
    inferInstance inferInstance L
  obtain ⟨-, hlc⟩ := hamp hL
  have hroot : ∀ k : ℕ, P.IsRoot ((k + 1 : ℕ) : ℚ) := by
    intro k
    have hsq := eulerCharacteristic_tensorPow_sq A g hg L hL (k + 1) (by omega) h (hpow (k + 1))
    rw [h0] at hsq
    have hz : eulerCharacteristic A.X.hom (tensorPow L.obj (k + 1)) (hpow (k + 1)) = 0 := by
      simpa using hsq
    rw [Polynomial.IsRoot, hP (k + 1), hz, Int.cast_zero]
  have hP0 : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ ↦ ((k + 1 : ℕ) : ℚ))
      (fun a b hab ↦ by simpa using hab) hroot
  rw [hP0, Polynomial.leadingCoeff_zero] at hlc
  exact lt_irrefl 0 hlc

/-- An ample line bundle on an abelian variety over an algebraically closed field has a
nonzero global section. -/
theorem exists_globalSection_ne_zero_of_isAmple (L : LineBundle A.X.left) (hL : L.IsAmple) :
    ∃ s : GlobalSections L.obj, s ≠ 0 := by
  have h := lineBundle_hasFiniteCohomology A L
  have hχ := (eulerCharacteristicBasic K A.X.left A.X.hom).2.2.2.2 L.obj h
    (ampleLineBundleHigherCohomologyVanishing K A L hL)
  have hne := eulerCharacteristic_ne_zero_of_isAmple A L hL h
  rw [hχ] at hne
  have hpos : 0 < Module.finrank K ((relativeCohomology A.X.hom 0).obj L.obj) := by
    exact Nat.pos_of_ne_zero (by exact_mod_cast hne)
  have : Nontrivial ((relativeCohomology A.X.hom 0).obj L.obj) :=
    Module.nontrivial_of_finrank_pos hpos
  have : Nontrivial ((relativeGlobalSections A.X.hom).obj L.obj) :=
    ((relativeCohomologyZeroIso A.X.hom).app L.obj).toLinearEquiv.symm.surjective.nontrivial
  obtain ⟨s, hs⟩ := exists_ne (0 : (relativeGlobalSections A.X.hom).obj L.obj)
  exact ⟨s, hs⟩

/-- An ample line bundle on an abelian variety over an algebraically closed field has a
global section that does not vanish at some rational point. -/
theorem exists_section_not_vanishesAlong_of_isAmple (L : LineBundle A.X.left)
    (hL : L.IsAmple) :
    ∃ (s : GlobalSections L.obj) (x : Spec (CommRingCat.of K) ⟶ A.X.left),
      IsRationalPoint A.X.hom x ∧ ¬ VanishesAlong L x s := by
  obtain ⟨s, hs⟩ := exists_globalSection_ne_zero_of_isAmple A L hL
  have : IsReduced A.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K _ A.X.hom
  have : IrreducibleSpace A.X.left :=
    Langlands.GroupScheme.SeparatingLineBundle.irreducibleSpace_of_smooth_of_isProper A.toGrp
  have hU : (trivializationOpen L.obj s : Set A.X.left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hU
    apply hs
    apply LineBundle.eq_zero_of_trivializationOpen_eq_bot L s
    exact TopologicalSpace.Opens.ext hU
  obtain ⟨x, hx, hmem⟩ := Langlands.GroupScheme.SeparatingLineBundle.exists_rationalPoint_mem_of_isOpen
    A.X.hom (fun _ : Unit ↦ (trivializationOpen L.obj s : Set A.X.left))
    (fun _ ↦ (trivializationOpen L.obj s).isOpen) (fun _ ↦ hU)
  refine ⟨s, x, hx, ?_⟩
  rw [vanishesAlong_field_iff L x s (IsLocalRing.closedPoint K), not_not]
  exact hmem ()

end Langlands.AbelianScheme
