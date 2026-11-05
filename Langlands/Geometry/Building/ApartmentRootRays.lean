import Langlands.Geometry.Building.KPApartmentAxioms
import Langlands.GroupScheme.Rational.RootRayDecomposition
import Mathlib.Algebra.Module.Rat

/-! # Actual root rays from the apartment axioms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.RelativeRoot
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.Geometry.Building.KPApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  (A : KPApartmentData i (localFieldOrder F)) (Z : CentralizerDatum i)

/-- An affine coroot lifts to a real torus vector with integral pairings
against every actual relative root. -/
theorem exists_integralRootCoroot
    (hA : A.SatisfiesApartmentAxioms Z) (a : relativeRoots i) :
    ∃ v : V S, eval S a.val v = 2 ∧
      ∀ b : relativeRoots i, ∃ n : ℤ, eval S b.val v = n := by
  have hroot (b : relativeRoots i) :
      rootForm i b ∈ AffineRootSystem.derivativeRoots A.affineRoots := by
    rw [hA.derivativeRoots_affineRoots]
    exact Set.mem_range_self b
  obtain ⟨ψ, hψ, hψlin⟩ := hroot a
  obtain ⟨q, hq⟩ := hA.isAffineRootSystem_affineRoots.exists_isCoroot ψ hψ
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (rootAnnihilator i) q
  refine ⟨v, ?_, fun b => ?_⟩
  · simpa only [hψlin, rootForm_mk] using hq.1
  · obtain ⟨ψb, hψb, hψblin⟩ := hroot b
    obtain ⟨n, hn⟩ := hA.isAffineRootSystem_affineRoots.coroot_integral ψb hψb ψ hψ _ hq
    exact ⟨n, by simpa only [hψblin, rootForm_mk] using hn⟩

/-- A chosen real coroot vector, lifted from the actual affine root system.
The vector need not be the image of an integral cocharacter. -/
def integralRootCoroot
    (hA : A.SatisfiesApartmentAxioms Z) (a : relativeRoots i) : V S :=
  (A.exists_integralRootCoroot Z hA a).choose

theorem integralRootCoroot_self
    (hA : A.SatisfiesApartmentAxioms Z) (a : relativeRoots i) :
    eval S a.val (A.integralRootCoroot Z hA a) = 2 :=
  (A.exists_integralRootCoroot Z hA a).choose_spec.1

theorem integralRootCoroot_integral
    (hA : A.SatisfiesApartmentAxioms Z) (a b : relativeRoots i) :
    ∃ n : ℤ, eval S b.val (A.integralRootCoroot Z hA a) = n :=
  (A.exists_integralRootCoroot Z hA a).choose_spec.2 b

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem eq_of_character_nsmul_eq
    (hS : IsSplitTorus S.toGrp) {r : ℕ} (hr : 0 < r)
    {a b : characterLattice S} (h : r • a = r • b) : a = b := by
  let := IsAddTorsionFree.of_module_rat (ℚ ⊗[ℤ] characterLattice S)
  apply hS.character_toRat_injective
  apply nsmul_right_injective (Nat.ne_of_gt hr)
  simpa only [← map_nsmul] using congrArg toRat h

/-- The apartment axioms classify common positive multiples of actual roots
without a global relative-root-system or rank-one factorization premise. -/
theorem root_eq_or_twice_of_common_positive_multiple
    (hA : A.SatisfiesApartmentAxioms Z) (hS : IsSplitTorus S.toGrp)
    {a b : characterLattice S} (ha : a ∈ relativeRoots i)
    (hb : b ∈ relativeRoots i) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m • a = n • b) :
    a = b ∨ a = 2 • b ∨ b = 2 • a := by
  let va := A.integralRootCoroot Z hA ⟨a, ha⟩
  let vb := A.integralRootCoroot Z hA ⟨b, hb⟩
  have hselfa : eval S a va = 2 := A.integralRootCoroot_self Z hA ⟨a, ha⟩
  have hselfb : eval S b vb = 2 := A.integralRootCoroot_self Z hA ⟨b, hb⟩
  obtain ⟨p, hp⟩ : ∃ p : ℤ, eval S b va = p :=
    A.integralRootCoroot_integral Z hA ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨q, hq⟩ : ∃ q : ℤ, eval S a vb = q :=
    A.integralRootCoroot_integral Z hA ⟨b, hb⟩ ⟨a, ha⟩
  have hca : 2 * (m : ℤ) = (n : ℤ) * p := by
    have he := congrArg (fun χ => eval S χ va) h
    simp only [eval_nsmul_char, hselfa, hp] at he
    exact_mod_cast (by nlinarith : (2 : ℝ) * (m : ℝ) = (n : ℝ) * (p : ℝ))
  have hcb : (m : ℤ) * q = 2 * (n : ℤ) := by
    have he := congrArg (fun χ => eval S χ vb) h
    simp only [eval_nsmul_char, hselfb, hq] at he
    exact_mod_cast (by nlinarith : (m : ℝ) * (q : ℝ) = (2 : ℝ) * (n : ℝ))
  have hmz : 0 < (m : ℤ) := by exact_mod_cast hm
  have hnz : 0 < (n : ℤ) := by exact_mod_cast hn
  have hprod : p * q = 4 := by
    apply mul_left_cancel₀ (ne_of_gt hnz)
    calc
      (n : ℤ) * (p * q) = ((n : ℤ) * p) * q := by ring
      _ = (2 * (m : ℤ)) * q := by rw [← hca]
      _ = 2 * ((m : ℤ) * q) := by ring
      _ = (n : ℤ) * 4 := by rw [hcb]; ring
  have hpos : 0 < p := by nlinarith
  have hpos' : 0 < q := by nlinarith
  have hle : p ≤ 4 := by nlinarith
  interval_cases hp' : p
  · have hn' : n = m * 2 := by omega
    right
    left
    apply eq_of_character_nsmul_eq hS hm
    calc
      m • a = n • b := h
      _ = (m * 2) • b := by rw [hn']
      _ = m • (2 • b) := by rw [smul_smul]
  · have hmn : m = n := by omega
    left
    subst n
    exact eq_of_character_nsmul_eq hS hm h
  · omega
  · have hm' : m = n * 2 := by omega
    right
    right
    apply eq_of_character_nsmul_eq hS hn
    calc
      n • b = m • a := h.symm
      _ = (n * 2) • a := by rw [hm']
      _ = n • (2 • a) := by rw [smul_smul]

/-- The positive integral rays of distinct actual indivisible roots are
disjoint under the unchanged apartment axioms. -/
theorem disjoint_cyclicTail_indivisibleRoots
    (hA : A.SatisfiesApartmentAxioms Z) (hS : IsSplitTorus S.toGrp)
    {a b : characterLattice S} (ha : a ∈ indivisibleRoots i)
    (hb : b ∈ indivisibleRoots i) (hne : a ≠ b) :
    Disjoint (cyclicTail a 1 : Set (characterLattice S))
      (cyclicTail b 1 : Set (characterLattice S)) := by
  apply Set.disjoint_left.mpr
  rintro χ ⟨m, _, hm, hma⟩ ⟨n, _, hn, hnb⟩
  rcases A.root_eq_or_twice_of_common_positive_multiple Z hA hS
      ha.1 hb.1 hm hn (hma.trans hnb.symm) with heq | heq | heq
  · exact hne heq
  · exact ha.2 b hb.1 2 (by omega) heq.symm
  · exact hb.2 a ha.1 2 (by omega) heq.symm

end Langlands.Geometry.Building.KPApartmentData
