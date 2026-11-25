/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineIdealGeneratorCover
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Compatible numerators on a finite principal-open cover

Source: Stacks Project, Properties, Lemma 01PM, denominator-clearing paragraphs.
(blueprint: lem-weil-pbc-affine-compatible-denominator-data).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Choose finite ideal generators and compatible numerators for one affine chart.

Source: Stacks Project, Properties, Lemma 01PM, proof from the choice of generators
through replacement of the numerators by further powers of the generators.
(blueprint: lem-weil-pbc-affine-compatible-denominator-data).

Proof: On V identify I with the finitely generated ideal J given by the image of
its sections. Choose generators g_i. The locus where the inclusion is surjective
on stalks is D(J), so their principal opens cover U intersect V. Quasi-coherence
identifies sections of F on D(g_i) with the localization of M=F(V). Choose a
positive common denominator exponent k and numerators x_i. On each overlap,
equality of the localized fractions implies that some power of g_i*g_j kills
(g_j^k*x_i-g_i^k*x_j). There are finitely many pairs, so choose a common e.
Replace x_i by g_i^e*x_i and k by k+e. This preserves the fractions and makes
every cross relation an equality in M. Restricting the fraction identity proves
the asserted identity on every smaller open. If J=0, use no generators and
k=1; the cover is empty. A unit ideal and an empty affine open need no special
argument: localization and the finite maximum construction still apply. -/
theorem affine_compatible_denominator_data
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (V : X.affineOpens) (s : Γ(F, U)) :
    ∃ (t k : ℕ) (g : Fin t → Γ(X, V.1)) (x : Fin t → Γ(F, V.1)),
      0 < k ∧
      (LinearMap.range (ι.val.app (op V.1)).hom : Ideal Γ(X, V.1)) =
        Ideal.span (Set.range g) ∧
      U ⊓ V.1 = ⨆ i, X.basicOpen (g i) ∧
      (∀ i j, g j ^ k • x i = g i ^ k • x j) ∧
      ∀ (i : Fin t) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V.1),
        W ≤ X.basicOpen (g i) →
        X.presheaf.map (homOfLE hWV).op (g i ^ k) •
          F.presheaf.map (homOfLE hWU).op s =
            F.presheaf.map (homOfLE hWV).op (x i) := by
  classical
  obtain ⟨t, g, hg, hcover⟩ := affine_ideal_generator_cover ι U hU V
  have hDU (i : Fin t) : X.basicOpen (g i) ≤ U :=
    (le_iSup (fun j ↦ X.basicOpen (g j)) i).trans (hcover.ge.trans inf_le_left)
  choose e m hm using fun i : Fin t ↦
    Modules.exists_map_eq_pow_smul_of_isAffineOpen F V.2 (g i)
      (F.presheaf.map (homOfLE (hDU i)).op s)
  let l := Finset.univ.sup e + 1
  have hel (i : Fin t) : e i ≤ l :=
    (Finset.le_sup (f := e) (Finset.mem_univ i)).trans (Nat.le_add_right _ _)
  let y (i : Fin t) := g i ^ (l - e i) • m i
  have hfrac (i : Fin t) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V.1)
      (hWD : W ≤ X.basicOpen (g i)) :
      X.presheaf.map (homOfLE hWV).op (g i ^ l) •
        F.presheaf.map (homOfLE hWU).op s = F.presheaf.map (homOfLE hWV).op (y i) := by
    have hy : F.presheaf.map (homOfLE (X.basicOpen_le (g i))).op (y i) =
        X.presheaf.map (homOfLE (X.basicOpen_le (g i))).op (g i) ^ l •
          F.presheaf.map (homOfLE (hDU i)).op s := by
      dsimp only [y]
      rw [F.map_smul, map_pow, hm i, smul_smul, ← pow_add, Nat.sub_add_cancel (hel i)]
    have hh := congrArg (F.presheaf.map (homOfLE hWD).op) hy
    conv_rhs at hh => rw [F.map_smul, ← map_pow]
    convert hh.symm using 1 <;>
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] <;> rfl
  have hzero (i j : Fin t) :
      F.presheaf.map (homOfLE (X.basicOpen_le (g i * g j))).op
        (g j ^ l • y i - g i ^ l • y j) = 0 := by
    let W := X.basicOpen (g i * g j)
    have hWi : W ≤ X.basicOpen (g i) := by
      dsimp only [W]
      rw [X.basicOpen_mul]
      exact inf_le_left
    have hWj : W ≤ X.basicOpen (g j) := by
      dsimp only [W]
      rw [X.basicOpen_mul]
      exact inf_le_right
    have hi := hfrac i W (hWi.trans (hDU i)) (X.basicOpen_le (g i * g j)) hWi
    have hj := hfrac j W (hWi.trans (hDU i)) (X.basicOpen_le (g i * g j)) hWj
    rw [map_sub,
      F.map_smul (homOfLE (X.basicOpen_le (g i * g j))) (g j ^ l) (y i),
      F.map_smul (homOfLE (X.basicOpen_le (g i * g j))) (g i ^ l) (y j),
      ← hi, ← hj, smul_comm, sub_self]
  choose a ha using fun ij : Fin t × Fin t ↦
    Modules.exists_pow_smul_eq_zero_of_isAffineOpen F V.2 (g ij.1 * g ij.2)
      (g ij.2 ^ l • y ij.1 - g ij.1 ^ l • y ij.2) (hzero ij.1 ij.2)
  let d := Finset.univ.sup a
  have had (ij : Fin t × Fin t) : a ij ≤ d := Finset.le_sup (Finset.mem_univ ij)
  have hkill (i j : Fin t) :
      (g i * g j) ^ d • (g j ^ l • y i - g i ^ l • y j) = 0 := by
    rw [← Nat.sub_add_cancel (had (i, j)), pow_add, mul_smul, ha (i, j), smul_zero]
  let x (i : Fin t) := g i ^ d • y i
  refine ⟨t, l + d, g, x, by dsimp [l]; omega, hg, hcover, ?_, ?_⟩
  · intro i j
    have hh := hkill i j
    rw [smul_sub, sub_eq_zero] at hh
    dsimp only [x]
    simpa only [mul_pow, pow_add, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hh
  · intro i W hWU hWV hWD
    dsimp only [x]
    rw [F.map_smul (homOfLE hWV) (g i ^ d) (y i),
      ← hfrac i W hWU hWV hWD, ← mul_smul, ← map_mul, ← pow_add, Nat.add_comm d l]

end AlgebraicGeometry.Scheme
