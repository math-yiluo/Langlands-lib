/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import WeilConjectures.AlgebraicGeometry.Curve.PicProperNTorsionTorsion
import WeilConjectures.AlgebraicGeometry.Curve.PicProperNTorsionCoker
import WeilConjectures.AlgebraicGeometry.Curve.PicProperNTorsionDiv

/-!
# Torsion and divisibility of the Picard group of a proper curve

Source: Weil-conjectures blueprint, sec-curve-estimates/sk-thm-curveestimate,
corollary-torsion-jacobian-field-extension (blueprint: corollary-torsion-jacobian-field-extension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Weil-conjectures blueprint, sec-curve-estimates/sk-thm-curveestimate,
corollary-torsion-jacobian-field-extension (blueprint: corollary-torsion-jacobian-field-extension).
For a proper smooth connected curve over an algebraically closed field, with `n` prime to
its characteristic, the Picard group's `n`-torsion is `(ℤ/n)^(2g)`, its multiplication-by-`n`
cokernel is `ℤ/n`, and its degree-zero part is `n`-divisible. The group law of `Pic(C)` is
written multiplicatively (tensor product), so multiplication by `n` is `powMonoidHom n`,
`Pic(C)[n]` is its kernel, the cokernel is the quotient by its range, and `ℤ/n` and
`(ℤ/n)^(2g)` appear as `Multiplicative (ZMod n)` and `Multiplicative (Fin (2g) → ZMod n)`.

Proof, following the node's four steps:
1. By corollary-torsion-jacobian-field-extension the dimension is one, hence
corollary-torsion-jacobian-field-extension makes the curve projective. By
corollary-torsion-jacobian-field-extension its local rings are domains. Finite type over a field
gives Noetherianity by corollary-torsion-jacobian-field-extension. Distinct irreducible components
are disjoint and the finitely many components are open, so connectedness gives integrality. Thus
corollary-torsion-jacobian-field-extension and corollary-torsion-jacobian-field-extension apply. A
rational point exists by lemma-representability-picard-functor; prose-C-04 gives geometric
integrality. Now theorem-picard-scheme-jacobian-over-separably--3 identifies
corollary-degree-jacobian--1 with the rational points of the Jacobian, an abelian variety of
dimension `g`; theorem-riemann-roch-coherent-serre-duality--6 identifies its genus with prose-C-05.
2. By corollary-degree-jacobian--1 the degree sequence splits as `ℤ ⊕ Pic⁰(C)`.
Clause (d) of corollary-torsion-jacobian-field-extension makes the second factor `n`-divisible. The
hypothesis on `n` implies `n ≥ 1`; the case `n = 1` is immediate.
3. By definition-abelian-variety--3 the torsion of the Jacobian's rational points is the rational
points of its torsion scheme. Clause (c) of corollary-torsion-jacobian-field-extension identifies
this with `(ℤ/n)^(2g)`. Multiplication is componentwise in the decomposition and `ℤ[n] = 0` for
positive `n`, so this also identifies the Picard group's torsion.
4. The multiplication image in the decomposition is `nℤ ⊕ n Pic⁰(C)`. Divisibility makes
the second summand all of `Pic⁰(C)`, so the cokernel is `ℤ/n`, including `n = 1`. -/
theorem Scheme.Hom.pic_proper_ntorsion
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty ((powMonoidHom n : C.Pic →* C.Pic).ker ≃*
      Multiplicative (Fin (2 * f.genus) → ZMod n)) ∧
    Nonempty (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃* Multiplicative (ZMod n)) ∧
    (∀ L : C.Pic, L ∈ f.picZero → ∃ M : C.Pic, M ∈ f.picZero ∧ M ^ n = L) := by
  have ht := Scheme.Hom.pic_proper_ntorsion_torsion f n _hn
  have hc := Scheme.Hom.pic_proper_ntorsion_coker f n _hn
  have hd := Scheme.Hom.pic_proper_ntorsion_div f n _hn
  exact ⟨ht, hc, hd⟩

end AlgebraicGeometry
