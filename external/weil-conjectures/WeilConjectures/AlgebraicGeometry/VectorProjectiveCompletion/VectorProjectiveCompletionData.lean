/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.RelativeProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebra
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Data for the projective completion of a vector bundle

Source: Stacks Project, Constructions, Tag 01OA (projective bundles), Tags 01OB,
01OE and 01NG; blueprint `sec-smooth-purity/sk-prop-an`, the first sentence of
`thm-amb-vector-bundle-purity.proof.md` (blueprint: def-amb-vector-projective-presentation-data).

The affine presentation below specifies the actual symmetric algebra of O plus F,
its symmetric grading and its restriction maps. No projective scheme or compactification
is selected from an uncharacterized existence assertion. All witnesses, including the
chart equivalences, are characterized in the theorem by their coefficients and generators.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Pointwise

noncomputable section

namespace AlgebraicGeometry.VectorProjectiveCompletion

/-- Affine-basis presentation of Sym(O_S ⊕ F), with its symmetric grading and its
actual restriction maps. A finite direct sum has section module R × F(V).
Source: Stacks Tag 01OA (blueprint: def-amb-vector-projective-presentation-data). -/
structure Presentation (S : Scheme.{u}) (F : S.Modules) where
  algebra : S.GradedAlgebraData
  equiv (V : S.affineOpens) :
    SymmetricAlgebra Γ(S, V.1) (Γ(S, V.1) × F.val.obj (op V.1)) ≃ₐ[Γ(S, V.1)] algebra.obj V
  grade_eq (V : S.affineOpens) (n : ℕ) :
    algebra.grading V n =
      ((LinearMap.range (SymmetricAlgebra.ι Γ(S, V.1)
        (Γ(S, V.1) × F.val.obj (op V.1)))) ^ n).map (equiv V).toLinearMap
  restriction (U V : S.affineOpens) (h : U.1 ≤ V.1)
      (a : Γ(S, V.1)) (m : F.val.obj (op V.1)) :
    algebra.res h (equiv V (SymmetricAlgebra.ι _ _ (a, m))) =
      equiv U (SymmetricAlgebra.ι _ _
        (S.presheaf.map (homOfLE h).op a, F.val.map (homOfLE h).op m))

/-- The degree-one coordinate from the first summand, namely t = j(1,0).
Source: Stacks Tag 01OA (blueprint: def-amb-vector-projective-presentation-data). -/
def t {S : Scheme.{u}} {F : S.Modules} (P : Presentation S F) (V : S.affineOpens) :
    P.algebra.obj V :=
  P.equiv V (SymmetricAlgebra.ι _ _ (1, 0))

/-- The degree-one coordinate from a section of F, namely x(m) = j(0,m).
Source: Stacks Tag 01OA (blueprint: def-amb-vector-projective-presentation-data). -/
def x {S : Scheme.{u}} {F : S.Modules} (P : Presentation S F) (V : S.affineOpens)
    (m : F.val.obj (op V.1)) : P.algebra.obj V :=
  P.equiv V (SymmetricAlgebra.ι _ _ (0, m))

end AlgebraicGeometry.VectorProjectiveCompletion
