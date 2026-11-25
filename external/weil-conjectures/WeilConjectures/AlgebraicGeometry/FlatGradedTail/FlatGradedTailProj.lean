/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.RelativeProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import WeilConjectures.RingTheory.GradedAlgebra.Standard
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Flat.Basic

/-! # Flatness and Hilbert polynomial from a locally free graded tail

Source: Stacks Project, Constructions, Tags 01M7, 01O3 and 07ZK;
Varieties, Tag 08AE; Coherent, Tag 0AG7
(blueprint: lem-sfb-flat-graded-tail-proj).

The quotient is presented by a surjective morphism from the existing polynomial
algebra sheaf. Its kernel is the homogeneous ideal of equations. In particular,
neither the degree-zero unit map nor any coordinate is required to be injective.
The relative Proj and its coefficient pullbacks use the canonical affine-basis API.
Chart-normalized isomorphisms identify the two existing projective-space models.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.FlatGradedTail

/-- The quotient map on polynomial sections, with the existing ordered coordinates.
Source: Stacks, Tag 07ZK (blueprint: lem-sfb-flat-graded-tail-proj). -/
def polynomialMap {U : Scheme.{u}} {n : ℕ} {B : RelativeProjAlgebra U}
    (q : (RelativeProjectiveSpace.algebra U n).affineData ⟶ B.affineData)
    (V : U.affineOpens) : MvPolynomial (Fin (n + 1)) Γ(U, V.1) →+* B.sections V :=
  (q.app V).toRingHom.comp (RelativeProjectiveSpace.affinePolynomialEquiv U n V).toRingHom

/-- The homogeneous equations on an affine base open are the kernel of the quotient.
This uses an ordinary ideal and imposes no saturation condition.
Source: Stacks, Tags 07ZK and 0AG7 (blueprint: lem-sfb-flat-graded-tail-proj). -/
def equations {U : Scheme.{u}} {n : ℕ} {B : RelativeProjAlgebra U}
    (q : (RelativeProjectiveSpace.algebra U n).affineData ⟶ B.affineData)
    (V : U.affineOpens) : Ideal (MvPolynomial (Fin (n + 1)) Γ(U, V.1)) :=
  RingHom.ker (polynomialMap q V)

end AlgebraicGeometry.FlatGradedTail
