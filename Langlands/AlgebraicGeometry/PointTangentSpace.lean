import Langlands.AlgebraicGeometry.RelativeDifferentials
import Langlands.AlgebraicGeometry.ModuleDual
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Cotangent and tangent modules at a section of a scheme over a base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.Scheme

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- The actual relative cotangent sheaf `e^* Ω_{X/S}` pulled back along a section
`e : S ⟶ X` of `X ⟶ S`, packaged as a slice morphism from the terminal object. -/
def cotangentAtSection (X : Over S) (e : Over.mk (𝟙 S) ⟶ X) : S.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pullback e.left).obj
    (Langlands.Scheme.relativeDifferentials X.hom)

/-- The tangent module at a section: the sheaf dual of the cotangent module at the section. -/
def tangentAtSection (X : Over S) (e : Over.mk (𝟙 S) ⟶ X) : S.Modules :=
  Langlands.Scheme.Modules.dual (cotangentAtSection X e)

/-- Over an affine base `Spec R`, the `R`-module of global sections of the tangent module at a
section. -/
def tangentSpaceAtPoint {R : CommRingCat.{u}}
    (X : Over (AlgebraicGeometry.Scheme.Spec.obj (op R)))
    (e : Over.mk (𝟙 _) ⟶ X) : ModuleCat.{u} R :=
  (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj (tangentAtSection X e)

end Langlands.Scheme
