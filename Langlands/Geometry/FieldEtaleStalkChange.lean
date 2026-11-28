import Langlands.MathlibBase
import WeilConjectures.AlgebraicGeometry.EtaleSheafDiscreteContinuousRep

/-!
# Stalks of étale sheaves on the spectrum of a field at two geometric points

Let `K` be a field, `Ω` a separable closure of `K`, `M` a separably closed field with a
`K`-algebra structure and `ι : Ω →ₐ[K] M`. Every `K`-morphism `Spec M → X` to an étale `K`-scheme
factors uniquely through `Spec ι : Spec M → Spec Ω`, since the residue fields of `X` are separable
over `K` (weil-conjectures's `AlgebraicGeometry.Scheme.pointSmallEtaleFiberIso`, applied with the
`Ω`-algebra structure of `M` given by `ι`). So the points `Spec Ω → Spec K` and `Spec M → Spec K`
of the small étale site of `Spec K` are isomorphic (`pointIso`), and their stalk functors on
sheaves with values in any category `A` with colimits are isomorphic (`sheafFiberIso`), the germ
of a section at a lift `x` going to its germ at `Spec ι ≫ x`
(`toPresheafFiber_sheafFiberIso_hom_app`, `fiberIso_hom_app_left`).
-/

noncomputable section

universe u u' v'

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace Langlands.Geometry.FieldEtaleStalkChange

variable (K Ω M : Type u) [Field K] [Field Ω] [Field M] [Algebra K Ω] [Algebra K M]
  [IsSepClosed Ω] [Algebra.IsSeparable K Ω] [IsSepClosed M] (ι : Ω →ₐ[K] M)

/-- Composition with `Spec ι : Spec M → Spec Ω` identifies the fibre functors of the geometric
points `Spec Ω → Spec K` and `Spec M → Spec K` of the small étale site of `Spec K`. -/
def fiberIso :
    (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω)).fiber ≅
      (Scheme.pointSmallEtale (Scheme.specAlgebraMap K M)).fiber :=
  letI : Algebra Ω M := ι.toRingHom.toAlgebra
  haveI : IsScalarTower K Ω M := IsScalarTower.of_algebraMap_eq fun k ↦ (ι.commutes k).symm
  Scheme.pointSmallEtaleFiberIso K Ω M

/-- `fiberIso` is composition with `Spec ι`. -/
lemma fiberIso_hom_app_left {X : (Spec (.of K)).Etale}
    (x : (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω)).fiber.obj X) :
    ((fiberIso K Ω M ι).hom.app X x).left = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ x.left :=
  rfl

/-- The isomorphism of points of the small étale site of `Spec K` given by `ι`. -/
def pointIso :
    Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω) ≅
      Scheme.pointSmallEtale (Scheme.specAlgebraMap K M) :=
  GrothendieckTopology.Point.isoMk (fiberIso K Ω M ι)

variable (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{u, u} A]

/-- The isomorphism of stalk functors at `Spec Ω → Spec K` and `Spec M → Spec K` on sheaves
with values in `A`: the germ of a section at a lift `x` goes to its germ at `Spec ι ≫ x`. -/
def sheafFiberIso :
    (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω)).sheafFiber (A := A) ≅
      (Scheme.pointSmallEtale (Scheme.specAlgebraMap K M)).sheafFiber :=
  (GrothendieckTopology.Point.sheafFiberIso (pointIso K Ω M ι).symm).symm

/-- `sheafFiberIso` sends the germ at a lift `x` to the germ at `(fiberIso K Ω M ι).hom.app X x`,
the lift `Spec ι ≫ x`. -/
@[reassoc]
lemma toPresheafFiber_sheafFiberIso_hom_app (F : Sheaf (Spec (.of K)).smallEtaleTopology A)
    (X : (Spec (.of K)).Etale)
    (x : (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω)).fiber.obj X) :
    (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω)).toPresheafFiber X x F.obj ≫
        (sheafFiberIso K Ω M ι A).hom.app F =
      (Scheme.pointSmallEtale (Scheme.specAlgebraMap K M)).toPresheafFiber X
        ((fiberIso K Ω M ι).hom.app X x) F.obj :=
  GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app (pointIso K Ω M ι).symm F X x

end Langlands.Geometry.FieldEtaleStalkChange
