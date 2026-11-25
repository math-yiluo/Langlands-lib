/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Curves, their genus, and the Picard group of a curve

A *curve* over a field `K` is a separated scheme of finite type over `K` whose underlying space
has Krull dimension at most one. "Of finite type" is spelled as `LocallyOfFiniteType` together
with `QuasiCompact`, Mathlib having no bundled class for the conjunction. For a smooth proper
connected curve `C` over `K` the *genus* is `g = dim_K H⁰(C, Ω¹_{C/K})`, the dimension of the
space of global differential forms.

The Picard group `Pic(C)` of isomorphism classes of invertible `𝒪_C`-modules is
`AlgebraicGeometry.Scheme.Pic`, introduced in
`WeilConjectures.AlgebraicGeometry.PicardFunctor`; on a curve it carries a *degree* map to `ℤ`,
whose kernel `Pic⁰(C)` is the subject of the Jacobian.

The sheaf `Ω¹_{C/K}` is `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, from
`WeilConjectures.AlgebraicGeometry.Modules.Differentials`. The degree of an invertible module
`L` is defined cohomologically, as `deg L = χ(L) - χ(𝒪_C)` (Stacks 0AYQ), through
`AlgebraicGeometry.Scheme.Modules.degree`.

## Main definitions

- `AlgebraicGeometry.IsCurve`: a separated morphism of finite type to `Spec K` whose source has
  topological Krull dimension at most one.
- `AlgebraicGeometry.IsConnectedCurve`: a curve whose source is connected, hence nonempty, and
  of topological Krull dimension exactly one.
- `AlgebraicGeometry.SmoothConnectedCurve`: the category of smooth connected curves.
- `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`: the sheaf `Ω¹_{X/S}` of relative
  differentials (see `WeilConjectures.AlgebraicGeometry.Modules.Differentials`).
- `AlgebraicGeometry.Scheme.Hom.genus`: the genus `dim_K Γ(C, Ω¹_{C/K})` of a curve.
- `AlgebraicGeometry.Scheme.Hom.picDegree`: the degree `χ(L) - χ(𝒪_C)` of an invertible module
  on a curve.
- `AlgebraicGeometry.Scheme.Hom.picZero`: the degree-zero part `Pic⁰(C)` of the Picard group.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.genus_eq_finrankH_zero`: the genus is `h⁰(C, Ω¹_{C/K})`.
- `AlgebraicGeometry.Scheme.Hom.picDegree_mk`: the degree of the class of an invertible module
  `M` is `χ(M) - χ(𝒪_C)`.

The degree as a group homomorphism, and its identification with the degree of divisors over an
algebraically closed field, are in `WeilConjectures/AlgebraicGeometry/Curve/Picard.lean`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {C : Scheme.{u}}

/-- Blueprint `def-sc-curves`: Curves and genus

Let `K` be a field (in the blueprint, algebraically closed). A *curve* over `K` is a separated
scheme of finite type over `K` of dimension at most one. Smoothness and properness of a curve
are the corresponding properties `Smooth` and `IsProper` of its structure morphism, so they are
not part of this class; the dimension condition is phrased with `topologicalKrullDim`, which is
valued in `WithBot ℕ∞` and is `⊥` exactly on the empty scheme.

This is also blueprint `def-sc-curves`. As blueprint `rem-pc-relation-sc` records, a smooth
projective curve in the sense of the curve-calculation chapter is a smooth connected curve here
(blueprint `lem-pc-curves-are-sc`). -/
class IsCurve (f : C ⟶ Spec (.of K)) : Prop
    extends IsSeparated f, LocallyOfFiniteType f, QuasiCompact f where
  /-- The underlying space of a curve has dimension at most one. -/
  krullDim_le_one : topologicalKrullDim C ≤ 1

/-- Blueprint `def-sc-curves`: Curves and genus

A *connected curve* over `K` is a curve over `K` that is connected (hence nonempty) and of
dimension exactly one. The last condition excludes points such as `Spec K`, for which the curve
estimate `proposition-smooth-proper-curves-torsion-prime` fails in degree two. It also implies
nonemptiness on its own, since `topologicalKrullDim` is `⊥` exactly on the empty space. This is also
part of blueprint `def-sc-curves`.

The field `IsConnectedCurve.connectedSpace` is not an instance, since `f` cannot be inferred
from `ConnectedSpace C`; use `have := IsConnectedCurve.connectedSpace (f := f)`. -/
class IsConnectedCurve (f : C ⟶ Spec (.of K)) : Prop extends IsCurve f where
  /-- The underlying space of a connected curve is connected, in particular nonempty. -/
  connectedSpace : ConnectedSpace C
  /-- The underlying space of a connected curve has dimension exactly one. -/
  krullDim_eq_one : topologicalKrullDim C = 1

/-- The underlying space of a connected curve is nonempty. -/
lemma IsConnectedCurve.nonempty (f : C ⟶ Spec (.of K)) [IsConnectedCurve f] : Nonempty C :=
  have := IsConnectedCurve.connectedSpace (f := f)
  inferInstance

variable (K) in
/-- Blueprint `def-sc-curves`: the category `𝒞` of smooth separated connected curves over `K`,
the full subcategory of `K`-schemes `C` whose structure morphism is smooth and a connected curve
(`AlgebraicGeometry.IsConnectedCurve`, which includes separatedness). -/
def SmoothConnectedCurve : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun C : Over (Spec (.of K)) ↦
    Smooth C.hom ∧ IsConnectedCurve C.hom

noncomputable instance : Category (SmoothConnectedCurve K) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory _))

/-- Blueprint `def-sc-curves`: Curves and genus

The *genus* of a smooth proper connected curve `C` over `K` is
`g = dim_K H⁰(C, Ω¹_{C/K})`, the `K`-dimension of the space of global sections of the sheaf of
relative differentials. Since `C` is proper the global sections form a finite-dimensional
`K`-vector space; the `K`-module structure on `Γ(Ω¹_{C/K}, ⊤)` comes from the `Γ(C, ⊤)`-module
structure by restriction of scalars along the `K`-algebra structure of `Γ(C, ⊤)`.

This definition makes sense for an arbitrary morphism `f : C ⟶ Spec K`, but is only the genus
in the intended sense when `f` is a smooth proper connected curve.

For a smooth proper curve, Serre duality identifies this with the arithmetic genus
`AlgebraicGeometry.Scheme.arithmeticGenus K C = dim_K H¹(C, 𝒪_C)`; see
`AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`. It is finite
(`AlgebraicGeometry.Scheme.finiteDimensional_H_relativeDifferentials`).

This is also blueprint `prose-C-05`. -/
noncomputable def Scheme.Hom.genus (f : C ⟶ Spec (.of K)) : ℕ :=
  letI := f.ΓAlgebra
  letI : Module K Γ(f.relativeDifferentials, ⊤) := Module.compHom _ (algebraMap K Γ(C, ⊤))
  Module.finrank K Γ(f.relativeDifferentials, ⊤)

/-- The genus `dim_K Γ(C, Ω¹_{C/K})` is `h⁰(C, Ω¹_{C/K})`: the global sections of a sheaf of
modules are its cohomology in degree `0`, compatibly with the `K`-module structures. -/
theorem Scheme.Hom.genus_eq_finrankH_zero [C.Over (Spec (.of K))] :
    (C ↘ Spec (.of K)).genus = Modules.finrankH K (C ↘ Spec (.of K)).relativeDifferentials 0 := by
  let e := Modules.H.zeroLinearEquiv (C ↘ Spec (.of K)).relativeDifferentials
  let := (C ↘ Spec (.of K)).ΓAlgebra
  let : Module K Γ((C ↘ Spec (.of K)).relativeDifferentials, ⊤) :=
    Module.compHom _ (algebraMap K Γ(C, ⊤))
  exact (LinearEquiv.finrank_eq (R := K)
    { e with map_smul' := fun c x ↦ e.map_smul (globalSectionsRingHom K c) x }).symm

/-- Blueprint `def-sc-picard-group`: Pic, degree, Pic⁰

The degree `deg L = χ(L) - χ(𝒪_C)` of the class `L` of an invertible module on a curve `C`
over `K` (Stacks 0AYQ), where `χ` is the Euler characteristic
`AlgebraicGeometry.Scheme.Modules.eulerChar` over `K`; this is
`AlgebraicGeometry.Scheme.Modules.degree` of a representative of `L`.

On a smooth projective geometrically integral curve this is the degree of any associated Weil
divisor, and the Riemann-Roch formula `χ(L) = deg L + 1 - g` holds.

(blueprint: `corollary-degree-jacobian--1`) -/
noncomputable def Scheme.Hom.picDegree (f : C ⟶ Spec (.of K)) (L : C.Pic) : ℤ :=
  letI : C.Over (Spec (.of K)) := ⟨f⟩
  Modules.degree K ((fromSkeleton C.Modules).obj L.val)

lemma Scheme.Hom.picDegree_eq (f : C ⟶ Spec (.of K)) (L : C.Pic) :
    letI : C.Over (Spec (.of K)) := ⟨f⟩
    f.picDegree L = Modules.degree K ((fromSkeleton C.Modules).obj L.val) :=
  rfl

/-- The degree of the class of an invertible module `M` is the degree `χ(M) - χ(𝒪_C)` of `M`. -/
@[simp]
lemma Scheme.Hom.picDegree_mk (f : C ⟶ Spec (.of K)) (M : C.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} M] :
    letI : C.Over (Spec (.of K)) := ⟨f⟩
    f.picDegree (Pic.mk M) = Modules.degree K M :=
  letI : C.Over (Spec (.of K)) := ⟨f⟩
  Modules.degree_congr K (fromSkeletonToSkeletonIso M)

/-- Blueprint `def-sc-picard-group`: Pic, degree, Pic⁰

Let `C` be a smooth projective geometrically integral curve over a field `K`. Its Picard group
`Pic(C) = H¹(C_ét, 𝔾ₘ)` is the group of invertible `𝒪_C`-modules up to isomorphism; it is
`AlgebraicGeometry.Scheme.Pic`. The degree homomorphism `deg : Pic(C) → ℤ` is
`AlgebraicGeometry.Scheme.Hom.picDegree`, and `Pic⁰(C) := ker(deg)` is the subgroup of classes
of degree zero, recorded here as the subset `f.picZero` of `C.Pic`.

For a smooth proper curve the degree is the group homomorphism
`AlgebraicGeometry.Scheme.picDegreeHom`, whose kernel is `picZero`
(`AlgebraicGeometry.Scheme.coe_ker_picDegreeHom`).

(blueprint: `corollary-degree-jacobian--1`) -/
def Scheme.Hom.picZero (f : C ⟶ Spec (.of K)) : Set C.Pic :=
  {L | f.picDegree L = 0}

end AlgebraicGeometry
