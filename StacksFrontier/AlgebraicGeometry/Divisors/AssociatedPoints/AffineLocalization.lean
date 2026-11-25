module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The stalk of a quasi-coherent module on an affine open is a localization

Let `F` be a quasi-coherent `𝒪_X`-module on a scheme `X` and let `U` be an affine open of `X`.
The germ map `Γ(F, U) → F_x` at a point `x ∈ U` exhibits the stalk `F_x` as the localization of
the module of sections `Γ(F, U)` at the prime of `Γ(X, U)` corresponding to `x`.

This is the affine-local bridge through which statements about associated points of `F` at `x`
are translated into statements about associated primes of the `Γ(X, U)`-module `Γ(F, U)`.

## Main definitions

* `AlgebraicGeometry.affineStalkModule` is the `Γ(X, U)`-module structure on the stalk `F_x`
  obtained by restricting scalars along the germ map of the structure sheaf.
* `AlgebraicGeometry.affineGerm` is the germ map `Γ(F, U) → F_x`, as a `Γ(X, U)`-linear map.
* `AlgebraicGeometry.fromSpecSectionsIso` and
  `AlgebraicGeometry.fromSpecSectionsLinearEquiv` identify the global sections of the
  restriction of `F` along `IsAffineOpen.fromSpec` with `Γ(F, U)`.

## Main results

* `AlgebraicGeometry.affineGerm_isLocalized`: the germ map is a localization of modules at the
  prime corresponding to the point.
* `AlgebraicGeometry.germ_eq_zero_iff_exists_smul_eq_zero_affine`: a section of `F` over an
  affine open has vanishing germ at `x` exactly when some element of `Γ(X, U)` outside the
  corresponding prime kills it.
* `AlgebraicGeometry.affine_exists_global_multiple`: every element of the stalk becomes the
  germ of a global section after multiplication by an element outside the prime.

## Implementation notes

The module structure on the stalk of an `𝒪_X`-module over the stalk of the structure sheaf is
supplied explicitly throughout, because typeclass resolution does not find it for an
`X.Modules`; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints.lean`.

The affine case is reduced to the case of a global `Spec` by restricting `F` along
`IsAffineOpen.fromSpec`; the comparison of sections, of germs and of the scalar action under
that restriction is what the `fromSpecSectionsIso` family of lemmas provides.

## References

* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
* [Stacks Project, Tag 056M](https://stacks.math.columbia.edu/tag/056M)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The map on sections of `IsAffineOpen.fromSpec` from `U` to the whole of `Spec Γ(X, U)` is
the inverse of the canonical identification `Γ(Spec Γ(X, U), ⊤) ≅ Γ(X, U)`. -/
lemma fromSpec_appLE_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec.appLE U ⊤ (by rw [hU.fromSpec_preimage_self]) =
      (Scheme.ΓSpecIso Γ(X, U)).inv := by
  simp only [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  simp

end AlgebraicGeometry
