/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineAlgebraUpperTruncationEdge
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-! # Exactness of affine cycles and boundaries

Source: Stacks Project, Tags 0AVW and 08D4.
(blueprint: new-affine-algebra-kinjective-boundary-exactness).
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- After affine direct image, cycle sections with zero homology class are
locally boundaries of the section complex.
Source: Stacks Project, Tag 0AVW, the cohomology calculation in its proof;
Tag 08D4, parts (1) and (2), with bound one.
(blueprint: new-affine-algebra-kinjective-boundary-exactness).

Proof: Fix an affine open V of Y and set U = f⁻¹V, also affine. Restriction
preserves quasi-coherence. Restriction also preserves K-injectivity, since it
is right adjoint to exact extension by zero (Tag 08BS). Thus I restricted to U
computes derived sections on U. Positive module cohomology on U vanishes by affine
vanishing. Sections on U commute with countable products. For E = Q(I), let
A = τ≤n I and B = τ≥n A, with canonical chain maps A → I and A → B.
B is H^n(I) placed in degree n. Derived sections of A → I induce an isomorphism
on H^n by left exactness (the complementary upper tail starts in degree n+1).
The lower tail τ≤(n-1)I has quasi-coherent cohomology and derived sections zero
in degrees n and n+1 by Tag 08D4 with N = 1. Its truncation triangle makes
H^n(RΓ(A)) → H^n(RΓ(B)) invertible. Bottom derived sections of B are Γ(U,H^n(I)).
Use the natural map from sections of a complex to its derived sections. It is
invertible on cohomology for I because I is K-injective. This does not require
its individual terms to be injective: a comparison to a K-injective resolution
is a homotopy equivalence, preserved by sections. Sections preserve kernels,
so H^n(Γ(A)) → H^n(Γ(I)) is invertible as well. Naturality for A → I now shows
that H^n(Γ(A)) → H^n(RΓ(A)) is invertible. Naturality for A → B identifies the
resulting isomorphism H^n(Γ(I)) → Γ(U,H^n(I)) with the raw cycle-class map:
A^n is the kernel of d^n and (A → B)^n is its homology quotient. This verifies
the identity of the map, rather than just existence of an unrelated isomorphism.
The chosen homology data identifies its K and π with these cycles and class map.
Injectivity of that isomorphism says that a cycle with zero homology-sheaf
class is zero in H^n(Γ(I)), so it is the differential of a degree-(n-1) section.
Thus on every affine open the kernel of the pushed π is the image of the pushed
f', the differential into cycles. The reverse inclusion is f' ≫ π = 0.
Equalities of kernels and images on this basis give exactness of the displayed
short complex of f_*O_X-module sheaves. All maps respect the scalar action and
restriction maps since they come from I. Zero complexes, empty opens and all
integer degrees are included; no boundedness of I is imposed. -/
theorem affine_algebra_kinjective_boundary_exactness
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    ((ShortComplex.mk (I.sc n).homologyData.left.f' (I.sc n).homologyData.left.π
      (I.sc n).homologyData.left.f'_π).map
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))).Exact := by
  let C := SheafOfModules.{v} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have : EnoughInjectives C :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let h := (I.sc n).homologyData.left
  have : IsIso ((DerivedCategory.homologyFunctor D n).map
      (F.complexDerivedUnit.app (I.truncLE n))) :=
    F.isIso_complexDerivedUnit_upperTruncation I n
  have : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map (I.ιTruncLE n)) n) :=
    (F.upperTruncation_comparisons I n).1
  have : IsIso (F.upperTruncationBoundaryComparison I n) := by
    dsimp [Functor.upperTruncationBoundaryComparison]
    infer_instance
  obtain ⟨e, he⟩ := affine_algebra_upper_truncation_edge f I hI n
  let B := (ShortComplex.mk h.f' h.π h.f'_π).map F
  apply B.exact_iff_mono_cokernel_desc.mpr
  have hd : Limits.cokernel.desc B.f B.g B.zero =
      F.upperTruncationBoundaryComparison I n ≫ e.hom := by
    apply (cancel_epi (Limits.cokernel.π B.f)).mp
    rw [Limits.cokernel.π_desc]
    dsimp only [B, ShortComplex.map, ShortComplex.mk, h, F]
    exact he.symm
  rw [hd]
  infer_instance

end AlgebraicGeometry
