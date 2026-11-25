/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentExtension

/-! # Triangulated closure of supported quasi-coherent complexes

Source: Stacks Project, Tag 0A9A, preceding definition of D_QCoh,T.
(blueprint: lem-pc-supported-qcoh-triangulated).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace AlgebraicGeometry

abbrev supportedProperty (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) : ObjectProperty (schemeDerivedCategory X) := fun K ↦
  schemeDerivedQCohProperty X K ∧ ∀ (n : ℤ) (x : X), x ∉ T →
    Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x))

private instance moduleToSheaf_additive (X : Scheme.{u}) :
    (SheafOfModules.toSheaf.{u} (moduleRings X.toRingedSpace)).Additive where
  map_add := by intros; rfl

private theorem qcoh_kernels (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).IsClosedUnderKernels := by
  constructor
  rintro _ ⟨f, k, hk, hM, hN⟩
  have := hM
  have := hN
  apply (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
  exact Scheme.Modules.isQuasicoherent_kernel (X := X) f

private theorem qcoh_cokernels (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).IsClosedUnderCokernels := by
  constructor
  rintro _ ⟨f, k, hk, hM, hN⟩
  have := hM
  have := hN
  apply (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
  exact Scheme.Modules.isQuasicoherent_cokernel (X := X) f

private theorem qcoh_extensions (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).IsClosedUnderExtensions := by
  constructor
  intro S hS h₁ h₃
  have := h₁
  have := h₃
  exact Scheme.Modules.isQuasicoherent_of_shortExact (X := X) (S := S) hS

/-- The supported quasi-coherent property contains a zero object.
Source: Stacks Project, Derived Categories of Schemes, definition preceding Tag 0A9A.
(blueprint: lem-pc-supported-qcoh-contains-zero).

Proof: Choose the zero object of the derived category. Each homology functor is additive,
so its image is a zero sheaf of modules. A zero module sheaf is quasi-coherent: on every
affine open it is the sheaf associated to the zero module, or equivalently it has the
presentation with no generators and no relations. Its underlying additive sheaf has
zero sections on every open, and hence zero stalk at every point. Thus all homology
sheaves are quasi-coherent and all stalks outside T are subsingleton, independently of T. -/
theorem supported_qcoh_containsZero (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) : (supportedProperty X T).ContainsZero := by
  have hzero : IsZero
      (SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free
      (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}⟩⟩
  refine ⟨⟨0, isZero_zero _, ?_, ?_⟩⟩
  · intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_isZero
      ((DerivedCategory.homologyFunctor _ n).map_isZero (isZero_zero _))
  · intro n x _
    let F := SheafOfModules.toSheaf.{u} (moduleRings X.toRingedSpace) ⋙
      TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    have : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive := inferInstance
    have : (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).Additive := inferInstance
    have : (SheafOfModules.toSheaf.{u} (moduleRings X.toRingedSpace)).Additive := inferInstance
    have : F.Additive := by dsimp [F]; infer_instance
    exact AddCommGrpCat.subsingleton_of_isZero
      (F.map_isZero ((DerivedCategory.homologyFunctor _ n).map_isZero (isZero_zero _)))

/-- The supported quasi-coherent property is stable under every integer shift.
Source: Stacks Project, Derived Categories of Schemes, definition preceding Tag 0A9A.
(blueprint: lem-pc-supported-qcoh-stable-shift).

Proof: For integers a and n, the shift sequence gives H^n(K[a]) ≅ H^(a+n)(K).
Transport quasi-coherence along its inverse. Applying the underlying additive
presheaf functor and the stalk functor at x gives an isomorphism of additive groups.
Its forward map is injective, so a subsingleton stalk of H^(a+n)(K) implies a
subsingleton stalk of H^n(K[a]). This works for all shifts and every subset T. -/
theorem supported_qcoh_stableShift (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) : (supportedProperty X T).IsStableUnderShift ℤ := by
  refine ⟨fun a ↦ ⟨fun K hK ↦ ?_⟩⟩
  constructor
  · intro n
    exact (SheafOfModules.isQuasicoherent.{u} (moduleRings X.toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).shiftIso
        a n (a + n) rfl).app K).symm (hK.1 (a + n))
  · intro n x hx
    let e := (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).shiftIso
      a n (a + n) rfl).app K)
    let F := SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.toPresheaf.{u} (moduleRings X.toRingedSpace).obj ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    let h : Subsingleton (↑(F.obj ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (a + n)).obj K))) :=
      hK.2 (a + n) x hx
    refine ⟨fun b c ↦ (ConcreteCategory.bijective_of_isIso (F.mapIso e).hom).1 ?_⟩
    exact h.elim _ _

/-- The supported quasi-coherent property is closed under middle terms of triangles.
Source: Stacks Project, Derived Categories of Schemes, definition preceding Tag 0A9A.
(blueprint: lem-pc-supported-qcoh-closed-middle).

Proof: For a distinguished triangle K → L → M → K[1] with K and M in the property,
the long exact homology sequence gives a short exact sequence from the cokernel of
H^(n-1)(M) → H^n(K) to H^n(L) to the kernel of H^n(M) → H^(n+1)(K).
Kernels, cokernels, and extensions of quasi-coherent module sheaves on a scheme are
quasi-coherent. For kernels and cokernels this follows on affine opens from exactness
of the module-to-sheaf correspondence. For extensions, on an affine open the outer
quasi-coherent sheaves have vanishing H^1, so sections form an exact extension of
modules; sheafifying this extension identifies its middle term with the given sheaf.
At a point x outside T, the stalk functor is exact and both outer stalks in the long
exact sequence are zero. Exactness forces the middle stalk to be zero as well.
Thus L itself has the property, and in particular lies in its isomorphism closure,
as required by IsTriangulatedClosed₂. The argument also covers empty T and T = X. -/
theorem supported_qcoh_closedMiddle (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) : (supportedProperty X T).IsTriangulatedClosed₂ := by
  constructor
  intro D hD h₁ h₃
  apply (supportedProperty X T).le_isoClosure
  constructor
  · have := qcoh_kernels X
    have := qcoh_cokernels X
    have := qcoh_extensions X
    intro n
    exact ObjectProperty.prop_of_exact_of_exact_of_exact
      (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace))
      ((DerivedCategory.homologyFunctor _ 0).homologySequence_exact₁ D hD
        (n - 1) n (by omega))
      ((DerivedCategory.homologyFunctor _ 0).homologySequence_exact₂ D hD n)
      ((DerivedCategory.homologyFunctor _ 0).homologySequence_exact₃ D hD n (n + 1) rfl)
      (h₃.1 (n - 1)) (h₁.1 n) (h₃.1 n) (h₁.1 (n + 1))
  · intro n x hx
    let F := SheafOfModules.toSheaf.{u} (moduleRings X.toRingedSpace) ⋙
      TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    have : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive := inferInstance
    have : (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).Additive := inferInstance
    have : (SheafOfModules.toSheaf.{u} (moduleRings X.toRingedSpace)).Additive := inferInstance
    have : F.Additive := by dsimp [F]; infer_instance
    have : PreservesFiniteLimits
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := inferInstance
    have : PreservesFiniteLimits F := by dsimp [F]; infer_instance
    have : PreservesFiniteColimits
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := inferInstance
    have : PreservesFiniteColimits F := by dsimp [F]; infer_instance
    have : Subsingleton (F.obj ((DerivedCategory.homologyFunctor _ n).obj D.obj₁)) :=
      h₁.2 n x hx
    have : Subsingleton (F.obj ((DerivedCategory.homologyFunctor _ n).obj D.obj₃)) :=
      h₃.2 n x hx
    have h := ((DerivedCategory.homologyFunctor _ 0).homologySequence_exact₂ D hD n).map F
    simp only [DerivedCategory.shift_homologyFunctor] at h
    dsimp only [ShortComplex.map] at h
    exact AddCommGrpCat.subsingleton_of_isZero
      (h.isZero_of_both_isZero (AddCommGrpCat.isZero_of_subsingleton _)
        (AddCommGrpCat.isZero_of_subsingleton _))

/-- Quasi-coherent cohomology with zero stalks off T is stable under triangles.
No compactness or closedness assumption on T is needed for this closure assertion.
Source: Stacks Project, Derived Categories of Schemes, definition preceding Tag 0A9A.
(blueprint: lem-pc-supported-qcoh-triangulated).

Proof:
1. The zero complex has zero cohomology sheaves; these are quasi-coherent and their
   stalks are zero. This verifies ContainsZero.
2. Cohomology of K shifted by m is canonically cohomology of K in degree n+m.
   Quasi-coherence and zero stalks are invariant under these isomorphisms. This verifies
   IsStableUnderShift for every integer shift, including negative shifts.
3. Apply cohomology to a distinguished triangle with its first and third objects in
   the property. Its middle cohomology sheaf is an extension of a cokernel between
   quasi-coherent cohomology sheaves and a kernel between such sheaves. Kernels,
   cokernels and extensions of quasi-coherent modules on a scheme are quasi-coherent,
   as can be checked on affine opens by the exact module-to-sheaf equivalence.
4. At a point outside T, stalks preserve exact sequences. The long exact cohomology
   sequence has zero terms on both sides of each middle term, so that term is zero.
   Consequently the middle object has the property itself, hence also its isoClosure.
   These three assertions give ObjectProperty.IsTriangulated. The empty subset and
   the whole space require exactly the same argument. -/
theorem supported_qcoh_isTriangulated (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) :
    ObjectProperty.IsTriangulated (fun K : schemeDerivedCategory X ↦
      schemeDerivedQCohProperty X K ∧
        ∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x))) := by
  let : (supportedProperty X T).ContainsZero := supported_qcoh_containsZero X T
  let : (supportedProperty X T).IsStableUnderShift ℤ := supported_qcoh_stableShift X T
  let : (supportedProperty X T).IsTriangulatedClosed₂ := supported_qcoh_closedMiddle X T
  exact ObjectProperty.IsTriangulated.mk


end AlgebraicGeometry
