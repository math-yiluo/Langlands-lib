/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.QCqsProjectionMateAffineDescent
import WeilConjectures.AlgebraicGeometry.QCqsProjectionMateShiftedUnit
import WeilConjectures.AlgebraicGeometry.QCqsProjectionMateAffineLocus
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.DerivedTensorRightCoproducts
import WeilConjectures.AlgebraicGeometry.ProjectionFormulaLocality

/-! # The quasi-coherent derived projection mate

Source: Stacks Project, perfect.tex, Tag 08EU, lemma-cohomology-base-change.
(blueprint: lem-pc-qcqs-derived-projection-mate).
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- The projection mate for quasi-coherent derived objects is invertible.
Source: Stacks Project, Tag 08EU (lemma-cohomology-base-change),
and the fourth Hom equality in Tag 0A9Q (lemma-iso-on-RSheafHom).
(blueprint: lem-pc-qcqs-derived-projection-mate).

Proof: write pi(M,L) for the displayed mate. It is natural in both arguments
by naturality of t, the counit, and the adjunction Hom equivalence. Restrict to
an affine open U of Y and f inverse U in X. Restriction is a localization:
its right adjoint on the derived category is fully faithful. Pullback and
tensor commute with restriction, and direct image commutes with restriction
to an open in the target. Consequently the bifunctors underlying t descend
to these localized categories, as does t itself (evaluate on the fully
faithful right adjoints and use the localization counit). The same operation
transports p, its counit, and its Hom equivalence. Thus restriction of pi is
the mate for the transported p and t; no equality with the canonical tensor
comparison is asserted. Isomorphisms are detected on an open cover.

Now Y is affine, say Spec A. For M = O_Y[n], the shift and unit comparisons
identify t(M,-) with a natural automorphism of shifted pullback. Its mate
under p and the shifted adjunction is a natural automorphism of shifted
direct image: the mate of the inverse is its inverse, by the triangle
identities. The displayed pi(M,L), after these shift and unit identifications,
is exactly that mate evaluated at L. It is therefore invertible for every
integer n and every quasi-coherent L. This argument allows arbitrary p and t.

Fix L. Under D(A) equivalent to D_QCoh(Y), use the property that pi(M[n],L)
is invertible for every integer n, rather than only at M. Both functors in M
are exact and preserve coproducts: pullback is a left adjoint, tensor preserves
coproducts, and qcqs direct image preserves quasi-coherent coproducts. Hence
this property is closed under coproducts and retracts. For a distinguished
triangle, apply Hom(T,-), for every ambient test object T, to its images and
all its shifts. These are exact sequences. Naturality of pi at the triangle
maps and at the connecting maps gives a diagram of these sequences using
pi at each shifted vertex. The five lemma proves the property for the third
vertex when it holds for the other two. This uses no compatibility of t with
a separately chosen shift comparison. The free-generation theorem for D(A)
now proves the property for every M, since it holds for all shifts of A.
Open-cover detection gives the result on Y. For zero objects and the empty
scheme every arrow concerned is the unique isomorphism between zero objects. -/
theorem qcqsDerivedProjectionMate_isIso (X Y : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedQCohCategory Y) (L : schemeDerivedQCohCategory X) :
    IsIso (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
      ((derivedPullback f).obj M.obj ⊗ L.obj)
        (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
          (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj))) := by
  classical
  apply qcqsProjectionMate_of_affine ?_ X Y f p t M L
  intro A _ Z _ _ _ _ g _ _ q s N E
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨e, _, _, htri, hunit⟩ := exists_affineQCohDerivedEquivalence A
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := fun K ↦
    ∀ (B : schemeDerivedQCohCategory (Spec (.of A))) (n : ℤ),
      Nonempty ((e.functor.obj (K⟦n⟧)).obj ≅ B.obj) →
      IsIso (q.homEquiv (B.obj ⊗ (schemeDerivedDirectImage g).obj E.obj)
        ((derivedPullback g).obj B.obj ⊗ E.obj)
          (s.hom.app (B.obj, (schemeDerivedDirectImage g).obj E.obj) ≫
            (𝟙 ((derivedPullback g).obj B.obj) ⊗ₘ q.counit.app E.obj)))
  obtain ⟨hcop, htriangle, hretract⟩ :=
    qcqsProjectionMate_affineLocus_closed A Z g q s E e htri
  have hgen : ∀ m : ℤ, P (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (ULift.{0} A)))⟦m⟧) :=
    by
      intro m B n hB
      obtain ⟨hB⟩ := hB
      let a : ModuleCat.of A (ULift.{0} A) ≅ ModuleCat.of A A :=
        (ULift.moduleEquiv : ULift.{0} A ≃ₗ[A] A).toModuleIso
      let d := ((shiftFunctorAdd (DerivedCategory (ModuleCat.{u} A)) m n).symm.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (ULift.{0} A)))) ≪≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (m + n)).mapIso
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso a)
      obtain ⟨hO⟩ := hunit (m + n)
      apply qcqsProjectionMate_shiftedUnit_isIso Z (Spec (.of A)) g q s
        B.obj E.obj (m + n)
      exact ⟨hB.symm ≪≫
        (schemeDerivedQCohProperty (Spec (.of A))).ι.mapIso (e.functor.mapIso d) ≪≫ hO⟩
  have hK : P (e.inverse.obj N) :=
    derivedModuleFreeGeneration.{u, 0, u + 1} A (e.inverse.obj N)
      P hgen hcop htriangle hretract
  apply hK N 0
  exact ⟨(schemeDerivedQCohProperty (Spec (.of A))).ι.mapIso
    (e.functor.mapIso ((shiftFunctorZero _ ℤ).app (e.inverse.obj N)) ≪≫
      e.counitIso.app N)⟩

end AlgebraicGeometry
