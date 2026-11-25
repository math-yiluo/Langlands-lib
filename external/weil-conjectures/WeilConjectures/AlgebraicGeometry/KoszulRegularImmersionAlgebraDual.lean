/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.KoszulRegularImmersionAlgebraDualHomology
import WeilConjectures.AlgebraicGeometry.ClosedImmersionRankedCohomologyReconstruction
/-! # Algebra-linear Koszul duality

Source: Stacks Project, Tag 0BQZ, Tag 0AX3 and Tag 0AVW
(blueprint: lem-sc-koszul-regular-immersion-algebra-dual).
-/

@[expose] public section

universe u wZ wY wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Koszul duality before forgetting the direct-image-algebra action. This
statement concerns the ambient scalar right adjoint, not a geometric right adjoint
on quasi-coherent complexes.

Source: Stacks Project, Duality for Schemes, Tag 0BQZ, Tag 0AX3; Tag 0AVW
(blueprint: lem-sc-koszul-regular-immersion-algebra-dual).

Proof: By uniqueness of right adjoints, replace H by the algebra-valued derived
sheaf Hom right adjoint computed in exists_affine_derivedHom_evaluation_counit.
For a K-injective resolution J of OY its value is Hom(i_* OZ, J), with the
algebra i_* OZ acting by precomposition. On an affine chart meeting Z, put
B = A/I and take the finite free Koszul resolution of B given by hregular.
The dual Koszul calculation has cohomology only in degree n, canonically
identified with the top exterior power of the B-dual of I/I². This identification
is B-linear: precomposition by multiplication in B induces its usual scalar
action. The rank condition hr identifies n with r on the chart. Under the affine
module correspondence the normal determinant on Z is the same B-module.
The affine cohomology formula identifies its algebra-valued derived direct image
with this sheaf, placed in degree n. The intrinsic determinant comparison commutes
with localization and with changes of regular generators. Hence its cohomology
sheaf maps glue as i_* OZ-module maps. Noetherian Z is quasi-compact, so r has
finite image. The characteristic sections of its finitely many clopen rank strata
give orthogonal idempotents in i_* OZ, summing to one. Split both algebra-module
complexes by these idempotents; on the rank-n summand only degree n survives.
Canonical truncation then turns the glued cohomology map into an isomorphism
on that summand. The finite sum of these isomorphisms yields the comparison
with locallyRankedExteriorComplex. These strata are clopen in Z; they need not
be clopen in Y, and no truncation across different ranks on Y is asserted. Away
from Z both complexes are zero; a local unit generator makes the Koszul complex
contractible there. Finally transport along the right-adjoint uniqueness
isomorphism to the specified H. This argument allows different chosen derived
categories on Z and Y and does not infer algebra linearity from scalar restriction.
For rank zero it is the usual structure-sheaf comparison, and for empty Z both
objects are zero. -/
theorem koszulRegularImmersion_algebraDual {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsNoetherian Y] [IsClosedImmersion i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    (H : schemeDerivedCategory Y ⥤ DerivedCategory (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i))))
    (adjH : (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace i))
      ⟨Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ H) :
    Nonempty ((RingedSpace.derivedModuleDirectImage
      (toDirectImageAlgebraSpace i)).obj ((DerivedCategory.Q (C :=
        SheafOfModules.{u} (moduleRings Z.toRingedSpace))).obj
          (Scheme.Modules.locallyRankedExteriorComplex
            (SheafOfModules.homObj (R := Z.sheaf)
              ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
              (SheafOfModules.unit Z.ringCatSheaf)) r)) ≅
        H.obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) := by
  have : CompactSpace Z := i.isClosedEmbedding.compactSpace
  have hfinite : (Set.range r).Finite := r.range_finite
  let M := SheafOfModules.homObj (R := Z.sheaf)
    ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
    (SheafOfModules.unit Z.ringCatSheaf)
  let K := H.obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
      (SheafOfModules.unit Y.ringCatSheaf))
  have hK : ∀ n : ℤ, Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj
          (Scheme.Modules.locallyRankedExteriorTerm M r n)) := by
    intro n
    exact koszulRegularImmersion_algebraDual_homology i hregular r hr H adjH n
  exact closedImmersion_rankedCohomology_reconstruction i M r hfinite K hK

end AlgebraicGeometry
