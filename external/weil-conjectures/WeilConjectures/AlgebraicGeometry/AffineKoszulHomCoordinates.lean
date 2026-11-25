/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.RingTheory.KoszulDualComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import WeilConjectures.AlgebraicGeometry.AffineKoszulHomComplexIso
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Affine coordinates for the sheafified Koszul Hom complex

Source: Stacks Project, Tag 0BQZ, displayed finite free Hom computation.
(blueprint: lem-sc-affine-koszul-hom-coordinates). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The cohomology of Hom from the sheafified Koszul complex into the structure
sheaf is the associated sheaf of the recorded signed dual Koszul homology.

Source: Stacks Project, Tag 0BQZ, local Hom complex computation; Tag 01HV,
exact associated sheafification on affine schemes.
(blueprint: lem-sc-affine-koszul-hom-coordinates).

Proof: In total degree k, the target single complex has only its degree-zero term.
Thus the product defining Hom has just one possibly nonzero factor, from source
cochain degree -k. For k>=0, use the wedge basis of the free module A^n to identify
sheaf Hom from its kth exterior power into O_U with tilde of its A-linear dual.
For negative k the source term is zero and so is the Hom term. Matrix entries
of the coordinate maps localize on basic opens, so these identifications agree
with restrictions and glue. The target differential vanishes, while the source
contribution to total Hom is -(-1)^k times precomposition by d_(k+1), equal to
(-1)^(k+1) times precomposition, exactly koszulDualBoundary. This gives an
isomorphism of integer-indexed complexes to the sheafified koszulDualCochainComplex.
Tilde is exact, as seen from localization on stalks, and transport along isoSpec
is an equivalence. Homology therefore commutes with their composite; taking
homology of the complex isomorphism gives the displayed isomorphism. This
calculation needs no regularity or augmentation. The empty sequence gives Hom
from O_U to O_U in degree zero, and negative degrees and empty charts give zero. -/
theorem affine_koszul_hom_coordinates
    {Y : Scheme.{u}} (U : Y.affineOpens) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (q : ℤ) :
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((ExteriorAlgebra.koszulComplex (Γ(Y, U.1) : Type u) n f).extend
        ComplexShape.embeddingDownNat)
    Nonempty ((homComplex (R := U.1.toScheme.toRingedSpace.sheaf) E
      ((CochainComplex.singleFunctor U.1.toScheme.Modules 0).obj
        (SheafOfModules.unit U.1.toScheme.ringCatSheaf))).homology q ≅
      T.obj ((ExteriorAlgebra.koszulDualCochainComplex
        (Γ(Y, U.1) : Type u) n f).homology q)) := by
  let A := (Γ(Y, U.1) : Type u)
  let T := tilde.functor Γ(Y, U.1)
  let R := Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let F := T ⋙ R
  let : PreservesFiniteLimits T := tilde_preserves_finite_limits A
  let : PreservesFiniteLimits R := by dsimp [R]; infer_instance
  let : PreservesFiniteColimits R := by dsimp [R]; infer_instance
  let : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  obtain ⟨e⟩ := affine_koszul_hom_complex_iso U n f
  exact ⟨(HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q).mapIso e ≪≫
    (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) q).app
      (ExteriorAlgebra.koszulDualCochainComplex A n f)⟩

end AlgebraicGeometry
