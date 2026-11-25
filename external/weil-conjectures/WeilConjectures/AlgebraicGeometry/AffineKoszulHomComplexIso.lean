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
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeDualComplexComparison
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Complex comparison in finite free affine Koszul coordinates

Source: Stacks Project, Tag 0BQZ, displayed finite free Hom computation.
(blueprint: lem-sc-affine-koszul-hom-complex-iso). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Hom from the sheafified Koszul complex into the structure sheaf is
isomorphic to the sheafified integer-indexed signed dual Koszul complex.

Source: Stacks Project, Tag 0BQZ, local Hom complex computation; Tag 01HV,
exact associated sheafification on affine schemes.
(blueprint: lem-sc-affine-koszul-hom-complex-iso).

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
The component maps are inverse because the wedge coordinates are bases and all
other product factors are zero. Thus they form the displayed complex isomorphism.
This calculation needs no regularity or augmentation. The empty sequence gives Hom
from O_U to O_U in degree zero, and negative degrees and empty charts give zero. -/
theorem affine_koszul_hom_complex_iso
    {Y : Scheme.{u}} (U : Y.affineOpens) (n : ℕ) (f : Fin n → Γ(Y, U.1)) :
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((ExteriorAlgebra.koszulComplex (Γ(Y, U.1) : Type u) n f).extend
        ComplexShape.embeddingDownNat)
    Nonempty (homComplex (R := U.1.toScheme.toRingedSpace.sheaf) E
      ((CochainComplex.singleFunctor U.1.toScheme.Modules 0).obj
        (SheafOfModules.unit U.1.toScheme.ringCatSheaf)) ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (ExteriorAlgebra.koszulDualCochainComplex
          (Γ(Y, U.1) : Type u) n f)) := by
  classical
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let K := ExteriorAlgebra.koszulComplex (Γ(Y, U.1) : Type u) n f
  have hfree (q : ℕ) : Module.Free Γ(Y, U.1) (K.X q) := by
    exact Module.Free.of_basis
      ((Finsupp.basisSingleOne : Module.Basis (Fin n) Γ(Y, U.1)
        (Fin n →₀ Γ(Y, U.1))).exteriorPower q)
  have hfinite (q : ℕ) : Module.Finite Γ(Y, U.1) (K.X q) := by
    exact Module.Finite.of_basis
      ((Finsupp.basisSingleOne : Module.Basis (Fin n) Γ(Y, U.1)
        (Fin n →₀ Γ(Y, U.1))).exteriorPower q)
  obtain ⟨a⟩ := homComplex_to_single_iso (R := U.1.toScheme.toRingedSpace.sheaf)
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingDownNat))
    (SheafOfModules.unit U.1.toScheme.ringCatSheaf)
  obtain ⟨b⟩ := affine_finite_free_dual_complex_comparison U K hfree hfinite
  exact ⟨a ≪≫ b⟩

end AlgebraicGeometry
