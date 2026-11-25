/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleCupAWComponents
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialInput
public import WeilConjectures.AlgebraicGeometry.ModuleCupResolutionData
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelPairing
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelsExist
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialExists
public import WeilConjectures.CategoryTheory.SimplexPresentationFaithful
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementRelations
public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementAugmentation
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementPairingForModels
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementIteratePairings
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementIteratePairingsCanonicalCollapse
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementIteratePairingsCanonical
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementBetaExists
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorCoordinatesExists
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorCoordinates
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorStalkPairingExists
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorMapOfPairingExists
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementPairingsFromBeta
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelQuasiIso
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementStalkContraction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Algebra.Homology.ModuleStalkExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementObjectFlasque
public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Algebra.Homology.Monoidal

/-! # Cross-scheme naturality of front/back summands

This construction uses only paired cosimplicial objects and natural transformations to pushforward.
No Godement construction or resolution property enters the argument.

## References

* Banerjee, arXiv:1004.1491, §1.1.4
* Stacks, Tag 0FKU
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private def crossComponent (X X' : Scheme.{v}) (f : X' ⟶ X)
    (A : CosimplicialObject X.Modules) (A' : CosimplicialObject X'.Modules)
    (g : A ⟶ A' ⋙ pushforward f) (n : ℤ) :
    (moduleCup_cosimplicialComplex X A).X n ⟶
      (pushforward f).obj ((moduleCup_cosimplicialComplex X' A').X n) :=
  if hn : 0 ≤ n then
    (((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
      ComplexShape.embeddingUpNat (i := n.toNat) (Int.toNat_of_nonneg hn)).hom ≫
      g.app ⦋n.toNat⦌ ≫ (pushforward f).map
        ((((alternatingCofaceMapComplex X'.Modules).obj A').extendXIso
          ComplexShape.embeddingUpNat (i := n.toNat) (Int.toNat_of_nonneg hn)).inv)
  else 0

private theorem crossComponent_nat (X X' : Scheme.{v}) (f : X' ⟶ X)
    (A : CosimplicialObject X.Modules) (A' : CosimplicialObject X'.Modules)
    (g : A ⟶ A' ⋙ pushforward f) (n : ℕ) :
    crossComponent X X' f A A' g (n : ℤ) =
      (((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
        ComplexShape.embeddingUpNat (i := n) rfl).hom ≫ g.app ⦋n⦌ ≫
        (pushforward f).map
          ((((alternatingCofaceMapComplex X'.Modules).obj A').extendXIso
            ComplexShape.embeddingUpNat (i := n) rfl).inv) := by
  simp only [crossComponent, Nat.cast_nonneg, dite_eq_left, Int.toNat_natCast]

private theorem crossComponent_comm (X X' : Scheme.{v}) (f : X' ⟶ X)
    (A : CosimplicialObject X.Modules) (A' : CosimplicialObject X'.Modules)
    (g : A ⟶ A' ⋙ pushforward f) (n : ℤ) :
    crossComponent X X' f A A' g n ≫
        (pushforward f).map ((moduleCup_cosimplicialComplex X' A').d n (n + 1)) =
      (moduleCup_cosimplicialComplex X A).d n (n + 1) ≫
        crossComponent X X' f A A' g (n + 1) := by
  -- In nonnegative degrees, conjugate the alternating coface naturality equation.
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have he : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by simp
    rw [he, crossComponent_nat, crossComponent_nat]
    dsimp only [moduleCup_cosimplicialComplex] at *
    erw [HomologicalComplex.extend_d_eq _ _ (i := m) (j := m + 1) rfl rfl,
      HomologicalComplex.extend_d_eq _ _ (i := m) (j := m + 1) rfl rfl]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]
    have hd : g.app ⦋m⦌ ≫ (pushforward f).map
        (((alternatingCofaceMapComplex X'.Modules).obj A').d m (m + 1)) =
      (((alternatingCofaceMapComplex X.Modules).obj A).d m (m + 1)) ≫ g.app ⦋m + 1⦌ := by
      simp only [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
        CochainComplex.of_d]
      simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul,
        Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
        Preadditive.zsmul_comp]
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun z ↦ ((-1 : ℤ) ^ (i : ℕ)) • z) (g.naturality _).symm
    erw [Functor.map_comp, ← Category.assoc (g.app _) ((pushforward f).map _), hd]
    simp only [Category.assoc]
  -- Every negative source term is zero, including the boundary degree -1.
  · have hz : IsZero ((moduleCup_cosimplicialComplex X A).X n) := by
      apply HomologicalComplex.isZero_extend_X
      intro i hi
      change (i : ℤ) = n at hi
      omega
    exact hz.eq_of_src _ _

private def crossMap (X X' : Scheme.{v}) (f : X' ⟶ X)
    (A : CosimplicialObject X.Modules) (A' : CosimplicialObject X'.Modules)
    (g : A ⟶ A' ⋙ pushforward f) :
    moduleCup_cosimplicialComplex X A ⟶
      ((pushforward f).mapHomologicalComplex (.up ℤ)).obj
        (moduleCup_cosimplicialComplex X' A') :=
  CochainComplex.ofHom (crossComponent X X' f A A' g)
    (crossComponent_comm X X' f A A' g)

end
end AlgebraicGeometry.Scheme.Modules
