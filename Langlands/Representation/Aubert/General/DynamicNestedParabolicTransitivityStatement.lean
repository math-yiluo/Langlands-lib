import Langlands.GroupScheme.Dynamic.NestedParabolic
import Langlands.Representation.Aubert.General.DynamicParabolic
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-! # Normalized transitivity for compatible nested dynamic parabolics -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Aubert.General

/-- Read the supplied all-test nested decomposition inside the actual outer
Levi. This only converts a structural input to the existing functor interface. -/
theorem dynamic_nested_isSemidirectDecomposition_in_levi
    {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
    (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hNested : Dynamic.NestedParabolicDecomposition χ ψ)
    (X : Over (Spec (CommRingCat.of F))) :
    IsSemidirectDecomposition
      (((Dynamic.parabolic χ).carrier X).subgroupOf ((Dynamic.centralizer ψ).carrier X))
      (((Dynamic.centralizer χ).carrier X).subgroupOf ((Dynamic.centralizer ψ).carrier X))
      (((Dynamic.unipotent χ).carrier X).subgroupOf ((Dynamic.centralizer ψ).carrier X)) := by
  obtain ⟨hVP, hMP, hNormal, hComplement, _⟩ := hNested X
  have h : IsSemidirectDecomposition
      ((Dynamic.centralizer ψ).carrier X ⊓ (Dynamic.parabolic χ).carrier X)
      ((Dynamic.centralizer χ).carrier X)
      ((Dynamic.centralizer ψ).carrier X ⊓ (Dynamic.unipotent χ).carrier X) :=
    IsSemidirectDecomposition.of_isComplement'_symm hMP hVP
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hVP).mp hNormal) hComplement
  simpa only [Subgroup.inf_subgroupOf_left] using h.subgroupOf inf_le_left

/-- Renard VI.1.4: both natural transitivity isomorphisms for the actual
normalized functors, with the nested structural decomposition visible. -/
def DynamicNestedParabolicTransitivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hPair : Dynamic.IsCompatibleNestedPair χ ψ)
    (hNested : Dynamic.NestedParabolicDecomposition χ ψ),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    let X := Over.mk (𝟙 (Spec (CommRingCat.of F)))
    ∀ [LocallyCompactSpace (RationalPoint F G.X)]
      [NonarchimedeanGroup (RationalPoint F G.X)]
      (hN : IsClosed ((Dynamic.unipotent χ).carrier X : Set (RationalPoint F G.X)))
      (hU : IsClosed ((Dynamic.unipotent ψ).carrier X : Set (RationalPoint F G.X)))
      (hL : IsClosed ((Dynamic.centralizer ψ).carrier X : Set (RationalPoint F G.X))),
      let hP := dynamic_isSemidirectDecomposition χ X
      let hQ := dynamic_isSemidirectDecomposition ψ X
      let hInner := dynamic_nested_isSemidirectDecomposition_in_levi χ ψ hNested X
      let hML : (Dynamic.centralizer χ).carrier X ≤ (Dynamic.centralizer ψ).carrier X :=
        hPair.2.1 X
      Nonempty
        (normalizedInductionFunctor.{u, uV} hP hN ≅
          leviNormalizedInductionFunctor.{u, uV} hL hML hInner hN ⋙
            normalizedInductionFunctor.{u, max u uV} hQ hU) ∧
      Nonempty
        (jacquetFunctor.{u, uV} hP hN ≅
          jacquetFunctor.{u, uV} hQ hU ⋙
            leviNormalizedJacquetFunctor.{u, uV} hL hML hInner hN)

end Langlands.Aubert.General
