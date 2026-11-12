import Langlands.Representation.Hecke.CornerAction
import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Smooth.FixedVectors.Definitions
import Langlands.Representation.Category.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-! # Fixed vectors of a compact open subgroup (Renard III.1.5)

The Proposition and the Theorem of Renard III.1.5 for smooth complex representations of a
locally profinite group, stated with the published fixed-vector projection `π(e_K)`, the
published corner `H(G, K)` of the Haar Hecke algebra and its published action on `V^K`.
-/

namespace Langlands.Hecke

open MeasureTheory

universe u v

/-- Renard III.1.5, Proposition (ii)–(iii): the kernel of `π(e_K)` is the span `V(K)` of the
vectors `π(e_K) v - v`, and `V = V^K ⊕ V(K)`. -/
def FixedProjectionKernelStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (A : SmoothRep.{0, u, v} ℂ G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
    LinearMap.ker (fixedProjection μ A.representation A.isSmooth K hK) =
        Submodule.span ℂ (Set.range fun x : A =>
          ((fixedProjection μ A.representation A.isSmooth K hK x : A) - x)) ∧
      IsCompl (fixedVectors A.representation K.toSubgroup)
        (LinearMap.ker (fixedProjection μ A.representation A.isSmooth K hK))

/-- Renard III.1.5, Proposition (iv): the functor `j_K : V ↦ V^K` is exact. For composable
morphisms `f : A ⟶ B` and `g : B ⟶ C` of smooth representations with `im f = ker g`, the
restrictions to `K`-fixed vectors satisfy `im (f^K) = ker (g^K)`. -/
def FixedVectorsExactStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (A B C : SmoothRep.{0, u, v} ℂ G) (f : A ⟶ B) (g : B ⟶ C) (K : OpenSubgroup G),
    IsCompact (K : Set G) →
    LinearMap.range (SmoothRep.hom f).toLinearMap = LinearMap.ker (SmoothRep.hom g).toLinearMap →
      LinearMap.range (fixedVectorsMap (SmoothRep.hom f) K.toSubgroup) =
        LinearMap.ker (fixedVectorsMap (SmoothRep.hom g) K.toSubgroup)

/-- Renard III.1.5, Theorem (i): a smooth representation is irreducible or zero if and only
if, for every compact open subgroup `K`, its `K`-fixed space is a simple or zero module over
the corner `H(G, K)`. -/
def IrreducibleIffFixedSimpleStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (A : SmoothRep.{0, u, v} ℂ G),
    (A.IsIrreducible ∨ Subsingleton A) ↔
      ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
        letI := cornerModule μ A.representation A.isSmooth K hK
        IsSimpleModule (HeckeAlgebra.Corner μ K hK)
            (fixedVectors A.representation K.toSubgroup) ∨
          fixedVectors A.representation K.toSubgroup = ⊥

/-- Renard III.1.5, Theorem (ii): two irreducible smooth representations with nonzero
`K`-fixed vectors are equivalent if and only if their `K`-fixed spaces are isomorphic
`H(G, K)`-modules. -/
def IrreducibleEquivIffFixedEquivStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (A B : SmoothRep.{0, u, v} ℂ G),
    A.IsIrreducible → B.IsIrreducible →
    ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
      fixedVectors A.representation K.toSubgroup ≠ ⊥ →
      fixedVectors B.representation K.toSubgroup ≠ ⊥ →
        letI := cornerModule μ A.representation A.isSmooth K hK
        letI := cornerModule μ B.representation B.isSmooth K hK
        (Nonempty (A.representation.Equiv B.representation) ↔
          Nonempty (fixedVectors A.representation K.toSubgroup ≃ₗ[HeckeAlgebra.Corner μ K hK]
            fixedVectors B.representation K.toSubgroup))

/-- Renard III.1.5, Theorem (iii): every simple `H(G, K)`-module is the `K`-fixed space of an
irreducible smooth representation, whose carrier lies in a universe containing those of `G`
and of the module. -/
def SimpleCornerModuleRealizationStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (W : Type v) [AddCommGroup W] [Module (HeckeAlgebra.Corner μ K hK) W],
    IsSimpleModule (HeckeAlgebra.Corner μ K hK) W →
      ∃ A : SmoothRep.{0, u, max u v} ℂ G, A.IsIrreducible ∧
        letI := cornerModule μ A.representation A.isSmooth K hK
        Nonempty (fixedVectors A.representation K.toSubgroup ≃ₗ[HeckeAlgebra.Corner μ K hK] W)

/-- The Proposition and the Theorem of Renard III.1.5. -/
def FixedVectorCornerStatements : Prop :=
  FixedProjectionKernelStatement.{u, v} ∧ FixedVectorsExactStatement.{u, v} ∧
    IrreducibleIffFixedSimpleStatement.{u, v} ∧ IrreducibleEquivIffFixedEquivStatement.{u, v} ∧
    SimpleCornerModuleRealizationStatement.{u, v}

end Langlands.Hecke
