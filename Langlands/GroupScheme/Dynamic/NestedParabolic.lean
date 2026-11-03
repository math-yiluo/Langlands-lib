import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Dynamic.Decomposition

/-! # Compatible nested dynamic parabolics and their decomposition predicate -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- The nested Levi formulas on every test scheme. The normality and complement
clauses express the semidirect decomposition of `L ∩ P` with Levi `M`. -/
def NestedLeviDecomposition (P M N L U : SubgroupFunctor G) : Prop :=
  ∀ X : Over S,
    let H := (L ⊓ P).carrier X
    let V := (L ⊓ N).carrier X
    let W := M.carrier X
    V ≤ H ∧ W ≤ H ∧ (V.subgroupOf H).Normal ∧
      (V.subgroupOf H).IsComplement' (W.subgroupOf H) ∧
      (↑H : Set (X ⟶ G.X)) = (↑W : Set (X ⟶ G.X)) * (↑V : Set (X ⟶ G.X)) ∧
      (↑(N.carrier X) : Set (X ⟶ G.X)) =
        (↑V : Set (X ⟶ G.X)) * (↑(U.carrier X) : Set (X ⟶ G.X)) ∧
      (↑(P.carrier X) : Set (X ⟶ G.X)) =
        (↑H : Set (X ⟶ G.X)) * (↑(U.carrier X) : Set (X ⟶ G.X))

/-- Evaluation at the identity test gives the same three products of actual
point subgroups. Over a field these are the rational-point formulas. -/
theorem NestedLeviDecomposition.identityTest_products
    {P M N L U : SubgroupFunctor G} (h : NestedLeviDecomposition P M N L U) :
    let X := Over.mk (𝟙 S)
    (↑((L ⊓ P).carrier X) : Set (X ⟶ G.X)) =
        (↑(M.carrier X) : Set (X ⟶ G.X)) *
          (↑((L ⊓ N).carrier X) : Set (X ⟶ G.X)) ∧
      (↑(N.carrier X) : Set (X ⟶ G.X)) =
        (↑((L ⊓ N).carrier X) : Set (X ⟶ G.X)) *
          (↑(U.carrier X) : Set (X ⟶ G.X)) ∧
      (↑(P.carrier X) : Set (X ⟶ G.X)) =
        (↑((L ⊓ P).carrier X) : Set (X ⟶ G.X)) *
          (↑(U.carrier X) : Set (X ⟶ G.X)) := by
  exact (h (Over.mk (𝟙 S))).2.2.2.2

end SubgroupFunctor

namespace Dynamic

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (χ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- The two dynamic parabolics are nested with nested Levis, and their defining
cocharacters are realized in one ambient maximal split torus. -/
def IsCompatibleNestedPair : Prop :=
  parabolic χ ≤ parabolic ψ ∧ centralizer χ ≤ centralizer ψ ∧
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (α β : cocharacterLattice T),
      IsMaximalSplitTorus i ∧
        CommGroupScheme.groupHom α ≫ i = χ ∧
        CommGroupScheme.groupHom β ≫ i = ψ

/-- The conclusion of the nested decomposition theorem, evaluated on the actual
dynamic subgroup functors. -/
abbrev NestedParabolicDecomposition : Prop :=
  SubgroupFunctor.NestedLeviDecomposition
    (parabolic χ) (centralizer χ) (unipotent χ) (centralizer ψ) (unipotent ψ)

theorem IsCompatibleNestedPair.parabolic_le (h : IsCompatibleNestedPair χ ψ) :
    parabolic χ ≤ parabolic ψ :=
  h.1

theorem IsCompatibleNestedPair.centralizer_le (h : IsCompatibleNestedPair χ ψ) :
    centralizer χ ≤ centralizer ψ :=
  h.2.1

/-- A pair of cocharacters of a common maximal split torus is compatible when
the parabolic and centralizer inclusions hold. -/
theorem isCompatibleNestedPair_of_torus
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (α β : cocharacterLattice T)
    (hP : parabolic (CommGroupScheme.groupHom α ≫ i) ≤
      parabolic (CommGroupScheme.groupHom β ≫ i))
    (hL : centralizer (CommGroupScheme.groupHom α ≫ i) ≤
      centralizer (CommGroupScheme.groupHom β ≫ i)) :
    IsCompatibleNestedPair (CommGroupScheme.groupHom α ≫ i)
      (CommGroupScheme.groupHom β ≫ i) :=
  ⟨hP, hL, T, i, α, β, hi, rfl, rfl⟩

end Dynamic

end Langlands.GroupScheme
