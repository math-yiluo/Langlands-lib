import Langlands.AbelianScheme.Tate.Topology

/-! # Positive multiplication on the actual full and away Tate limits -/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- Positive multiplication embeds the full limit with open image and its original topology. -/
def FullMultiplicationOpenEmbeddings : Prop :=
  ∀ n : ℕ, 0 < n → Topology.IsOpenEmbedding (fun x : Full G T => n • x)

/-- Positive multiplication embeds the away limit with open image and its original topology. -/
def AwayMultiplicationOpenEmbeddings (m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → Topology.IsOpenEmbedding (fun x : Away G T m => n • x)

/-- The full limit and every away limit satisfy the positive-multiplication lattice condition. -/
def MultiplicationOpenEmbeddings : Prop :=
  FullMultiplicationOpenEmbeddings G T ∧
    ∀ m : ℕ, AwayMultiplicationOpenEmbeddings G T m

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate

universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)

/-- Full positive-multiplication condition on the actual abelian-scheme Tate group. -/
abbrev FullMultiplicationOpenEmbeddings : Prop :=
  GroupScheme.Tate.FullMultiplicationOpenEmbeddings A.toGrp T

/-- Away positive-multiplication condition on the actual abelian-scheme Tate group. -/
abbrev AwayMultiplicationOpenEmbeddings (m : ℕ) : Prop :=
  GroupScheme.Tate.AwayMultiplicationOpenEmbeddings A.toGrp T m

/-- Both positive-multiplication conditions specialized to an actual abelian scheme. -/
abbrev MultiplicationOpenEmbeddings : Prop :=
  GroupScheme.Tate.MultiplicationOpenEmbeddings A.toGrp T

end Langlands.AbelianScheme.Tate
