import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Dynamic.GeneralLinear
import Mathlib.GroupTheory.Complement

/-! # Dynamic subgroups of `GL_n` for diagonal cocharacters: statements -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

/-- Conrad–Gabber–Prasad, Example 2.1.1, for `GL_n` over every commutative ring `R`: for the
diagonal cocharacter `t ↦ diag(t ^ e i)`, the dynamic subgroup functors `P(λ)`, `Z(λ)` and `U(λ)`
on all schemes over `Spec R` are the block parabolic, block Levi and block unipotent subgroup
functors of the weights `e`. -/
def DiagonalCocharacterDynamicStatement : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}) (e : n → ℤ),
    Dynamic.parabolic (diagonalCocharacter n R e) = blockParabolic n R e ∧
      Dynamic.centralizer (diagonalCocharacter n R e) = blockLevi n R e ∧
      Dynamic.unipotent (diagonalCocharacter n R e) = blockUnipotent n R e

/-- The same computation for the standard cocharacter of an ordered block shape `B`, stated with
the subgroup functors built from the Library's `B.parabolic`, `B.leviSubgroup` and
`B.unipotentSubgroup`. -/
def BlockShapeDynamicStatement : Prop :=
  ∀ (N : ℕ) (B : Langlands.GeneralLinear.BlockShape N) (R : CommRingCat.{u}),
    Dynamic.parabolic (blockShapeCocharacter B R) = blockShapeParabolic B R ∧
      Dynamic.centralizer (blockShapeCocharacter B R) = blockShapeLevi B R ∧
      Dynamic.unipotent (blockShapeCocharacter B R) = blockShapeUnipotent B R

/-- Conrad–Gabber–Prasad, Lemma 2.1.5 and Proposition 2.1.8(2), for `GL_n` and a diagonal
cocharacter over every commutative ring: a point `g` over any test scheme `T` has the limit `l`
at `t = 0` of its conjugation orbit exactly when `g` is block upper triangular for the weights
`e`, and then `l` is the block diagonal part of `g`. -/
def DiagonalCocharacterLimitStatement : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}) (e : n → ℤ)
    (T : Over (Spec R)) (g l : T ⟶ (groupScheme n R).X),
    Dynamic.HasLimit (diagonalCocharacter n R e) g l ↔
      ∃ hg : g ∈ (blockParabolic n R e).carrier T,
        pointsEquiv n R T l = blockLeviProjection Γ(T.left, ⊤) e ⟨pointsEquiv n R T g, hg⟩

/-- Conrad–Gabber–Prasad, Proposition 2.1.8(2), for `GL_n` and a diagonal cocharacter over
every commutative ring, on the points over every test scheme `T`: inside the group of points of
`P(λ)`, the points of `U(λ)` form a normal subgroup and the points of `Z(λ)` form a complement
of it. -/
def DiagonalCocharacterLeviDecompositionStatement : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}) (e : n → ℤ)
    (T : Over (Spec R)),
    (((Dynamic.unipotent (diagonalCocharacter n R e)).carrier T).subgroupOf
        ((Dynamic.parabolic (diagonalCocharacter n R e)).carrier T)).Normal ∧
      (((Dynamic.unipotent (diagonalCocharacter n R e)).carrier T).subgroupOf
          ((Dynamic.parabolic (diagonalCocharacter n R e)).carrier T)).IsComplement'
        (((Dynamic.centralizer (diagonalCocharacter n R e)).carrier T).subgroupOf
          ((Dynamic.parabolic (diagonalCocharacter n R e)).carrier T))

/-- The limit computation for the standard cocharacter of an ordered block shape `B`, in terms
of the Library's `B.parabolic`, `B.leviProjection` and `B.leviEmbedding`. -/
def BlockShapeLimitStatement : Prop :=
  ∀ (N : ℕ) (B : Langlands.GeneralLinear.BlockShape N) (R : CommRingCat.{u})
    (T : Over (Spec R)) (g l : T ⟶ (groupScheme (Fin N) R).X),
    Dynamic.HasLimit (blockShapeCocharacter B R) g l ↔
      ∃ hg : pointsEquiv (Fin N) R T g ∈ B.parabolic Γ(T.left, ⊤),
        pointsEquiv (Fin N) R T l =
          B.leviEmbedding Γ(T.left, ⊤) (B.leviProjection Γ(T.left, ⊤) ⟨_, hg⟩)

/-- The five statements of this module together: the dynamic subgroups, the limit map and the
decomposition of `P(λ)` for diagonal and block-shape cocharacters of `GL_n`. -/
def DynamicStatement : Prop :=
  DiagonalCocharacterDynamicStatement.{u} ∧ BlockShapeDynamicStatement.{u} ∧
    DiagonalCocharacterLimitStatement.{u} ∧ DiagonalCocharacterLeviDecompositionStatement.{u} ∧
    BlockShapeLimitStatement.{u}

end Langlands.GroupScheme.GeneralLinear
