import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: centre and derived group of `GL_n`, and perfectness of `PGL_n`
(Milne 6.22, 12.47) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Centre and derived group of `GL_n`** (Milne, *Algebraic Groups*, Example 6.22 and
Example 12.47). Let `k` be a field, `n` a natural number and `G = GL_n` over `k`.
1. A point `g` of `G` over a test scheme `T` lies in the centre of `G` exactly when its matrix
   is a scalar matrix `u • 1` for a unit `u` of `Γ(T, 𝒪_T)`. For `n ≥ 1` the scalar map
   `u ↦ u • 1` is injective, so the centre is `𝔾_m`. For `n = 0` the group `GL_0` and its
   centre are trivial, and every unit gives the same empty matrix.
2. The inclusion `SL_n → GL_n` exhibits the derived group of `GL_n`.
3. Every fppf quotient of `GL_n` by its centre (for `n ≥ 1`, `PGL_n = GL_n / 𝔾_m`) is perfect:
   its derived subgroup is everything.

This is a statement only; nothing is proved here. -/
def GeneralLinearCenterDerivedStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    let G := GeneralLinear.groupScheme (Fin n) (CommRingCat.of k)
    (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
        g ∈ (center G).carrier T ↔
          ∃ u : Γ(T.left, ⊤)ˣ,
            ((GeneralLinear.pointsEquiv (Fin n) (CommRingCat.of k) T g :
                GL (Fin n) Γ(T.left, ⊤)) : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) =
              Matrix.scalar (Fin n) (u : Γ(T.left, ⊤))) ∧
      IsDerivedSubgroup (SpecialLinear.inclusion (Fin n) (CommRingCat.of k)) ∧
      ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
        RelativeRoot.IsFppfQuotient (center G) q → derivedSubgroup Q = ⊤

end Langlands.GroupScheme
