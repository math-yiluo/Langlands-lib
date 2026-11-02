import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Dynamic.Basic

/-! # Split components and rational characters of connected reductive groups

Statements, without proofs: existence and uniqueness of the split component `A_G`, finiteness of
the rational characters `X^*(G)_k`, the finite-index restriction `X^*(G)_k → X^*(A_G)`, split
components of Levi subgroups `Z_G(μ)`, and the case of `GL_n` and its block Levi subgroups.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field `k`, a connected reductive group `G` has a split component, and any two split
components `i : A ⟶ G` and `i' : A' ⟶ G` are isomorphic over `G`: there is `e : A ≅ A'` with
`e.hom ≫ i' = i`. -/
def SplitComponentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    (∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (i : A.toGrp ⟶ G), IsSplitComponent i) ∧
    ∀ (A A' : CommGroupScheme (Spec (CommRingCat.of k))) (i : A.toGrp ⟶ G) (i' : A'.toGrp ⟶ G),
      IsSplitComponent i → IsSplitComponent i' → ∃ e : A.toGrp ≅ A'.toGrp, e.hom ≫ i' = i

/-- Over every field `k`, the rational characters `X^*(G)_k` of a connected reductive group `G`
form a free `ℤ`-module of finite rank. -/
def RationalCharacterLatticeStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    Module.Free ℤ (rationalCharacters G) ∧ Module.Finite ℤ (rationalCharacters G)

/-- Over every field `k`, for a split component `i : A ⟶ G` of a connected reductive group `G`,
restriction `X^*(G)_k → X^*(A)` is injective and its range has finite index. -/
def CharacterRestrictionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (i : A.toGrp ⟶ G), IsSplitComponent i →
      Function.Injective (characterRestrict i) ∧ (characterRestrict i).range.FiniteIndex

/-- Over every field `k`, let `i : T ⟶ G` be a maximal split torus of a connected reductive group
`G`, `μ` a cocharacter of `T`, and `j : M ⟶ G` a closed subgroup representing the centralizer
`Z_G(μ)` of `μ ≫ i`. Then `M` is connected reductive, and every split component `A_G` of `G`
factors through a split component `A_M` of `M` that factors through `i`, so that
`A_G ⊆ A_M ⊆ M ⊆ G`, and the restrictions `X^*(G)_k → X^*(M)_k → X^*(A_M) → X^*(A_G)` compose to
the restriction `X^*(G)_k → X^*(A_G)`. -/
def LeviSplitComponentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
    ∀ (μ : cocharacterLattice T) (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
      IsClosedSubgroup j →
      (Dynamic.centralizer (CommGroupScheme.groupHom μ ≫ i)).IsRepresentedBy j →
      IsConnectedReductive M ∧
      ∀ (A_G : CommGroupScheme (Spec (CommRingCat.of k))) (iG : A_G.toGrp ⟶ G),
        IsSplitComponent iG →
        ∃ (A_M : CommGroupScheme (Spec (CommRingCat.of k))) (iM : A_M.toGrp ⟶ M)
          (f : A_G.toGrp ⟶ A_M.toGrp) (g : A_M.toGrp ⟶ T.toGrp),
          IsSplitComponent iM ∧ f ≫ iM ≫ j = iG ∧ g ≫ i = iM ≫ j ∧
            (characterRestrict f).comp ((characterRestrict iM).comp (characterRestrict j)) =
              characterRestrict iG

/-- Over every field `k` and for every `n`: the rational characters of `GL_n` are the integer
multiples of the determinant, freely for `n ≥ 1`, and zero for `n = 0`; for `n ≥ 1` the scalar
torus is a split component of `GL_n`; the determinant restricts to the scalar torus as `n` times
the identity character of `𝔾_m`. For every block shape `B` of `N`, the block determinants form a
basis of the rational characters of the block Levi subgroup scheme of `GL_N`. -/
def GeneralLinearCharactersStatement : Prop :=
  ∀ (k : Type u) [Field k],
    (∀ n : ℕ,
      (∀ χ : rationalCharacters (GeneralLinear.groupScheme (Fin n) (CommRingCat.of k)),
        ∃ m : ℤ, χ = m • GeneralLinear.determinantCharacter (Fin n) (CommRingCat.of k)) ∧
      (n = 0 →
        ∀ χ : rationalCharacters (GeneralLinear.groupScheme (Fin n) (CommRingCat.of k)),
          χ = 0) ∧
      (1 ≤ n → ∀ m : ℤ,
        m • GeneralLinear.determinantCharacter (Fin n) (CommRingCat.of k) = 0 → m = 0) ∧
      (1 ≤ n → IsSplitComponent (GeneralLinear.scalarTorus (Fin n) (CommRingCat.of k))) ∧
      characterRestrict (GeneralLinear.scalarTorus (Fin n) (CommRingCat.of k))
          (GeneralLinear.determinantCharacter (Fin n) (CommRingCat.of k)) =
        n • Additive.ofMul (𝟙 (Gm (Spec (CommRingCat.of k))).toGrp)) ∧
    ∀ (N : ℕ) (B : Langlands.GeneralLinear.BlockShape N),
      ∃ b : Module.Basis (Fin B.length) ℤ
          (rationalCharacters (GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
            (GeneralLinear.blockShapeWeight B))),
        ∀ i, b i = GeneralLinear.blockDeterminantCharacter (CommRingCat.of k) B i

end Langlands.GroupScheme
