import Langlands.GroupScheme.Reductive.RootDatum
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.Algebra.DirectSum.Module
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Statements: weight decomposition, root data of split reductive groups, and `GL_n` -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Classical in
/-- **Weight decomposition** (Milne 12.12 applied to `Ad`, §21.a). For an affine group scheme
`G` locally of finite type over a field `k`, a split torus `T` and any homomorphism
`i : T ⟶ G`, the Lie algebra `Lie(G)(k)` is the internal direct sum of the weight spaces
`weightSpace i χ`, `χ ∈ X^*(T)`. -/
def WeightDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, DirectSum.IsInternal (weightSpace i)

/-- **Existence of the root datum** (Milne Theorem 21.11 and Corollary 21.12). For a connected
reductive group `G` over a field with a split maximal torus `i : T ⟶ G`, there is a reduced
Mathlib root datum, indexed by a finite type, which is the root datum of `i`. -/
def RootDatumExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      ∃ (J : Type u) (_ : Finite J)
        (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P ∧ P.IsReduced

/-- **Uniqueness of the root datum** (Milne Theorem 21.11, uniqueness of the coroot). Under the
hypotheses of `RootDatumExistenceStatement`, any two root data of `i` differ by a reindexing
which matches both their roots and their coroots. -/
def RootDatumUniquenessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      ∀ (J J' : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T))
        (P' : RootDatum J' (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P → IsRootDatumOf i P' →
          ∃ e : J ≃ J', ⇑P'.root ∘ ⇑e = ⇑P.root ∧ ⇑P'.coroot ∘ ⇑e = ⇑P.coroot

/-- **The Weyl group** (Milne 21.1, Theorem 21.37 and Corollary 21.38). Under the hypotheses of
`RootDatumExistenceStatement`, for every root datum `P` of `i`, the image of the Weyl action of
the normalizer is the image of the Weyl group of `P` in the automorphisms of the character
lattice, and the kernel of the Weyl action is the centralizer. -/
def WeylGroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i),
      haveI := hG.isAffineHom
      haveI : IsClosedImmersion i.hom.hom.left := hi.2.1
      ∀ (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P →
          weylImage i = P.weylGroup.map (RootPairing.Equiv.weightHom P) ∧
            (weylAction i).ker = (centralizerPoints i).subgroupOf (normalizerPoints i)

/-- **The root datum of `GL_n`** (Milne Examples 17.88, 21.6 and 21.40). Over a field `k`, the
diagonal torus of `GL_n` is a maximal torus, its roots are the characters `eᵢ - eⱼ` (`i ≠ j`)
under `characterLatticeEquiv`, `GeneralLinear.rootDatum n k` is its root datum and is reduced,
and the image of its Weyl action is the image of the injective permutation action of `S_n`. -/
def GeneralLinearRootDatumStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : Type) [Fintype n] [DecidableEq n],
    IsMaximalTorus (GeneralLinear.diagonalTorus n (CommRingCat.of k)) ∧
    roots (GeneralLinear.diagonalTorus n (CommRingCat.of k)) =
      {χ | ∃ i j : n, i ≠ j ∧ splitTorus.characterLatticeEquiv k (ULift.{u} n) χ =
        Pi.single (ULift.up i) 1 - Pi.single (ULift.up j) 1} ∧
    IsRootDatumOf (GeneralLinear.diagonalTorus n (CommRingCat.of k))
      (GeneralLinear.rootDatum n k) ∧
    (GeneralLinear.rootDatum n k).IsReduced ∧
    weylImage (GeneralLinear.diagonalTorus n (CommRingCat.of k)) =
      (GeneralLinear.permutationAction n k).range ∧
    Function.Injective (GeneralLinear.permutationAction n k)

end Langlands.GroupScheme
