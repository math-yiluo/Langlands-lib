import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.RepresentationTheory.Basic

/-! # Realization of Galois modules by groups of multiplicative type: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Every finitely generated Galois module is the character module of a group of
multiplicative type** (the essential surjectivity in Milne, *Algebraic Groups* (2017),
Theorem 12.23, for actions factoring through a finite Galois extension). Let `L/k` be a finite
Galois extension and let `M` be a finitely generated abelian group with a `ℤ`-linear action
`ρ` of `Gal(L/k)`. Then there are a commutative group scheme `T` over `k`, an isomorphism
`T_L ≅ D_L(M)` with the diagonalizable group of `M` over `L`, and an additive isomorphism
`e : M ≃ X^*(T_L)` such that `e m` is the character `t ↦ t(m)` of `D_L(M)` transported to
`T_L`, and `e` intertwines `ρ` with the Galois action on the characters of `T_L`. -/
def MultiplicativeTypeGaloisModuleRealizationStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (M : Type u) [AddCommGroup M] [AddGroup.FG M] (ρ : Representation ℤ (L ≃ₐ[k] L) M),
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T ≅
        Diagonalizable.groupScheme (CommRingCat.of L) M)
      (e : M ≃+ characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)),
      (∀ (m : M) (U : Over (Spec (CommRingCat.of L)))
        (x : U ⟶ ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).X),
        Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom (e m)).hom.hom) =
          Diagonalizable.characterPointsEquiv (CommRingCat.of L) M U
            (x ≫ (CommGroupScheme.groupHom i.hom).hom.hom) (Multiplicative.ofAdd m)) ∧
      ∀ (σ : L ≃ₐ[k] L) (m : M),
        e (ρ σ m) = characterLattice.galoisRepresentation k L T σ (e m)

end Langlands.GroupScheme
