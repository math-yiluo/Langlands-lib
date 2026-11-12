import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.Split
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RepresentationTheory.Basic

/-! # Realization of Galois lattices by tori: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Every Galois lattice is the character lattice of a torus** (the torus part of the
essential surjectivity in Milne, *Algebraic Groups* (2017), Theorem 12.23, for actions
factoring through a finite Galois extension). Let `L/k` be a finite Galois extension and let
`M` be a free `ℤ`-module of finite rank with a `ℤ`-linear action `ρ` of `Gal(L/k)`. Then
there is a commutative group scheme `T` over `k` whose base change `T_L` is a split torus,
together with an additive isomorphism `e : M ≃ X^*(T_L)` that intertwines `ρ` with the
Galois action `(σ χ)(t) = σ (χ (σ⁻¹ t))` on the characters of `T_L`. -/
def TorusGaloisLatticeRealizationStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (M : Type u) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (ρ : Representation ℤ (L ≃ₐ[k] L) M),
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (e : M ≃+ characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)),
      IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp ∧
        ∀ (σ : L ≃ₐ[k] L) (m : M),
          e (ρ σ m) = characterLattice.galoisRepresentation k L T σ (e m)

end Langlands.GroupScheme
