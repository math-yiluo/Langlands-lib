import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic
import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Torus.Lattice

/-! # Relative roots and the minimal parabolic of the quasi-split unitary group `U(1,1)`:
statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- For a nontrivial conjugation `c`, the diagonal cocharacter `λ : t ↦ diag(t, t⁻¹)` of
`U(1,1)` over `F` is a maximal split torus, its relative roots are the two characters
`t ↦ t ^ 2` and `t ↦ t ^ (-2)` of `𝔾_m`, the identity cocharacter of `𝔾_m` is generic for
`λ`, and for every generic cocharacter `ν` of `𝔾_m` the dynamic parabolic subgroup of
`ν ≫ λ` is a minimal rational parabolic subgroup functor whose dynamic Levi subgroup is the
centralizer of `λ`. -/
def RelativeRootsStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    (κ : Type u) [Fintype κ] (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
    (c : E ≃ₐ[F] E), c ≠ AlgEquiv.refl →
      IsMaximalSplitTorus (cocharacter b c) ∧
      relativeRoots (cocharacter b c) =
        {Gm.powerHom (Spec (CommRingCat.of F)) 2,
          Gm.powerHom (Spec (CommRingCat.of F)) (-2)} ∧
      IsGenericCocharacter (cocharacter b c) (𝟙 (Gm (Spec (CommRingCat.of F)))) ∧
      ∀ ν : cocharacterLattice (Gm (Spec (CommRingCat.of F))),
        IsGenericCocharacter (cocharacter b c) ν →
          IsMinimalParabolicFunctor
              (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ cocharacter b c)) ∧
            Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ cocharacter b c) =
              torusCentralizer (cocharacter b c)

end Langlands.GroupScheme.QuasiSplitUnitary
