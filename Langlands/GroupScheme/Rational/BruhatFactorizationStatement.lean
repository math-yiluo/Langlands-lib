import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.SubgroupIntersection

/-! # The unipotent scheme product for a rational Bruhat cell -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BruhatFactorization

/-- Multiplication of the two scheme-theoretic intersections, with codomain the
common subgroup. The factors are projected into `U` before multiplication. -/
def multiplication {S : Scheme.{u}} {G U A B : GroupScheme S}
    (iU : U ⟶ G) (iA : A ⟶ G) (iB : B ⟶ G) :
    (subgroupIntersection iU iA).X ⊗ (subgroupIntersection iU iB).X ⟶ U.X :=
  (fst _ _ ≫ (subgroupIntersectionFst iU iA).hom.hom) *
    (snd _ _ ≫ (subgroupIntersectionFst iU iB).hom.hom)

end BruhatFactorization

/-- The scheme multiplication `(U ∩ n V n⁻¹) × (U ∩ n U n⁻¹) ⟶ U` is an
isomorphism for a rational normalizer representative of a maximal split torus.
Here `U` and `V` are the unipotent subgroups of a generic cocharacter and its inverse. -/
def RationalBruhatFactorizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i → ∀ ν : cocharacterLattice T,
    letI := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsGenericCocharacter i ν → ∀ n : normalizerPoints i,
      let χ := CommGroupScheme.groupHom ν ≫ i
      let ψ := χ ≫ (G.innerIso n.val).hom
      let ψminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ ψ
      IsIso (BruhatFactorization.multiplication (Dynamic.Affine.unipotentHom χ)
        (Dynamic.Affine.unipotentHom ψminus) (Dynamic.Affine.unipotentHom ψ))

end Langlands.GroupScheme
