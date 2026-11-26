import Langlands.GroupScheme.Dynamic.FlagQuotientSections
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Langlands.GroupScheme.Rational.Statement
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Locally closed multiplication for a rational Bruhat double coset -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BruhatCell

variable {k : Type u} [Field k]
  {G U V P : GroupScheme (Spec (CommRingCat.of k))}
  (u : U ⟶ G) (v : V ⟶ G) (p : P ⟶ G)
  (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)

/-- The actual intersection `n V n⁻¹ ∩ U`. Projection to `V` followed by the
conjugated inclusion of `V` is the inclusion of the intersection into `G`. -/
abbrev factor : GroupScheme (Spec (CommRingCat.of k)) :=
  subgroupIntersection (v ≫ (G.innerIso n).hom) u

/-- The map `(a,p') ↦ a n p'`, with `a` a point of the intersection.
It first uses the coordinate `n⁻¹ a n` in `V`, then multiplies by the
point of `P`, and finally translates on the left by `n`. -/
def parametrization : (factor u v n).X ⊗ P.X ⟶ G.X :=
  ((subgroupIntersectionFst (v ≫ (G.innerIso n).hom) u).hom.hom ⊗ₘ 𝟙 P.X) ≫
    SubgroupFunctor.cellMultiplication v p ≫ (Dynamic.rationalLeftTranslation k G n).hom

end BruhatCell

/-- For a generic cocharacter of a maximal split torus, the actual Bruhat
multiplication morphism for each rational normalizer representative is a
locally closed immersion and parametrizes its parabolic double coset on
rational points. -/
def RationalBruhatCellStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i → ∀ ν : cocharacterLattice T,
    letI := hG.isAffineHom
    IsGenericCocharacter i ν →
    let χ := CommGroupScheme.groupHom ν ≫ i
    let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
    ∀ (P U V : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (u : U ⟶ G) (v : V ⟶ G),
      (Dynamic.parabolic χ).IsRepresentedBy p →
      (Dynamic.unipotent χ).IsRepresentedBy u → IsClosedSubgroup u →
      (Dynamic.unipotent χminus).IsRepresentedBy v →
      ∀ n : normalizerPoints i,
        let f := BruhatCell.parametrization u v p n.val
        IsImmersion f.left ∧
          ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
            (∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (BruhatCell.factor u v n.val).X ⊗ P.X,
              x ≫ f = g) ↔
            ∃ a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X,
              g = (a ≫ p.hom.hom) * n.val * (b ≫ p.hom.hom)

end Langlands.GroupScheme
