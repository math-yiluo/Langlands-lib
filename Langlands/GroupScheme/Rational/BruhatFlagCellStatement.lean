import Langlands.GroupScheme.Dynamic.FlagQuotientSections
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Rational.Statement
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Rational Bruhat cells in the flag quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BruhatFlagCell

variable {k : Type u} [Field k]
  {G U V : GroupScheme (Spec (CommRingCat.of k))}
  (u : U ⟶ G) (v : V ⟶ G)
  {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
  (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)

/-- The flag map `a ↦ a n P` from the intersection `n V n⁻¹ ∩ U`. -/
def parametrization : (subgroupIntersection (v ≫ (G.innerIso n).hom) u).X ⟶ Q :=
  (subgroupIntersectionFst (v ≫ (G.innerIso n).hom) u).hom.hom ≫ v.hom.hom ≫
    (Dynamic.rationalLeftTranslation k G n).hom ≫ q

end BruhatFlagCell

/-- The translated unipotent intersections give locally closed maps into a
represented minimal-parabolic quotient. They parametrize the parabolic orbits
and partition the rational points by the relative Weyl group. -/
def RationalBruhatFlagCellStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i → ∀ ν : cocharacterLattice T,
    letI := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsGenericCocharacter i ν →
    let χ := CommGroupScheme.groupHom ν ≫ i
    let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
    let u := Dynamic.Affine.unipotentHom χ
    let v := Dynamic.Affine.unipotentHom χminus
    let S₀ := Over.mk (𝟙 (Spec (CommRingCat.of k)))
    ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q)
      [Smooth q.left] [Surjective q.left] [QuasiCompact q.left],
      (∀ (X : Over (Spec (CommRingCat.of k))) (g h : X ⟶ G.X),
        g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier X) →
      let cell : normalizerPoints i → Set (S₀ ⟶ Q) := fun n =>
        Set.range (fun x => x ≫ BruhatFlagCell.parametrization u v q n.val)
      (∀ n : normalizerPoints i, IsImmersion (BruhatFlagCell.parametrization u v q n.val).left ∧
        ∀ x : S₀ ⟶ Q, x ∈ cell n ↔
          ∃ p ∈ (Dynamic.parabolic χ).carrier S₀, (p * n.val) ≫ q = x) ∧
      ∃ cells : relativeWeylGroup i → Set (S₀ ⟶ Q),
        (∀ n : normalizerPoints i, cells (QuotientGroup.mk n) = cell n) ∧
        ∀ x : S₀ ⟶ Q, ∃! w, x ∈ cells w

end Langlands.GroupScheme
