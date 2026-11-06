import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.Absolute.TripleCell

/-! # Statement: root groups and the open cell in semisimple rank one -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Root groups, open cell and the rank-one relation** (Conrad, *Reductive group schemes*,
Theorem 4.1.4, Remark 4.2.4 and Theorem 4.2.6 with linked parametrizations, over a field).
Let `i : T ⟶ G` be a split maximal torus of a connected reductive group over a field, with
root datum `P`, such that any two roots are linearly dependent over `ℤ`. For every root
`α = P.root r` there are homomorphisms `xp xm : 𝔾ₐ ⟶ G` such that

* `T` acts on `xp` through `α` and on `xm` through `-α` by conjugation;
* the multiplication `(Y, t, X) ↦ xm(Y) t xp(X)` from `𝔾ₐ × T × 𝔾ₐ` is an open immersion
  (the open cell `Ω`);
* over every test scheme, `xp(X) xm(Y)` lies in `Ω` if and only if `1 + XY` is a unit;
* if `u = 1 + XY` is a unit, then
  `xp(X) xm(Y) = xm(u⁻¹ Y) α^∨(u) xp(u⁻¹ X)`, where `α^∨ = P.coroot r`. -/
def SplitRankOneRootCellStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ (i : T.toGrp ⟶ G), IsMaximalTorus i →
    ∀ (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
      (haveI := hG.isAffineHom; IsRootDatumOf i P) →
      (haveI := hG.isAffineHom
        ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) →
      ∀ r : J, ∃ xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
        (∀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ T.X)
            (a : Z ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
          (t ≫ i.hom.hom) * (a ≫ xp.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
            VectorGroup.weightPointAction (P.root r) Z t a ≫ xp.hom.hom) ∧
        (∀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ T.X)
            (b : Z ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
          (t ≫ i.hom.hom) * (b ≫ xm.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
            VectorGroup.weightPointAction (-P.root r) Z t b ≫ xm.hom.hom) ∧
        IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left ∧
        (∀ (Z : Over (Spec (CommRingCat.of k)))
            (a b : Z ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
          (∃ c, c ≫ Dynamic.tripleCellMultiplication xm i xp =
              (a ≫ xp.hom.hom) * (b ≫ xm.hom.hom)) ↔
            IsUnit (1 + (VectorGroup.coordinates (CommRingCat.of k) 1 Z a).toAdd 0 *
              (VectorGroup.coordinates (CommRingCat.of k) 1 Z b).toAdd 0)) ∧
        (∀ (Z : Over (Spec (CommRingCat.of k)))
            (a b a' b' : Z ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X)
            (u : (Γ(Z.left, ⊤))ˣ),
          (u : Γ(Z.left, ⊤)) = 1 + (VectorGroup.coordinates (CommRingCat.of k) 1 Z a).toAdd 0 *
              (VectorGroup.coordinates (CommRingCat.of k) 1 Z b).toAdd 0 →
          (VectorGroup.coordinates (CommRingCat.of k) 1 Z a').toAdd 0 =
              ↑u⁻¹ * (VectorGroup.coordinates (CommRingCat.of k) 1 Z a).toAdd 0 →
          (VectorGroup.coordinates (CommRingCat.of k) 1 Z b').toAdd 0 =
              ↑u⁻¹ * (VectorGroup.coordinates (CommRingCat.of k) 1 Z b).toAdd 0 →
          (a ≫ xp.hom.hom) * (b ≫ xm.hom.hom) =
            (b' ≫ xm.hom.hom) *
              ((Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom (P.coroot r)).hom.hom ≫
                i.hom.hom) * (a' ≫ xp.hom.hom))

end Langlands.GroupScheme
