import Langlands.GroupScheme.Reductive.AffineReynoldsRegular
import Langlands.GroupScheme.Reductive.InvariantLinearForm
import Langlands.GroupScheme.HomogeneousCharacterCoordinates
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Big-cell and Steinberg data for simply connected groups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open AffineLinearEmbedding MatrixRepresentation

local instance steinbergBigCellInst {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- For a simply connected semisimple group over an algebraically closed field of
positive characteristic there are an actual diagonalizable subgroup `j`, an actual subgroup
map `i : H → G`, a rational point `n` with conjugate subgroup map `i' = i ≫ inn(n)`, a
coordinate `χ` of `H` and a coordinate `d` of `G` such that: `d(i(h) g) = χ(h) d(g)` and
`d(g i'(h)⁻¹) = χ(h) d(g)` on all test schemes; `d(1) = 1`; `d` is a nonzerodivisor;
every test point at which `d` is a unit is a product `i(b) i'(b')⁻¹`; every common test
point of `i` and `i'` comes from `j`; and for cofinally many `e` the coordinates covariant
for `i` of weight `χ ^ e` have a finite basis on which right translation is rationally
irreducible. This is a proposition to be proved, not an assumed theorem. -/
def SteinbergBigCellStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    IsSimplyConnected G →
    ∃ (Λ : Type u) (_ : AddCommGroup Λ)
      (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G)
      (H : GroupScheme (Spec (CommRingCat.of k))) (_ : IsAffineHom H.X.hom)
      (i : H ⟶ G) (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
      (χ : AffineCoordinates.algebra H) (d : AffineCoordinates.algebra G),
      d ∈ AffineCoordinates.leftCovariantSubspace i χ ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
        AffineCoordinates.pointAlgebraHom G T
            (g * (h ≫ (i ≫ (G.innerIso n).hom).hom.hom)⁻¹) d =
          AffineCoordinates.pointAlgebraHom H T h χ *
            AffineCoordinates.pointAlgebraHom G T g d) ∧
      AffineCoordinates.pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 d = 1 ∧
      d ∈ nonZeroDivisors (AffineCoordinates.algebra G) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
        IsUnit (AffineCoordinates.pointAlgebraHom G T g d) →
          ∃ b b' : T ⟶ H.X,
            g = (b ≫ i.hom.hom) * (b' ≫ (i ≫ (G.innerIso n).hom).hom.hom)⁻¹) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (c c' : T ⟶ H.X),
        c ≫ i.hom.hom = c' ≫ (i ≫ (G.innerIso n).hom).hom.hom →
          ∃ t : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X,
            c ≫ i.hom.hom = t ≫ j.hom.hom) ∧
      (∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
        (bX : Module.Basis (Fin m) k (AffineCoordinates.leftCovariantSubspace i (χ ^ e'))),
        (Chevalley.affineRegularRepresentation G _ bX
          (fun f _ hv => AffineCoordinates.rightAct_mem_leftCovariantSubspace i (χ ^ e') f
            hv)).rationalRepresentation.IsIrreducible)

end Langlands.GroupScheme
