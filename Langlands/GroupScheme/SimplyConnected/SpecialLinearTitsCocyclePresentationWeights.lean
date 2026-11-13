import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocyclePresentation
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleWeights

/-! # Diagonal weights of the finite Galois special-linear presentation -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {d : TitsIndexData G} {n : ℕ}
  {e : d.Vertex ≃ Fin n}

/-- The diagonal characters of the original maximal split torus supplied by the
finite Galois coordinate presentation. -/
def Presentation.diagonalWeights (p : Presentation d e) (i : Fin (n + 1)) :
    characterLattice d.splitTorus :=
  stageDiagonalWeight d p.stage p.torusIso p.coordinate i

/-- The transported numbering identifies each stage simple-root index with the
original simple-root index carrying the same number. -/
theorem Presentation.numbering_index (p : Presentation d e) (i : Fin n) :
    p.rootEquiv.indexEquiv (p.numbering.symm i).val = (e.symm i).val := by
  have h : (p.rootEquiv.indexEquiv.subtypeEquiv p.base_iff)
      (p.numbering.symm i) = e.symm i := by
    apply e.injective
    change p.numbering (p.numbering.symm i) = e (e.symm i)
    simp only [Equiv.apply_symm_apply]
  exact congrArg Subtype.val h

/-- The original numbered simple-root restriction is the difference of the two
adjacent diagonal characters of the presentation. -/
theorem Presentation.rootRestriction_diagonalWeights (p : Presentation d e) (i : Fin n) :
    d.rootRestriction (e.symm i).val =
      p.diagonalWeights i.castSucc - p.diagonalWeights i.succ := by
  let : Algebra p.L (SeparableClosure K) := p.embedding.toRingHom.toAlgebra
  exact numbered_rootRestriction_stageDiagonalWeight_sub d p.stage p.torusIso
    p.coordinate p.tower_commutes p.rootEquiv p.weight_eq e p.numbering_index i

/-- The actual local group-scheme presentation carries every point of the original
maximal split torus to the diagonal matrix of its diagonal characters. -/
theorem Presentation.diagonal (p : Presentation d e)
    (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K p.L)
    (s : Z ⟶ d.splitTorus.X) :
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
        ((p.localIso.toFun a).symm (s ≫ d.splitInclusion.hom.hom)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      Matrix.diagonal fun i =>
        ((Gm.pointsEquiv _ Z
          (s ≫ (CommGroupScheme.groupHom (p.diagonalWeights i)).hom.hom) :
          Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
  exact diagonal_stageDiagonalWeight d p.stage p.torusIso p.coordinate
    p.inclusion_eq p.localIso p.localIso_toBaseChangeIso_hom Z a s

end Langlands.GroupScheme.SpecialLinearTitsCocycle
