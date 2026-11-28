import Langlands.GroupScheme.Absolute.SplitTorusDynamicDescent
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.QuasiSplitAdaptedSplitTorus
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Conjugacy and field descent of cocharacters for split reductive groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Any cocharacter of a split connected reductive group after algebraic scalar
extension is conjugate by a point over that extension to a ground-field cocharacter. -/
def SplitCocharacterConjugacyDescentStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (G : GroupScheme (Spec (CommRingCat.of K))),
    IsConnectedReductive G → HasSplitMaximalTorus G →
    let b := algebraBaseMap K L
    let Gₗ := (GroupScheme.baseChange b).obj G
    ∀ χ : (Gm (Spec (CommRingCat.of L))).toGrp ⟶ Gₗ,
      ∃ (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ G)
        (g : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶ Gₗ.X),
        Dynamic.baseChangeCocharacter b ν ≫ (Gₗ.innerIso g).hom = χ

set_option backward.isDefEq.respectTransparency false in
/-- Conjugate into the base change of a split maximal torus, then descend the
resulting cocharacter in the unchanged integral lattice of that torus. -/
theorem splitCocharacterConjugacyDescent : SplitCocharacterConjugacyDescentStatement.{u} := by
  intro K L _ _ _ _ G hG hsplit b Gₗ χ
  have hGₗ : IsConnectedReductive Gₗ := hG.baseChange_of_algebraicExtension
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom Gₗ.X.hom := hGₗ.isAffineHom
  let : Smooth Gₗ.X.hom := hGₗ.smooth
  obtain ⟨T, i, hT, hi⟩ := hsplit
  let Tₗ := (CommGroupScheme.baseChange b).obj T
  let iₗ : Tₗ.toGrp ⟶ Gₗ := (GroupScheme.baseChange b).map i
  have hiₗ : IsMaximalSplitTorus iₗ :=
    (maximalTorusBaseChangeForward K L G T i hi).isMaximalSplitTorus (hT.baseChange b)
  obtain ⟨M, j, hj, f, hf, -⟩ := exists_maximalSplitTorus_through_cocharacter χ
  obtain ⟨x, e, hx⟩ := (maximalSplitTorusConjugacy L Gₗ hGₗ).1 M Tₗ j iₗ hj hiₗ
  obtain ⟨ν, hν, -⟩ := hT.existsUnique_baseChangeCocharacter b T (f ≫ e.hom)
  have hconj : χ ≫ (Gₗ.innerIso x).hom =
      Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ i) := by
    rw [Dynamic.baseChangeCocharacter_comp, hν, ← hf, Category.assoc, hx, Category.assoc]
  refine ⟨CommGroupScheme.groupHom ν ≫ i, x⁻¹, ?_⟩
  rw [← hconj, innerIso_inv_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Langlands.GroupScheme
