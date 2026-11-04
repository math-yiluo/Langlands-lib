import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.SubgroupFunctor.FppfProductTrivial
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Dynamic presentations after a trivial split-radical reduction

An exact product replacement, kept as an explicit input, identifies a supplied
pseudo-parabolic inclusion with a dynamic parabolic when the replacement
factor is trivial. The resulting actual cocharacter and representing-model
isomorphism preserve the original inclusion on every relative scheme test.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G P : GroupScheme (Spec (CommRingCat.of k))}

/-- Actual cocharacter data identifying the supplied inclusion with its dynamic
parabolic on all relative scheme tests. -/
structure DynamicParabolicPresentation (i : P ⟶ G) where
  cocharacter : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G
  isRepresentedBy : (Dynamic.parabolic cocharacter).IsRepresentedBy i

namespace DynamicParabolicPresentation

variable {i : P ⟶ G}

/-- Replace the ordinary-radical product using the supplied all-test equality,
then descend the trivial right factor by fppf saturation of the dynamic
parabolic. The product equality itself is not proved here. -/
def ofSplitProduct
    (hi : IsPseudoParabolicSubgroup i)
    {N : GroupScheme (Spec (CommRingCat.of k))} (n : N ⟶ G)
    (hzero : SubgroupFunctor.range n = ⊥)
    (hproduct : ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ G),
      IsUnipotentRadical j →
      ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
        (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        SubgroupFunctor.FppfLocallyInProduct
          (Dynamic.parabolic χ) (SubgroupFunctor.range j) x ↔
        SubgroupFunctor.FppfLocallyInProduct
          (Dynamic.parabolic χ) (SubgroupFunctor.range n) x) :
    DynamicParabolicPresentation i :=
  Classical.choice (by
    let : IsAffineHom G.X.hom := hi.isAffineHom
    let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    obtain ⟨U, j, χ, hj, hprod⟩ := hi.presentation
    have hsplit : (Dynamic.parabolic χ).IsFppfProduct (SubgroupFunctor.range n) i :=
      ⟨hprod.isClosedSubgroup, fun T x =>
        (hprod.mem_range_iff T x).trans (hproduct U j hj χ T x)⟩
    have hrep := Dynamic.Affine.isRepresentedBy_parabolicHom χ
    have hrange := hsplit.range_eq_left_of_right_eq_bot hrep hzero
    let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
    exact ⟨⟨χ, ⟨Over.mono_of_mono_left _, hrange⟩⟩⟩)

/-- The equality concerns full subgroup functors, not just rational points. -/
theorem range_eq (D : DynamicParabolicPresentation i) :
    SubgroupFunctor.range i = Dynamic.parabolic D.cocharacter :=
  D.isRepresentedBy.2

/-- A supplied right-coset fiber criterion becomes exactly the criterion for
the chosen dynamic parabolic, with the same original quotient and projection. -/
theorem quotient_fibers (D : DynamicParabolicPresentation i)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X) :
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (Dynamic.parabolic D.cocharacter).carrier T := by
  rw [← D.range_eq]
  exact hfib T g h

section Affine

variable [IsAffine G.X.left]

/-- The original subgroup model is isomorphic over G to the existing chosen
affine representative of the dynamic parabolic. -/
def modelIso (D : DynamicParabolicPresentation i) :
    P ≅ Dynamic.Affine.parabolicScheme D.cocharacter :=
  D.isRepresentedBy.isoOfIsRepresentedBy
    (Dynamic.Affine.isRepresentedBy_parabolicHom D.cocharacter)

/-- The isomorphism preserves the actual original subgroup homomorphism. -/
theorem modelIso_hom_comp (D : DynamicParabolicPresentation i) :
    D.modelIso.hom ≫ Dynamic.Affine.parabolicHom D.cocharacter = i :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The inverse also commutes with the actual ambient subgroup maps. -/
theorem modelIso_inv_comp (D : DynamicParabolicPresentation i) :
    D.modelIso.inv ≫ i = Dynamic.Affine.parabolicHom D.cocharacter := by
  calc
    D.modelIso.inv ≫ i =
        D.modelIso.inv ≫ (D.modelIso.hom ≫
          Dynamic.Affine.parabolicHom D.cocharacter) :=
      congrArg (D.modelIso.inv ≫ ·) D.modelIso_hom_comp.symm
    _ = Dynamic.Affine.parabolicHom D.cocharacter := by
      rw [← Category.assoc, D.modelIso.inv_hom_id, Category.id_comp]

end Affine

end DynamicParabolicPresentation
end Langlands.GroupScheme
