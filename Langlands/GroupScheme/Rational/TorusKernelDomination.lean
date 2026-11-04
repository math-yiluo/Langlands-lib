import Langlands.GroupScheme.Rational.KernelDomination
import Langlands.GroupScheme.Torus.SplitOfDomination
import Langlands.GroupScheme.DominantHomFlat

/-! # Kernel parametrizations for torus quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusKernelDomination

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k]
    {D H Q : GroupScheme (Spec (CommRingCat.of k))}

/-- Pointed torus rigidity turns the composite with a torus quotient into a
homomorphism, with the original underlying scheme morphism. -/
def quotientHom (hD : IsTorus D) (hQ : IsTorus Q)
    (q : H ⟶ Q) (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X]) : D ⟶ Q :=
  hD.homOfPointedMorphism hQ (p ≫ q.hom.hom)
    (by rw [← Category.assoc, hp, IsMonHom.one_hom])

@[simp] theorem quotientHom_hom (hD : IsTorus D) (hQ : IsTorus Q)
    (q : H ⟶ Q) (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X]) :
    (quotientHom hD hQ q p hp).hom.hom = p ≫ q.hom.hom := rfl

private theorem flat_to_torus {A B : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType A.X.hom] [IsAffineHom A.X.hom]
    (hB : IsTorus B) (f : A ⟶ B) [IsDominant f.hom.hom.left] :
    Flat f.hom.hom.left := by
  have : Smooth B.X.hom := hB.smooth
  have : IsAffine B.X.left := SplittingAssembly.isAffine_of_isTorus B hB
  have : IsAffineHom B.X.hom := inferInstance
  have : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  have : IsReduced B.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k B.X.left B.X.hom
  have : LocallyOfFiniteType (f.hom.hom.left ≫ B.X.hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType f.hom.hom.left :=
    locallyOfFiniteType_of_comp f.hom.hom.left B.X.hom
  have : QuasiCompact (f.hom.hom.left ≫ B.X.hom) := by
    rw [Over.w]
    infer_instance
  have : QuasiCompact f.hom.hom.left := QuasiCompact.of_comp _ B.X.hom
  exact DominantHomFlat.flat_of_isDominant f

/-- The full kernel-valued difference for a pointed parametrization by a torus. -/
def parametrization (hD : IsTorus D) (hQ : IsTorus Q)
    (q : H ⟶ Q) (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X]) :
    D.X ⊗ (kernel (quotientHom hD hQ q p hp)).X ⟶ (kernel q).X :=
  KernelDomination.parametrization (quotientHom hD hQ q p hp) q p rfl

/-- The constructed map takes the identity pair to the identity. -/
theorem parametrization_one (hD : IsTorus D) (hQ : IsTorus Q)
    (q : H ⟶ Q) (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X]) :
    lift (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ D.X)
      (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶
        (kernel (quotientHom hD hQ q p hp)).X) ≫
      parametrization hD hQ q p hp = 1 :=
  KernelDomination.parametrization_one _ _ _ _

/-- A dominant pointed torus parametrization of a smooth affine group, over
a dominant torus quotient, induces a dominant map to the full quotient kernel.
Both quotient maps' flatness follows from dominance and finite type. -/
theorem parametrization_isDominant
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hD : IsTorus D) (hQ : IsTorus Q)
    (q : H ⟶ Q) [IsDominant q.hom.hom.left]
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X])
    (hd : IsDominant p.left) : IsDominant (parametrization hD hQ q p hp).left := by
  have := hd
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k H.X.left H.X.hom
  have : IsSchemeTheoreticallyDominant p.left :=
    IsSchemeTheoreticallyDominant.of_isDominant p.left
  have : IsAffine D.X.left := SplittingAssembly.isAffine_of_isTorus D hD
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffineHom D.X.hom := inferInstance
  have : Smooth D.X.hom := hD.smooth
  have : QuasiCompact p.left := inferInstance
  have : IsDominant (quotientHom hD hQ q p hp).hom.hom.left := by
    change IsDominant (p.left ≫ q.hom.hom.left)
    infer_instance
  have : Flat q.hom.hom.left := flat_to_torus hQ q
  have : Flat (quotientHom hD hQ q p hp).hom.hom.left := flat_to_torus hQ _
  exact KernelDomination.parametrization_isDominant _ _ _ _

/-- A split torus source forces the dominant torus quotient itself to be split. -/
theorem isSplitTorus_quotient (hD : IsSplitTorus D) (hQ : IsTorus Q)
    (q : H ⟶ Q) [IsDominant q.hom.hom.left]
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X])
    (hd : IsDominant p.left) : IsSplitTorus Q := by
  have := hd
  have : IsDominant (p ≫ q.hom.hom).left := by
    change IsDominant (p.left ≫ q.hom.hom.left)
    infer_instance
  exact hQ.isSplitTorus_of_pointed_dominant_morphism hD (p ≫ q.hom.hom)
    (by rw [← Category.assoc, hp, IsMonHom.one_hom]) inferInstance

end Langlands.GroupScheme.TorusKernelDomination
