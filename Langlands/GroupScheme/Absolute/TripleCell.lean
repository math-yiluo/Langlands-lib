import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Dynamic.ParabolicProduct
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # The three-factor open cell of a smooth affine group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G M Z U : GroupScheme S}

/-- The actual multiplication morphism from three subgroup sources,
with source associated as `M × (Z × U)`. -/
def tripleCellMultiplication (iM : M ⟶ G) (iZ : Z ⟶ G) (iU : U ⟶ G) :
    M.X ⊗ (Z.X ⊗ U.X) ⟶ G.X :=
  (fst M.X (Z.X ⊗ U.X) ≫ iM.hom.hom) *
    (snd M.X (Z.X ⊗ U.X) ≫ SubgroupFunctor.cellMultiplication iZ iU)

@[simp]
theorem lift_tripleCellMultiplication (iM : M ⟶ G) (iZ : Z ⟶ G) (iU : U ⟶ G)
    {T : Over S} (m : T ⟶ M.X) (z : T ⟶ Z.X) (v : T ⟶ U.X) :
    lift m (lift z v) ≫ tripleCellMultiplication iM iZ iU =
      (m ≫ iM.hom.hom) * ((z ≫ iZ.hom.hom) * (v ≫ iU.hom.hom)) := by
  simp only [tripleCellMultiplication, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
    SubgroupFunctor.lift_cellMultiplication]

/-- Replacing the centralizer and unipotent product by the parabolic gives
the opposite-cell multiplication. -/
theorem whiskerLeft_parabolicProductIso_comp_cellMultiplication
    [IsSeparated G.X.hom] (χ : (Gm S).toGrp ⟶ G)
    {P : GroupScheme S} (iM : M ⟶ G) {iZ : Z ⟶ G} {iU : U ⟶ G} {iP : P ⟶ G}
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (hP : (parabolic χ).IsRepresentedBy iP) :
    (M.X ◁ (parabolicProductIso χ hZ hU hP).hom) ≫
        SubgroupFunctor.cellMultiplication iM iP =
      tripleCellMultiplication iM iZ iU := by
  rw [SubgroupFunctor.cellMultiplication, MonObj.comp_mul,
    whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
    parabolicProductIso_hom_comp]
  rfl

/-- For any smooth affine group over any field, the multiplication
`U(-χ) × Z(χ) × U(χ) → G` is an open immersion for any actual representatives
of these intrinsic dynamic functors. -/
theorem isOpenImmersion_tripleCellMultiplication
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {M Z U : GroupScheme (Spec (CommRingCat.of k))}
    {iM : M ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
    (hM : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy iM)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU) :
    IsOpenImmersion (tripleCellMultiplication iM iZ iU).left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let P := Affine.parabolicScheme χ
  let iP : P ⟶ G := Affine.parabolicHom χ
  have hP : (parabolic χ).IsRepresentedBy iP := Affine.isRepresentedBy_parabolicHom χ
  let e := parabolicProductIso χ hZ hU hP
  have : IsIso (M.X ◁ e.hom).left :=
    (inferInstance : IsIso ((Over.forget _).mapIso (whiskerLeftIso M.X e)).hom)
  have : IsOpenImmersion (SubgroupFunctor.cellMultiplication iM iP).left :=
    oppositeCellStatement k G χ M P iM iP hM hP
  have h : IsOpenImmersion
      ((M.X ◁ e.hom) ≫ SubgroupFunctor.cellMultiplication iM iP).left := by
    change IsOpenImmersion
      ((M.X ◁ e.hom).left ≫ (SubgroupFunctor.cellMultiplication iM iP).left)
    infer_instance
  rw [whiskerLeft_parabolicProductIso_comp_cellMultiplication χ iM hZ hU hP] at h
  exact h

end Langlands.GroupScheme.Dynamic
