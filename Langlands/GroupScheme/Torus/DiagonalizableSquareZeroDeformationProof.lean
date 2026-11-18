import Langlands.GroupScheme.Torus.DiagonalizableSquareZeroDeformationStatement
import Langlands.GroupScheme.Torus.CompleteLocalDeformation.Lifting
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Torus.FlatDiagonalizableSubgroup
import Langlands.GroupScheme.Torus.GroupLikeHopfBaseChange
import Langlands.GroupScheme.HopfFiberCentrality

/-! # Lifting a specified diagonalizable reduction across a square-zero ideal -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

open CompleteLocalDeformation HopfCoordinates HopfFiberCentrality

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private def groupAlgebraToTensor (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (N : Type u) [AddCommGroup N] :
    AddMonoidAlgebra S N ≃ₐc[S] S ⊗[R] AddMonoidAlgebra R N := by
  let e := (AddMonoidAlgebra.scalarTensorEquiv R S (M := N)).symm
  have hsingle (n : N) : IsGroupLikeElem S (e (AddMonoidAlgebra.single n 1)) := by
    change IsGroupLikeElem S ((AddMonoidAlgebra.scalarTensorEquiv R S).symm
      (AddMonoidAlgebra.single n 1))
    rw [AddMonoidAlgebra.scalarTensorEquiv_symm_single]
    exact isGroupLikeElem_one_tmul (AddMonoidAlgebra.isGroupLikeElem_single_one n)
  refine BialgEquiv.ofAlgEquiv e ?_ ?_
  · apply AddMonoidAlgebra.algHom_ext
    · intro n
      simpa using (hsingle n).counit_eq_one
    · exact Subsingleton.elim _ _
  · apply AddMonoidAlgebra.algHom_ext
    · intro n
      simpa using (hsingle n).comul_eq_tmul_self.symm
    · exact Subsingleton.elim _ _

@[simp] private theorem groupAlgebraToTensor_single (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] {N : Type u} [AddCommGroup N]
    (n : N) (s : S) :
    groupAlgebraToTensor R S N (AddMonoidAlgebra.single n s) =
      s ⊗ₜ[R] (AddMonoidAlgebra.single n 1 : AddMonoidAlgebra R N) :=
  AddMonoidAlgebra.scalarTensorEquiv_symm_single (R := R) n s

private theorem exists_hopfIso_lift {R : Type u} [CommRing R] (J : Ideal R)
    (hJ : IsNilpotent J) (N : Type u) [AddCommGroup N]
    (A : CommHopfAlgCat.{u} (CommRingCat.of R)) [Module.Flat R A]
    (i₀ : scalarExtension R (R ⧸ J) (AddMonoidAlgebra R N) ≅
      scalarExtension R (R ⧸ J) A) :
    ∃ i : Diagonalizable.hopfAlgebra (CommRingCat.of R) N ≅ A,
      scalarExtensionMap (R ⧸ J) i.hom = i₀.hom := by
  let β := groupAlgebraToTensor R (R ⧸ J) N
  let e := β.trans (CommHopfAlgCat.ofIso i₀)
  obtain ⟨θ, hθ⟩ := exists_bialgEquiv_lift_of_baseChange J hJ e.symm
  let i : Diagonalizable.hopfAlgebra (CommRingCat.of R) N ≅ A :=
    CommHopfAlgCat.isoMk θ.symm ≪≫ CommHopfAlgCat.ofIsoSelf A
  refine ⟨i, CommHopfAlgCat.hom_ext ?_⟩
  suffices h : (scalarExtensionMap (R ⧸ J) i.hom).hom.comp β.toBialgHom =
      i₀.hom.hom.comp β.toBialgHom by
    ext x : 1
    obtain ⟨y, rfl⟩ := β.surjective x
    exact DFunLike.congr_fun h y
  apply AddMonoidAlgebra.bialgHom_ext
  · intro n
    have hn := hθ n
    change (1 : R ⧸ J) ⊗ₜ[R] θ.symm.toBialgHom (AddMonoidAlgebra.single n 1) =
      i₀.hom.hom (β (AddMonoidAlgebra.single n 1)) at hn
    change
      Bialgebra.TensorProduct.map (BialgHom.id (R ⧸ J) (R ⧸ J)) θ.symm.toBialgHom
          (β (AddMonoidAlgebra.single n 1)) =
        i₀.hom.hom (β (AddMonoidAlgebra.single n 1))
    simpa only [β, groupAlgebraToTensor_single, Bialgebra.TensorProduct.map_tmul,
      BialgHom.id_apply] using hn
  · exact Subsingleton.elim _ _

/-- A flat affine diagonalizable deformation lifts its specified isomorphism
through a square-zero ideal (Conrad, *Reductive group schemes*, p. 289). -/
theorem diagonalizableSquareZeroDeformation : DiagonalizableSquareZeroDeformationStatement.{u} := by
  intro R _ J hJ N _ _ G _ _ _ r D f₀
  let S := R ⧸ J
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let A := AffineCoordinates.hopfAlgebra G
  let B := Diagonalizable.hopfAlgebra (CommRingCat.of R) N
  let : Module.Flat R A := Diagonalizable.flat_hopfAlgebra (H := G)
  let eG := AffineCoordinates.hopfSpecIso G
  let eD : (hopfSpec (CommRingCat.of R)).obj (op B) ≅ D :=
    Diagonalizable.hopfSpecIso (CommRingCat.of R) N ≪≫
      Diagonalizable.relativeModelIso (CommRingCat.of R) N
  let cA := baseChangeSpecIso R S A
  let cB := baseChangeSpecIso R S B
  let v₀ := cA.symm ≪≫ (baseChange r).mapIso eG ≪≫ f₀ ≪≫
    ((baseChange r).mapIso eD).symm ≪≫ cB
  let i₀ := (hopfSpec.fullyFaithful.preimageIso v₀).unop
  obtain ⟨i, hi⟩ := exists_hopfIso_lift J ⟨2, by simpa only [Ideal.zero_eq_bot] using hJ⟩ N A i₀
  let v := (hopfSpec (CommRingCat.of R)).mapIso i.op
  have hv : (baseChange r).map v.hom = cA.hom ≫ v₀.hom ≫ cB.inv := by
    have h := baseChange_hopfSpec (R := CommRingCat.of R) S i.hom
    change (baseChange r).map v.hom =
      cA.hom ≫ (hopfSpec (CommRingCat.of S)).map (scalarExtensionMap S i.hom).op ≫ cB.inv at h
    rw [h, hi]
    have he : (hopfSpec (CommRingCat.of S)).map i₀.hom.op = v₀.hom :=
      hopfSpec.fullyFaithful.map_preimage v₀.hom
    rw [he]
  refine ⟨eG.symm ≪≫ v ≪≫ eD, ?_⟩
  change (baseChange r).map (eG.symm ≪≫ v ≪≫ eD).hom = f₀.hom
  simp only [Iso.trans_hom, Functor.map_comp, hv, Category.assoc, v₀, Iso.symm_hom,
    ← Functor.mapIso_inv, ← Functor.mapIso_hom, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

end Langlands.GroupScheme
