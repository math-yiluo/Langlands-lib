import Langlands.GroupScheme.Examples.HermitianRootSplitting
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryReductiveProof
import Langlands.GroupScheme.Reductive.SpecialLinear

/-! # Connected reductivity of the actual weighted Hermitian group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.HermitianRoot.SchemeModel

open SU3Root Langlands.Shimura.AlgebraInvolution.SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

/-- The actual weighted Hermitian group is smooth, by its special-linear splitting
and descent along the faithfully flat quadratic extension. -/
theorem smooth_groupScheme : Smooth (groupScheme k L H w hw).X.hom := by
  have hL : Smooth (baseChangeGroupScheme k L H w hw).X.hom :=
    GroupScheme.smooth_of_over_iso ((Grp.forget _).mapIso (splittingIso k L H w hw))
      (SpecialLinear.smooth_groupScheme (Index Middle) (Sum.inl ()) (CommRingCat.of L))
  obtain ⟨h1, h2, h3⟩ := QuasiSplitUnitary.scalarMap_fpqc (F := k) (E := L)
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := (groupScheme k L H w hw).X.hom) (g := scalarBaseMap k L)
    ⟨⟨h1, h2⟩, h3⟩ hL

/-- The actual weighted Hermitian group is affine over its base field. -/
theorem isAffineHom_groupScheme : IsAffineHom (groupScheme k L H w hw).X.hom :=
  isAffineHom_of_isAffine _

/-- Connectedness of the actual special-linear splitting descends through the
surjective projection of the quadratic scalar extension. -/
theorem connectedSpace_groupScheme : ConnectedSpace (groupScheme k L H w hw).X.left := by
  have hL : ConnectedSpace (baseChangeGroupScheme k L H w hw).X.left := by
    have := SpecialLinear.connectedSpace_groupScheme (Index Middle) (Sum.inl ()) L
    have := isIso_left_of_iso (splittingIso k L H w hw)
    let φ := Scheme.homeoOfIso (asIso (splittingIso k L H w hw).hom.hom.hom.left)
    exact φ.symm.surjective.connectedSpace φ.symm.continuous
  have : Surjective (scalarBaseMap k L) :=
    (QuasiSplitUnitary.scalarMap_fpqc (F := k) (E := L)).1
  have hs : Surjective (pullback.fst (groupScheme k L H w hw).X.hom (scalarBaseMap k L)) :=
    inferInstance
  have : ConnectedSpace ↥(pullback (groupScheme k L H w hw).X.hom
      (scalarBaseMap k L) : Scheme.{u}) := hL
  exact hs.surj.connectedSpace (pullback.fst (groupScheme k L H w hw).X.hom
    (scalarBaseMap k L)).continuous

/-- The actual geometric extension of the Hermitian model is special linear. -/
def geometricSplittingIso :
    (GroupScheme.baseChange (toAlgebraicClosure k)).obj (groupScheme k L H w hw) ≅
      SpecialLinear.groupScheme (Index Middle) (CommRingCat.of (AlgebraicClosure k)) := by
  have : Module.Finite k L :=
    Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two k L)
  let liftMap : L →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let ψ : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Spec (CommRingCat.of L) :=
    Spec.map (CommRingCat.ofHom liftMap.toRingHom)
  have hψ : toAlgebraicClosure k = ψ ≫ scalarBaseMap k L := by
    rw [toAlgebraicClosure, scalarBaseMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (RingHom.ext fun x => (liftMap.commutes x).symm)
  rw [hψ]
  exact (Functor.mapGrpNatIso (Over.pullbackComp ψ (scalarBaseMap k L))).app
        (groupScheme k L H w hw) ≪≫ Functor.mapGrpCompIso.app (groupScheme k L H w hw) ≪≫
      (GroupScheme.baseChange ψ).mapIso (splittingIso k L H w hw) ≪≫
      SpecialLinear.baseChangeModelIso (Index Middle) ψ

/-- The geometric unipotent radical of the actual Hermitian model is trivial. -/
theorem hasTrivialGeometricUnipotentRadical_groupScheme :
    HasTrivialUnipotentRadical
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj (groupScheme k L H w hw)) :=
  HasTrivialUnipotentRadical.of_iso (geometricSplittingIso k L H w hw)
    (SpecialLinear.hasTrivialUnipotentRadical (AlgebraicClosure k) (Index Middle))

/-- Every actual nondegenerate weighted Hermitian model with a hyperbolic plane
is connected reductive over the original field, in every characteristic. -/
theorem isConnectedReductive : IsConnectedReductive (groupScheme k L H w hw) where
  smooth := smooth_groupScheme k L H w hw
  isAffineHom := isAffineHom_groupScheme k L H w hw
  connectedSpace := connectedSpace_groupScheme k L H w hw
  hasTrivialGeometricUnipotentRadical :=
    hasTrivialGeometricUnipotentRadical_groupScheme k L H w hw

end Langlands.GroupScheme.HermitianRoot.SchemeModel
