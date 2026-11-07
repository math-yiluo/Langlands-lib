import Langlands.Representation.Exponents.LeviParabolicExtensionStatement
import Langlands.Representation.Exponents.LeviParabolicPreimageGeometry
import Langlands.GroupScheme.Rational.LeviPreimageUnipotentRadical
import Langlands.GroupScheme.Rational.LeviPreimageMultiplication

/-! # Actual extension of a parabolic from the original rational Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The actual inverse image under the supplied outer Levi retraction proves
the full extension statement, retaining the original inner Levi scheme. -/
theorem leviParabolicExtension : LeviParabolicExtensionStatement.{u} := by
  intro k _ G hG P M U p l r hp hl hr hmul Q N V q n s hq hn hs hmulQ
  have : IsIso (subgroupMultiplication l r) := hmul
  have : IsIso (subgroupMultiplication n s) := hmulQ
  have : IsAffineHom P.X.hom := hl.isAffineHom
  have : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
  have : IsAffineHom Q.X.hom := hn.isAffineHom
  have : Smooth Q.X.hom := hq.smooth
  have : IsClosedImmersion r.hom.hom.left := hr.1.isClosedSubgroup
  have : IsAffineHom U.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  have : Smooth U.X.hom := hr.1.smooth
  have : ConnectedSpace U.X.left := hr.1.connectedSpace
  have : GeometricallyConnected U.X.hom := geometricallyConnected_of_connected U
  have : IsClosedImmersion s.hom.hom.left := hs.1.isClosedSubgroup
  have : IsAffineHom V.X.hom := by
    rw [← Over.w s.hom.hom]
    infer_instance
  have : Smooth V.X.hom := hs.1.smooth
  have : ConnectedSpace V.X.left := hs.1.connectedSpace
  have : GeometricallyConnected V.X.hom := geometricallyConnected_of_connected V
  have : ConnectedSpace N.X.left := hn.isConnectedReductive.connectedSpace
  let tq := leviRetraction n s hs.1.isNormal
  have : Smooth tq.hom.hom.left := smooth_leviRetraction n s hs.1.isNormal
  have : GeometricallyConnected tq.hom.hom.left :=
    geometricallyConnected_leviRetraction n s hs.1.isNormal
  have : ConnectedSpace Q.X.left :=
    GeometricallyConnected.connectedSpace tq.hom.hom.left tq.hom.hom.left.isOpenMap
  let tP := leviRetraction l r hr.1.isNormal
  have : Smooth tP.hom.hom.left := smooth_leviRetraction l r hr.1.isNormal
  have : GeometricallyConnected tP.hom.hom.left :=
    geometricallyConnected_leviRetraction l r hr.1.isNormal
  let R := LeviPreimage.group l r hr.1.isNormal q
  let i : R ⟶ P := LeviPreimage.inclusion l r hr.1.isNormal q
  let t : R ⟶ Q := LeviPreimage.projection l r hr.1.isNormal q
  let sectionQ : Q ⟶ R := LeviPreimage.leviSection l r hr.1.isNormal q
  let iU : U ⟶ R := LeviPreimage.radicalLift l r hr.1.isNormal q
  have hi : IsClosedSubgroup i :=
    SubgroupPreimage.isClosedSubgroup tP q hq.isClosedSubgroup
  have : IsAffineHom R.X.hom := SubgroupPreimage.isAffineHom tP q hq.isClosedSubgroup
  have : Smooth R.X.hom := SubgroupPreimage.smooth tP q
  have : ConnectedSpace R.X.left := SubgroupPreimage.connectedSpace tP q
  have : Smooth t.hom.hom.left := SubgroupPreimage.smooth_projection tP q
  have htsec : sectionQ ≫ t = 𝟙 Q :=
    LeviPreimage.section_projection l r hr.1.isNormal q
  have : Surjective t.hom.hom.left := by
    have he : sectionQ.hom.hom.left ≫ t.hom.hom.left = 𝟙 Q.X.left :=
      congrArg (fun f : Q ⟶ Q => f.hom.hom.left) htsec
    have : Surjective (sectionQ.hom.hom.left ≫ t.hom.hom.left) := by
      rw [he]
      infer_instance
    exact Surjective.of_comp sectionQ.hom.hom.left t.hom.hom.left
  have : QuasiCompact t.hom.hom.left := HomImage.quasiCompact_hom t
  have : Mono r.hom.hom := hr.1.isClosedSubgroup.mono_overHom
  have : Mono iU.hom.hom := LeviPreimage.mono_radicalLift l r hr.1.isNormal q
  have hkernel : SubgroupFunctor.range (kernelι t) = SubgroupFunctor.range iU :=
    LeviPreimage.range_kernel_projection l r hr.1.isNormal q
  have ht : HasSmoothConnectedUnipotentKernel t :=
    ⟨KernelRepresentative.smooth t iU hkernel,
      KernelRepresentative.connectedSpace t iU hkernel,
      KernelRepresentative.isUnipotent t iU hkernel hr.1.isUnipotent⟩
  let W := SubgroupPreimage.groupScheme t s
  let rR : W ⟶ R := SubgroupPreimage.inclusion t s
  have hrR : LeviSubgroup.IsGeometricUnipotentRadical rR :=
    HasSmoothConnectedUnipotentKernel.isGeometricUnipotentRadical_preimage t s ht hs
  let nR : N ⟶ R := n ≫ sectionQ
  have hnRt : nR ≫ t = n := by
    dsimp only [nR]
    rw [Category.assoc, htsec, Category.comp_id]
  have hmulR : IsIso (subgroupMultiplication nR rR) :=
    isIso_subgroupMultiplication_preimage t n s nR hnRt
  have hnRi : nR ≫ i = n ≫ q ≫ l := by
    simp only [nR, i, sectionQ, Category.assoc, LeviPreimage.section_inclusion]
  have hnRclosed : IsClosedSubgroup nR := by
    apply IsClosedSubgroup.of_comp hi
    rw [hnRi]
    exact hn.isClosedSubgroup.comp (hq.isClosedSubgroup.comp hl.isClosedSubgroup)
  have hnR : IsRationalLeviSubgroup nR :=
    ⟨inferInstance, hnRclosed, hn.isConnectedReductive, W, rR, hrR, hmulR⟩
  have hpR : IsParabolicSubgroup (i ≫ p) :=
    LeviPreimage.isParabolicSubgroup_ambient l r hr.1.isNormal q p hp hl hr hq
  have : Mono p.hom.hom := hp.isClosedSubgroup.mono_overHom
  have : Mono l.hom.hom := hl.isClosedSubgroup.mono_overHom
  refine ⟨R, W, i ≫ p, nR, rR, hpR, hnR, hrR, hmulR, ?_,
    LeviPreimage.range_ambient_le l r hr.1.isNormal q p,
    LeviPreimage.range_ambient_intersection l r hr.1.isNormal q p⟩
  rw [← Category.assoc, hnRi, Category.assoc, Category.assoc]

end Langlands.Aubert.General.RepresentedParabolic
