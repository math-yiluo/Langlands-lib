import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientStatement
import Langlands.GroupScheme.Reductive.UnipotentExtension
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.SubgroupPreimageKernel
import Langlands.GroupScheme.ConnectedKernelGeometry
import Langlands.GroupScheme.SmoothNormalQuotient
import Langlands.GroupScheme.AffineQuotientModel
import Langlands.GroupScheme.MatrixRepresentation.UnipotentQuotient

/-! # The radical maximality argument for an actual smooth quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G U Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : U ⟶ G}

/-- A smooth scheme-surjective quasi-compact quotient with the exact
represented radical kernel has trivial ground-field unipotent radical. -/
theorem IsUnipotentRadical.hasTrivialUnipotentRadical_of_smooth_quotient
    (hi : IsUnipotentRadical i) (q : G ⟶ Q)
    [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (hk : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i) :
    HasTrivialUnipotentRadical Q := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffineHom (kernel q).X.hom :=
    KernelRepresentative.isAffineHom q i hk
  have : GeometricallyConnected (kernel q).X.hom :=
    hi.geometricallyConnected_kernel q hk
  have hK : IsUnipotent (kernel q) := KernelRepresentative.isUnipotent q i hk hi.isUnipotent
  apply hi.hasTrivialUnipotentRadical_of_preimages q hk
  intro H j hj hs hc hu _hn
  have : Smooth H.X.hom := hs
  have : ConnectedSpace H.X.left := hc
  have : IsAffineHom (SubgroupPreimage.groupScheme q j).X.hom :=
    SubgroupPreimage.isAffineHom q j hj
  have : Flat (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.flat_projection q j
  have : Surjective (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.surjective_projection q j
  have : QuasiCompact (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.quasiCompact_projection q j
  have : IsAffineHom (kernel (SubgroupPreimage.projection q j)).X.hom :=
    SubgroupPreimage.isAffineHom_kernel q j
  exact ⟨SubgroupPreimage.smooth q j,
    SubgroupPreimage.connectedSpace_of_geometricallyConnected_kernel q j,
    isUnipotent_of_kernel_of_quotient (SubgroupPreimage.projection q j)
      (SubgroupPreimage.isUnipotent_kernel q j hK) hu⟩

/-- The quotient by a supplied represented ground-field unipotent radical is
an actual represented fppf pseudo-reductive quotient over the original field. -/
theorem unipotentRadicalQuotient : UnipotentRadicalQuotientStatement.{u} := by
  intro k _ G _ _ _ U i hi
  let D := SmoothNormalQuotient.ofClosedNormal i hi.isClosedSubgroup hi.smooth hi.isNormal
  let Q := D.quotient
  let q : G ⟶ Q := D.projection
  have : Smooth Q.X.hom := D.smooth
  have : LocallyOfFiniteType Q.X.hom := D.locallyOfFiniteType
  have : QuasiCompact Q.X.hom := D.quasiCompact
  have : Smooth q.hom.hom.left := D.smooth_projection
  have : Surjective q.hom.hom.left := D.surjective_projection
  have : QuasiCompact q.hom.hom.left := D.quasiCompact_projection
  have hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q := D.isFppfQuotient
  obtain ⟨n, ρ, hρ⟩ := MatrixRepresentation.exists_faithful_of_unipotent_kernel
    i hi.isClosedSubgroup hi.isUnipotent hi.isNormal q hq.2.2.2
  have : Mono ρ.hom.hom := hρ
  let A := AffineQuotientModel.ofFaithfulRepresentation q ρ
  exact ⟨Q, q, hq, ⟨D.smooth, A.isAffineHom, D.connectedSpace,
    hi.hasTrivialUnipotentRadical_of_smooth_quotient q hq.2.2.2⟩⟩

end Langlands.GroupScheme
