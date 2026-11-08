import Langlands.GroupScheme.Rational.PinnedGaloisInnerTwist
import Langlands.GroupScheme.Reductive.PinnedGaloisBorel
import Langlands.GroupScheme.Reductive.PinningConstruction
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Adjoint.QuasiSplitProof
import Langlands.GroupScheme.Adjoint.ExistenceStatement
import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormExistenceStatement

/-! # Quasi-split inner forms from root-datum and adjoint-quotient existence -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Descent

/-- Existence of root data for split maximal tori and existence of adjoint quotients
together give quasi-split inner forms of all connected reductive field groups. -/
theorem quasiSplitInnerFormExistence_of_rootDatum_adjoint
    (hroot : RootDatumExistenceStatement.{u})
    (hadj : AdjointQuotientExistenceStatement.{u}) :
    QuasiSplitInnerFormExistenceStatement.{u} := by
  intro k _ H hH
  have : Smooth H.X.hom := hH.smooth
  have : IsAffineHom H.X.hom := hH.isAffineHom
  have : LocallyOfFiniteType H.X.hom := inferInstance
  obtain ⟨T₀, i₀, hi₀⟩ := maximalTorusExistence k H
  obtain ⟨K, _, _, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k T₀.toGrp hi₀.1
  have : FiniteDimensional k K := hfin
  have : IsGalois k K := hgal
  have hHK : IsConnectedReductive ((GroupScheme.baseChange (fieldMap k K)).obj H) :=
    hH.baseChange_of_algebraicExtension
  have : IsAffineHom ((GroupScheme.baseChange (fieldMap k K)).obj H).X.hom :=
    hHK.isAffineHom
  have hiK : IsMaximalTorus (T := (CommGroupScheme.baseChange (fieldMap k K)).obj T₀)
      ((GroupScheme.baseChange (fieldMap k K)).map i₀) :=
    (maximalTorusBaseChange k K H T₀ i₀ hi₀.1 hi₀.2.1).1 hi₀
  have hTK : IsSplitTorus ((CommGroupScheme.baseChange (fieldMap k K)).obj T₀).toGrp :=
    hsplit
  obtain ⟨J, hJ, P, hP, hred⟩ := hroot K _ hHK _ hTK _ hiK
  have : Finite J := hJ
  let p : SplitPinning ((GroupScheme.baseChange (fieldMap k K)).obj H) :=
    SplitPinning.ofRootDatum hHK hTK _ hiK P hP hred (splitRootLieLine K _ hHK _ hTK _ hiK)
  have : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  let δ : (K ≃ₐ[k] K) →* p.rootDatum.Aut :=
    IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k K i₀ hTK hiK.2.1 hP
  let ρ : (K ≃ₐ[k] K) →* p.basedRootDatumAut := p.basedRootDatumProjection.comp δ
  let τ : ∀ σ : K ≃ₐ[k] K,
      (CommGroupScheme.baseChange (galoisBaseMap k K σ)).obj p.torus ≅ p.torus := fun σ =>
    CommGroupScheme.descentBaseChangeIso (fieldMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) T₀
  have hτ : ∀ σ, (GroupScheme.baseChange (galoisBaseMap k K σ)).map p.inclusion ≫
      (descentBaseChangeIso (fieldMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) H).hom =
      CommGroupScheme.groupHom (τ σ).hom ≫ p.inclusion := fun σ =>
    descentBaseChangeIso_naturality (fieldMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) i₀
  have hδ : ∀ σ χ, (δ σ).weightEquiv χ =
      (τ σ).inv ≫ characterLattice.baseChange (galoisBaseMap k K σ) p.torus χ :=
    fun _ _ => rfl
  have hw : ∀ σ, (ρ σ).val * (δ σ)⁻¹ ∈ p.rootDatum.weylGroup := fun σ =>
    p.basedRootDatumProjection_correction (δ σ)
  let s := (p.galoisQuasiSplitSolution ρ).group
  have hs : IsQuasiSplit s.obj := p.isQuasiSplit_galoisQuasiSplitSolution ρ
  obtain ⟨A, q, hq⟩ := hadj k s.obj hs.isConnectedReductive
  obtain ⟨A', q', hq'⟩ := hadj K _ hHK
  have hA : IsQuasiSplit A := adjointQuotientQuasiSplitStatement k s.obj A q hq hs
  exact ⟨QuasiSplitInnerForm.ofInnerDiscrepancy hs q hq hA K
    (LocalGroupIso.ofBaseChangeIso
      (U := Langlands.AlgebraicGeometry.PointTopology.ringTest k K) s.iso)
    (p.hasInnerDiscrepancy_solution ρ τ hτ δ hδ hw hq' s hq)⟩

/-- Under root-datum and adjoint-quotient existence, a chosen quasi-split inner form
of a connected reductive field group. -/
def quasiSplitInnerFormOfRootDatumAdjoint
    (hroot : RootDatumExistenceStatement.{u})
    (hadj : AdjointQuotientExistenceStatement.{u})
    {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H) : QuasiSplitInnerForm H :=
  Classical.choice (quasiSplitInnerFormExistence_of_rootDatum_adjoint hroot hadj k H hH)

end Langlands.GroupScheme
