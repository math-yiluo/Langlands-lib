import Langlands.Geometry.Building.Kottwitz.IntegralCosetLifting
import Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceStatement
import Langlands.Geometry.Building.IntegerValuationChamberBounded
import Langlands.GroupScheme.IntegralModel.UnramifiedStableSetModelDescent
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement

/-! # Rational lifting from a stable chamber's neutral model -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.Kottwitz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

private instance stableChamberExtendedAffineHom [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- Actual-map equivariance preserves its upstairs kernel. -/
theorem rationalConjugate_mem_reductiveKottwitzOnBaseChange_ker
    (hG : IsConnectedReductive G) (hequiv : ReductiveKottwitzEquivariant F G hG)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    {g : rationalPoints (baseChanged F (inertiaFixedField F) G)}
    (hg : g ∈ (reductiveKottwitzOnBaseChange F G hG).ker) :
    rationalConjugate F (inertiaFixedField F) G σ g ∈
      (reductiveKottwitzOnBaseChange F G hG).ker := by
  change reductiveKottwitz F F G hG
    (baseChangeCoeffEquiv F (inertiaFixedField F) G
      (rationalConjugate F (inertiaFixedField F) G σ g)) = 1
  rw [baseChangeCoeffEquiv_rationalConjugate]
  apply Multiplicative.toAdd.injective
  rw [hequiv]
  have hzero : (reductiveKottwitz F F G hG
      (baseChangeCoeffEquiv F (inertiaFixedField F) G g)).toAdd = 0 :=
    congrArg Multiplicative.toAdd hg
  rw [hzero, map_zero]
  rfl

/-- Descend an actual smooth connected-fibre kernel model, then apply integral
coset lifting. All exactness and actual-map laws remain explicit inputs. -/
theorem rationalSubgroupSurjective_of_unramifiedModel
    (hdescent : IntegralModel.UnramifiedSmoothModelDescentStatement.{u})
    (hG : IsConnectedReductive G)
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (P : Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)))
    (hstable : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (g : rationalPoints (baseChanged F (inertiaFixedField F) G)),
      g ∈ P → rationalConjugate F (inertiaFixedField F) G σ g ∈ P)
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hN : N.IsSmooth) (hconn : N.HasConnectedFibres)
    (himage : N.integralPoints = (reductiveKottwitzOnBaseChange F G hG).ker ⊓ P)
    (hsurj : Function.Surjective ((reductiveKottwitzOnBaseChange F G hG).domRestrict P))
    (hequiv : ReductiveKottwitzEquivariant F G hG)
    (hres : IsReductiveKottwitzRestriction F G hG (reductiveKottwitzRational F G hG)) :
    Function.Surjective ((reductiveKottwitzRational F G hG).domRestrict
      (P.comap (rationalExtend F (inertiaFixedField F) G))) := by
  have hNstable : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (g : rationalPoints (baseChanged F (inertiaFixedField F) G)),
      g ∈ N.integralPoints →
        rationalConjugate F (inertiaFixedField F) G σ g ∈ N.integralPoints := by
    intro σ g hg
    rw [himage] at hg ⊢
    exact ⟨rationalConjugate_mem_reductiveKottwitzOnBaseChange_ker hG hequiv σ hg.1,
      hstable σ g hg.2⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := hdescent F G N hN hNstable
  have hMconn := M.hasConnectedSpecialFibre_of_unramified_iso eM hconn
  let e := baseChangeCoeffEquiv F (inertiaFixedField F) G
  let H := P.comap e.symm.toMonoidHom
  have hHstable : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (x : reductiveKPoints F F G), x ∈ H →
        GaloisPoint.conjugate F (inertiaFixedField F) G σ x ∈ H := by
    intro σ x hx
    change e.symm (GaloisPoint.conjugate F (inertiaFixedField F) G σ x) ∈ P
    have h := hstable σ (e.symm x) hx
    have hconj : rationalConjugate F (inertiaFixedField F) G σ (e.symm x) =
        e.symm (GaloisPoint.conjugate F (inertiaFixedField F) G σ x) := by
      apply e.injective
      simp only [e, baseChangeCoeffEquiv_rationalConjugate, MulEquiv.apply_symm_apply]
    rwa [hconj] at h
  have hHsurj : Function.Surjective ((reductiveKottwitz F F G hG).domRestrict H) := by
    intro a
    obtain ⟨g, hg⟩ := hsurj a
    refine ⟨⟨e g.val, ?_⟩, hg⟩
    change e.symm (e g.val) ∈ P
    simpa only [MulEquiv.symm_apply_apply] using g.property
  have hint (x : reductiveKPoints F F G) :
      M.HasIntegralCoordinates (inertiaFixedField F) x ↔
        x ∈ H ∧ reductiveKottwitz F F G hG x = 1 := by
    rw [← M.mem_baseChangeUnramified_integralPoints_iff, eM.integralPoints_eq, himage]
    change (reductiveKottwitz F F G hG (e (e.symm x)) = 1 ∧ e.symm x ∈ P) ↔ _
    simp only [MulEquiv.apply_symm_apply]
    exact and_comm
  have hlift := integralCosetLifting F G hG M hM hMconn H hHstable hHsurj hint hequiv hres
  have hpre : rationalCoefficientPreimage F G H =
      P.comap (rationalExtend F (inertiaFixedField F) G) := by
    ext g
    rfl
  rwa [hpre] at hlift

/-- On supplied building data, a stable chamber has rational Kottwitz lifts,
conditional on the parahoric-model, smooth-descent, exactness and map inputs. -/
def StableChamberLiftingStatement : Prop :=
  UnramifiedParahoricModelStatement.{u} →
  IntegralModel.UnramifiedSmoothModelDescentStatement.{u} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
      (D : MaximalUnramified.SemilinearApartmentData B)
      (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
      (Cch : Set B.ReducedBuilding), B.IsChamber Cch →
      (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, D.action σ '' Cch = Cch) →
      let P := MulAction.stabilizer
        (rationalPoints (baseChanged F (inertiaFixedField F) G)) Cch
      let κ := reductiveKottwitzOnBaseChange F G hG
      Function.Surjective (κ.domRestrict P) →
      E.zeroPoints ⊓ B.pointwiseFixer Cch = κ.ker ⊓ P →
      ReductiveKottwitzEquivariant F G hG →
      IsReductiveKottwitzRestriction F G hG (reductiveKottwitzRational F G hG) →
      Function.Surjective ((reductiveKottwitzRational F G hG).domRestrict
        (P.comap (rationalExtend F (inertiaFixedField F) G)))

/-- A chamber is a nonempty bounded apartment subset. Its neutral parahoric model
has the exact kernel image and descends because that image is coefficient-stable. -/
theorem stableChamberLifting : StableChamberLiftingStatement.{u} := by
  intro hparahoric hdescent F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  intro B D E Cch hch hstable P κ hsurj hker hequiv hres
  obtain ⟨g, Ca, hne, hbounded, hCa⟩ := MaximalUnramified.isChamber_exists_bounded B hch
  obtain ⟨M, _, hneutral⟩ := hparahoric F G B E g Ca hne hbounded
  have himage : M.neutral.integralPoints = κ.ker ⊓ P := by
    rw [hneutral, ← hCa]
    exact hker
  apply rationalSubgroupSurjective_of_unramifiedModel hdescent hG P ?_
    M.neutral M.neutral_smooth M.neutral_connectedFibres himage hsurj hequiv hres
  intro σ g hg
  change (rationalConjugate F (inertiaFixedField F) G σ g • ·) '' Cch = Cch
  exact D.conjugate_stabilizes hstable σ hg

end Langlands.Geometry.Building.Kottwitz
