import Langlands.GroupScheme.Adjoint.ExistenceProof
import Langlands.GroupScheme.Rational.FiniteGaloisBaseChangeDiscrepancy
import Langlands.GroupScheme.Rational.PinnedGaloisInnerTwist
import Langlands.GroupScheme.Reductive.PinnedWeylInner
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Reductive.InnerFormStarForward

/-! # Star-compatible torus isomorphisms and inner discrepancy -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.StarCompatibleInnerTwist

local instance baseChangeAffine (k L : Type u) [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (d : GaloisPinningData k L G) (d' : GaloisPinningData k L H)

/-- A group isomorphism identifying the two supplied split maximal tori. -/
structure Comparison where
  groupIso : (GroupScheme.baseChange (algebraBaseMap k L)).obj G ≅
    (GroupScheme.baseChange (algebraBaseMap k L)).obj H
  torusIso : d.toSplitPinning.torus ≅ d'.toSplitPinning.torus
  square : d.toSplitPinning.inclusion ≫ groupIso.hom =
    CommGroupScheme.groupHom torusIso.hom ≫ d'.toSplitPinning.inclusion

/-- Forget the root-vector conditions on a pinned comparison. -/
def Comparison.ofPinnedIso (E : SplitPinning.Iso d.toSplitPinning d'.toSplitPinning) :
    Comparison d d' :=
  ⟨E.groupIso, E.torusIso, E.square⟩

variable (E : Comparison d d')

/-- The torus isomorphism `E_T` of the pinned isomorphism, with its domain written as the
base change of the `k`-torus of `d`. -/
def torusIso : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus ≅
    (CommGroupScheme.baseChange (algebraBaseMap k L)).obj d'.torus :=
  E.torusIso

/-- The automorphism `σ^*E ∘ E⁻¹` of `H_L`. -/
def twistIso (σ : L ≃ₐ[k] L) :
    (GroupScheme.baseChange (algebraBaseMap k L)).obj H ≅
      (GroupScheme.baseChange (algebraBaseMap k L)).obj H :=
  InnerFormStarForward.twistIso E.groupIso σ

/-- The torus automorphism of `T'_L` induced by `σ^*E ∘ E⁻¹`. -/
def twistTorusIso (σ : L ≃ₐ[k] L) :
    d'.toSplitPinning.torus ≅ d'.toSplitPinning.torus :=
  InnerFormStarForward.twistTorusIso d d' E.torusIso σ

/-- The twist automorphism normalizes the pinned torus through `twistTorusIso`. -/
theorem inclusion_comp_twistIso (σ : L ≃ₐ[k] L) :
    d'.toSplitPinning.inclusion ≫ (twistIso d d' E σ).hom =
      CommGroupScheme.groupHom (twistTorusIso d d' E σ).hom ≫ d'.toSplitPinning.inclusion :=
  InnerFormStarForward.inclusion_comp_twistIso d d' E.groupIso E.torusIso E.square σ

open StarActionIndependence

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]

/-- Equal based projections give a Weyl difference of the ordinary actions. -/
theorem galoisAction_difference_mem
    (e : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum)
    (hb : ∀ a, a ∈ d.toSplitPinning.base.support ↔
      e.indexEquiv a ∈ d'.toSplitPinning.base.support)
    (σ : L ≃ₐ[k] L)
    (hσ : e.comp (d.starAction σ).val = (d'.starAction σ).val.comp e) :
    d'.galoisAction σ * (conjAut e (d.galoisAction σ))⁻¹ ∈
      d'.toSplitPinning.rootDatum.weylGroup := by
  have hc := comp_basedRootDatumProjection d.toSplitPinning d'.toSplitPinning e hb
    (d.galoisAction σ) (conjAut e (d.galoisAction σ)) (by simp)
  have hp : d'.toSplitPinning.basedRootDatumProjection (conjAut e (d.galoisAction σ)) =
      d'.starAction σ := by
    apply Subtype.ext
    apply equiv_ext_of_weightMap
    intro y
    obtain ⟨χ, rfl⟩ := e.weightEquiv.surjective y
    have h := congrArg (fun f => f.weightMap χ) (hc.symm.trans hσ)
    exact h
  apply (d'.toSplitPinning.basedRootDatumProjection_eq_one_iff _).mp
  rw [map_mul, map_inv, hp]
  exact mul_inv_cancel _

/-- The character action of the torus discrepancy is the difference of the
ordinary Galois actions. -/
theorem characterAut_twistTorusIso_eq (σ : L ≃ₐ[k] L)
    (e : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum)
    (he : ∀ χ, e.weightMap χ = E.torusIso.inv ≫ χ) :
    characterAut (twistTorusIso d d' E σ) =
      (d'.galoisAction σ * (conjAut e (d.galoisAction σ))⁻¹).weightEquiv := by
  let F := twistIso d d' E σ
  let τ := twistTorusIso d d' E σ
  have hs : d'.toSplitPinning.inclusion ≫ F.hom =
      CommGroupScheme.groupHom τ.hom ≫ d'.toSplitPinning.inclusion :=
    inclusion_comp_twistIso d d' E σ
  have hsinv : d'.toSplitPinning.inclusion ≫ F.inv =
      CommGroupScheme.groupHom τ.inv ≫ d'.toSplitPinning.inclusion := by
    rw [Iso.comp_inv_eq, Category.assoc, hs, ← Category.assoc]
    change _ = CommGroupScheme.groupHom (τ.inv ≫ τ.hom) ≫ _
    rw [Iso.inv_hom_id]
    exact (Category.id_comp _).symm
  let w : d'.toSplitPinning.rootDatum.Aut :=
    rootDatumEquivOfTorusCompatibleIso d'.isConnectedReductive d'.isConnectedReductive
      d'.isSplitTorus d'.isSplitTorus d'.isMaximalTorus d'.isMaximalTorus
      F.symm τ.symm hsinv d'.isRootDatum d'.isRootDatum
  have hwχ (χ : characterLattice d'.toSplitPinning.torus) : w.weightMap χ = τ.inv ≫ χ :=
    rootDatumEquivOfTorusCompatibleIso_weightMap d'.isConnectedReductive
      d'.isConnectedReductive d'.isSplitTorus d'.isSplitTorus d'.isMaximalTorus
      d'.isMaximalTorus F.symm τ.symm hsinv d'.isRootDatum d'.isRootDatum χ
  have heq := InnerFormStarForward.galoisAction_eq_twist_mul d d' E.torusIso e he σ w hwχ
  have hw : w = d'.galoisAction σ * (conjAut e (d.galoisAction σ))⁻¹ := by
    rw [heq, mul_inv_cancel_right]
  calc
    characterAut (twistTorusIso d d' E σ) = w.weightEquiv := by
      apply LinearEquiv.ext
      intro χ
      exact (hwχ χ).symm
    _ = (d'.galoisAction σ * (conjAut e (d.galoisAction σ))⁻¹).weightEquiv :=
      congrArg (fun z : d'.toSplitPinning.rootDatum.Aut => z.weightEquiv) hw

/-- A based torus identification intertwining star actions has Weyl discrepancy. -/
theorem characterAut_twistTorusIso_mem_weylImage (σ : L ≃ₐ[k] L)
    (e : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum)
    (he : ∀ χ, e.weightMap χ = E.torusIso.inv ≫ χ)
    (hb : ∀ a, a ∈ d.toSplitPinning.base.support ↔
      e.indexEquiv a ∈ d'.toSplitPinning.base.support)
    (hσ : e.comp (d.starAction σ).val = (d'.starAction σ).val.comp e)
    [Mono d'.toSplitPinning.inclusion.hom.hom.left] :
    characterAut (twistTorusIso d d' E σ) ∈ weylImage d'.toSplitPinning.inclusion := by
  rw [characterAut_twistTorusIso_eq d d' E σ e he]
  exact d'.toSplitPinning.isRootDatum.abstractWeylImage_le
    ⟨_, galoisAction_difference_mem d d' e hb σ hσ, rfl⟩

variable [FiniteDimensional k L] [IsGalois k L]

/-- A torus comparison whose based root map intertwines star actions has
all-test inner discrepancy over a finite Galois extension. -/
theorem hasInnerDiscrepancy
    (e : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum)
    (he : ∀ χ, e.weightMap χ = E.torusIso.inv ≫ χ)
    (hb : ∀ a, a ∈ d.toSplitPinning.base.support ↔
      e.indexEquiv a ∈ d'.toSplitPinning.base.support)
    (hstar : ∀ σ : L ≃ₐ[k] L,
      e.comp (d.starAction σ).val = (d'.starAction σ).val.comp e)
    {A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ A} (hq : IsAdjointQuotient q) :
    (LocalGroupIso.ofBaseChangeIso
      (U := Langlands.AlgebraicGeometry.PointTopology.ringTest k L)
        E.groupIso).HasInnerDiscrepancy hq.innerAction := by
  obtain ⟨A', q', hq'⟩ := adjointQuotientExistence L _ d'.isConnectedReductive
  let : IsClosedImmersion d'.toSplitPinning.inclusion.hom.hom.left :=
    d'.isMaximalTorus.2.1
  apply IsAdjointQuotient.hasInnerDiscrepancy_of_galois_baseChange hq E.groupIso
  intro σ
  let hqL := adjointQuotientBaseChangeStatement.isAdjointQuotient (K := L) hq
  let Φ := hqL.mapIso hq' E.groupIso
  obtain ⟨y, hy⟩ := d'.toSplitPinning.exists_adjointPoint_of_weylImage hq'
    (twistIso d d' E σ) (twistTorusIso d d' E σ) (inclusion_comp_twistIso d d' E σ)
    (characterAut_twistTorusIso_mem_weylImage d d' E σ e he hb (hstar σ))
  refine ⟨y ≫ Φ.inv.hom.hom, ?_⟩
  have hxy : (y ≫ Φ.inv.hom.hom) ≫ Φ.hom.hom.hom = y := by
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id]
    exact Category.comp_id y
  rw [hqL.basePointIso_trans hq' E.groupIso, hxy, hy, twistIso,
    InnerFormStarForward.twistIso]
  ext
  simp

end Langlands.GroupScheme.StarCompatibleInnerTwist
