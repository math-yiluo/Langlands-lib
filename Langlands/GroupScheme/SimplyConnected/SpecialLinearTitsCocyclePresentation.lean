import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocyclePinning
import Langlands.GroupScheme.Reductive.StarActionFiniteStageTorus
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleStatement
import Langlands.GroupScheme.SpecialLinearBaseChange
import Langlands.GroupScheme.LocalGroupIsoBaseChange
import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence

/-! # A coordinate special-linear presentation over a finite Galois cover -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

local instance presentationBaseChangeAffine (K L : Type u) [Field K] [Field L] [Algebra K L]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap K L)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap K L))
  infer_instance

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n)

/-- A finite Galois stage and actual coordinate pinned presentation retaining the original
Tits torus, full character comparison, numbering and star action. -/
structure Presentation where
  L : Type u
  [fieldL : Field L]
  [algebraL : Algebra K L]
  [finiteL : FiniteDimensional K L]
  [galoisL : IsGalois K L]
  embedding : L →ₐ[K] SeparableClosure K
  stage : GaloisPinningData K L G
  torusIso : stage.torus ≅ d.pinning.torus
  rootEquiv : RootPairing.Equiv stage.toSplitPinning.rootDatum d.pinning.toSplitPinning.rootDatum
  inclusion_eq : CommGroupScheme.groupHom torusIso.hom ≫ d.pinning.inclusion = stage.inclusion
  tower_commutes :
    let : Algebra L (SeparableClosure K) := embedding.toRingHom.toAlgebra
    algebraBaseMap L (SeparableClosure K) ≫ algebraBaseMap K L =
      algebraBaseMap K (SeparableClosure K)
  weight_eq :
    let : Algebra L (SeparableClosure K) := embedding.toRingHom.toAlgebra
    ∀ χ, rootEquiv.weightMap χ = StarActionFiniteStage.stageCharacter
      (algebraBaseMap K L) (algebraBaseMap L (SeparableClosure K)) torusIso
      (algebraBaseMap K (SeparableClosure K)) tower_commutes χ
  base_iff : ∀ a, a ∈ stage.toSplitPinning.base.support ↔
    rootEquiv.indexEquiv a ∈ d.pinning.toSplitPinning.base.support
  star_eq : ∀ (σ : L ≃ₐ[K] L) (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K),
    (∀ y, τ (embedding y) = embedding (σ y)) →
      RootPairing.Equiv.comp rootEquiv (stage.starAction σ).val =
        RootPairing.Equiv.comp (d.pinning.starAction τ).val rootEquiv
  coordinate : CoordinatePinnedIso stage.toSplitPinning
    ((rootEquiv.indexEquiv.subtypeEquiv base_iff).trans e)

attribute [instance] Presentation.fieldL Presentation.algebraL Presentation.finiteL Presentation.galoisL

variable {d e}

/-- The prescribed numbering on the finite-stage simple roots. -/
def Presentation.numbering (p : Presentation d e) : p.stage.base.support ≃ Fin n :=
  (p.rootEquiv.indexEquiv.subtypeEquiv p.base_iff).trans e

/-- The actual isomorphism over the finite Galois extension, including comparison of
special-linear base-change models. -/
def Presentation.baseChangeIso (p : Presentation d e) :
    (GroupScheme.baseChange (algebraBaseMap K p.L)).obj
        (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) ≅
      (GroupScheme.baseChange (algebraBaseMap K p.L)).obj G :=
  (SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K p.L)) ≪≫
    p.coordinate.pinningIso.groupIso

/-- The natural local group-scheme isomorphism over the finite Galois cover. -/
def Presentation.localIso (p : Presentation d e) :
    LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
      (cover K p.L) :=
  LocalGroupIso.ofBaseChangeIso p.baseChangeIso

/-- Recovering the base-change isomorphism retains the defining coordinate composite. -/
@[simp] theorem Presentation.localIso_toBaseChangeIso (p : Presentation d e) :
    p.localIso.toBaseChangeIso = p.baseChangeIso :=
  LocalGroupIso.toBaseChangeIso_ofBaseChangeIso (U := cover K p.L) p.baseChangeIso

/-- The recovered forward morphism is the model comparison followed by the pinned map. -/
theorem Presentation.localIso_toBaseChangeIso_hom (p : Presentation d e) :
    p.localIso.toBaseChangeIso.hom =
      (SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K p.L)).hom ≫
        p.coordinate.pinningIso.groupIso.hom := by
  rw [p.localIso_toBaseChangeIso]
  rfl

/-- The finite-stage star action is identified with the given absolute star action on
simple vertices. -/
theorem Presentation.star_vertex (p : Presentation d e)
    (σ : p.L ≃ₐ[K] p.L) (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (hστ : ∀ y, τ (p.embedding y) = p.embedding (σ y))
    (a : p.stage.base.support) :
    p.rootEquiv.indexEquiv ((p.stage.starAction σ).val.indexEquiv a.val) =
      (d.star τ ⟨p.rootEquiv.indexEquiv a.val, (p.base_iff a.val).mp a.property⟩).val := by
  have h := p.star_eq σ τ hστ
  exact congrArg (fun r => r.indexEquiv a.val) h

/-- Every simply connected group with the supplied type-A Tits numbering has a finite
Galois coordinate presentation, before specifying its discrepancy matrices or torus weights. -/
theorem exists_presentation (hG : IsSimplyConnected G)
    (hcartan : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) :
    Nonempty (Presentation d e) := by
  obtain ⟨L, hL, hKL, hfin, hgal, ι, hstage⟩ :=
    StarActionFiniteStage.exists_finiteGaloisStage_torus d.pinning
  let : Field L := hL
  let : Algebra K L := hKL
  have : FiniteDimensional K L := hfin
  have : IsGalois K L := hgal
  let : Algebra L (SeparableClosure K) := ι.toRingHom.toAlgebra
  obtain ⟨hc, q, t, r, hi, he, hb, hs⟩ := hstage
  let eL : q.toSplitPinning.base.support ≃ Fin n := (r.indexEquiv.subtypeEquiv hb).trans e
  have hcartanL : ∀ a b : q.toSplitPinning.base.support,
      q.toSplitPinning.rootDatum.pairing a b = CartanMatrix.A n (eL a) (eL b) := by
    intro a b
    rw [← r.toHom.pairing]
    exact hcartan ⟨r.indexEquiv a.val, (hb a.val).mp a.property⟩
      ⟨r.indexEquiv b.val, (hb b.val).mp b.property⟩
  obtain ⟨c⟩ := exists_coordinatePinnedIso q.toSplitPinning
    (isSimplyConnectedFieldExtension K L G hG) eL hcartanL
  exact ⟨{ L := L
           embedding := ι
           stage := q
           torusIso := t
           rootEquiv := r
           inclusion_eq := hi
           tower_commutes := hc
           weight_eq := he
           base_iff := hb
           star_eq := hs
           coordinate := c }⟩

end Langlands.GroupScheme.SpecialLinearTitsCocycle
