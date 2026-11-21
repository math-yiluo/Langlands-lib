import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusIsoInvarianceStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusBaseChangeProof
import Langlands.AlgebraicGeometry.Modules.SchemeIsoCohomology

/-! # Isomorphism invariance of the projective frame locus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules (pullbackComp pullbackId pullbackPushforwardAdjunction
  pushforward pushforwardComp pushforwardCongr conjugateEquiv_pullbackComp_inv)
open Langlands.AlgebraicGeometry.Modules (pushforwardEquivalence)
open Langlands.Scheme.Modules (compIso homEquiv_conjugate homEquiv_comp_map)
open Langlands.Scheme.Modules.LineBundleFlatDescent (compIso_rfl compIso_assoc compIso_naturality)

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

set_option backward.isDefEq.respectTransparency false

/-- Transport of the direct image along an isomorphism over the base. -/
private def directImageIso {X Y S : Scheme.{u}} (q : X ⟶ Y) [IsIso q]
    (p : Y ⟶ S) (p' : X ⟶ S) (h : q ≫ p = p') {L : Y.Modules} {L' : X.Modules}
    (e : (Scheme.Modules.pullback q).obj L ≅ L') :
    (pushforward p).obj L ≅ (pushforward p').obj L' := by
  letI : (pushforward q).IsEquivalence := (pushforwardEquivalence (asIso q)).isEquivalence_functor
  exact (pushforward p).mapIso
      (asIso ((pullbackPushforwardAdjunction q).unit.app L) ≪≫ (pushforward q).mapIso e) ≪≫
    (pushforwardComp q p).app L' ≪≫ (pushforwardCongr h).app L'

/-- The comparison is adjoint to pullback of the original counit followed by the
coefficient isomorphism. -/
private lemma directImageIso_counit {X Y S : Scheme.{u}} (q : X ⟶ Y) [IsIso q]
    (p : Y ⟶ S) (p' : X ⟶ S) (h : q ≫ p = p') {L : Y.Modules} {L' : X.Modules}
    (e : (Scheme.Modules.pullback q).obj L ≅ L') :
    (Scheme.Modules.pullback p').map (directImageIso q p p' h e).hom ≫
        (pullbackPushforwardAdjunction p').counit.app L' =
      (compIso q p p' h ((pushforward p).obj L)).inv ≫
        (Scheme.Modules.pullback q).map ((pullbackPushforwardAdjunction p).counit.app L) ≫ e.hom := by
  subst p'
  rw [compIso_rfl]
  let adj := pullbackPushforwardAdjunction (q ≫ p)
  let E := adj.homEquiv ((pushforward p).obj L) L'
  apply E.injective
  change E (E.symm (directImageIso q p (q ≫ p) rfl e).hom) =
    E ((pullbackComp q p).inv.app ((pushforward p).obj L) ≫
      (Scheme.Modules.pullback q).map ((pullbackPushforwardAdjunction p).counit.app L) ≫ e.hom)
  rw [Equiv.apply_symm_apply]
  dsimp only [E, adj]
  rw [homEquiv_conjugate ((pullbackPushforwardAdjunction p).comp (pullbackPushforwardAdjunction q))
      (pullbackPushforwardAdjunction (q ≫ p)) (pullbackComp q p).inv,
    conjugateEquiv_pullbackComp_inv, homEquiv_comp_map]
  have h₁ : (pullbackPushforwardAdjunction p).homEquiv _ L
      ((pullbackPushforwardAdjunction p).counit.app L) = 𝟙 _ := by
    rw [← Adjunction.homEquiv_symm_id, Equiv.apply_symm_apply]
  have h₂ : (pushforwardCongr (rfl : q ≫ p = q ≫ p)).hom.app L' = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    simp
  dsimp only [Functor.id_obj]
  rw [h₁, Category.id_comp, Adjunction.homEquiv_unit]
  simp only [directImageIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom,
    h₂, Category.comp_id]

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ} {a b : Datum P S g d n}

private def rigidificationIso (α : PolarizedIso a b) :
    b.rigidificationModule ≅ a.rigidificationModule :=
  directImageIso (hom α.abelianIso.hom) b.abelian.X.hom a.abelian.X.hom
    (hom_structure α.abelianIso.hom) α.cubicBundlePullbackIso

private def torsionTargetIso (α : PolarizedIso a b) (r : Fin (2 * g) → ZMod n) :
    (Scheme.Modules.pullback (b.torsionPoint r)).obj b.cubicBundle.obj ≅
      (Scheme.Modules.pullback (a.torsionPoint r)).obj a.cubicBundle.obj :=
  (compIso (a.torsionPoint r) (hom α.abelianIso.hom) (b.torsionPoint r)
    (α.torsionPoint_hom r) b.cubicBundle.obj).symm ≪≫
    (Scheme.Modules.pullback (a.torsionPoint r)).mapIso α.cubicBundlePullbackIso

set_option maxHeartbeats 900000 in
private lemma torsionEvaluation_comm (α : PolarizedIso a b) (r : Fin (2 * g) → ZMod n) :
    (rigidificationIso α).hom ≫ a.torsionEvaluation r =
      b.torsionEvaluation r ≫ (torsionTargetIso α r).hom := by
  let q := hom α.abelianIso.hom
  let p := b.abelian.X.hom
  let p' := a.abelian.X.hom
  let σ := b.torsionPoint r
  let σ' := a.torsionPoint r
  let M := b.rigidificationModule
  let N := a.rigidificationModule
  let D := rigidificationIso α
  let e := α.cubicBundlePullbackIso
  let C (V : S.Modules) := compIso q p p' (hom_structure α.abelianIso.hom) V
  let B (V : S.Modules) := compIso σ p (𝟙 S) (b.torsionPoint_hom r) V
  let A (V : S.Modules) := compIso σ' p' (𝟙 S) (a.torsionPoint_hom r) V
  let T (L : b.abelian.X.left.Modules) := compIso σ' q σ (α.torsionPoint_hom r) L
  have hc := directImageIso_counit q p p' (hom_structure α.abelianIso.hom) e
  change (Scheme.Modules.pullback p').map D.hom ≫ a.cubicEvaluationAdjoint =
    (C M).inv ≫ (Scheme.Modules.pullback q).map b.cubicEvaluationAdjoint ≫ e.hom at hc
  have hD : (C M).hom ≫ (Scheme.Modules.pullback p').map D.hom ≫ a.cubicEvaluationAdjoint =
      (Scheme.Modules.pullback q).map b.cubicEvaluationAdjoint ≫ e.hom := by
    rw [hc, Iso.hom_inv_id_assoc]
  have ha : (T ((Scheme.Modules.pullback p).obj M)).hom ≫ (B M).hom =
      (Scheme.Modules.pullback σ').map (C M).hom ≫ (A M).hom :=
    compIso_assoc σ' q p σ p' (𝟙 S) (α.torsionPoint_hom r) (hom_structure α.abelianIso.hom)
      (a.torsionPoint_hom r) (b.torsionPoint_hom r) M
  have hId : (pullbackId S).hom.app M ≫ D.hom =
      (Scheme.Modules.pullback (𝟙 S)).map D.hom ≫ (pullbackId S).hom.app N :=
    ((pullbackId S).hom.naturality D.hom).symm
  have hA : (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullback p').map D.hom) ≫
      (A N).hom = (A M).hom ≫ (Scheme.Modules.pullback (𝟙 S)).map D.hom :=
    compIso_naturality σ' p' (𝟙 S) (a.torsionPoint_hom r) D.hom
  have hT : (Scheme.Modules.pullback σ').map
        ((Scheme.Modules.pullback q).map b.cubicEvaluationAdjoint) ≫ (T b.cubicBundle.obj).hom =
      (T ((Scheme.Modules.pullback p).obj M)).hom ≫
        (Scheme.Modules.pullback σ).map b.cubicEvaluationAdjoint :=
    compIso_naturality σ' q σ (α.torsionPoint_hom r) b.cubicEvaluationAdjoint
  -- Identify the source with the iterated pullback along `p`, `q`, and `σ'`.
  let t := (T ((Scheme.Modules.pullback p).obj M)).hom ≫ (B M).hom ≫ (pullbackId S).hom.app M
  have : IsIso t := by dsimp [t]; infer_instance
  rw [← cancel_epi t, a.torsionEvaluation_eq, b.torsionEvaluation_eq]
  change t ≫ D.hom ≫ (pullbackId S).inv.app N ≫ (A N).inv ≫
      (Scheme.Modules.pullback σ').map a.cubicEvaluationAdjoint =
    t ≫ ((pullbackId S).inv.app M ≫ (B M).inv ≫
      (Scheme.Modules.pullback σ).map b.cubicEvaluationAdjoint) ≫
      ((T b.cubicBundle.obj).symm ≪≫ (Scheme.Modules.pullback σ').mapIso e).hom
  simp only [t, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hId, Iso.hom_inv_id_app_assoc, reassoc_of% ha, ← reassoc_of% hA,
    Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_comp, hD, Functor.map_comp,
    ← reassoc_of% hT, Iso.hom_inv_id_assoc]

private def frameTargetIso (α : PolarizedIso a b) {m : ℕ}
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (k : Fin (m + 2)) :
    (∏ᶜ fun j : {j : Fin (m + 2) // j ≠ k} =>
      (Scheme.Modules.pullback (b.torsionPoint (ρ j))).obj b.cubicBundle.obj) ≅
    ∏ᶜ fun j : {j : Fin (m + 2) // j ≠ k} =>
      (Scheme.Modules.pullback (a.torsionPoint (ρ j))).obj a.cubicBundle.obj :=
  Pi.mapIso fun j => torsionTargetIso α (ρ j)

private lemma frameEvaluation_comm (α : PolarizedIso a b) {m : ℕ}
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (k : Fin (m + 2)) :
    (rigidificationIso α).hom ≫ a.frameEvaluation ρ k =
      b.frameEvaluation ρ k ≫ (frameTargetIso α ρ k).hom := by
  apply Pi.hom_ext
  intro j
  simp only [Datum.frameEvaluation, frameTargetIso, Category.assoc, Pi.mapIso_hom_π,
    Pi.lift_comp_π, Pi.lift_comp_π_assoc]
  exact torsionEvaluation_comm α (ρ j)

/-- The projective frame locus is invariant under polarized isomorphisms. -/
theorem frameLocusIsoInvariance : FrameLocusIsoInvarianceStatement.{u} := by
  intro P S g d n m a b ρ ⟨α⟩
  unfold Datum.frameLocus
  apply congrArg sSup
  ext W
  change (∀ k, IsIso ((Scheme.Modules.pullback W.ι).map (a.frameEvaluation ρ k))) ↔
    (∀ k, IsIso ((Scheme.Modules.pullback W.ι).map (b.frameEvaluation ρ k)))
  refine forall_congr' fun k => ?_
  let F := Scheme.Modules.pullback W.ι
  let i := rigidificationIso α
  let j := frameTargetIso α ρ k
  have w : F.map i.hom ≫ F.map (a.frameEvaluation ρ k) =
      F.map (b.frameEvaluation ρ k) ≫ F.map j.hom := by
    rw [← Functor.map_comp, ← Functor.map_comp, frameEvaluation_comm α ρ k]
  calc
    IsIso (F.map (a.frameEvaluation ρ k)) ↔
        IsIso (F.map i.hom ≫ F.map (a.frameEvaluation ρ k)) := (isIso_comp_left_iff _ _).symm
    _ ↔ IsIso (F.map (b.frameEvaluation ρ k) ≫ F.map j.hom) := by rw [w]
    _ ↔ IsIso (F.map (b.frameEvaluation ρ k)) := isIso_comp_right_iff _ _

end Langlands.AbelianScheme.PolarizedFiniteLevel
