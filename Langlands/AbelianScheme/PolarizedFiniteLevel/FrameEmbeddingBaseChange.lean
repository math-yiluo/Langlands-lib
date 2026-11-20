import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalBundle
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof
import Langlands.AlgebraicGeometry.LinearSystem.SectionRatio

/-! # Base change of frame-normalized cubic embeddings -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard GroupScheme.Tate
open Langlands.SchemeModule

variable {P : Prerequisites.{u}} {S S' : Scheme.{u}} {g d n m : ℕ}

/-- The torsion points of a pulled-back datum lie over the original torsion points.
(The same computation appears in the unpublished frame-locus base-change draft of
Task 3449's frame-locus base-change task.) -/
theorem Datum.pullback_torsionPoint_fst (a : Datum P S g d n) (f : S' ⟶ S)
    (r : Fin (2 * g) → ZMod n) :
    (a.pullback f).torsionPoint r ≫ pullback.fst a.abelian.X.hom f = f ≫ a.torsionPoint r := by
  have h := congrArg (fun x => (Additive.toMul (toSection _ _ n x)).left)
    (enumerateTuple_pullback a.level.sections f r)
  simp only [toSection_levelRestrict] at h
  exact h

/-- Equal pullbacks of two sections stay equal along every composite. -/
lemma pullbackSection_comp_congr {X T T' : Scheme.{u}} {M : X.Modules} {v : T ⟶ X}
    (w : T' ⟶ T) {s₁ s₂ : GlobalSections M}
    (H : pullbackSection v M s₁ = pullbackSection v M s₂) :
    pullbackSection (w ≫ v) M s₁ = pullbackSection (w ≫ v) M s₂ := by
  rw [← LinearSystem.pullbackSection_comp, H, LinearSystem.pullbackSection_comp]

/-- Pulled-back sections have equal pullbacks along `w` exactly when the original sections
have equal pullbacks along the composite. -/
lemma pullbackSection_pullback_eq_iff {X Y T : Scheme.{u}} {M : X.Modules} (v : Y ⟶ X)
    (w : T ⟶ Y) (s₁ s₂ : GlobalSections M) :
    pullbackSection w ((Scheme.Modules.pullback v).obj M) (pullbackSection v M s₁) =
        pullbackSection w ((Scheme.Modules.pullback v).obj M) (pullbackSection v M s₂) ↔
      pullbackSection (w ≫ v) M s₁ = pullbackSection (w ≫ v) M s₂ := by
  rw [← LinearSystem.pullbackSection_comp, ← LinearSystem.pullbackSection_comp]
  have : IsIso (((Scheme.Modules.pullbackComp w v).hom.app M).app ⊤) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp inferInstance ⊤
  exact (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackComp w v).hom.app M).app ⊤)).injective.eq_iff.symm

variable (a : Datum P S g d n) (f : S' ⟶ S)

/-- The base change of a morphism of the abelian scheme to relative projective space. -/
def Datum.pullbackEmbedding (ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m) :
    (a.pullback f).abelian.X.left ⟶ RelativeProjectiveSpace S' m :=
  RelativeProjectiveSpace.lift m (pullback.snd a.abelian.X.hom f)
    (pullback.fst a.abelian.X.hom f ≫ ψ ≫ RelativeProjectiveSpace.toIntegral S m)

variable {a f}

lemma Datum.pullbackEmbedding_map {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
    (hψ : ψ ≫ RelativeProjectiveSpace.toBase S m = a.abelian.X.hom) :
    a.pullbackEmbedding f ψ ≫ RelativeProjectiveSpace.map m f =
      pullback.fst a.abelian.X.hom f ≫ ψ := by
  apply RelativeProjectiveSpace.hom_ext
  · simp only [Datum.pullbackEmbedding, Category.assoc, RelativeProjectiveSpace.map_toBase,
      RelativeProjectiveSpace.lift_toBase_assoc, hψ]
    exact pullback.condition.symm
  · simp [Datum.pullbackEmbedding]

lemma Datum.isPullback_pullbackEmbedding {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
    (hψ : ψ ≫ RelativeProjectiveSpace.toBase S m = a.abelian.X.hom) :
    IsPullback (pullback.fst a.abelian.X.hom f) (a.pullbackEmbedding f ψ) ψ
      (RelativeProjectiveSpace.map m f) := by
  refine IsPullback.of_bot (v₂₁ := RelativeProjectiveSpace.toBase S' m)
    (v₂₂ := RelativeProjectiveSpace.toBase S m) (h₃₁ := f) ?_
    (Datum.pullbackEmbedding_map hψ).symm (RelativeProjectiveSpace.isPullback_map m f).flip
  rw [hψ]
  simpa [Datum.pullbackEmbedding] using IsPullback.of_hasPullback a.abelian.X.hom f

/-- The base change of a frame-normalized embedding realizes the pulled-back family. -/
theorem Datum.Realizes.pullback {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
    {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n}
    {I : (RelativeProjectiveSpace S m).IdealSheafData}
    {σ : (Fin (2 * g) → ZMod n) → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)}
    (h : a.IsFrameEmbedding ρ ψ) (hr : a.Realizes ψ I σ) :
    (a.pullback f).Realizes (a.pullbackEmbedding f ψ)
      (I.comap (RelativeProjectiveSpace.map m f)) (fun r => f ≫ σ r) := by
  have := h.isClosedImmersion
  refine ⟨?_, fun r => ?_⟩
  · have sq := (Datum.isPullback_pullbackEmbedding (f := f) h.toBase).flip
    rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, hr.1]
  · simp only [Datum.pullbackEmbedding, RelativeProjectiveSpace.lift_toIntegral]
    rw [← Category.assoc, Datum.pullback_torsionPoint_fst, Category.assoc, hr.2 r]

/-- The base change of a frame-normalized embedding is a frame-normalized embedding of the
pulled-back datum. -/
theorem Datum.IsFrameEmbedding.pullback {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
    {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n} (h : a.IsFrameEmbedding ρ ψ) :
    (a.pullback f).IsFrameEmbedding ρ (a.pullbackEmbedding f ψ) where
  toBase := RelativeProjectiveSpace.lift_toBase _ _ _
  isClosedImmersion := by
    have := h.isClosedImmersion
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Datum.isPullback_pullbackEmbedding h.toBase) this
  cubic := by
    obtain ⟨N, ⟨i⟩⟩ := h.cubic
    have hcomp : a.pullbackEmbedding f ψ ≫ RelativeProjectiveSpace.toIntegral S' m =
        pullback.fst a.abelian.X.hom f ≫ ψ ≫ RelativeProjectiveSpace.toIntegral S m :=
      RelativeProjectiveSpace.lift_toIntegral _ _ _
    refine ⟨(LineBundle.pullback f).obj N, ⟨?_⟩⟩
    refine (LineBundle.pullbackComp _ _).app _ ≪≫
      eqToIso (congrArg (fun q => (LineBundle.pullback q).obj
        (RelativeProjectiveSpace.integralTwistOne m)) hcomp) ≪≫
      ((LineBundle.pullbackComp _ _).app _).symm ≪≫
      (LineBundle.pullback _).mapIso (((LineBundle.pullbackComp _ _).app _).symm ≪≫ i) ≪≫
      LineBundle.pullbackTensorObjIso P.preservation _ _ _ ≪≫
      LineBundle.tensorIso P.preservation (a.cubicBundlePullbackIso f).symm
        ((LineBundle.pullbackComp _ _).app _ ≪≫
          eqToIso (congrArg (fun q => (LineBundle.pullback q).obj N)
            (pullback.condition (f := a.abelian.X.hom) (g := f))) ≪≫
          ((LineBundle.pullbackComp _ _).app _).symm)
  basis j k hkj := by
    have hb := h.basis j k hkj
    unfold RelativeProjectiveSpace.twistOne RelativeProjectiveSpace.twistOneCoordinate at hb ⊢
    rw [vanishesAlong_pullback_iff] at hb ⊢
    have hc : (a.pullback f).torsionPoint (ρ j.castSucc) ≫ a.pullbackEmbedding f ψ ≫
        RelativeProjectiveSpace.toIntegral S' m =
        f ≫ a.torsionPoint (ρ j.castSucc) ≫ ψ ≫ RelativeProjectiveSpace.toIntegral S m := by
      simp only [Datum.pullbackEmbedding, RelativeProjectiveSpace.lift_toIntegral]
      rw [← Category.assoc, Datum.pullback_torsionPoint_fst, Category.assoc]
    simp only [Category.assoc] at hb ⊢
    rw [hc]
    exact LinearSystem.vanishesAlong_comp f hb
  unit i k := by
    have hu := h.unit i k
    unfold RelativeProjectiveSpace.twistOne RelativeProjectiveSpace.twistOneCoordinate at hu ⊢
    change pullbackSection _ ((Scheme.Modules.pullback _).obj _) (pullbackSection _ _ _) =
      pullbackSection _ ((Scheme.Modules.pullback _).obj _) (pullbackSection _ _ _) at hu
    change pullbackSection _ ((Scheme.Modules.pullback _).obj _) (pullbackSection _ _ _) =
      pullbackSection _ ((Scheme.Modules.pullback _).obj _) (pullbackSection _ _ _)
    rw [pullbackSection_pullback_eq_iff] at hu ⊢
    have hc : ((a.pullback f).torsionPoint (ρ (Fin.last (m + 1))) ≫ a.pullbackEmbedding f ψ) ≫
        RelativeProjectiveSpace.toIntegral S' m =
        f ≫ (a.torsionPoint (ρ (Fin.last (m + 1))) ≫ ψ) ≫
          RelativeProjectiveSpace.toIntegral S m := by
      simp only [Datum.pullbackEmbedding, RelativeProjectiveSpace.lift_toIntegral,
        Category.assoc]
      rw [← Category.assoc, Datum.pullback_torsionPoint_fst, Category.assoc]
    rw [hc]
    exact pullbackSection_comp_congr f hu

end Langlands.AbelianScheme.PolarizedFiniteLevel
