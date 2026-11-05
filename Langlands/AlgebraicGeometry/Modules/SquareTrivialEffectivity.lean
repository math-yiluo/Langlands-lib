import Langlands.AlgebraicGeometry.Modules.TrivialIsoDescentProof
import Langlands.AlgebraicGeometry.Modules.SquarePullbackComparison
import Langlands.AlgebraicGeometry.Picard.NilpotentUnitReduction

/-! # Effectivity for globally trivial modules over a nilpotent-surjective leg -/

universe u

open CategoryTheory AlgebraicGeometry Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.Scheme.Modules.SquareTrivialEffectivity

section Lift

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hf : Function.Surjective f.appTop.hom)
  (hn : IsNilpotent (RingHom.ker f.appTop.hom))

include hf hn

/-- An isomorphism between the pullbacks of globally trivial modules lifts when
actual global functions form a nilpotent surjection. -/
lemma exists_iso {M N : Y.Modules}
    (τ : M ≅ structureModule Y) (σ : N ≅ structureModule Y)
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N) :
    ∃ e₀ : M ≅ N, (Scheme.Modules.pullback f).mapIso e₀ = e := by
  let α := (Scheme.Modules.pullback f).mapIso τ ≪≫ pullbackUnitIso f
  let β := (Scheme.Modules.pullback f).mapIso σ ≪≫ pullbackUnitIso f
  let δ := α.symm ≪≫ e ≪≫ β
  obtain ⟨t, ht⟩ :=
    Langlands.AlgebraicGeometry.Picard.NilpotentUnitReduction.unitsMap_surjective
      f.appTop.hom hf hn (structureAutScalar δ)
  have hd : structureAutPullback f (structureAutOfUnit t) = δ := by
    apply structureAutScalar_injective
    rw [structureAutScalar_pullback, structureAutScalar_ofUnit]
    exact ht
  let e₀ := τ ≪≫ structureAutOfUnit t ≪≫ σ.symm
  refine ⟨e₀, ?_⟩
  apply Iso.ext
  apply (cancel_epi α.inv).mp
  apply (cancel_mono β.hom).mp
  change (α.symm ≪≫ (Scheme.Modules.pullback f).mapIso e₀ ≪≫ β).hom = δ.hom
  have hnorm := normalizeIso_pullback f τ σ e₀
  change α.symm ≪≫ (Scheme.Modules.pullback f).mapIso e₀ ≪≫ β = _ at hnorm
  rw [hnorm]
  have hcancel : τ.symm ≪≫ e₀ ≪≫ σ = structureAutOfUnit t := by
    simp [e₀]
  rw [hcancel, hd]

/-- A chosen lift of an actual isomorphism between pullbacks of trivial modules. -/
def liftIso {M N : Y.Modules}
    (τ : M ≅ structureModule Y) (σ : N ≅ structureModule Y)
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N) :
    M ≅ N :=
  (exists_iso f hf hn τ σ e).choose

/-- The chosen lift has exactly the prescribed ordinary pullback. -/
lemma pullback_liftIso {M N : Y.Modules}
    (τ : M ≅ structureModule Y) (σ : N ≅ structureModule Y)
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N) :
    (Scheme.Modules.pullback f).mapIso (liftIso f hf hn τ σ e) = e :=
  (exists_iso f hf hn τ σ e).choose_spec

end Lift

section Square

variable {Y₀ Y₁ Y₂ Y : Scheme.{u}}
  (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)
  (w : i₁ ≫ j₁ = i₂ ≫ j₂)
  (hi₂ : Function.Surjective i₂.appTop.hom)
  (hn : IsNilpotent (RingHom.ker i₂.appTop.hom))
  {M₁ : Y₁.Modules} {M₂ : Y₂.Modules}
  (τ₁ : M₁ ≅ structureModule Y₁) (τ₂ : M₂ ≅ structureModule Y₂)
  (e : (Scheme.Modules.pullback i₁).obj M₁ ≅ (Scheme.Modules.pullback i₂).obj M₂)

/-- The first leg uses the given trivialization. -/
def leftIso : (Scheme.Modules.pullback j₁).obj (structureModule Y) ≅ M₁ :=
  pullbackUnitIso j₁ ≪≫ τ₁.symm

/-- The second leg lifts the prescribed overlap after the ordinary square comparison. -/
def rightIso : (Scheme.Modules.pullback j₂).obj (structureModule Y) ≅ M₂ :=
  liftIso i₂ hi₂ hn (pullbackUnitIso j₂) τ₂
    ((squarePullbackIso j₂ i₁ i₂ j₁ w (structureModule Y)).symm ≪≫
      (Scheme.Modules.pullback i₁).mapIso (leftIso j₁ τ₁) ≪≫ e)

/-- The two chosen frames realize the given overlap with the ordinary square
pullback comparison, including its canonical coherence maps. -/
lemma compatible :
    (squarePullbackIso j₂ i₁ i₂ j₁ w (structureModule Y)).hom ≫
        (Scheme.Modules.pullback i₂).map (rightIso i₁ i₂ j₁ j₂ w hi₂ hn τ₁ τ₂ e).hom =
      (Scheme.Modules.pullback i₁).map (leftIso j₁ τ₁).hom ≫ e.hom := by
  have h := congrArg Iso.hom
    (pullback_liftIso i₂ hi₂ hn (pullbackUnitIso j₂) τ₂
      ((squarePullbackIso j₂ i₁ i₂ j₁ w (structureModule Y)).symm ≪≫
        (Scheme.Modules.pullback i₁).mapIso (leftIso j₁ τ₁) ≪≫ e))
  change (Scheme.Modules.pullback i₂).map
    (rightIso i₁ i₂ j₁ j₂ w hi₂ hn τ₁ τ₂ e).hom = _ at h
  rw [h]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc]

include hi₂ hn τ₁ τ₂ in
/-- Every pair of globally trivial modules and every prescribed overlap is
realized by the structure module on the base. -/
lemma exists_compatible_isos :
    ∃ (e₁ : (Scheme.Modules.pullback j₁).obj (structureModule Y) ≅ M₁)
      (e₂ : (Scheme.Modules.pullback j₂).obj (structureModule Y) ≅ M₂),
      (squarePullbackIso j₂ i₁ i₂ j₁ w (structureModule Y)).hom ≫
          (Scheme.Modules.pullback i₂).map e₂.hom =
        (Scheme.Modules.pullback i₁).map e₁.hom ≫ e.hom :=
  ⟨leftIso j₁ τ₁, rightIso i₁ i₂ j₁ j₂ w hi₂ hn τ₁ τ₂ e,
    compatible i₁ i₂ j₁ j₂ w hi₂ hn τ₁ τ₂ e⟩

end Square

end Langlands.Scheme.Modules.SquareTrivialEffectivity
