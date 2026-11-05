import Langlands.AlgebraicGeometry.Modules.TrivialIsoDescentProof
import Langlands.AlgebraicGeometry.Modules.SquarePullbackComparison
import Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOnePatching

/-! # Isomorphism descent for trivial modules around a ring-pullback square -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.Scheme.Modules.SquareTrivialIsoDescent

variable {Y₀ Y₁ Y₂ Y : Scheme.{u}}
  (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)
  (w : i₁ ≫ j₁ = i₂ ≫ j₂)

private lemma unitCongr {V W : Scheme.{u}} {f g : V ⟶ W} (h : f = g) :
    (Scheme.Modules.pullbackCongr h).hom.app (SheafOfModules.unit W.ringCatSheaf) ≫
        (pullbackUnitIso g).hom = (pullbackUnitIso f).hom := by
  subst h
  rfl

/-- The square comparison respects the canonical structure-module comparisons. -/
lemma square_unit :
    (squarePullbackIso j₂ i₁ i₂ j₁ w (structureModule Y)).hom ≫
        (Scheme.Modules.pullback i₂).map (pullbackUnitIso j₂).hom ≫
        (pullbackUnitIso i₂).hom =
      (Scheme.Modules.pullback i₁).map (pullbackUnitIso j₁).hom ≫
        (pullbackUnitIso i₁).hom := by
  rw [← pullbackUnitComposition _ _ _ i₂ j₂]
  simp only [structureModule, squarePullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [unitCongr, pullbackUnitComposition]

/-- Base trivializations respect the same ordinary square comparison. -/
lemma trivialization_compatible {M : Y.Modules} (τ : M ≅ structureModule Y) :
    (squarePullbackIso j₂ i₁ i₂ j₁ w M).hom ≫
        (Scheme.Modules.pullback i₂).map
          (((Scheme.Modules.pullback j₂).mapIso τ ≪≫ pullbackUnitIso j₂).hom) ≫
        (pullbackUnitIso i₂).hom =
      (Scheme.Modules.pullback i₁).map
          (((Scheme.Modules.pullback j₁).mapIso τ ≪≫ pullbackUnitIso j₁).hom) ≫
        (pullbackUnitIso i₁).hom := by
  have hn := ((Scheme.Modules.pullbackComp i₁ j₁ ≪≫
    Scheme.Modules.pullbackCongr w ≪≫
      (Scheme.Modules.pullbackComp i₂ j₂).symm).hom.naturality τ.hom)
  change (Scheme.Modules.pullback i₁).map ((Scheme.Modules.pullback j₁).map τ.hom) ≫
      (squarePullbackIso j₂ i₁ i₂ j₁ w (structureModule Y)).hom =
    (squarePullbackIso j₂ i₁ i₂ j₁ w M).hom ≫
      (Scheme.Modules.pullback i₂).map ((Scheme.Modules.pullback j₂).map τ.hom) at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, square_unit]

/-- A compatible pair of isomorphisms has compatible normalized global units. -/
lemma scalar_compatible {M N : Y.Modules}
    (τ : M ≅ structureModule Y) (σ : N ≅ structureModule Y)
    (e₁ : (Scheme.Modules.pullback j₁).obj M ≅ (Scheme.Modules.pullback j₁).obj N)
    (e₂ : (Scheme.Modules.pullback j₂).obj M ≅ (Scheme.Modules.pullback j₂).obj N)
    (he : (Scheme.Modules.pullback i₁).map e₁.hom ≫
        (squarePullbackIso j₂ i₁ i₂ j₁ w N).hom =
      (squarePullbackIso j₂ i₁ i₂ j₁ w M).hom ≫
        (Scheme.Modules.pullback i₂).map e₂.hom) :
    Units.map i₁.appTop.hom.toMonoidHom
        (structureAutScalar
          (((Scheme.Modules.pullback j₁).mapIso τ ≪≫ pullbackUnitIso j₁).symm ≪≫ e₁ ≪≫
            (Scheme.Modules.pullback j₁).mapIso σ ≪≫ pullbackUnitIso j₁)) =
      Units.map i₂.appTop.hom.toMonoidHom
        (structureAutScalar
          (((Scheme.Modules.pullback j₂).mapIso τ ≪≫ pullbackUnitIso j₂).symm ≪≫ e₂ ≪≫
            (Scheme.Modules.pullback j₂).mapIso σ ≪≫ pullbackUnitIso j₂)) := by
  let α₁ := (Scheme.Modules.pullback j₁).mapIso τ ≪≫ pullbackUnitIso j₁
  let α₂ := (Scheme.Modules.pullback j₂).mapIso τ ≪≫ pullbackUnitIso j₂
  let β₁ := (Scheme.Modules.pullback j₁).mapIso σ ≪≫ pullbackUnitIso j₁
  let β₂ := (Scheme.Modules.pullback j₂).mapIso σ ≪≫ pullbackUnitIso j₂
  let δ₁ := α₁.symm ≪≫ e₁ ≪≫ β₁
  let δ₂ := α₂.symm ≪≫ e₂ ≪≫ β₂
  change Units.map i₁.appTop.hom.toMonoidHom (structureAutScalar δ₁) =
    Units.map i₂.appTop.hom.toMonoidHom (structureAutScalar δ₂)
  rw [← structureAutScalar_pullback i₁ δ₁, ← structureAutScalar_pullback i₂ δ₂]
  congr 1
  apply Iso.ext
  have hα := trivialization_compatible i₁ i₂ j₁ j₂ w τ
  have hβ := trivialization_compatible i₁ i₂ j₁ j₂ w σ
  change (squarePullbackIso j₂ i₁ i₂ j₁ w M).hom ≫
      (Scheme.Modules.pullback i₂).map α₂.hom ≫ (pullbackUnitIso i₂).hom =
    (Scheme.Modules.pullback i₁).map α₁.hom ≫ (pullbackUnitIso i₁).hom at hα
  change (squarePullbackIso j₂ i₁ i₂ j₁ w N).hom ≫
      (Scheme.Modules.pullback i₂).map β₂.hom ≫ (pullbackUnitIso i₂).hom =
    (Scheme.Modules.pullback i₁).map β₁.hom ≫ (pullbackUnitIso i₁).hom at hβ
  apply (cancel_epi ((Scheme.Modules.pullback i₁).map α₁.hom ≫
    (pullbackUnitIso i₁).hom)).mp
  simp only [structureAutPullback_hom, δ₁, δ₂, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  simp only [Iso.hom_inv_id_assoc, Iso.map_hom_inv_id_assoc]
  rw [← hβ, ← Category.assoc, ← Category.assoc, he]
  simp only [Category.assoc]
  rw [← reassoc_of% hα]
  simp

variable (hR : IsPullback j₁.appTop j₂.appTop i₁.appTop i₂.appTop)

include hR in
/-- The two ring maps jointly distinguish global units. -/
lemma units_ext {s t : Γ(Y, ⊤)ˣ}
    (h₁ : Units.map j₁.appTop.hom.toMonoidHom s =
      Units.map j₁.appTop.hom.toMonoidHom t)
    (h₂ : Units.map j₂.appTop.hom.toMonoidHom s =
      Units.map j₂.appTop.hom.toMonoidHom t) : s = t := by
  apply Units.ext
  exact Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOnePatching.element_ext
    j₁.appTop.hom j₂.appTop.hom i₁.appTop.hom i₂.appTop.hom hR
    (congrArg Units.val h₁) (congrArg Units.val h₂)

include hR in
/-- The two pullbacks jointly distinguish isomorphisms between trivial modules. -/
lemma iso_joint_injective {M N : Y.Modules}
    (τ : M ≅ structureModule Y) (σ : N ≅ structureModule Y) :
    Function.Injective (fun e : M ≅ N ↦
      ((Scheme.Modules.pullback j₁).mapIso e, (Scheme.Modules.pullback j₂).mapIso e)) := by
  intro e e' he
  have hn (V : Scheme.{u}) (j : V ⟶ Y)
      (hj : (Scheme.Modules.pullback j).mapIso e =
        (Scheme.Modules.pullback j).mapIso e') :
      Units.map j.appTop.hom.toMonoidHom (structureAutScalar (τ.symm ≪≫ e ≪≫ σ)) =
        Units.map j.appTop.hom.toMonoidHom (structureAutScalar (τ.symm ≪≫ e' ≪≫ σ)) := by
    rw [← structureAutScalar_pullback, ← structureAutScalar_pullback,
      ← normalizeIso_pullback j τ σ e, ← normalizeIso_pullback j τ σ e', hj]
  have hs := units_ext i₁ i₂ j₁ j₂ hR
    (hn Y₁ j₁ (congrArg Prod.fst he)) (hn Y₂ j₂ (congrArg Prod.snd he))
  have hd := structureAutScalar_injective hs
  apply Iso.ext
  apply (cancel_epi τ.inv).mp
  apply (cancel_mono σ.hom).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using congrArg Iso.hom hd

include hR in
/-- Compatible isomorphisms descend uniquely across an actual global-ring pullback
when the two base modules have specified trivializations. -/
lemma existsUnique_iso {M N : Y.Modules}
    (τ : M ≅ structureModule Y) (σ : N ≅ structureModule Y)
    (e₁ : (Scheme.Modules.pullback j₁).obj M ≅ (Scheme.Modules.pullback j₁).obj N)
    (e₂ : (Scheme.Modules.pullback j₂).obj M ≅ (Scheme.Modules.pullback j₂).obj N)
    (he : (Scheme.Modules.pullback i₁).map e₁.hom ≫
        (squarePullbackIso j₂ i₁ i₂ j₁ w N).hom =
      (squarePullbackIso j₂ i₁ i₂ j₁ w M).hom ≫
        (Scheme.Modules.pullback i₂).map e₂.hom) :
    ∃! e : M ≅ N, (Scheme.Modules.pullback j₁).mapIso e = e₁ ∧
      (Scheme.Modules.pullback j₂).mapIso e = e₂ := by
  let α₁ := (Scheme.Modules.pullback j₁).mapIso τ ≪≫ pullbackUnitIso j₁
  let α₂ := (Scheme.Modules.pullback j₂).mapIso τ ≪≫ pullbackUnitIso j₂
  let β₁ := (Scheme.Modules.pullback j₁).mapIso σ ≪≫ pullbackUnitIso j₁
  let β₂ := (Scheme.Modules.pullback j₂).mapIso σ ≪≫ pullbackUnitIso j₂
  let δ₁ := α₁.symm ≪≫ e₁ ≪≫ β₁
  let δ₂ := α₂.symm ≪≫ e₂ ≪≫ β₂
  obtain ⟨t, ht, _⟩ :=
    Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOnePatching.existsUnique_unit
      j₁.appTop.hom j₂.appTop.hom i₁.appTop.hom i₂.appTop.hom hR
      (structureAutScalar δ₁) (structureAutScalar δ₂)
      (scalar_compatible i₁ i₂ j₁ j₂ w τ σ e₁ e₂ he)
  let e := τ ≪≫ structureAutOfUnit t ≪≫ σ.symm
  have hcancel : τ.symm ≪≫ e ≪≫ σ = structureAutOfUnit t := by
    simp [e]
  have hpull (V : Scheme.{u}) (j : V ⟶ Y)
      (e' : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback j).obj N)
      (ht' : Units.map j.appTop.hom.toMonoidHom t =
        structureAutScalar
          (((Scheme.Modules.pullback j).mapIso τ ≪≫ pullbackUnitIso j).symm ≪≫ e' ≪≫
            (Scheme.Modules.pullback j).mapIso σ ≪≫ pullbackUnitIso j)) :
      (Scheme.Modules.pullback j).mapIso e = e' := by
    let α := (Scheme.Modules.pullback j).mapIso τ ≪≫ pullbackUnitIso j
    let β := (Scheme.Modules.pullback j).mapIso σ ≪≫ pullbackUnitIso j
    have hd : structureAutPullback j (structureAutOfUnit t) = α.symm ≪≫ e' ≪≫ β := by
      apply structureAutScalar_injective
      rw [structureAutScalar_pullback, structureAutScalar_ofUnit]
      exact ht'
    apply Iso.ext
    apply (cancel_epi α.inv).mp
    apply (cancel_mono β.hom).mp
    change (α.symm ≪≫ (Scheme.Modules.pullback j).mapIso e ≪≫ β).hom =
      (α.symm ≪≫ e' ≪≫ β).hom
    rw [normalizeIso_pullback j τ σ, hcancel, hd]
  have he₁ := hpull Y₁ j₁ e₁ ht.1
  have he₂ := hpull Y₂ j₂ e₂ ht.2
  refine ⟨e, ⟨he₁, he₂⟩, ?_⟩
  intro e' he'
  apply iso_joint_injective i₁ i₂ j₁ j₂ hR τ σ
  exact Prod.ext (he'.1.trans he₁.symm) (he'.2.trans he₂.symm)

/-- Pairs of actual isomorphisms satisfying the ordinary square compatibility. -/
def CompatiblePair (M N : Y.Modules) :=
  {e : ((Scheme.Modules.pullback j₁).obj M ≅ (Scheme.Modules.pullback j₁).obj N) ×
      ((Scheme.Modules.pullback j₂).obj M ≅ (Scheme.Modules.pullback j₂).obj N) //
    (Scheme.Modules.pullback i₁).map e.1.hom ≫
        (squarePullbackIso j₂ i₁ i₂ j₁ w N).hom =
      (squarePullbackIso j₂ i₁ i₂ j₁ w M).hom ≫
        (Scheme.Modules.pullback i₂).map e.2.hom}

/-- The ordinary two-leg restriction of a module isomorphism. -/
def restrictIso {M N : Y.Modules} (e : M ≅ N) :
    CompatiblePair i₁ i₂ j₁ j₂ w M N :=
  ⟨((Scheme.Modules.pullback j₁).mapIso e, (Scheme.Modules.pullback j₂).mapIso e),
    (Scheme.Modules.pullbackComp i₁ j₁ ≪≫
      Scheme.Modules.pullbackCongr w ≪≫
      (Scheme.Modules.pullbackComp i₂ j₂).symm).hom.naturality e.hom⟩

/-- Isomorphisms between globally trivial modules are exactly their compatible
restrictions when the actual global-section ring square is a pullback. -/
def isoEquiv {M N : Y.Modules}
    (τ : M ≅ structureModule Y) (σ : N ≅ structureModule Y) :
    (M ≅ N) ≃ CompatiblePair i₁ i₂ j₁ j₂ w M N where
  toFun := restrictIso i₁ i₂ j₁ j₂ w
  invFun e := (existsUnique_iso i₁ i₂ j₁ j₂ w hR τ σ e.val.1 e.val.2 e.property).choose
  left_inv e := by
    apply iso_joint_injective i₁ i₂ j₁ j₂ hR τ σ
    have h := (existsUnique_iso i₁ i₂ j₁ j₂ w hR τ σ
      ((restrictIso i₁ i₂ j₁ j₂ w e).val.1)
      ((restrictIso i₁ i₂ j₁ j₂ w e).val.2)
      (restrictIso i₁ i₂ j₁ j₂ w e).property).choose_spec.1
    exact Prod.ext h.1 h.2
  right_inv e := by
    apply Subtype.ext
    have h := (existsUnique_iso i₁ i₂ j₁ j₂ w hR τ σ
      e.val.1 e.val.2 e.property).choose_spec.1
    exact Prod.ext h.1 h.2

end Langlands.Scheme.Modules.SquareTrivialIsoDescent
