import Langlands.AlgebraicGeometry.Modules.SquareTrivialIsoDescent
import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStr

/-! # Local lifts of compatible isomorphism pairs across a cube of schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.Scheme.Modules.SquareLocalIsoLift

open UnitCocycleDescentUniqueness
open Langlands.SchemeModule.RigidifiedModule

section Leg

variable {T₀ T₁ T Y₀ Y₁ Y : Scheme.{u}} (t : T ⟶ Y) (s : T₁ ⟶ T) (ι : T₀ ⟶ T₁)
  (g : T₁ ⟶ Y₁) (g₀ : T₀ ⟶ Y₀) (i : Y₀ ⟶ Y₁) (j : Y₁ ⟶ Y)
  (h : s ≫ t = g ≫ j) (k : ι ≫ g = g₀ ≫ i)

/-- The comparison `ι^* s^* t^* M ≅ g₀^* i^* j^* M` along one face of a cube. -/
def legIso (M : Y.Modules) :
    (Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback s).obj
        ((Scheme.Modules.pullback t).obj M)) ≅
      (Scheme.Modules.pullback g₀).obj ((Scheme.Modules.pullback i).obj
        ((Scheme.Modules.pullback j).obj M)) :=
  (Scheme.Modules.pullback ι).mapIso (squarePullbackIso j s g t h M) ≪≫
    squarePullbackIso i ι g₀ g k ((Scheme.Modules.pullback j).obj M)

/-- The isomorphism `s^* t^* M ≅ s^* t^* N` obtained by transporting
`e : j^* M ≅ j^* N` along `g` and the square `s ≫ t = g ≫ j`. -/
def localIso {M N : Y.Modules}
    (e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback j).obj N) :
    (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback t).obj M) ≅
      (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback t).obj N) :=
  squarePullbackIso j s g t h M ≪≫ (Scheme.Modules.pullback g).mapIso e ≪≫
    (squarePullbackIso j s g t h N).symm

/-- The face comparison is natural with respect to the transported isomorphism. -/
@[reassoc]
lemma localIso_legIso {M N : Y.Modules}
    (e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback j).obj N) :
    (Scheme.Modules.pullback ι).map (localIso t s g j h e).hom ≫
        (legIso t s ι g g₀ i j h k N).hom =
      (legIso t s ι g g₀ i j h k M).hom ≫
        (Scheme.Modules.pullback g₀).map ((Scheme.Modules.pullback i).map e.hom) := by
  have n := squarePullbackIso_naturality i ι g₀ g k e.hom
  simp only [legIso, localIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← n]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]

/-- An isomorphism with transported restriction is compatible at the given square. -/
lemma compatibleAt_of_localIso {M N : Y.Modules}
    (e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback j).obj N)
    (E : (Scheme.Modules.pullback t).obj M ≅ (Scheme.Modules.pullback t).obj N)
    (hE : (Scheme.Modules.pullback s).mapIso E = localIso t s g j h e) :
    LineBundleIsoDescent.CompatibleAt j e t E.hom g s h := by
  unfold LineBundleIsoDescent.CompatibleAt
  have hE' := congrArg Iso.hom hE
  simp only [Functor.mapIso_hom] at hE'
  rw [hE']
  simp [localIso]

/-- If the square is cartesian, compatibility at it gives compatibility everywhere. -/
lemma compatible_of_isPullback {M N : Y.Modules}
    (e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback j).obj N)
    (P : IsPullback g s j t)
    (E : (Scheme.Modules.pullback t).obj M ≅ (Scheme.Modules.pullback t).obj N)
    (hE : (Scheme.Modules.pullback s).mapIso E = localIso t s g j P.w.symm e) :
    LineBundleIsoDescent.Compatible j e t E.hom := by
  intro Z g' h' hs
  exact LineBundleIsoDescent.compatibleAt_precomp j e t E.hom
    (P.lift g' h' hs.symm) g s P.w.symm
    (compatibleAt_of_localIso t s g j P.w.symm e E hE) g' h'
    (P.lift_fst _ _ _) (P.lift_snd _ _ _) hs

end Leg

section Cube

variable {Y₀ Y₁ Y₂ Y : Scheme.{u}}
  (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)
  (w : i₁ ≫ j₁ = i₂ ≫ j₂)
  {T₀ T₁ T₂ T : Scheme.{u}} (t : T ⟶ Y)
  (s₁ : T₁ ⟶ T) (s₂ : T₂ ⟶ T) (ι₁ : T₀ ⟶ T₁) (ι₂ : T₀ ⟶ T₂)
  (wT : ι₁ ≫ s₁ = ι₂ ≫ s₂)
  (g₁ : T₁ ⟶ Y₁) (g₂ : T₂ ⟶ Y₂) (g₀ : T₀ ⟶ Y₀)
  (h₁ : s₁ ≫ t = g₁ ≫ j₁) (h₂ : s₂ ≫ t = g₂ ≫ j₂)
  (k₁ : ι₁ ≫ g₁ = g₀ ≫ i₁) (k₂ : ι₂ ≫ g₂ = g₀ ≫ i₂)

/-- The two faces of a commuting cube are compatible with the square comparisons
of its top and bottom squares. -/
lemma cube_coherence (M : Y.Modules) :
    (squarePullbackIso s₂ ι₁ ι₂ s₁ wT ((Scheme.Modules.pullback t).obj M)).hom ≫
        (legIso t s₂ ι₂ g₂ g₀ i₂ j₂ h₂ k₂ M).hom =
      (legIso t s₁ ι₁ g₁ g₀ i₁ j₁ h₁ k₁ M).hom ≫
        (Scheme.Modules.pullback g₀).map (squarePullbackIso j₂ i₁ i₂ j₁ w M).hom := by
  have hv : ι₂ ≫ s₂ = ι₁ ≫ s₁ := wT.symm
  have hc₁ : ι₁ ≫ s₁ ≫ t = (ι₁ ≫ s₁) ≫ t := (Category.assoc _ _ _).symm
  have hc₂ : ι₂ ≫ s₂ ≫ t = (ι₁ ≫ s₁) ≫ t := by
    rw [← Category.assoc, hv]
  have hn₁ : (ι₁ ≫ g₁) ≫ j₁ = (ι₁ ≫ s₁) ≫ t := by
    rw [Category.assoc, ← h₁, Category.assoc]
  have hn₂ : (ι₂ ≫ g₂) ≫ j₂ = (ι₁ ≫ s₁) ≫ t := by
    rw [Category.assoc, ← h₂, ← Category.assoc, hv]
  have hd : g₀ ≫ i₁ ≫ j₁ = (ι₁ ≫ s₁) ≫ t := by
    rw [← Category.assoc, ← k₁, Category.assoc, ← h₁, Category.assoc]
  have a₁ := LineBundleFlatDescent.compIso_assoc ι₂ s₂ t (ι₁ ≫ s₁) (s₂ ≫ t) ((ι₁ ≫ s₁) ≫ t) hv rfl hc₂ rfl M
  have a₂ := LineBundleFlatDescent.compIso_assoc ι₂ g₂ j₂ (ι₂ ≫ g₂) (s₂ ≫ t) ((ι₁ ≫ s₁) ≫ t) rfl h₂.symm hc₂
    hn₂ M
  have a₃ := LineBundleFlatDescent.compIso_assoc ι₁ s₁ t (ι₁ ≫ s₁) (s₁ ≫ t) ((ι₁ ≫ s₁) ≫ t) rfl rfl hc₁ rfl M
  have a₄ := LineBundleFlatDescent.compIso_assoc ι₁ g₁ j₁ (ι₁ ≫ g₁) (s₁ ≫ t) ((ι₁ ≫ s₁) ≫ t) rfl h₁.symm hc₁
    hn₁ M
  have a₅ := LineBundleFlatDescent.compIso_assoc g₀ i₁ j₁ (ι₁ ≫ g₁) (i₁ ≫ j₁) ((ι₁ ≫ s₁) ≫ t) k₁.symm rfl hd
    hn₁ M
  have a₆ := LineBundleFlatDescent.compIso_assoc g₀ i₂ j₂ (ι₂ ≫ g₂) (i₁ ≫ j₁) ((ι₁ ≫ s₁) ≫ t) k₂.symm w.symm hd
    hn₂ M
  rw [← cancel_mono ((Scheme.Modules.pullback g₀).map
      (compIso i₂ j₂ (i₁ ≫ j₁) w.symm M).hom ≫
    (compIso g₀ (i₁ ≫ j₁) ((ι₁ ≫ s₁) ≫ t) hd M).hom)]
  simp only [legIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [squarePullbackIso_hom_eq_compIso s₂ ι₁ ι₂ s₁ wT (ι₁ ≫ s₁) rfl hv,
    squarePullbackIso_hom_eq_compIso j₂ s₂ g₂ t h₂ (s₂ ≫ t) rfl h₂.symm,
    squarePullbackIso_hom_eq_compIso i₂ ι₂ g₀ g₂ k₂ (ι₂ ≫ g₂) rfl k₂.symm,
    squarePullbackIso_hom_eq_compIso j₁ s₁ g₁ t h₁ (s₁ ≫ t) rfl h₁.symm,
    squarePullbackIso_hom_eq_compIso i₁ ι₁ g₀ g₁ k₁ (ι₁ ≫ g₁) rfl k₁.symm,
    squarePullbackIso_hom_eq_compIso j₂ i₁ i₂ j₁ w (i₁ ≫ j₁) rfl w.symm]
  simp only [Langlands.Scheme.Modules.compIso] at a₁ a₂ a₃ a₄ a₅ a₆ ⊢
  simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [← a₆, Iso.inv_hom_id_assoc, ← a₅, Iso.inv_hom_id_assoc, a₂, a₄]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← a₁, ← a₃, Iso.inv_hom_id_assoc]

variable {M N : Y.Modules}
  (e₁ : (Scheme.Modules.pullback j₁).obj M ≅ (Scheme.Modules.pullback j₁).obj N)
  (e₂ : (Scheme.Modules.pullback j₂).obj M ≅ (Scheme.Modules.pullback j₂).obj N)

include g₀ k₁ k₂ in
/-- A pair compatible with the bottom square transports to a pair compatible with
the top square of a commuting cube. -/
lemma localIso_compatible
    (he : (Scheme.Modules.pullback i₁).map e₁.hom ≫
        (squarePullbackIso j₂ i₁ i₂ j₁ w N).hom =
      (squarePullbackIso j₂ i₁ i₂ j₁ w M).hom ≫
        (Scheme.Modules.pullback i₂).map e₂.hom) :
    (Scheme.Modules.pullback ι₁).map (localIso t s₁ g₁ j₁ h₁ e₁).hom ≫
        (squarePullbackIso s₂ ι₁ ι₂ s₁ wT ((Scheme.Modules.pullback t).obj N)).hom =
      (squarePullbackIso s₂ ι₁ ι₂ s₁ wT ((Scheme.Modules.pullback t).obj M)).hom ≫
        (Scheme.Modules.pullback ι₂).map (localIso t s₂ g₂ j₂ h₂ e₂).hom := by
  rw [← cancel_mono (legIso t s₂ ι₂ g₂ g₀ i₂ j₂ h₂ k₂ N).hom]
  simp only [Category.assoc]
  rw [cube_coherence i₁ i₂ j₁ j₂ w t s₁ s₂ ι₁ ι₂ wT g₁ g₂ g₀ h₁ h₂ k₁ k₂ N,
    localIso_legIso_assoc, localIso_legIso,
    reassoc_of% (cube_coherence i₁ i₂ j₁ j₂ w t s₁ s₂ ι₁ ι₂ wT g₁ g₂ g₀ h₁ h₂ k₁ k₂ M),
    ← Functor.map_comp, he, Functor.map_comp]

include wT g₀ k₁ k₂ in
/-- On a cube whose two side faces are cartesian and whose top square has a
ring-pullback of global sections, compatible isomorphisms on the bottom legs
have a local lift on the corner, provided both modules are trivial there. -/
lemma exists_compatible_lift
    (P₁ : IsPullback g₁ s₁ j₁ t) (P₂ : IsPullback g₂ s₂ j₂ t)
    (hT : IsPullback s₁.appTop s₂.appTop ι₁.appTop ι₂.appTop)
    (τ : (Scheme.Modules.pullback t).obj M ≅ structureModule T)
    (σ : (Scheme.Modules.pullback t).obj N ≅ structureModule T)
    (he : (Scheme.Modules.pullback i₁).map e₁.hom ≫
        (squarePullbackIso j₂ i₁ i₂ j₁ w N).hom =
      (squarePullbackIso j₂ i₁ i₂ j₁ w M).hom ≫
        (Scheme.Modules.pullback i₂).map e₂.hom) :
    ∃ E : (Scheme.Modules.pullback t).obj M ≅ (Scheme.Modules.pullback t).obj N,
      LineBundleIsoDescent.Compatible j₁ e₁ t E.hom ∧
        LineBundleIsoDescent.Compatible j₂ e₂ t E.hom := by
  obtain ⟨E, ⟨hE₁, hE₂⟩, -⟩ := SquareTrivialIsoDescent.existsUnique_iso ι₁ ι₂ s₁ s₂ wT hT
    τ σ (localIso t s₁ g₁ j₁ P₁.w.symm e₁) (localIso t s₂ g₂ j₂ P₂.w.symm e₂)
    (localIso_compatible i₁ i₂ j₁ j₂ w t s₁ s₂ ι₁ ι₂ wT g₁ g₂ g₀ P₁.w.symm P₂.w.symm
      k₁ k₂ e₁ e₂ he)
  exact ⟨E, compatible_of_isPullback t s₁ g₁ j₁ e₁ P₁ E hE₁,
    compatible_of_isPullback t s₂ g₂ j₂ e₂ P₂ E hE₂⟩

end Cube

end Langlands.Scheme.Modules.SquareLocalIsoLift
