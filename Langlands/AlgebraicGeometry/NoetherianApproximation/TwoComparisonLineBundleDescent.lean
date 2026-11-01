import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.SimultaneousLineBundleIsoDescent
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.Tensor

/-! # Finite algebra models of line bundles with two trivial restrictions -/

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

namespace TwoComparisonDescent

/-- Base change of a morphism over a fixed base. -/
def overMap {S X Y T : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    (g : Y ⟶ X) (w : g ≫ fX = fY) (b : T ⟶ S) :
    pullback fY b ⟶ pullback fX b :=
  pullback.lift (pullback.fst fY b ≫ g) (pullback.snd fY b) (by
    rw [Category.assoc, w, pullback.condition])

@[reassoc (attr := simp)]
theorem overMap_fst {S X Y T : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    (g : Y ⟶ X) (w : g ≫ fX = fY) (b : T ⟶ S) :
    overMap fX fY g w b ≫ pullback.fst fX b = pullback.fst fY b ≫ g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem overMap_snd {S X Y T : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    (g : Y ⟶ X) (w : g ≫ fX = fY) (b : T ⟶ S) :
    overMap fX fY g w b ≫ pullback.snd fX b = pullback.snd fY b :=
  pullback.lift_snd _ _ _

/-- The transition between two base changes along a compatible base map. -/
def transition {S X T₁ T₂ : Scheme.{u}} (fX : X ⟶ S)
    (b₁ : T₁ ⟶ S) (b₂ : T₂ ⟶ S) (d : T₂ ⟶ T₁) (w : d ≫ b₁ = b₂) :
    pullback fX b₂ ⟶ pullback fX b₁ :=
  pullback.lift (pullback.fst fX b₂) (pullback.snd fX b₂ ≫ d) (by
    rw [Category.assoc, w, pullback.condition])

@[reassoc (attr := simp)]
theorem transition_fst {S X T₁ T₂ : Scheme.{u}} (fX : X ⟶ S)
    (b₁ : T₁ ⟶ S) (b₂ : T₂ ⟶ S) (d : T₂ ⟶ T₁) (w : d ≫ b₁ = b₂) :
    transition fX b₁ b₂ d w ≫ pullback.fst fX b₁ = pullback.fst fX b₂ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem transition_snd {S X T₁ T₂ : Scheme.{u}} (fX : X ⟶ S)
    (b₁ : T₁ ⟶ S) (b₂ : T₂ ⟶ S) (d : T₂ ⟶ T₁) (w : d ≫ b₁ = b₂) :
    transition fX b₁ b₂ d w ≫ pullback.snd fX b₁ = pullback.snd fX b₂ ≫ d :=
  pullback.lift_snd _ _ _

theorem transition_isPullback {S X T₁ T₂ : Scheme.{u}} (fX : X ⟶ S)
    (b₁ : T₁ ⟶ S) (b₂ : T₂ ⟶ S) (d : T₂ ⟶ T₁) (w : d ≫ b₁ = b₂) :
    IsPullback (transition fX b₁ b₂ d w) (pullback.snd fX b₂)
      (pullback.snd fX b₁) d := by
  refine IsPullback.of_right (h₁₂ := pullback.fst fX b₁) (v₁₃ := fX)
    (h₂₂ := b₁) ?_ (transition_snd fX b₁ b₂ d w)
    (IsPullback.of_hasPullback fX b₁)
  rw [transition_fst, w]
  exact IsPullback.of_hasPullback fX b₂

theorem overMap_transition {S X Y T₁ T₂ : Scheme.{u}}
    (fX : X ⟶ S) (fY : Y ⟶ S) (g : Y ⟶ X) (wg : g ≫ fX = fY)
    (b₁ : T₁ ⟶ S) (b₂ : T₂ ⟶ S) (d : T₂ ⟶ T₁) (w : d ≫ b₁ = b₂) :
    overMap fX fY g wg b₂ ≫ transition fX b₁ b₂ d w =
      transition fY b₁ b₂ d w ≫ overMap fX fY g wg b₁ := by
  apply pullback.hom_ext <;> simp only [Category.assoc, transition_fst,
    transition_snd, overMap_fst, overMap_snd, transition_fst_assoc, overMap_snd_assoc]

/-- The comparison from a given base-change square to an intermediate stage. -/
def comparison {S X X₀ T V : Scheme.{u}} (a : X ⟶ X₀) (f : X ⟶ V)
    (f₀ : X₀ ⟶ S) (b : T ⟶ S) (k : V ⟶ T)
    (w : a ≫ f₀ = f ≫ k ≫ b) : X ⟶ pullback f₀ b :=
  pullback.lift a (f ≫ k) (by simpa only [Category.assoc] using w)

@[reassoc (attr := simp)]
theorem comparison_fst {S X X₀ T V : Scheme.{u}} (a : X ⟶ X₀) (f : X ⟶ V)
    (f₀ : X₀ ⟶ S) (b : T ⟶ S) (k : V ⟶ T)
    (w : a ≫ f₀ = f ≫ k ≫ b) :
    comparison a f f₀ b k w ≫ pullback.fst f₀ b = a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem comparison_snd {S X X₀ T V : Scheme.{u}} (a : X ⟶ X₀) (f : X ⟶ V)
    (f₀ : X₀ ⟶ S) (b : T ⟶ S) (k : V ⟶ T)
    (w : a ≫ f₀ = f ≫ k ≫ b) :
    comparison a f f₀ b k w ≫ pullback.snd f₀ b = f ≫ k :=
  pullback.lift_snd _ _ _

theorem comparison_isPullback {S X X₀ T V : Scheme.{u}} (a : X ⟶ X₀) (f : X ⟶ V)
    (f₀ : X₀ ⟶ S) (b : T ⟶ S) (k : V ⟶ T)
    (w : a ≫ f₀ = f ≫ k ≫ b) (h : IsPullback a f f₀ (k ≫ b)) :
    IsPullback (comparison a f f₀ b k w) f (pullback.snd f₀ b) k := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f₀ b) (v₁₃ := f₀)
    (h₂₂ := b) ?_ (comparison_snd a f f₀ b k w)
    (IsPullback.of_hasPullback f₀ b)
  rw [comparison_fst]
  exact h

end TwoComparisonDescent

open TwoComparisonDescent

/-- A finite algebra stage carrying an actual bundle and its two trivial restrictions.
The comparison to the original bundle holds along every compatible stage map. -/
structure TwoComparisonLineBundleModel
    {C A : Type u} [CommRing C] [CommRing A] [Algebra C A]
    {X₀ Y₀ : Scheme.{u}} (fX₀ : X₀ ⟶ Spec (CommRingCat.of C))
    (fY₀ : Y₀ ⟶ Spec (CommRingCat.of C)) (g₁ g₂ : Y₀ ⟶ X₀)
    (w₁ : g₁ ≫ fX₀ = fY₀) (w₂ : g₂ ≫ fX₀ = fY₀)
    {X : Scheme.{u}} (aX : X ⟶ X₀) (fX : X ⟶ Spec (CommRingCat.of A))
    (M : LineBundle X) where
  T : Subalgebra C A
  fg : T.FG
  bundle : LineBundle (pullback fX₀ (Spec.map (CommRingCat.ofHom (algebraMap C T))))
  first : Nonempty ((Scheme.Modules.pullback
    (overMap fX₀ fY₀ g₁ w₁ (Spec.map (CommRingCat.ofHom (algebraMap C T))))).obj
      bundle.obj ≅ structureSheaf _)
  second : Nonempty ((Scheme.Modules.pullback
    (overMap fX₀ fY₀ g₂ w₂ (Spec.map (CommRingCat.ofHom (algebraMap C T))))).obj
      bundle.obj ≅ structureSheaf _)
  comparison : ∀ c : X ⟶ pullback fX₀
      (Spec.map (CommRingCat.ofHom (algebraMap C T))),
    c ≫ pullback.fst _ _ = aX →
    c ≫ pullback.snd _ _ = fX ≫ Spec.map (CommRingCat.ofHom (algebraMap T A)) →
    Nonempty ((Scheme.Modules.pullback c).obj bundle.obj ≅ M.obj)

/-- An actual line bundle with two trivial restrictions descends to one finite
algebra stage, together with those two restrictions. -/
theorem exists_twoComparisonLineBundleModel
    {C A : Type u} [CommRing C] [CommRing A] [Algebra C A]
    {X₀ Y₀ : Scheme.{u}} (fX₀ : X₀ ⟶ Spec (CommRingCat.of C))
    (fY₀ : Y₀ ⟶ Spec (CommRingCat.of C))
    [QuasiCompact fX₀] [QuasiSeparated fX₀]
    [QuasiCompact fY₀] [QuasiSeparated fY₀]
    (g₁ g₂ : Y₀ ⟶ X₀) (w₁ : g₁ ≫ fX₀ = fY₀) (w₂ : g₂ ≫ fX₀ = fY₀)
    {X Y : Scheme.{u}} (aX : X ⟶ X₀) (fX : X ⟶ Spec (CommRingCat.of A))
    (aY : Y ⟶ Y₀) (fY : Y ⟶ Spec (CommRingCat.of A))
    (hX : IsPullback aX fX fX₀ (Spec.map (CommRingCat.ofHom (algebraMap C A))))
    (hY : IsPullback aY fY fY₀ (Spec.map (CommRingCat.ofHom (algebraMap C A))))
    (t₁ t₂ : Y ⟶ X)
    (ht₁ : t₁ ≫ aX = aY ≫ g₁) (ht₂ : t₂ ≫ aX = aY ≫ g₂)
    (hf₁ : t₁ ≫ fX = fY) (hf₂ : t₂ ≫ fX = fY)
    (M : LineBundle X)
    (e₁ : Nonempty ((Scheme.Modules.pullback t₁).obj M.obj ≅ structureSheaf Y))
    (e₂ : Nonempty ((Scheme.Modules.pullback t₂).obj M.obj ≅ structureSheaf Y))
    (s : Finset A) :
    ∃ S : TwoComparisonLineBundleModel fX₀ fY₀ g₁ g₂ w₁ w₂ aX fX M,
      (↑s : Set A) ⊆ S.T := by
  obtain ⟨B, hB, hsB, NB, hNB, hmodel⟩ :=
    lineBundleSubalgebraDescent fX₀ aX fX hX M.obj M.property s
  let βB := Spec.map (CommRingCat.ofHom (algebraMap C B))
  let κB := Spec.map (CommRingCat.ofHom (algebraMap B A))
  have hκB : κB ≫ βB = Spec.map (CommRingCat.ofHom (algebraMap C A)) := by
    dsimp only [κB, βB]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hwX : aX ≫ fX₀ = fX ≫ κB ≫ βB := by rw [hκB]; exact hX.w
  have hwY : aY ≫ fY₀ = fY ≫ κB ≫ βB := by rw [hκB]; exact hY.w
  let cX := comparison aX fX fX₀ βB κB hwX
  let cY := comparison aY fY fY₀ βB κB hwY
  obtain ⟨eX⟩ := hmodel cX (comparison_fst ..) (comparison_snd ..)
  have hcY : IsPullback cY fY (pullback.snd fY₀ βB) κB := by
    apply comparison_isPullback
    rw [hκB]
    exact hY
  have hcompare (g : Y₀ ⟶ X₀) (wg : g ≫ fX₀ = fY₀) (t : Y ⟶ X)
      (ht : t ≫ aX = aY ≫ g) (hf : t ≫ fX = fY) :
      cY ≫ overMap fX₀ fY₀ g wg βB = t ≫ cX := by
    apply pullback.hom_ext
    · dsimp only [cX, cY]
      simp only [Category.assoc, overMap_fst, comparison_fst_assoc,
        comparison_fst]
      exact ht.symm
    · dsimp only [cX, cY]
      simpa only [Category.assoc, overMap_snd, comparison_snd,
        comparison_snd_assoc] using congrArg (fun q => q ≫ κB) hf.symm
  have hiso (g : Y₀ ⟶ X₀) (wg : g ≫ fX₀ = fY₀) (t : Y ⟶ X)
      (ht : t ≫ aX = aY ≫ g) (hf : t ≫ fX = fY)
      (e : Nonempty ((Scheme.Modules.pullback t).obj M.obj ≅ structureSheaf Y)) :
      Nonempty ((Scheme.Modules.pullback cY).obj
          ((Scheme.Modules.pullback (overMap fX₀ fY₀ g wg βB)).obj NB) ≅
        (Scheme.Modules.pullback cY).obj (structureSheaf (pullback fY₀ βB))) := by
    obtain ⟨e⟩ := e
    exact ⟨(Scheme.Modules.pullbackComp cY (overMap fX₀ fY₀ g wg βB)).app NB ≪≫
      (Scheme.Modules.pullbackCongr (hcompare g wg t ht hf)).app NB ≪≫
      ((Scheme.Modules.pullbackComp t cX).app NB).symm ≪≫
      (Scheme.Modules.pullback t).mapIso eX ≪≫ e ≪≫ (pullbackUnitIso cY).symm⟩
  obtain ⟨U, hU, _, hall⟩ := exists_fg_pair_lineBundle_iso
    (pullback.snd fY₀ βB)
    ((Scheme.Modules.pullback (overMap fX₀ fY₀ g₁ w₁ βB)).obj NB) (structureSheaf _)
    ((Scheme.Modules.pullback (overMap fX₀ fY₀ g₂ w₂ βB)).obj NB) (structureSheaf _)
    (hNB.pullback _) (LineBundle.trivial _).property
    (hNB.pullback _) (LineBundle.trivial _).property cY fY hcY
    (hiso g₁ w₁ t₁ ht₁ hf₁ e₁) (hiso g₂ w₂ t₂ ht₂ hf₂ e₂) ∅
  let T := U.restrictScalars C
  have hBft : Algebra.FiniteType C B := (Subalgebra.fg_iff_finiteType _).1 hB
  have hUft : Algebra.FiniteType B U := (Subalgebra.fg_iff_finiteType _).1 hU
  have hT : T.FG := by
    apply (Subalgebra.fg_iff_finiteType _).2
    change Algebra.FiniteType C U
    exact Algebra.FiniteType.trans hBft hUft
  let βT := Spec.map (CommRingCat.ofHom (algebraMap C T))
  let θ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B U))
  let κT := Spec.map (CommRingCat.ofHom (algebraMap T A))
  have hθ : θ ≫ βB = βT := by
    change Spec.map (CommRingCat.ofHom (algebraMap B U)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap C B)) =
      Spec.map (CommRingCat.ofHom (algebraMap C U))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hκθ : κT ≫ θ = κB := by
    change Spec.map (CommRingCat.ofHom (algebraMap U A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B U)) =
      Spec.map (CommRingCat.ofHom (algebraMap B A))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let pX := transition fX₀ βB βT θ hθ
  let pY := transition fY₀ βB βT θ hθ
  obtain ⟨i₁, i₂⟩ := hall pY (pullback.snd fY₀ βT)
    (transition_isPullback fY₀ βB βT θ hθ)
  have htriv (g : Y₀ ⟶ X₀) (wg : g ≫ fX₀ = fY₀)
      (i : Nonempty ((Scheme.Modules.pullback pY).obj
          ((Scheme.Modules.pullback (overMap fX₀ fY₀ g wg βB)).obj NB) ≅
        (Scheme.Modules.pullback pY).obj (structureSheaf (pullback fY₀ βB)))) :
      Nonempty ((Scheme.Modules.pullback (overMap fX₀ fY₀ g wg βT)).obj
        ((Scheme.Modules.pullback pX).obj NB) ≅ structureSheaf _) := by
    obtain ⟨i⟩ := i
    exact ⟨(Scheme.Modules.pullbackComp (overMap fX₀ fY₀ g wg βT) pX).app NB ≪≫
      (Scheme.Modules.pullbackCongr (overMap_transition ..)).app NB ≪≫
      ((Scheme.Modules.pullbackComp pY (overMap fX₀ fY₀ g wg βB)).app NB).symm ≪≫
      i ≪≫ pullbackUnitIso pY⟩
  refine ⟨⟨T, hT, ⟨(Scheme.Modules.pullback pX).obj NB, hNB.pullback _⟩,
    htriv g₁ w₁ i₁, htriv g₂ w₂ i₂, ?_⟩, ?_⟩
  · intro c hc₁ hc₂
    have hcp₁ : (c ≫ pX) ≫ pullback.fst fX₀ βB = aX := by
      rw [Category.assoc, show pX ≫ pullback.fst fX₀ βB =
        pullback.fst fX₀ βT from transition_fst fX₀ βB βT θ hθ]
      exact hc₁
    have hcp₂ : (c ≫ pX) ≫ pullback.snd fX₀ βB = fX ≫ κB := by
      rw [Category.assoc, show pX ≫ pullback.snd fX₀ βB =
        pullback.snd fX₀ βT ≫ θ from transition_snd fX₀ βB βT θ hθ,
        ← Category.assoc c, hc₂,
        Category.assoc, hκθ]
    obtain ⟨e⟩ := hmodel (c ≫ pX) hcp₁ hcp₂
    exact ⟨(Scheme.Modules.pullbackComp c pX).app NB ≪≫ e⟩
  · intro x hx
    exact U.algebraMap_mem (⟨x, hsB hx⟩ : B)

end Langlands.AlgebraicGeometry.NoetherianApproximation
