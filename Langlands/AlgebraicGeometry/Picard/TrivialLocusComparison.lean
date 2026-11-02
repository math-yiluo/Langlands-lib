import Langlands.AlgebraicGeometry.Picard.ClassEqualizerReduction
import Langlands.AlgebraicGeometry.Picard.FrameCombinationTrivialization
import Langlands.AlgebraicGeometry.Modules.SchemeIsoCohomology

/-! # Comparing base changes of line bundles and their global sections

The triviality locus of a line bundle `N` on `T ×_S X` is phrased with the chosen fibre products
`(relativeSpace f).obj T'`. Cohomology and base change theorems use other fibre products. This
file transfers triviality from one to the other, and compares global sections of pullbacks of a
module along two pullback squares of the same cospan, as modules over the base ring.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.TwoAffineOpenCover (moduleSectionsOfHom)
open Langlands.AlgebraicGeometry.AlgebraicSpace (specOver)

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace RelativePicard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The relative space functor sends a morphism of `Over S` to a pullback square. -/
lemma relativeSpace_isPullback {T V : Over S} (φ : V ⟶ T) :
    IsPullback ((relativeSpace f).map φ) (pullback.fst V.hom f) (pullback.fst T.hom f) φ.left := by
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback T.hom f).flip
  · rw [relativeSpace_map_snd, Over.w φ]
    exact (IsPullback.of_hasPullback V.hom f).flip
  · simp only [relativeSpace, Functor.comp_map, Over.forget_map, Over.pullback_map_left]
    exact pullback.lift_fst _ _ _

/-- If `N` becomes trivial along `g`, then it becomes trivial along every morphism `q` lying
over `g`. -/
lemma nonempty_pullback_iso_trivial_of_mem {T : Over S} {N : LineBundle ((relativeSpace f).obj T)}
    {T' : Scheme.{u}} {g : T' ⟶ T.left} (hg : isoLocus f T N (LineBundle.trivial _) g)
    {P : Scheme.{u}} (q : P ⟶ (relativeSpace f).obj T) (p : P ⟶ T')
    (w : q ≫ pullback.fst T.hom f = p ≫ g) :
    Nonempty ((LineBundle.pullback q).obj N ≅ LineBundle.trivial P) := by
  obtain ⟨e⟩ := (isoLocus_trivial_iff f N g).mp hg
  let c : P ⟶ (relativeSpace f).obj (Over.mk (g ≫ T.hom)) :=
    pullback.lift p (q ≫ pullback.snd T.hom f) (by
      simp only [Over.mk_hom]
      rw [Category.assoc, ← pullback.condition, reassoc_of% w])
  have hc : c ≫ (relativeSpace f).map (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T) = q := by
    apply pullback.hom_ext
    · rw [Category.assoc, (relativeSpace_isPullback f _).w, w]
      exact pullback.lift_fst_assoc _ _ _ _
    · rw [Category.assoc, relativeSpace_map_snd]
      exact pullback.lift_snd _ _ _
  exact ⟨(LineBundle.pullbackCompEqIso c _ hc N).symm ≪≫ (LineBundle.pullback c).mapIso e ≪≫
    LineBundle.pullbackTrivialIso c⟩

end RelativePicard

/-! ### Global sections as modules over the base ring -/

namespace SectionsComparison

variable {A : Type u} [CommRing A]

/-- A morphism of modules is linear over the base ring on global sections. -/
def sectionsMap {P : Scheme.{u}} (p : P ⟶ Spec (.of A)) {M M' : P.Modules} (φ : M ⟶ M') :
    letI := moduleSectionsOfHom p M ⊤; letI := moduleSectionsOfHom p M' ⊤
    Γ(M, ⊤) →ₗ[A] Γ(M', ⊤) :=
  letI := moduleSectionsOfHom p M ⊤; letI := moduleSectionsOfHom p M' ⊤
  { toFun := φ.app ⊤
    map_add' := map_add (φ.app ⊤).hom
    map_smul' := fun _ x => Scheme.Modules.Hom.app_smul φ _ x }

lemma sectionsMap_apply {P : Scheme.{u}} (p : P ⟶ Spec (.of A)) {M M' : P.Modules}
    (φ : M ⟶ M') (x : Γ(M, ⊤)) : sectionsMap p φ x = φ.app ⊤ x :=
  rfl

/-- An isomorphism of modules gives a linear equivalence of global sections. -/
def sectionsEquivOfIso {P : Scheme.{u}} (p : P ⟶ Spec (.of A)) {M M' : P.Modules}
    (e : M ≅ M') :
    letI := moduleSectionsOfHom p M ⊤; letI := moduleSectionsOfHom p M' ⊤
    Γ(M, ⊤) ≃ₗ[A] Γ(M', ⊤) :=
  letI := moduleSectionsOfHom p M ⊤; letI := moduleSectionsOfHom p M' ⊤
  { sectionsMap p e.hom with
    invFun := e.inv.app ⊤
    left_inv := fun x => by
      change (e.hom ≫ e.inv).app ⊤ x = x
      rw [e.hom_inv_id]
      rfl
    right_inv := fun x => by
      change (e.inv ≫ e.hom).app ⊤ x = x
      rw [e.inv_hom_id]
      rfl }

/-- Pulling back global sections along a morphism over `Spec A` is `A`-linear. -/
def pullbackSectionsMap {P₁ P₂ : Scheme.{u}} (p₁ : P₁ ⟶ Spec (.of A)) (p₂ : P₂ ⟶ Spec (.of A))
    (c : P₁ ⟶ P₂) (hc : c ≫ p₂ = p₁) (M : P₂.Modules) :
    letI := moduleSectionsOfHom p₂ M ⊤
    letI := moduleSectionsOfHom p₁ ((Scheme.Modules.pullback c).obj M) ⊤
    Γ(M, ⊤) →ₗ[A] Γ((Scheme.Modules.pullback c).obj M, ⊤) :=
  letI := moduleSectionsOfHom p₂ M ⊤
  letI := moduleSectionsOfHom p₁ ((Scheme.Modules.pullback c).obj M) ⊤
  { toFun := FrameCombination.pullbackGlobalSection c
    map_add' := fun x y => by
      simpa using FrameCombination.pullbackGlobalSection_sum c Finset.univ ![x, y]
    map_smul' := fun r x => by
      change FrameCombination.pullbackGlobalSection c
          ((p₂.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of A)).inv.hom r) • x) =
        (p₁.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of A)).inv.hom r) •
          FrameCombination.pullbackGlobalSection c x
      rw [FrameCombination.pullbackGlobalSection_smul]
      congr 1
      have h : p₂.appLE ⊤ ⊤ le_top ≫ c.appTop = p₁.appLE ⊤ ⊤ le_top := by
        have h₁ : p₁.appLE ⊤ ⊤ le_top = p₁.appTop := p₁.appLE_eq_app
        have h₂ : p₂.appLE ⊤ ⊤ le_top = p₂.appTop := p₂.appLE_eq_app
        rw [h₁, h₂, ← hc]
        rfl
      rw [← h]
      rfl }

lemma pullbackSectionsMap_apply {P₁ P₂ : Scheme.{u}} (p₁ : P₁ ⟶ Spec (.of A))
    (p₂ : P₂ ⟶ Spec (.of A)) (c : P₁ ⟶ P₂) (hc : c ≫ p₂ = p₁) (M : P₂.Modules) (x : Γ(M, ⊤)) :
    pullbackSectionsMap p₁ p₂ c hc M x = FrameCombination.pullbackGlobalSection c x :=
  rfl

/-- Pulling back global sections along an isomorphism over `Spec A` is an `A`-linear
equivalence. -/
def pullbackSectionsEquiv {P₁ P₂ : Scheme.{u}} (p₁ : P₁ ⟶ Spec (.of A)) (p₂ : P₂ ⟶ Spec (.of A))
    (c : P₁ ⟶ P₂) [IsIso c] (hc : c ≫ p₂ = p₁) (M : P₂.Modules) :
    letI := moduleSectionsOfHom p₂ M ⊤
    letI := moduleSectionsOfHom p₁ ((Scheme.Modules.pullback c).obj M) ⊤
    Γ(M, ⊤) ≃ₗ[A] Γ((Scheme.Modules.pullback c).obj M, ⊤) :=
  letI := moduleSectionsOfHom p₂ M ⊤
  letI := moduleSectionsOfHom p₁ ((Scheme.Modules.pullback c).obj M) ⊤
  have : (Scheme.Modules.pushforward c).IsEquivalence :=
    (Modules.pushforwardEquivalence (asIso c)).isEquivalence_functor
  have := (Scheme.Modules.pullbackPushforwardAdjunction c).isEquivalence_left_of_isEquivalence_right
  let u := (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M
  LinearEquiv.ofBijective (pullbackSectionsMap p₁ p₂ c hc M) <| by
    change Function.Bijective (u.app ⊤)
    have : IsIso u := inferInstance
    refine ⟨fun x y hxy => ?_, fun y => ⟨(inv u).app ⊤ y, ?_⟩⟩
    · have := congrArg ((inv u).app ⊤) hxy
      change (u ≫ inv u).app ⊤ x = (u ≫ inv u).app ⊤ y at this
      simpa using this
    · change (inv u ≫ u).app ⊤ y = y
      rw [IsIso.inv_hom_id]
      rfl

/-- Global sections of the structure sheaf of isomorphic schemes over `Spec A` agree. -/
def unitSectionsEquiv {P₁ P₂ : Scheme.{u}} (p₁ : P₁ ⟶ Spec (.of A)) (p₂ : P₂ ⟶ Spec (.of A))
    (c : P₁ ⟶ P₂) [IsIso c] (hc : c ≫ p₂ = p₁) :
    letI := moduleSectionsOfHom p₁ (SheafOfModules.unit P₁.ringCatSheaf) ⊤
    letI := moduleSectionsOfHom p₂ (SheafOfModules.unit P₂.ringCatSheaf) ⊤
    Γ(SheafOfModules.unit P₁.ringCatSheaf, ⊤) ≃ₗ[A] Γ(SheafOfModules.unit P₂.ringCatSheaf, ⊤) :=
  ((pullbackSectionsEquiv p₁ p₂ c hc _).trans
    (sectionsEquivOfIso p₁ (Langlands.Scheme.Modules.pullbackUnitIso c))).symm

/-- Global sections of the pullbacks of a module along two pullback squares of the same cospan
agree as modules over the base ring. -/
def sectionsEquivOfIsPullback {Y S₀ P₁ P₂ : Scheme.{u}} {u : Y ⟶ S₀} {v : Spec (.of A) ⟶ S₀}
    {q₁ : P₁ ⟶ Y} {p₁ : P₁ ⟶ Spec (.of A)} {q₂ : P₂ ⟶ Y} {p₂ : P₂ ⟶ Spec (.of A)}
    (h₁ : IsPullback q₁ p₁ u v) (h₂ : IsPullback q₂ p₂ u v) (M : Y.Modules) :
    letI := moduleSectionsOfHom p₁ ((Scheme.Modules.pullback q₁).obj M) ⊤
    letI := moduleSectionsOfHom p₂ ((Scheme.Modules.pullback q₂).obj M) ⊤
    Γ((Scheme.Modules.pullback q₁).obj M, ⊤) ≃ₗ[A] Γ((Scheme.Modules.pullback q₂).obj M, ⊤) :=
  ((pullbackSectionsEquiv p₁ p₂ (h₁.isoIsPullback _ _ h₂).hom
      (h₁.isoIsPullback_hom_snd _ _ h₂) _).trans
    (sectionsEquivOfIso p₁ ((Scheme.Modules.pullbackComp _ q₂).app M ≪≫
      (Scheme.Modules.pullbackCongr (h₁.isoIsPullback_hom_fst _ _ h₂)).app M))).symm

/-- The structure sheaf version of `sectionsEquivOfIsPullback`. -/
def unitSectionsEquivOfIsPullback {Y S₀ P₁ P₂ : Scheme.{u}} {u : Y ⟶ S₀}
    {v : Spec (.of A) ⟶ S₀} {q₁ : P₁ ⟶ Y} {p₁ : P₁ ⟶ Spec (.of A)} {q₂ : P₂ ⟶ Y}
    {p₂ : P₂ ⟶ Spec (.of A)} (h₁ : IsPullback q₁ p₁ u v) (h₂ : IsPullback q₂ p₂ u v) :
    letI := moduleSectionsOfHom p₁ (SheafOfModules.unit P₁.ringCatSheaf) ⊤
    letI := moduleSectionsOfHom p₂ (SheafOfModules.unit P₂.ringCatSheaf) ⊤
    Γ(SheafOfModules.unit P₁.ringCatSheaf, ⊤) ≃ₗ[A] Γ(SheafOfModules.unit P₂.ringCatSheaf, ⊤) :=
  unitSectionsEquiv p₁ p₂ (h₁.isoIsPullback _ _ h₂).hom (h₁.isoIsPullback_hom_snd _ _ h₂)

end SectionsComparison

end Langlands.AlgebraicGeometry.Picard
