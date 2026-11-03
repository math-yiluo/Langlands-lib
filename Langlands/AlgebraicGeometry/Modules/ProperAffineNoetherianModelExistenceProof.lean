import Langlands.AlgebraicGeometry.Modules.ProperAffineNoetherianModelExistenceStatement
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsNoetherianReduction
import Langlands.AlgebraicGeometry.NoetherianApproximation.IsProperSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.FlatnessSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentProof

/-! # Noetherian models of proper schemes with two finitely presented modules -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

namespace ProperNoetherianModelProof

open NoetherianReduction NoetherianApproximation

variable {A : Type u} [CommRing A]

/-- Final stage: descend the flatness of the target module over a noetherian base. -/
theorem exists_model_of_modules {T : Type u} [CommRing T] [IsNoetherianRing T] [Algebra T A]
    {X₅ Y : Scheme.{u}} (f₅ : X₅ ⟶ Spec (CommRingCat.of T)) [IsProper f₅]
    [LocallyOfFinitePresentation f₅] {a₅ : Y ⟶ X₅} {p : Y ⟶ Spec (CommRingCat.of A)}
    (h₅ : IsPullback a₅ p f₅ (Spec.map (CommRingCat.ofHom (algebraMap T A))))
    {M N : Y.Modules} (M₅ N₅ : X₅.Modules) [M₅.IsFinitePresentation]
    [N₅.IsFinitePresentation] (eM : (Scheme.Modules.pullback a₅).obj M₅ ≅ M)
    (eN : (Scheme.Modules.pullback a₅).obj N₅ ≅ N) (hflat : IsFlatOver p N) :
    HasAffineNoetherianModel p M N := by
  obtain ⟨T₆, hT₆, -, hfl⟩ := isFlatOverSubalgebraDescent f₅ N₅ inferInstance a₅ p h₅
    ((isFlatOver_iff_of_iso p eN).mpr hflat) (∅ : Finset A)
  have := NoetherianReduction.isNoetherianRing_of_fg hT₆
  obtain ⟨a₆, ha₆fst, -, h₆⟩ := exists_isPullback_subalgebra h₅ T₆
  let fst := pullback.fst f₅ (Spec.map (CommRingCat.ofHom (algebraMap T T₆)))
  refine ⟨CommRingCat.of T₆, this, CommRingCat.ofHom (algebraMap T₆ A), _,
    pullback.snd f₅ (Spec.map (CommRingCat.ofHom (algebraMap T T₆))), a₆,
    (Scheme.Modules.pullback fst).obj M₅, (Scheme.Modules.pullback fst).obj N₅,
    inferInstance, inferInstance, isFinitePresentation_pullback fst M₅,
    isFinitePresentation_pullback fst N₅,
    hfl fst (pullback.snd _ _) (IsPullback.of_hasPullback _ _), h₆, ⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackComp a₆ fst).app M₅ ≪≫
      (Scheme.Modules.pullbackCongr ha₆fst).app M₅ ≪≫ eM
  · exact (Scheme.Modules.pullbackComp a₆ fst).app N₅ ≪≫
      (Scheme.Modules.pullbackCongr ha₆fst).app N₅ ≪≫ eN

/-- Target-module stage: descend the target module over a noetherian base. -/
theorem exists_model_of_module {T : Type u} [CommRing T] [IsNoetherianRing T] [Algebra T A]
    {X₄ Y : Scheme.{u}} (f₄ : X₄ ⟶ Spec (CommRingCat.of T)) [IsProper f₄]
    [LocallyOfFinitePresentation f₄] {a₄ : Y ⟶ X₄} {p : Y ⟶ Spec (CommRingCat.of A)}
    (h₄ : IsPullback a₄ p f₄ (Spec.map (CommRingCat.ofHom (algebraMap T A))))
    {M N : Y.Modules} (M₄ : X₄.Modules) [M₄.IsFinitePresentation]
    (eM : (Scheme.Modules.pullback a₄).obj M₄ ≅ M) (hN : N.IsFinitePresentation)
    (hflat : IsFlatOver p N) : HasAffineNoetherianModel p M N := by
  obtain ⟨T₅, hT₅, -, N₅, hN₅, hc⟩ :=
    finitePresentationModuleSubalgebraDescent f₄ a₄ p h₄ N hN (∅ : Finset A)
  have := NoetherianReduction.isNoetherianRing_of_fg hT₅
  obtain ⟨a₅, ha₅fst, ha₅snd, h₅⟩ := exists_isPullback_subalgebra h₄ T₅
  obtain ⟨eN⟩ := hc a₅ ha₅fst ha₅snd
  let fst := pullback.fst f₄ (Spec.map (CommRingCat.ofHom (algebraMap T T₅)))
  have := isFinitePresentation_pullback fst M₄
  exact exists_model_of_modules (pullback.snd f₄ (Spec.map (CommRingCat.ofHom (algebraMap T T₅))))
    h₅ ((Scheme.Modules.pullback fst).obj M₄) N₅
    ((Scheme.Modules.pullbackComp a₅ fst).app M₄ ≪≫
      (Scheme.Modules.pullbackCongr ha₅fst).app M₄ ≪≫ eM) eN hflat

/-- Source-module stage: descend the source module over a noetherian base. -/
theorem exists_model_of_isProper {T : Type u} [CommRing T] [IsNoetherianRing T] [Algebra T A]
    {X₃ Y : Scheme.{u}} (f₃ : X₃ ⟶ Spec (CommRingCat.of T)) [IsProper f₃]
    [LocallyOfFinitePresentation f₃] {a₃ : Y ⟶ X₃} {p : Y ⟶ Spec (CommRingCat.of A)}
    (h₃ : IsPullback a₃ p f₃ (Spec.map (CommRingCat.ofHom (algebraMap T A))))
    {M N : Y.Modules} (hM : M.IsFinitePresentation) (hN : N.IsFinitePresentation)
    (hflat : IsFlatOver p N) : HasAffineNoetherianModel p M N := by
  obtain ⟨T₄, hT₄, -, M₄, hM₄, hc⟩ :=
    finitePresentationModuleSubalgebraDescent f₃ a₃ p h₃ M hM (∅ : Finset A)
  have := NoetherianReduction.isNoetherianRing_of_fg hT₄
  obtain ⟨a₄, ha₄fst, ha₄snd, h₄⟩ := exists_isPullback_subalgebra h₃ T₄
  obtain ⟨eM⟩ := hc a₄ ha₄fst ha₄snd
  exact exists_model_of_module (pullback.snd f₃ (Spec.map (CommRingCat.ofHom (algebraMap T T₄))))
    h₄ M₄ eM hN hflat

/-- Properness stage: descend properness over a noetherian base. -/
theorem exists_model_of_isSeparated {T : Type u} [CommRing T] [IsNoetherianRing T]
    [Algebra T A] {X₂ Y : Scheme.{u}} (f₂ : X₂ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₂]
    [QuasiCompact f₂] [LocallyOfFinitePresentation f₂] {a₂ : Y ⟶ X₂}
    {p : Y ⟶ Spec (CommRingCat.of A)} [IsProper p]
    (h₂ : IsPullback a₂ p f₂ (Spec.map (CommRingCat.ofHom (algebraMap T A))))
    {M N : Y.Modules} (hM : M.IsFinitePresentation) (hN : N.IsFinitePresentation)
    (hflat : IsFlatOver p N) : HasAffineNoetherianModel p M N := by
  have : IsProper (pullback.snd f₂ (Spec.map (CommRingCat.ofHom (algebraMap T A)))) :=
    (iff_pullback_snd_of_isPullback @IsProper h₂).mp ‹_›
  obtain ⟨T₃, hT₃, -, hpr₃⟩ := isProperSubalgebraDescent f₂ (∅ : Finset A)
  have := NoetherianReduction.isNoetherianRing_of_fg hT₃
  obtain ⟨X₃, f₃, a₃, b₃, hb₃, h₃⟩ := exists_isPullback_subalgebra' h₂ T₃
  have : IsProper f₃ := (iff_pullback_snd_of_isPullback @IsProper hb₃).mpr hpr₃
  have : LocallyOfFinitePresentation f₃ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hb₃ ‹_›
  exact exists_model_of_isProper f₃ h₃ hM hN hflat

/-- Separatedness stage: descend separatedness over a noetherian base. -/
theorem exists_model_of_finitePresentation {T : Type u} [CommRing T] [IsNoetherianRing T]
    [Algebra T A] {X₁ Y : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of T))
    [LocallyOfFinitePresentation f₁] [QuasiCompact f₁] [QuasiSeparated f₁] {a₁ : Y ⟶ X₁}
    {p : Y ⟶ Spec (CommRingCat.of A)} [IsProper p]
    (h₁ : IsPullback a₁ p f₁ (Spec.map (CommRingCat.ofHom (algebraMap T A))))
    {M N : Y.Modules} (hM : M.IsFinitePresentation) (hN : N.IsFinitePresentation)
    (hflat : IsFlatOver p N) : HasAffineNoetherianModel p M N := by
  have : IsSeparated (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap T A)))) :=
    (iff_pullback_snd_of_isPullback @IsSeparated h₁).mp inferInstance
  obtain ⟨T₂, hT₂, -, hsep₂⟩ := isSeparatedSubalgebraDescent f₁ (∅ : Finset A)
  have := NoetherianReduction.isNoetherianRing_of_fg hT₂
  obtain ⟨X₂, f₂, a₂, b₂, hb₂, h₂⟩ := exists_isPullback_subalgebra' h₁ T₂
  have : IsSeparated f₂ := (iff_pullback_snd_of_isPullback @IsSeparated hb₂).mpr hsep₂
  have : QuasiCompact f₂ := MorphismProperty.of_isPullback (P := @QuasiCompact) hb₂ ‹_›
  have : LocallyOfFinitePresentation f₂ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hb₂ ‹_›
  exact exists_model_of_isSeparated f₂ h₂ hM hN hflat

/-- Over an arbitrary commutative ring: descend the scheme to a finitely generated
subalgebra over the prime subring. -/
theorem exists_model {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of A)) [IsProper p]
    [LocallyOfFinitePresentation p] {M N : Y.Modules} (hM : M.IsFinitePresentation)
    (hN : N.IsFinitePresentation) (hflat : IsFlatOver p N) :
    HasAffineNoetherianModel p M N := by
  have : IsNoetherianRing (⊥ : Subalgebra ℤ A) := by
    have := (Subalgebra.fg_iff_finiteType (⊥ : Subalgebra ℤ A)).mp Subalgebra.fg_bot
    exact Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨T₁, hT₁, -, X₁, f₁, a₁, _, _, _, h₁⟩ :=
    schemeSubalgebraDescent (A₀ := (⊥ : Subalgebra ℤ A)) p ∅
  have := NoetherianReduction.isNoetherianRing_of_fg hT₁
  exact exists_model_of_finitePresentation f₁ h₁ hM hN hflat

end ProperNoetherianModelProof

/-- A proper finitely presented scheme over an arbitrary affine base, with two finitely
presented modules the second of which is flat over the base, has an actual noetherian model. -/
theorem properAffineNoetherianModelExistence :
    ProperAffineNoetherianModelExistenceStatement.{u} := by
  intro R Y p hp hfp M N hM hN hflat
  have := hp
  have := hfp
  exact ProperNoetherianModelProof.exists_model (A := R) p hM hN hflat

end Langlands.AlgebraicGeometry.Modules
