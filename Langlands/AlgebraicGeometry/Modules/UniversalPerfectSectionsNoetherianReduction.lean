import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsStatement
import Langlands.AlgebraicGeometry.Modules.NoetherianUniversalPerfectSectionsStatement
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsIsoTransportProof
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsScalarTowerProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentStatements
import Langlands.AlgebraicGeometry.NoetherianApproximation.SchemeSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.SmoothSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.IsSeparatedSubalgebraDescentProof
import Mathlib.RingTheory.FiniteType

/-! # Reduction of universal perfect sections to noetherian bases -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

/-- Properness descent, line-bundle descent and the noetherian case together give
universal perfect representatives over every affine base. -/
def UniversalPerfectSectionsNoetherianReductionStatement : Prop :=
  NoetherianApproximation.IsProperSubalgebraDescentStatement.{u} →
  NoetherianApproximation.LineBundleSubalgebraDescentStatement.{u} →
  NoetherianUniversalPerfectSectionsStatement.{u} →
  UniversalPerfectSectionsStatement.{u}

namespace NoetherianReduction

/-- A finitely generated subalgebra over a noetherian ring is noetherian. -/
theorem isNoetherianRing_of_fg {R : Type u} [CommRing R] [IsNoetherianRing R]
    {B : Type u} [CommRing B] [Algebra R B] {T : Subalgebra R B} (hT : T.FG) :
    IsNoetherianRing T := by
  have := (Subalgebra.fg_iff_finiteType T).mp hT
  exact Algebra.FiniteType.isNoetherianRing R T

/-- A base-change-stable property of the second projection of a pullback square
holds exactly when it holds for the chosen second pullback projection. -/
theorem iff_pullback_snd_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    {X Y Z W : Scheme.{u}} {a : X ⟶ Y} {f : X ⟶ W} {g : Y ⟶ Z} {ψ : W ⟶ Z}
    (h : IsPullback a f g ψ) : P f ↔ P (pullback.snd g ψ) := by
  rw [← h.isoPullback_hom_snd, P.cancel_left_of_respectsIso]

variable {A : Type u} [CommRing A]

/-- Pasting a pullback square over `Spec T` with the base change to an intermediate
subalgebra `T'` gives a pullback square over `Spec T'`. -/
theorem exists_isPullback_subalgebra {T : Type u} [CommRing T] [Algebra T A]
    {X Y : Scheme.{u}} {a : X ⟶ Y} {f : X ⟶ Spec (CommRingCat.of A)}
    {g : Y ⟶ Spec (CommRingCat.of T)}
    (h : IsPullback a f g (Spec.map (CommRingCat.ofHom (algebraMap T A))))
    (T' : Subalgebra T A) :
    ∃ a' : X ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap T T'))),
      a' ≫ pullback.fst _ _ = a ∧
      a' ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom (algebraMap T' A)) ∧
      IsPullback a' f (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap T T'))))
        (Spec.map (CommRingCat.ofHom (algebraMap T' A))) := by
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap T' A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap T T')) =
      Spec.map (CommRingCat.ofHom (algebraMap T A)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  refine ⟨pullback.lift a (f ≫ Spec.map (CommRingCat.ofHom (algebraMap T' A)))
    (by rw [Category.assoc, hcomp, h.w]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, hcomp]
  exact h

/-- The same pasting, with the new scheme over `Spec T'` kept abstract: it is a base
change of the old one, and the original scheme is its base change to `Spec A`. -/
theorem exists_isPullback_subalgebra' {T : Type u} [CommRing T] [Algebra T A]
    {X Y : Scheme.{u}} {a : X ⟶ Y} {f : X ⟶ Spec (CommRingCat.of A)}
    {g : Y ⟶ Spec (CommRingCat.of T)}
    (h : IsPullback a f g (Spec.map (CommRingCat.ofHom (algebraMap T A))))
    (T' : Subalgebra T A) :
    ∃ (Y' : Scheme.{u}) (g' : Y' ⟶ Spec (CommRingCat.of T')) (a' : X ⟶ Y') (b : Y' ⟶ Y),
      IsPullback b g' g (Spec.map (CommRingCat.ofHom (algebraMap T T'))) ∧
      IsPullback a' f g' (Spec.map (CommRingCat.ofHom (algebraMap T' A))) := by
  obtain ⟨a', -, -, h'⟩ := exists_isPullback_subalgebra h T'
  exact ⟨_, _, a', _, IsPullback.of_hasPullback _ _, h'⟩

/-- Final stage: over a noetherian base, descend the line bundle, apply the noetherian
case and extend scalars back to `A`. -/
theorem exists_rep_of_isProper {T : Type u} [CommRing T] [IsNoetherianRing T] [Algebra T A]
    (hL : NoetherianApproximation.LineBundleSubalgebraDescentStatement.{u})
    (hN : NoetherianUniversalPerfectSectionsStatement.{u})
    {X₄ X : Scheme.{u}} (f₄ : X₄ ⟶ Spec (CommRingCat.of T)) [Smooth f₄] [IsProper f₄]
    {a₄ : X ⟶ X₄} {f : X ⟶ Spec (CommRingCat.of A)}
    (h₄ : IsPullback a₄ f f₄ (Spec.map (CommRingCat.ofHom (algebraMap T A))))
    (L : Picard.LineBundle X) :
    ∃ K : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ,
      IsUniversalPerfectSectionsRepresentative f L.obj K := by
  obtain ⟨T₅, hT₅, -, M₀, hM₀, hc⟩ := hL f₄ a₄ f h₄ L.obj L.property (∅ : Finset A)
  have := isNoetherianRing_of_fg hT₅
  obtain ⟨a₅, ha₅fst, ha₅snd, h₅⟩ := exists_isPullback_subalgebra h₄ T₅
  obtain ⟨K₀, hK₀⟩ := hN (CommRingCat.of T₅) _
    (pullback.snd f₄ (Spec.map (CommRingCat.ofHom (algebraMap T T₅))))
    inferInstance inferInstance ⟨M₀, hM₀⟩
  have hK := universalPerfectSectionsScalarTower _ _ _ M₀ K₀ hK₀
    (CommRingCat.of A) (CommRingCat.ofHom (algebraMap T₅ A))
  obtain ⟨η⟩ := hc (h₅.isoPullback.hom ≫ pullback.fst _ _)
    (by rw [IsPullback.isoPullback_hom_fst]; exact ha₅fst)
    (by rw [Category.assoc, pullback.condition, IsPullback.isoPullback_hom_snd_assoc])
  have hX := universalPerfectSectionsIsoTransport (CommRingCat.of A) X _ h₅.isoPullback
    (pullback.snd _ _) L.obj _ (η.symm ≪≫ ((Scheme.Modules.pullbackComp _ _).app M₀).symm) _ hK
  rw [IsPullback.isoPullback_hom_snd] at hX
  exact ⟨_, hX⟩

/-- Properness stage: descend properness over a noetherian base. -/
theorem exists_rep_of_isSeparated {T : Type u} [CommRing T] [IsNoetherianRing T] [Algebra T A]
    (hP : NoetherianApproximation.IsProperSubalgebraDescentStatement.{u})
    (hL : NoetherianApproximation.LineBundleSubalgebraDescentStatement.{u})
    (hN : NoetherianUniversalPerfectSectionsStatement.{u})
    {X₃ X : Scheme.{u}} (f₃ : X₃ ⟶ Spec (CommRingCat.of T)) [Smooth f₃] [IsSeparated f₃]
    [QuasiCompact f₃] {a₃ : X ⟶ X₃} {f : X ⟶ Spec (CommRingCat.of A)} [IsProper f]
    (h₃ : IsPullback a₃ f f₃ (Spec.map (CommRingCat.ofHom (algebraMap T A))))
    (L : Picard.LineBundle X) :
    ∃ K : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ,
      IsUniversalPerfectSectionsRepresentative f L.obj K := by
  have : IsProper (pullback.snd f₃ (Spec.map (CommRingCat.ofHom (algebraMap T A)))) :=
    (iff_pullback_snd_of_isPullback @IsProper h₃).mp ‹_›
  obtain ⟨T₄, hT₄, -, hpr₄⟩ := hP f₃ (∅ : Finset A)
  have := isNoetherianRing_of_fg hT₄
  obtain ⟨X₄, f₄, a₄, b₄, hb₄, h₄⟩ := exists_isPullback_subalgebra' h₃ T₄
  have : IsProper f₄ := (iff_pullback_snd_of_isPullback @IsProper hb₄).mpr hpr₄
  have : Smooth f₄ := MorphismProperty.of_isPullback (P := @Smooth) hb₄ ‹_›
  exact exists_rep_of_isProper hL hN f₄ h₄ L

/-- Separatedness stage: descend separatedness over a noetherian base. -/
theorem exists_rep_of_smooth {T : Type u} [CommRing T] [IsNoetherianRing T] [Algebra T A]
    (hP : NoetherianApproximation.IsProperSubalgebraDescentStatement.{u})
    (hL : NoetherianApproximation.LineBundleSubalgebraDescentStatement.{u})
    (hN : NoetherianUniversalPerfectSectionsStatement.{u})
    {X₂ X : Scheme.{u}} (f₂ : X₂ ⟶ Spec (CommRingCat.of T)) [Smooth f₂] [QuasiCompact f₂]
    [QuasiSeparated f₂] {a₂ : X ⟶ X₂} {f : X ⟶ Spec (CommRingCat.of A)} [IsProper f]
    (h₂ : IsPullback a₂ f f₂ (Spec.map (CommRingCat.ofHom (algebraMap T A))))
    (L : Picard.LineBundle X) :
    ∃ K : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ,
      IsUniversalPerfectSectionsRepresentative f L.obj K := by
  have : IsSeparated (pullback.snd f₂ (Spec.map (CommRingCat.ofHom (algebraMap T A)))) :=
    (iff_pullback_snd_of_isPullback @IsSeparated h₂).mp inferInstance
  obtain ⟨T₃, hT₃, -, hsep₃⟩ :=
    NoetherianApproximation.isSeparatedSubalgebraDescent f₂ (∅ : Finset A)
  have := isNoetherianRing_of_fg hT₃
  obtain ⟨X₃, f₃, a₃, b₃, hb₃, h₃⟩ := exists_isPullback_subalgebra' h₂ T₃
  have : IsSeparated f₃ := (iff_pullback_snd_of_isPullback @IsSeparated hb₃).mpr hsep₃
  have : Smooth f₃ := MorphismProperty.of_isPullback (P := @Smooth) hb₃ ‹_›
  have : QuasiCompact f₃ := MorphismProperty.of_isPullback (P := @QuasiCompact) hb₃ ‹_›
  exact exists_rep_of_isSeparated hP hL hN f₃ h₃ L

/-- Smoothness stage: descend smoothness over a noetherian base. -/
theorem exists_rep_of_finitePresentation {T : Type u} [CommRing T] [IsNoetherianRing T]
    [Algebra T A]
    (hP : NoetherianApproximation.IsProperSubalgebraDescentStatement.{u})
    (hL : NoetherianApproximation.LineBundleSubalgebraDescentStatement.{u})
    (hN : NoetherianUniversalPerfectSectionsStatement.{u})
    {X₁ X : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of T)) [LocallyOfFinitePresentation f₁]
    [QuasiCompact f₁] [QuasiSeparated f₁] {a₁ : X ⟶ X₁} {f : X ⟶ Spec (CommRingCat.of A)}
    [Smooth f] [IsProper f]
    (h₁ : IsPullback a₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap T A))))
    (L : Picard.LineBundle X) :
    ∃ K : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ,
      IsUniversalPerfectSectionsRepresentative f L.obj K := by
  have : Smooth (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap T A)))) :=
    (iff_pullback_snd_of_isPullback @Smooth h₁).mp ‹_›
  obtain ⟨T₂, hT₂, -, hsm₂⟩ :=
    NoetherianApproximation.smoothSubalgebraDescent f₁ (∅ : Finset A)
  have := isNoetherianRing_of_fg hT₂
  obtain ⟨X₂, f₂, a₂, b₂, hb₂, h₂⟩ := exists_isPullback_subalgebra' h₁ T₂
  have : Smooth f₂ := (iff_pullback_snd_of_isPullback @Smooth hb₂).mpr hsm₂
  have : QuasiCompact f₂ := MorphismProperty.of_isPullback (P := @QuasiCompact) hb₂ ‹_›
  have : QuasiSeparated f₂ := MorphismProperty.of_isPullback (P := @QuasiSeparated) hb₂ ‹_›
  exact exists_rep_of_smooth hP hL hN f₂ h₂ L

/-- The reduction over an arbitrary commutative ring `A`: descend the scheme to a
finitely generated subalgebra over the prime subring. -/
theorem exists_isUniversalPerfectSectionsRepresentative
    (hP : NoetherianApproximation.IsProperSubalgebraDescentStatement.{u})
    (hL : NoetherianApproximation.LineBundleSubalgebraDescentStatement.{u})
    (hN : NoetherianUniversalPerfectSectionsStatement.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [Smooth f] [IsProper f]
    (L : Picard.LineBundle X) :
    ∃ K : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ,
      IsUniversalPerfectSectionsRepresentative f L.obj K := by
  -- The prime subring `⊥ : Subalgebra ℤ A` is noetherian.
  have : IsNoetherianRing (⊥ : Subalgebra ℤ A) := by
    have := (Subalgebra.fg_iff_finiteType (⊥ : Subalgebra ℤ A)).mp Subalgebra.fg_bot
    exact Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨T₁, hT₁, -, X₁, f₁, a₁, _, _, _, h₁⟩ :=
    NoetherianApproximation.schemeSubalgebraDescent (A₀ := (⊥ : Subalgebra ℤ A)) f ∅
  have := isNoetherianRing_of_fg hT₁
  exact exists_rep_of_finitePresentation hP hL hN f₁ h₁ L

end NoetherianReduction

/-- Universal perfect representatives over every affine base follow from properness
descent, line-bundle descent and the noetherian case. -/
theorem universalPerfectSectionsNoetherianReduction :
    UniversalPerfectSectionsNoetherianReductionStatement.{u} := by
  intro hP hL hN R X f hf hp L
  have := hf
  have := hp
  exact NoetherianReduction.exists_isUniversalPerfectSectionsRepresentative
    (A := R) hP hL hN f L

end Langlands.AlgebraicGeometry.Modules
