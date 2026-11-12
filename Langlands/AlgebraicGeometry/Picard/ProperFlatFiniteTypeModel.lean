import Langlands.AlgebraicGeometry.Picard.LineBundleStalkFlatness
import Langlands.AlgebraicGeometry.Picard.LineBundleFinitePresentation
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsNoetherianReduction
import Langlands.AlgebraicGeometry.NoetherianApproximation.SchemeSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.IsSeparatedSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.IsProperSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.FlatnessSubalgebraDescentProof
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.FiniteType

/-! # Proper flat models over finite-type `ℤ`-algebras -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules

/-- A morphism is flat if some locally free rank-one module sheaf on its source is
flat over its target. -/
lemma IsLocallyFreeRankOne.flat_of_isFlatOver {X Y : Scheme.{u}} {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) (f : X ⟶ Y) (h : IsFlatOver f M) : Flat f := by
  refine Flat.of_stalkMap f fun x ↦ ?_
  let := relativeStalkModule f M x
  let := Module.compHom (X.presheaf.stalk x) (f.stalkMap x).hom
  have : Module.Flat (Y.presheaf.stalk (f x)) (stalk M x) := h x
  exact Module.Flat.of_linearEquiv (hM.relativeStalkLinearEquiv f x).symm

/-- A morphism `p : Y ⟶ Spec A` has a proper flat model over a finite-type `ℤ`-algebra:
an actual Cartesian square exhibiting `p` as the base change of a proper flat morphism
to `Spec R`, along `Spec A ⟶ Spec R` for some algebra `R → A` with `R` of finite type
over `ℤ`. -/
def HasProperFlatFiniteTypeModel {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∃ (R : Type u) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R) (_ : Algebra R A)
    (X₀ : Scheme.{u}) (p₀ : X₀ ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ X₀),
    IsProper p₀ ∧ Flat p₀ ∧
      IsPullback π p p₀ (Spec.map (CommRingCat.ofHom (algebraMap R A)))

namespace ProperFlatFiniteTypeModel

open NoetherianReduction NoetherianApproximation

variable {A : Type u} [CommRing A]

/-- A finitely generated subalgebra over a finite-type `ℤ`-algebra is of finite type
over `ℤ`. -/
lemma finiteType_of_fg {T : Type u} [CommRing T] [Algebra.FiniteType ℤ T] [Algebra T A]
    {T' : Subalgebra T A} (hT' : T'.FG) : Algebra.FiniteType ℤ T' :=
  Algebra.FiniteType.trans (S := T) inferInstance ((Subalgebra.fg_iff_finiteType T').mp hT')

/-- Flatness stage: descend flatness of the trivial line bundle. -/
theorem of_isProper {T : Type u} [CommRing T] [Algebra.FiniteType ℤ T] [Algebra T A]
    {X₃ Y : Scheme.{u}} (f₃ : X₃ ⟶ Spec (CommRingCat.of T)) [IsProper f₃]
    {a₃ : Y ⟶ X₃} {p : Y ⟶ Spec (CommRingCat.of A)} [Flat p]
    (h₃ : IsPullback a₃ p f₃ (Spec.map (CommRingCat.ofHom (algebraMap T A)))) :
    HasProperFlatFiniteTypeModel p := by
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℤ T
  have hfl : IsFlatOver p ((Scheme.Modules.pullback a₃).obj (LineBundle.trivial X₃).obj) :=
    ((LineBundle.pullback a₃).obj (LineBundle.trivial X₃)).isFlatOver p
  obtain ⟨T₄, hT₄, -, hfl₄⟩ := isFlatOverSubalgebraDescent f₃ (LineBundle.trivial X₃).obj
    inferInstance a₃ p h₃ hfl (∅ : Finset A)
  have := finiteType_of_fg (T := T) hT₄
  obtain ⟨a₄, -, -, h₄⟩ := exists_isPullback_subalgebra h₃ T₄
  let fst := pullback.fst f₃ (Spec.map (CommRingCat.ofHom (algebraMap T T₄)))
  refine ⟨T₄, inferInstance, inferInstance, inferInstance, _,
    pullback.snd f₃ (Spec.map (CommRingCat.ofHom (algebraMap T T₄))), a₄,
    inferInstance, ?_, h₄⟩
  exact ((LineBundle.trivial X₃).property.pullback fst).flat_of_isFlatOver _
    (hfl₄ fst (pullback.snd _ _) (IsPullback.of_hasPullback _ _))

/-- Properness stage: descend properness over a noetherian base. -/
theorem of_isSeparated {T : Type u} [CommRing T] [Algebra.FiniteType ℤ T] [Algebra T A]
    {X₂ Y : Scheme.{u}} (f₂ : X₂ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₂]
    [QuasiCompact f₂] [LocallyOfFinitePresentation f₂] {a₂ : Y ⟶ X₂}
    {p : Y ⟶ Spec (CommRingCat.of A)} [IsProper p] [Flat p]
    (h₂ : IsPullback a₂ p f₂ (Spec.map (CommRingCat.ofHom (algebraMap T A)))) :
    HasProperFlatFiniteTypeModel p := by
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℤ T
  have : IsProper (pullback.snd f₂ (Spec.map (CommRingCat.ofHom (algebraMap T A)))) :=
    (iff_pullback_snd_of_isPullback @IsProper h₂).mp ‹_›
  obtain ⟨T₃, hT₃, -, hpr₃⟩ := isProperSubalgebraDescent f₂ (∅ : Finset A)
  have := finiteType_of_fg (T := T) hT₃
  obtain ⟨X₃, f₃, a₃, b₃, hb₃, h₃⟩ := exists_isPullback_subalgebra' h₂ T₃
  have : IsProper f₃ := (iff_pullback_snd_of_isPullback @IsProper hb₃).mpr hpr₃
  exact of_isProper f₃ h₃

/-- Separatedness stage: descend separatedness over a noetherian base. -/
theorem of_finitePresentation {T : Type u} [CommRing T] [Algebra.FiniteType ℤ T]
    [Algebra T A] {X₁ Y : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of T))
    [LocallyOfFinitePresentation f₁] [QuasiCompact f₁] [QuasiSeparated f₁] {a₁ : Y ⟶ X₁}
    {p : Y ⟶ Spec (CommRingCat.of A)} [IsProper p] [Flat p]
    (h₁ : IsPullback a₁ p f₁ (Spec.map (CommRingCat.ofHom (algebraMap T A)))) :
    HasProperFlatFiniteTypeModel p := by
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℤ T
  have : IsSeparated (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap T A)))) :=
    (iff_pullback_snd_of_isPullback @IsSeparated h₁).mp inferInstance
  obtain ⟨T₂, hT₂, -, hsep₂⟩ := isSeparatedSubalgebraDescent f₁ (∅ : Finset A)
  have := finiteType_of_fg (T := T) hT₂
  obtain ⟨X₂, f₂, a₂, b₂, hb₂, h₂⟩ := exists_isPullback_subalgebra' h₁ T₂
  have : IsSeparated f₂ := (iff_pullback_snd_of_isPullback @IsSeparated hb₂).mpr hsep₂
  have : QuasiCompact f₂ := MorphismProperty.of_isPullback (P := @QuasiCompact) hb₂ ‹_›
  have : LocallyOfFinitePresentation f₂ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hb₂ ‹_›
  exact of_isSeparated f₂ h₂

end ProperFlatFiniteTypeModel

/-- A proper flat morphism of finite presentation to the spectrum of an arbitrary
commutative ring is the base change of a proper flat morphism over a finite-type
`ℤ`-algebra. -/
theorem hasProperFlatFiniteTypeModel {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) [IsProper p] [LocallyOfFinitePresentation p]
    [Flat p] : HasProperFlatFiniteTypeModel p := by
  have : Algebra.FiniteType ℤ (⊥ : Subalgebra ℤ A) :=
    (Subalgebra.fg_iff_finiteType (⊥ : Subalgebra ℤ A)).mp Subalgebra.fg_bot
  obtain ⟨T₁, hT₁, -, X₁, f₁, a₁, _, _, _, h₁⟩ :=
    NoetherianApproximation.schemeSubalgebraDescent (A₀ := (⊥ : Subalgebra ℤ A)) p ∅
  have := ProperFlatFiniteTypeModel.finiteType_of_fg (T := (⊥ : Subalgebra ℤ A)) hT₁
  exact ProperFlatFiniteTypeModel.of_finitePresentation f₁ h₁

/-- A proper scheme over a field is the base change of a proper flat scheme over a
finite-type `ℤ`-algebra. -/
theorem field_hasProperFlatFiniteTypeModel (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) (hX : IsProper X.hom) :
    HasProperFlatFiniteTypeModel X.hom := by
  have := hX
  exact hasProperFlatFiniteTypeModel X.hom

end Langlands.AlgebraicGeometry.Picard
