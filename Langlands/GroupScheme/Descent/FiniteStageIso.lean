import Langlands.GroupScheme.Descent.FiniteStageHom
import Langlands.GroupScheme.LocalGroupIsoBaseChange
import Mathlib.FieldTheory.SeparableClosure

/-! # Finite fields of definition of specified group-scheme isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Descent.FiniteStage

open Langlands.AlgebraicGeometry.Picard

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

variable {k Ω}

/-- A finite model of an invertible homomorphism is itself invertible. -/
theorem HomModel.isIso
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {f : (baseChange (algebraBaseMap k Ω)).obj G ⟶
      (baseChange (algebraBaseMap k Ω)).obj H}
    (D : HomModel k Ω f) [IsIso f] : IsIso D.hom := by
  let E := D.fieldOfDefinition
  let q := algebraBaseMap E.1 Ω
  let : Surjective q := (fieldExtension_fpqc E.1 Ω).1
  let : Flat q := (fieldExtension_fpqc E.1 Ω).2.1
  let : QuasiCompact q := (fieldExtension_fpqc E.1 Ω).2.2
  have hmap : (baseChange q).map D.hom =
      (comparison k Ω E G).inv ≫ f ≫ (comparison k Ω E H).hom := by
    apply (cancel_epi (comparison k Ω E G).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using D.recovery
  let : IsIso ((baseChange q).map D.hom) := by
    rw [hmap]
    infer_instance
  exact isIso_of_baseChange q D.hom

/-- The actual finite-stage isomorphism attached to an invertible homomorphism model. -/
def HomModel.iso
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {f : (baseChange (algebraBaseMap k Ω)).obj G ⟶
      (baseChange (algebraBaseMap k Ω)).obj H}
    (D : HomModel k Ω f) [IsIso f] :
    (baseChange (algebraBaseMap k D.fieldOfDefinition.1)).obj G ≅
      (baseChange (algebraBaseMap k D.fieldOfDefinition.1)).obj H :=
  letI := D.isIso
  asIso D.hom

@[simp] theorem HomModel.iso_hom
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {f : (baseChange (algebraBaseMap k Ω)).obj G ⟶
      (baseChange (algebraBaseMap k Ω)).obj H}
    (D : HomModel k Ω f) [IsIso f] : D.iso.hom = D.hom :=
  rfl

variable (k Ω)

/-- A field of definition with an actual isomorphism recovering the specified one. -/
structure IsoModel {G H : GroupScheme (Spec (CommRingCat.of k))}
    (e : (baseChange (algebraBaseMap k Ω)).obj G ≅
      (baseChange (algebraBaseMap k Ω)).obj H) where
  fieldOfDefinition : FinIntermediateField k Ω
  iso : (baseChange (algebraBaseMap k fieldOfDefinition.1)).obj G ≅
    (baseChange (algebraBaseMap k fieldOfDefinition.1)).obj H
  recovery : (comparison k Ω fieldOfDefinition G).hom ≫
      (baseChange (algebraBaseMap fieldOfDefinition.1 Ω)).map iso.hom =
    e.hom ≫ (comparison k Ω fieldOfDefinition H).hom

/-- A specified isomorphism over an algebraic extension has a finite model. -/
theorem nonempty_isoModel [Algebra.IsAlgebraic k Ω]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (e : (baseChange (algebraBaseMap k Ω)).obj G ≅
      (baseChange (algebraBaseMap k Ω)).obj H) : Nonempty (IsoModel k Ω e) := by
  obtain ⟨D⟩ := nonempty_homModel k Ω e.hom
  exact ⟨⟨D.fieldOfDefinition, D.iso, D.recovery⟩⟩

/-- Choose a finite model while retaining the specified extension-field isomorphism. -/
def isoModel [Algebra.IsAlgebraic k Ω]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (e : (baseChange (algebraBaseMap k Ω)).obj G ≅
      (baseChange (algebraBaseMap k Ω)).obj H) : IsoModel k Ω e :=
  Classical.choice (nonempty_isoModel k Ω e)

variable {k Ω}

/-- The recovery equation also identifies the actual composed isomorphisms. -/
theorem IsoModel.recovery_iso
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {e : (baseChange (algebraBaseMap k Ω)).obj G ≅
      (baseChange (algebraBaseMap k Ω)).obj H}
    (D : IsoModel k Ω e) :
    comparison k Ω D.fieldOfDefinition G ≪≫
        (baseChange (algebraBaseMap D.fieldOfDefinition.1 Ω)).mapIso D.iso =
      e ≪≫ comparison k Ω D.fieldOfDefinition H := by
  apply Iso.ext
  exact D.recovery

/-- A finite actual model gives natural multiplicative equivalences on every relative test. -/
def IsoModel.localIso
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {e : (baseChange (algebraBaseMap k Ω)).obj G ≅
      (baseChange (algebraBaseMap k Ω)).obj H}
    (D : IsoModel k Ω e) :
    LocalGroupIso G H (Over.mk (algebraBaseMap k D.fieldOfDefinition.1)) :=
  LocalGroupIso.ofBaseChangeIso D.iso

/-- An isomorphism over the separable closure supplies a finite separable local isomorphism
in the original universe. -/
theorem exists_finiteSeparable_localIso_of_separableClosure
    (k : Type u) [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (e : (baseChange (algebraBaseMap k (SeparableClosure k))).obj G ≅
      (baseChange (algebraBaseMap k (SeparableClosure k))).obj H) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      Nonempty (LocalGroupIso G H (Over.mk (algebraBaseMap k L))) := by
  let D := isoModel k (SeparableClosure k) e
  let E := D.fieldOfDefinition
  have : FiniteDimensional k E.1 := E.2
  exact ⟨E.1, inferInstance, inferInstance, inferInstance, inferInstance, ⟨D.localIso⟩⟩

end Langlands.GroupScheme.Descent.FiniteStage
