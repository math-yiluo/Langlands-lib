import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableDecomposition
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Algebra.MonoidAlgebra.Module

/-! # Finiteness of locally quasi-finite groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {S : Scheme.{u}} {H : GroupScheme S}

/-- Finiteness of a diagonalizable group over a nonzero ring forces its
full character group to be finite. -/
theorem finite_characters_of_isFinite (R : CommRingCat.{u}) [Nontrivial R]
    (Λ : Type u) [AddCommGroup Λ]
    [IsFinite (Diagonalizable.groupScheme R Λ).X.hom] : Finite Λ := by
  have h : (algebraMap R (AddMonoidAlgebra R Λ)).Finite :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom
      (algebraMap R (AddMonoidAlgebra R Λ)))).mp
      (inferInstanceAs (IsFinite (Diagonalizable.groupScheme R Λ).X.hom))
  rw [RingHom.finite_algebraMap] at h
  let : Module.Finite R (AddMonoidAlgebra R Λ) := h
  exact Module.Finite.finite_basis (AddMonoidAlgebra.basis Λ R)

/-- A finite character group gives a finite split model over every scheme. -/
theorem isFinite_diagonalizable (S : Scheme.{u}) (Λ : Type u)
    [AddCommGroup Λ] [Finite Λ] : IsFinite (diagonalizable S Λ).X.hom := by
  change IsFinite (pullback.snd _ _)
  infer_instance

/-- On a nonempty base, local quasi-finiteness of a split model forces its
character group to be finite. -/
theorem finite_characters_of_locallyQuasiFinite [Nonempty S]
    (Λ : Type u) [AddCommGroup Λ]
    [LocallyQuasiFinite (diagonalizable S Λ).X.hom] : Finite Λ := by
  obtain ⟨s⟩ := ‹Nonempty S›
  let b := S.fromSpecResidueField s
  let e := diagonalizableBaseChangeIso b Λ ≪≫
    Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec (S.residueField s))) Λ
  have hq : LocallyQuasiFinite
      ((GroupScheme.baseChange b).obj (diagonalizable S Λ)).X.hom := by
    change LocallyQuasiFinite (pullback.snd _ _)
    infer_instance
  have : LocallyQuasiFinite (Diagonalizable.groupScheme (S.residueField s) Λ).X.hom := by
    rw [← Over.w e.inv.hom.hom]
    infer_instance
  have : IsFinite (Diagonalizable.groupScheme (S.residueField s) Λ).X.hom :=
    IsFinite.of_locallyQuasiFinite _
  exact finite_characters_of_isFinite (S.residueField s) Λ

/-- A presentation of the actual group by a finite full character group. -/
structure FiniteDiagonalizableModel (H : GroupScheme S) where
  characters : Type u
  [characterGroup : AddCommGroup characters]
  [finiteCharacters : Finite characters]
  iso : H ≅ diagonalizable S characters

attribute [instance] FiniteDiagonalizableModel.characterGroup
  FiniteDiagonalizableModel.finiteCharacters

/-- A finite-character presentation proves finiteness over the given base. -/
theorem FiniteDiagonalizableModel.isFinite (M : FiniteDiagonalizableModel H) :
    IsFinite H.X.hom := by
  have : IsFinite (diagonalizable S M.characters).X.hom :=
    isFinite_diagonalizable S M.characters
  rw [← Over.w M.iso.hom.hom.hom]
  infer_instance

/-- A locally quasi-finite diagonalizable group over a nonempty base admits
a presentation by a finite character group. -/
theorem IsDiagonalizable.nonempty_finiteModel [Nonempty S] (hH : IsDiagonalizable H)
    [LocallyQuasiFinite H.X.hom] : Nonempty (FiniteDiagonalizableModel H) := by
  obtain ⟨Λ, hΛ, _, ⟨e⟩⟩ := hH
  let : AddCommGroup Λ := hΛ
  have : LocallyQuasiFinite (diagonalizable S Λ).X.hom := by
    rw [← Over.w e.inv.hom.hom]
    infer_instance
  let : Finite Λ := finite_characters_of_locallyQuasiFinite (S := S) Λ
  exact ⟨{
    characters := Λ
    characterGroup := hΛ
    finiteCharacters := inferInstance
    iso := e }⟩

/-- A chosen finite-character presentation of a locally quasi-finite
diagonalizable group over a nonempty base. -/
def IsDiagonalizable.finiteModel [Nonempty S] (hH : IsDiagonalizable H)
    [LocallyQuasiFinite H.X.hom] : FiniteDiagonalizableModel H :=
  Classical.choice hH.nonempty_finiteModel

/-- Every locally quasi-finite diagonalizable group is finite, including
over the empty base. -/
theorem IsDiagonalizable.isFinite (hH : IsDiagonalizable H)
    [LocallyQuasiFinite H.X.hom] : IsFinite H.X.hom := by
  by_cases hS : Nonempty S
  · let : Nonempty S := hS
    exact hH.finiteModel.isFinite
  · apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
    intro s
    exact (hS ⟨s⟩).elim

/-- A locally quasi-finite group of multiplicative type is finite over an
arbitrary base scheme. -/
theorem IsMultiplicativeType.isFinite (hH : IsMultiplicativeType H)
    [LocallyQuasiFinite H.X.hom] : IsFinite H.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  have : MorphismProperty.IsLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S := 𝒰
  apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱
  intro i
  have : LocallyQuasiFinite ((GroupScheme.baseChange (𝒰.f i)).obj H).X.hom := by
    change LocallyQuasiFinite (pullback.snd _ _)
    infer_instance
  exact (h𝒰 i).isFinite

end Langlands.GroupScheme.RelativeMultiplicativeType
