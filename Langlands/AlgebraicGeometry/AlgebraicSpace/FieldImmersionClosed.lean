import Langlands.AlgebraicGeometry.Morphisms.GenericFiniteness
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Closed immersions of etale field schemes into locally Noetherian schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k]

/-- Over an affine Noetherian scheme, an immersion from an etale field scheme
is a closed immersion. -/
lemma isClosedImmersion_of_etale_field_source_affine
    {Z U : Scheme.{u}} (i : Z ⟶ U) (p : U ⟶ Spec (CommRingCat.of k))
    [IsImmersion i] [IsAffine U] [IsLocallyNoetherian U] [Etale (i ≫ p)] :
    _root_.AlgebraicGeometry.IsClosedImmersion i := by
  have : IsNoetherian U := ⟨⟩
  have : TopologicalSpace.NoetherianSpace Z := i.isEmbedding.isInducing.noetherianSpace
  have : LocallyQuasiFinite (i ≫ p) :=
    GenericFiniteness.locallyQuasiFinite_of_formallyUnramified (i ≫ p)
  have : IsFinite (i ≫ p) := IsFinite.of_locallyQuasiFinite (i ≫ p)
  have : IsFinite i := IsFinite.of_comp i p
  exact (IsClosedImmersion.iff_isFinite_and_mono i).mpr ⟨inferInstance, inferInstance⟩

/-- An immersion of a scheme etale over a field into a locally Noetherian
scheme over that field is closed, with no compactness hypothesis. -/
lemma isClosedImmersion_of_etale_field_source
    {Z U : Scheme.{u}} (i : Z ⟶ U) (p : U ⟶ Spec (CommRingCat.of k))
    [IsImmersion i] [IsLocallyNoetherian U] [Etale (i ≫ p)] :
    _root_.AlgebraicGeometry.IsClosedImmersion i := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @_root_.AlgebraicGeometry.IsClosedImmersion)
    U.affineCover
  intro j
  let i' := pullback.snd i (U.affineCover.f j)
  let p' := U.affineCover.f j ≫ p
  have hw : i' ≫ p' = pullback.fst i (U.affineCover.f j) ≫ (i ≫ p) := by
    dsimp [i', p']
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  have : Etale (i' ≫ p') := by
    rw [hw]
    infer_instance
  exact isClosedImmersion_of_etale_field_source_affine i' p'

/-- The open complement of an immersed etale field scheme in a locally
Noetherian scheme. -/
def etaleFieldImmersionComplement
    {Z U : Scheme.{u}} (i : Z ⟶ U) (p : U ⟶ Spec (CommRingCat.of k))
    [IsImmersion i] [IsLocallyNoetherian U] [Etale (i ≫ p)] : U.Opens := by
  have := isClosedImmersion_of_etale_field_source i p
  exact ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

@[simp]
lemma mem_etaleFieldImmersionComplement
    {Z U : Scheme.{u}} (i : Z ⟶ U) (p : U ⟶ Spec (CommRingCat.of k))
    [IsImmersion i] [IsLocallyNoetherian U] [Etale (i ≫ p)] (x : U) :
    x ∈ etaleFieldImmersionComplement i p ↔ x ∉ Set.range i :=
  Iff.rfl

end Langlands.AlgebraicGeometry.AlgebraicSpace
