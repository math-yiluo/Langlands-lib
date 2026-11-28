import Langlands.Geometry.Analytic.LocalizedOpenRelation

/-! # The glued topological space of gluing data along open subspaces -/

noncomputable section

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (R : LocalizedOpenRelation K)

/-- The glued space: the points of all pieces modulo the relation, with the quotient
topology. -/
abbrev Space : Type u := Quotient R.pointSetoid

/-- The map from a piece to the glued space. -/
def ι (m : R.M) : localizedSpaceFunctor.obj (R.Z m) → R.Space :=
  fun z => Quotient.mk R.pointSetoid ⟨m, z⟩

variable {R}

theorem continuous_ι (m : R.M) : Continuous (R.ι m) :=
  continuous_quotient_mk'.comp continuous_sigmaMk

theorem ι_eq_ι_iff {m n : R.M} {z : localizedSpaceFunctor.obj (R.Z m)}
    {z' : localizedSpaceFunctor.obj (R.Z n)} :
    R.ι m z = R.ι n z' ↔ ∃ σ : localizedSpaceFunctor.obj (R.S m n),
      localizedSpaceFunctor.map (R.a m n) σ = z ∧ localizedSpaceFunctor.map (R.b m n) σ = z' :=
  Quotient.eq (r := R.pointSetoid)

theorem ι_a_eq_ι_b {m n : R.M} (σ : localizedSpaceFunctor.obj (R.S m n)) :
    R.ι m (localizedSpaceFunctor.map (R.a m n) σ) = R.ι n (localizedSpaceFunctor.map (R.b m n) σ) :=
  ι_eq_ι_iff.2 ⟨σ, rfl, rfl⟩

theorem injective_ι (m : R.M) : Function.Injective (R.ι m) := by
  intro z z' h
  obtain ⟨σ, rfl, rfl⟩ := ι_eq_ι_iff.1 h
  rw [R.a_self_eq_b_self]

theorem preimage_ι_image_ι {m : R.M} (U : Set (localizedSpaceFunctor.obj (R.Z m))) (n : R.M) :
    R.ι n ⁻¹' (R.ι m '' U) =
      localizedSpaceFunctor.map (R.b m n) '' (localizedSpaceFunctor.map (R.a m n) ⁻¹' U) := by
  ext z'
  constructor
  · rintro ⟨z, hz, h⟩
    obtain ⟨σ, rfl, rfl⟩ := ι_eq_ι_iff.1 h
    exact ⟨σ, hz, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, hσ, ι_a_eq_ι_b σ⟩

theorem isOpenMap_ι (m : R.M) : IsOpenMap (R.ι m) := by
  intro U hU
  rw [isQuotientMap_quotient_mk'.isOpen_preimage.symm, isOpen_sigma_iff]
  intro n
  change IsOpen (R.ι n ⁻¹' (R.ι m '' U))
  rw [preimage_ι_image_ι]
  exact (openImmersion.isOpenEmbedding (R.b_open m n)).isOpenMap _
    (hU.preimage (localizedSpaceFunctor.map (R.a m n)).hom.continuous)

theorem isOpenEmbedding_ι (m : R.M) : IsOpenEmbedding (R.ι m) :=
  .of_continuous_injective_isOpenMap (continuous_ι m) (injective_ι m) (isOpenMap_ι m)

theorem preimage_range_ι (m n : R.M) : R.ι m ⁻¹' range (R.ι n) = R.domainSet m n := by
  ext z
  constructor
  · rintro ⟨z', h⟩
    obtain ⟨σ, hσ, -⟩ := ι_eq_ι_iff.1 h.symm
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨_, (ι_a_eq_ι_b σ).symm⟩

theorem exists_ι_eq (y : R.Space) : ∃ m z, R.ι m z = y := by
  induction y using Quotient.inductionOn with
  | h p => exact ⟨p.1, p.2, rfl⟩

/-- Related morphisms have the same points in the glued space. -/
theorem Rel.ι_apply {T : LocalizedCategory.{u, u, u} (K := K)} {m n : R.M}
    {f : T ⟶ R.Z m} {g : T ⟶ R.Z n} (h : R.Rel f g) (x : localizedSpaceFunctor.obj T) :
    R.ι m (localizedSpaceFunctor.map f x) = R.ι n (localizedSpaceFunctor.map g x) := by
  obtain ⟨s, rfl, rfl⟩ := h
  rw [Functor.map_comp, Functor.map_comp, TopCat.comp_app, TopCat.comp_app]
  exact ι_a_eq_ι_b _

end Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation
