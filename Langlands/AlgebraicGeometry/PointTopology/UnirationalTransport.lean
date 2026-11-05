import Langlands.AlgebraicGeometry.PointTopology.UnirationalDensity
import Mathlib.AlgebraicGeometry.Birational.Birational

/-! # Finite affine birational models and transport of unirationality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A birational model over the ground field with finitely many affine
coordinates. The finiteness is explicit, unlike `Scheme.IsRationalOver`. -/
def HasFiniteAffineBirationalModel (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι),
    Scheme.BirationalOver X.hom (𝔸(ι; Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k))

/-- Composing a parametrization with an actual dense-range morphism
gives a parametrization of its target. -/
theorem IsUnirational.map
    {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : IsUnirational k X) (f : X ⟶ Y) (hf : DenseRange f.left) :
    IsUnirational k Y := by
  obtain ⟨ι, hι, U, hU, p, hp⟩ := hX
  exact ⟨ι, hι, U, hU, p ≫ f, hf.comp hp f.left.continuous⟩

/-- An isomorphism over the ground field transports an actual
unirational parametrization. -/
theorem IsUnirational.of_iso
    {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : IsUnirational k X) (e : X ≅ Y) :
    IsUnirational k Y := by
  have : IsIso e.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  exact hX.map e.hom e.hom.left.denseRange

/-- Unirationality is invariant under isomorphism over the ground field. -/
theorem isUnirational_iff_of_iso
    {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))} (e : X ≅ Y) :
    IsUnirational k X ↔ IsUnirational k Y :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/-- The inverse of the birational model, followed by the dense open
inclusion in `X`, is the required actual finite affine-open morphism. -/
theorem HasFiniteAffineBirationalModel.isUnirational
    {k : Type u} [Field k]
    {X : Over (Spec (CommRingCat.of k))}
    (hX : HasFiniteAffineBirationalModel k X) :
    IsUnirational k X := by
  obtain ⟨ι, hι, e, he⟩ := hX
  refine ⟨ι, hι, e.target, e.dense_target.nonempty,
    Over.homMk (e.iso.inv ≫ e.source.ι) ?_, ?_⟩
  · simpa [Scheme.PartialIso.IsOver, Scheme.PartialIso.symm, Category.assoc]
      using Scheme.PartialIso.IsOver.symm he
  · have : IsDominant e.source.ι := Opens.isDominant_ι e.dense_source
    exact (e.iso.inv ≫ e.source.ι).denseRange

end Langlands.AlgebraicGeometry.PointTopology
