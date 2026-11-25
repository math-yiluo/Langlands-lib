import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionClosedImmersionStatement

/-! # Finite-type Weil restriction preserves closed immersions of affine schemes

Let `B` be a finite projective `A`-algebra. A surjection `φ : C →ₐ[B] D` of `B`-algebras of
finite type induces a surjection of Weil restriction algebras (`map_surjective`), and hence
a closed immersion of the affine Weil restriction schemes
(`affineWeilRestrictionMap_isClosedImmersion`).

The algebraic step rests on `range_le_iff_range_homEquiv_le`: a homomorphism `g` out of the
Weil restriction algebra takes its values in a subalgebra `S` of `T` exactly when the
corresponding point `C →ₐ[B] B ⊗[A] T` takes its values in the image of `B ⊗[A] S`.
-/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.WeilRestrictionFiniteType

/-- An algebra homomorphism `f` factors through an injective algebra homomorphism `j` exactly
when the range of `f` is contained in the range of `j`. -/
private theorem range_le_range_iff_exists_comp {R X Y Z : Type*} [CommSemiring R]
    [Semiring X] [Semiring Y] [Semiring Z] [Algebra R X] [Algebra R Y] [Algebra R Z]
    {j : X →ₐ[R] Y} (hj : Function.Injective j) {f : Z →ₐ[R] Y} :
    f.range ≤ j.range ↔ ∃ v : Z →ₐ[R] X, j.comp v = f := by
  constructor
  · intro h
    -- `j` is an isomorphism onto its range; compose its inverse with `f`.
    let e : X ≃ₐ[R] j.range := AlgEquiv.ofInjective j hj
    refine ⟨e.symm.toAlgHom.comp (f.codRestrict j.range fun z ↦ h (f.mem_range_self z)),
      AlgHom.ext fun z ↦ ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · rintro ⟨v, rfl⟩
    exact AlgHom.range_comp_le_range v j

variable {A B C T : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing T]
  [Algebra A B] [Module.Finite A B] [Module.Projective A B]
  [Algebra B C] [Algebra.FiniteType B C] [Algebra A T]

/-- A homomorphism from the Weil restriction algebra to `T` has its range in a subalgebra
`S` if and only if the corresponding point `C →ₐ[B] B ⊗[A] T` has its range in the image of
`B ⊗[A] S`. -/
theorem range_le_iff_range_homEquiv_le
    {g : WeilRestrictionFiniteType A B C →ₐ[A] T} {S : Subalgebra A T} :
    g.range ≤ S ↔
      (homEquiv A B C T g).range ≤
        (Algebra.TensorProduct.lTensor (S := B) B S.val).range := by
  -- `B` is flat over `A`, so `B ⊗[A] S → B ⊗[A] T` is injective.
  have hj : Function.Injective (Algebra.TensorProduct.lTensor (S := B) B S.val) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := B) S.val.toLinearMap
      Subtype.val_injective
  -- Both conditions say that a map factors through an injective one.
  have hS := range_le_range_iff_exists_comp (j := S.val) (f := g) Subtype.val_injective
  rw [Subalgebra.range_val] at hS
  rw [hS, range_le_range_iff_exists_comp hj]
  -- Factorizations of `g` and of its point correspond under the representing bijections.
  constructor
  · rintro ⟨g', rfl⟩
    exact ⟨homEquiv A B C S g', (homEquiv_comp g' S.val).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨(homEquiv A B C S).symm v, (homEquiv A B C T).injective ?_⟩
    rw [homEquiv_comp, Equiv.apply_symm_apply, hv]

/-- The map of Weil restriction algebras induced by a surjection is surjective. -/
theorem map_surjective {D : Type*} [CommRing D] [Algebra B D]
    [Algebra.FiniteType B D] {φ : C →ₐ[B] D} (hφ : Function.Surjective φ) :
    Function.Surjective (map A B φ) := by
  -- The identity of the Weil restriction of `D` corresponds to the universal point.
  have hid : homEquiv A B D _ (AlgHom.id A (WeilRestrictionFiniteType A B D)) =
      universalPoint A B D := by
    rw [← map_id, homEquiv_map, AlgHom.comp_id]
  -- The point of `map A B φ` is the universal point composed with `φ`. It has values over
  -- the range of `map A B φ`, and so has the universal point, because `φ` is surjective.
  have h : (universalPoint A B D).range ≤
      (Algebra.TensorProduct.lTensor (S := B) B (map A B φ).range.val).range := by
    have h' := range_le_iff_range_homEquiv_le.mp (le_refl (map A B φ).range)
    rwa [homEquiv_map, AlgHom.range_comp, (AlgHom.range_eq_top φ).mpr hφ, Algebra.map_top]
      at h'
  -- Hence the identity has its range in the range of `map A B φ`.
  have hle : (AlgHom.id A (WeilRestrictionFiniteType A B D)).range ≤ (map A B φ).range :=
    range_le_iff_range_homEquiv_le.mpr (by rw [hid]; exact h)
  intro x
  exact (AlgHom.mem_range _).mp (hle ((AlgHom.mem_range _).mpr ⟨x, rfl⟩))

end Langlands.Algebra.WeilRestrictionFiniteType

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

open Langlands.Algebra

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The Weil restriction of a closed immersion of affine schemes of finite type over `B` is
a closed immersion. -/
theorem affineWeilRestrictionMap_isClosedImmersion
    {X Y : Over (Spec (CommRingCat.of B))}
    [IsAffine X.left] [IsAffine Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsClosedImmersion f.left] :
    IsClosedImmersion (affineWeilRestrictionMap A B f).left := by
  -- A closed immersion into an affine scheme is surjective on global sections.
  have hsurj : Function.Surjective (affineCoordinatePullback B f) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).2
  -- The map of Weil restrictions is `Spec` of the induced map of representing algebras.
  have hleft : (affineWeilRestrictionMap A B f).left = Spec.map (CommRingCat.ofHom
      (WeilRestrictionFiniteType.map A B (affineCoordinatePullback B f)).toRingHom) :=
    ringTestMap_left A _
  rw [hleft]
  exact IsClosedImmersion.spec_of_surjective _ (WeilRestrictionFiniteType.map_surjective hsurj)

theorem weilRestrictionClosedImmersionProperties_proof :
    WeilRestrictionClosedImmersionProperties A B :=
  ⟨fun _ _ _ _ _ _ _ _ _ hφ ↦ WeilRestrictionFiniteType.map_surjective hφ,
    fun _ _ _ _ _ _ f _ ↦ affineWeilRestrictionMap_isClosedImmersion A B f⟩

end Langlands.AlgebraicGeometry.PointTopology
