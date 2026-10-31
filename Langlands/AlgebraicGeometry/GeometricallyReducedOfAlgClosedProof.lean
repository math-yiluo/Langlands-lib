import Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedStatement
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Proof: geometric reducedness from algebraically closed base changes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

namespace GeometricallyReducedOfAlgClosedProof

/-- Reducedness descends along a flat surjective morphism: local flat maps of stalks are
faithfully flat, hence injective. -/
lemma isReduced_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsReduced X] : IsReduced Y := by
  have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := f.surjective y
    algebraize [(f.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    exact isReduced_of_injective _ ‹RingHom.FaithfullyFlat _›.injective
  exact isReduced_of_isReduced_stalk Y

/-- The spectrum of a field extension maps surjectively onto the spectrum of the base. -/
lemma surjective_specMap_field (K L : Type u) [Field K] [Field L] (φ : K →+* L) :
    Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  constructor
  intro x
  exact ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩

end GeometricallyReducedOfAlgClosedProof

open GeometricallyReducedOfAlgClosedProof in
/-- Geometric reducedness follows from reducedness after algebraically closed base change. -/
theorem geometricallyReducedOfAlgClosed : GeometricallyReducedOfAlgClosedStatement.{u} := by
  intro X Y f H
  rw [GeometricallyReduced.eq_geometrically, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  let q : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have : Surjective q := surjective_specMap_field _ _ _
  have := H (AlgebraicClosure K) (q ≫ y)
  have : IsReduced (pullback (pullback.snd f y) q) :=
    isReduced_of_isOpenImmersion (pullbackLeftPullbackSndIso f y q).hom
  exact isReduced_of_flat_of_surjective (pullback.fst (pullback.snd f y) q)

end Langlands.AlgebraicGeometry
