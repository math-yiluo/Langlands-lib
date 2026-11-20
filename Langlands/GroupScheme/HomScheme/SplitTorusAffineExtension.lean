import Langlands.GroupScheme.Torus.DiagonalizableTorsionDensity
import Langlands.GroupScheme.Torus.TorsionCoefficientDescent

/-! # Descent of maps from a split torus to an affine scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TorsionDensity

variable {R K : Type u} [CommRing R] [CommRing K]

/-- The map on split character schemes induced by a change of coefficients. -/
abbrev coefficientProjection (M : Type u) [AddCommGroup M] (φ : R →+* K) :
    Spec (CommRingCat.of (AddMonoidAlgebra K M)) ⟶
      Spec (CommRingCat.of (AddMonoidAlgebra R M)) :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom M φ))

/-- The spectrum of the group-algebra quotient by the `n`-multiples in the lattice. -/
abbrev torsionProjection (L : Type u) [Fintype L] (A : Type u) [CommRing A] (n : ℕ) :
    Spec (CommRingCat.of (AddMonoidAlgebra A ((L → ℤ) ⧸ multiples (L → ℤ) n))) ⟶
      Spec (CommRingCat.of (AddMonoidAlgebra A (L → ℤ))) :=
  Spec.map (CommRingCat.ofHom (torsionCoefficientMap L A n))

/-- An affine-target map on the scalar extension of a split torus descends uniquely
if its restrictions to the specified unbounded torsion orders descend. -/
theorem existsUnique_hom_of_torsion_coefficients (L : Type u) [Fintype L]
    (φ : R →+* K) (hφ : Function.Injective φ)
    {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of (AddMonoidAlgebra K (L → ℤ))) ⟶ Y)
    (P : ℕ → Prop) (hP : ∀ m : ℕ, ∃ n, P n ∧ m < n)
    (ht : ∀ n, P n →
      ∃ g : Spec (CommRingCat.of (AddMonoidAlgebra R ((L → ℤ) ⧸ multiples (L → ℤ) n))) ⟶ Y,
        coefficientProjection _ φ ≫ g = torsionProjection L K n ≫ f) :
    ∃! g : Spec (CommRingCat.of (AddMonoidAlgebra R (L → ℤ))) ⟶ Y,
      coefficientProjection _ φ ≫ g = f := by
  let f' := (Spec.preimage (f ≫ Y.isoSpec.hom)).hom
  have hcoeff : ∀ n, P n →
      ∃ g : Γ(Y, ⊤) →+* AddMonoidAlgebra R ((L → ℤ) ⧸ multiples (L → ℤ) n),
        (AddMonoidAlgebra.mapRingHom _ φ).comp g = (torsionCoefficientMap L K n).comp f' := by
    intro n hn
    obtain ⟨g, hg⟩ := ht n hn
    refine ⟨(Spec.preimage (g ≫ Y.isoSpec.hom)).hom, ?_⟩
    have hcoord : Spec.preimage (g ≫ Y.isoSpec.hom) ≫
        CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom _ φ) =
        Spec.preimage (f ≫ Y.isoSpec.hom) ≫
          CommRingCat.ofHom (torsionCoefficientMap L K n) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage,
        ← Category.assoc, ← Category.assoc]
      exact congrArg (fun a => a ≫ Y.isoSpec.hom) hg
    exact congrArg CommRingCat.Hom.hom hcoord
  obtain ⟨g, hg, hunique⟩ :=
    existsUnique_ringHom_of_torsionCoefficientMap L φ hφ f' P hP hcoeff
  refine ⟨Spec.map (CommRingCat.ofHom g) ≫ Y.isoSpec.inv, ?_, ?_⟩
  · change coefficientProjection _ φ ≫ (Spec.map (CommRingCat.ofHom g) ≫ Y.isoSpec.inv) = f
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
    simp [f']
  · intro k hk
    have hcoord : Spec.preimage (k ≫ Y.isoSpec.hom) ≫
        CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom _ φ) =
        Spec.preimage (f ≫ Y.isoSpec.hom) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc]
      exact congrArg (fun a => a ≫ Y.isoSpec.hom) hk
    have hkg := congrArg (fun a => Spec.map (CommRingCat.ofHom a))
      (hunique _ (congrArg CommRingCat.Hom.hom hcoord))
    change Spec.map (Spec.preimage (k ≫ Y.isoSpec.hom)) = Spec.map (CommRingCat.ofHom g) at hkg
    rw [Spec.map_preimage] at hkg
    simpa only [Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun a => a ≫ Y.isoSpec.inv) hkg

end Langlands.GroupScheme.TorsionDensity
