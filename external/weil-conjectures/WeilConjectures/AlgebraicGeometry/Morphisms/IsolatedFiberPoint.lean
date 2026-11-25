/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteDimensionalResidueFieldOfIsolatedFiberPoint
public import WeilConjectures.AlgebraicGeometry.IsolatedFibrePointBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Residue fields at isolated points of fibres

## References

* Stacks Project, Morphisms, Lemmas 01TH and 01TG and their stability under base change
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

theorem isOpen_singleton_of_field_pullback
    {k K : Type u} [Field k] [Field K] {F T : Scheme.{u}}
    (p : F ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (q : Spec (.of K) ⟶ Spec (.of k)) (h : T ⟶ F) (b : T ⟶ Spec (.of K))
    (hp : IsPullback h b p q) (z : T) (hz : IsOpen ({h z} : Set F)) :
    IsOpen ({z} : Set T) := by
  let U : F.Opens := ⟨{h z}, hz⟩
  have : Subsingleton U.toScheme := by
    change Subsingleton ↥({h z} : Set F)
    infer_instance
  have : LocallyQuasiFinite (U.ι ≫ p) :=
    LocallyQuasiFinite.of_injective (fun a a' _ ↦ Subsingleton.elim a a')
  have hpU := (isPullback_morphismRestrict h U).paste_vert hp
  have : LocallyQuasiFinite ((h ⁻¹ᵁ U).ι ≫ b) :=
    MorphismProperty.of_isPullback hpU inferInstance
  have : IsLocallyArtinian (h ⁻¹ᵁ U).toScheme :=
    IsLocallyArtinian.of_locallyQuasiFinite ((h ⁻¹ᵁ U).ι ≫ b)
  let zU : (h ⁻¹ᵁ U).toScheme := ⟨z, Set.mem_singleton _⟩
  simpa [Set.image_singleton, zU] using
    (h ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap ({zU} : Set (h ⁻¹ᵁ U).toScheme)
      (isOpen_discrete _)

end AlgebraicGeometry
