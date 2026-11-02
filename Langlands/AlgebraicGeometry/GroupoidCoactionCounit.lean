import Langlands.AlgebraicGeometry.GroupoidCoactionInduced

/-! # The counit from extension of the invariant module -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M N : Type (max u v)} [AddCommGroup M] [Module B M]
  [AddCommGroup N] [Module B N]

/-- Multiplication of scalars with invariant elements. -/
def invariantCounit (θ : GroupoidCoaction t M) :
    B ⊗[invariantRing t] θ.invariantSubmodule →ₗ[B] M :=
  AlgebraTensorModule.lift
    (LinearMap.smulRight (LinearMap.id : B →ₗ[B] B) θ.invariantSubmodule.subtype)

@[simp]
lemma invariantCounit_tmul (θ : GroupoidCoaction t M) (b : B)
    (m : θ.invariantSubmodule) :
    invariantCounit θ (b ⊗ₜ[invariantRing t] m) = b • (m : M) :=
  rfl

/-- The canonical counit respects the induced and original coactions. -/
lemma invariantCounit_isHom (θ : GroupoidCoaction t M) :
    (induced t θ.invariantSubmodule).IsHom θ (invariantCounit θ) := by
  intro x
  induction x with
  | tmul b m =>
      change θ.coaction (b • (m : M)) = t b ⊗ₜ[B] ((1 : B) • (m : M))
      rw [θ.map_smul, show θ.coaction (m : M) = (1 : C) ⊗ₜ[B] (m : M) from m.property]
      simp [smul_tmul', smul_eq_mul]
  | add x y hx hy => simp [hx, hy]

/-- Naturality of the counit for equivariant linear maps. -/
lemma invariantCounit_natural (θM : GroupoidCoaction t M)
    (θN : GroupoidCoaction t N) (f : M →ₗ[B] N) (hf : θM.IsHom θN f) :
    f.comp (invariantCounit θM) =
      (invariantCounit θN).comp ((θM.invariantsMap θN f hf).baseChange B) := by
  apply AlgebraTensorModule.ext
  intro b m
  simp

/-- On invariants, the counit is a left inverse of the unit. -/
lemma invariantCounit_invariantsMap_comp_unit (θ : GroupoidCoaction t M) :
    ((induced t θ.invariantSubmodule).invariantsMap θ
      (invariantCounit θ) (invariantCounit_isHom θ)).comp
        (inducedUnit t θ.invariantSubmodule) = LinearMap.id := by
  ext m
  simp

/-- Every invariant lies in the image on invariants of the counit. -/
lemma invariantCounit_invariantsMap_surjective (θ : GroupoidCoaction t M) :
    Function.Surjective ((induced t θ.invariantSubmodule).invariantsMap θ
      (invariantCounit θ) (invariantCounit_isHom θ)) := by
  intro m
  refine ⟨inducedUnit t θ.invariantSubmodule m, ?_⟩
  exact DFunLike.congr_fun (invariantCounit_invariantsMap_comp_unit θ) m

/-- Surjectivity of the unit makes the counit injective on invariants. -/
lemma invariantCounit_invariantsMap_injective (θ : GroupoidCoaction t M)
    (hunit : Function.Surjective (inducedUnit t θ.invariantSubmodule)) :
    Function.Injective ((induced t θ.invariantSubmodule).invariantsMap θ
      (invariantCounit θ) (invariantCounit_isHom θ)) := by
  intro x y h
  obtain ⟨m, rfl⟩ := hunit x
  obtain ⟨n, rfl⟩ := hunit y
  have hm := DFunLike.congr_fun (invariantCounit_invariantsMap_comp_unit θ) m
  have hn := DFunLike.congr_fun (invariantCounit_invariantsMap_comp_unit θ) n
  exact congrArg (inducedUnit t θ.invariantSubmodule) (hm.symm.trans (h.trans hn))

end Langlands.AlgebraicGeometry.GroupoidCoaction
