import Langlands.AlgebraicGeometry.Modules.ModuleSupport
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Complements of finite sets of rational points and module support -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- Vanishing on an open subscheme puts the actual stalk support in its complement. -/
theorem stalkSupport_subset_compl_of_isZero_pullback {X : Scheme.{u}}
    (U : X.Opens) (M : X.Modules)
    (h : IsZero ((Scheme.Modules.pullback U.ι).obj M)) :
    stalkSupport M ⊆ (U : Set X)ᶜ := by
  intro x hx hxU
  have hr : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj M) :=
    h.of_iso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M)
  have hz := (isZero_iff_forall_isZero_stalk.mp hr) ⟨x, hxU⟩
  exact hx (hz.of_iso ((Scheme.Modules.restrictStalkNatIso U.ι ⟨x, hxU⟩).app M).symm)

variable {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]

/-- Evaluation at the unique point identifies rational points with their underlying points. -/
theorem rationalPoint_apply_injective :
    Function.Injective
      (fun x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk g =>
        x.left (IsLocalRing.closedPoint K)) := by
  intro x y h
  apply Over.OverMorphism.ext
  exact ext_of_apply_closedPoint_eq g x.w y.w h

/-- The open complement of the underlying points of a finite set of rational points. -/
def rationalPointComplement
    (F : Set (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk g)) (hF : F.Finite) :
    X.Opens :=
  ⟨((fun x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk g =>
      x.left (IsLocalRing.closedPoint K)) '' F)ᶜ, by
    apply isOpen_compl_iff.mpr
    rw [Set.image_eq_iUnion]
    exact hF.isClosed_biUnion fun x _ => (pointEquivClosedPoint g ⟨x.left, x.w⟩).property⟩

@[simp]
theorem mem_rationalPointComplement_iff
    (F : Set (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk g)) (hF : F.Finite)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk g) :
    x.left (IsLocalRing.closedPoint K) ∈ rationalPointComplement g F hF ↔ x ∉ F := by
  change x.left (IsLocalRing.closedPoint K) ∉
    (fun y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk g =>
      y.left (IsLocalRing.closedPoint K)) '' F ↔ x ∉ F
  constructor
  · intro h hx
    exact h ⟨x, hx, rfl⟩
  · rintro h ⟨y, hy, he⟩
    exact h ((rationalPoint_apply_injective g he) ▸ hy)

/-- A module vanishing on the complement of finitely many rational points has finite
closed support, without a coherence hypothesis. -/
theorem hasFiniteClosedSupport_of_isZero_rationalPointComplement
    (F : Set (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk g)) (hF : F.Finite)
    (M : X.Modules)
    (h : IsZero ((Scheme.Modules.pullback (rationalPointComplement g F hF).ι).obj M)) :
    HasFiniteClosedSupport M := by
  refine HasFiniteClosedSupport.of_subset
    (hF.image (fun x => x.left (IsLocalRing.closedPoint K))) ?_ ?_
  · rintro z ⟨x, _, rfl⟩
    exact (pointEquivClosedPoint g ⟨x.left, x.w⟩).property
  · simpa only [rationalPointComplement, TopologicalSpace.Opens.coe_mk, compl_compl] using
      stalkSupport_subset_compl_of_isZero_pullback (rationalPointComplement g F hF) M h

end Langlands.AlgebraicGeometry.Modules
