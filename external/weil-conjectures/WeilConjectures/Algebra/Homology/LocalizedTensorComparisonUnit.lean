/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonRepresentativeSquare
import WeilConjectures.Algebra.Homology.BaseDerivedTensorModelQuasiIsoComparison

/-! # Localized tensor comparison for the unit

Source: Stacks Project, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-localized-tensor-comparison-unit).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- The unshifted free rank-one generator satisfies the comparison predicate.
Source: Stacks Project, Tag 0DJA(1), with Tag 0BYJ.

Proof: let S be A placed in degree zero. The ULift equivalence identifies the
specified free module with A, and the chain left unitor identifies S tensor Q
with Q. Scalar extension is monoidal, so its unit comparison identifies F(S)
with C in degree zero. Under these identifications, the map
mu.inv followed by F(S) tensor t is t. For any base-derived model of S tensor Q,
uniqueness of the universal left-derived counit identifies its cohomology with
that of m. Naturality for multiplication by a in A makes this identification
A tensor_R B-linear; the B action is already part of the target module category.
The equations comparison_eq and localized_eq then identify the comparison
square, and extension to C preserves the source isomorphism. Thus the given
all-degree hypothesis proves comparison for S.
For an arbitrary A-K-flat U representing S in D(A), take a roof implementing
this derived isomorphism and resolve its apex A-K-flatly. Both maps from that
apex to U and S are quasi-isomorphisms. Tensor with the A-K-flat Q preserves
these maps, as does scalar extension of the K-flat complexes to C, followed
by tensor with N. Apply the universal R-to-B counit to the two tensor maps;
its naturality gives commuting cohomology squares. The same scalar-action
argument makes their source maps A tensor_R B-linear isomorphisms. After
extension to C, the localized_eq equations give the comparison squares.
Invertibility for S transports along both roof legs to U, for every model
and every degree. No flatness of C is used; all transports are isomorphisms.
(blueprint: lem-pc-localized-tensor-comparison-unit). -/
theorem localizedTensorComparisonProperty_unit
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (m : BaseDerivedTensorCohomologyModel R A B Q C)
    (h : ∀ i : ℤ, IsIso (m.localizedComparison i ≫ HomologicalComplex.homologyMap t i)) :
    localizedTensorComparisonProperty R A B C Q N t
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (ULift.{0} A))) := by
  let F := (extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)
  let S : CochainComplex (ModuleCat.{u} A) ℤ := 𝟙_ _
  have hS : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V S (curriedTensor _)).Acyclic := by
    intro V hV j
    exact (hV j).of_iso (ρ_ V).symm
  have hsingle : ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (ULift.{0} A))) ≅ DerivedCategory.Q.obj S :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
      (ULift.moduleEquiv : ULift.{0} A ≃ₗ[A] A).toModuleIso
  obtain ⟨mS⟩ := nonempty_baseDerivedTensorCohomologyModel R A B (S ⊗ Q) C
  have hunit (i : ℤ) : IsIso (mS.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F S Q).inv ≫ (F.obj S ◁ t)) i) := by
    obtain ⟨e, he⟩ := exists_baseDerivedTensorModel_quasiIso_comparison
      R A B C (λ_ Q).hom (by infer_instance) mS m i
    let d : F.obj S ⊗ N ≅ N :=
      tensorIso (Functor.Monoidal.εIso F).symm (Iso.refl N) ≪≫ λ_ N
    have hchain : ((Functor.Monoidal.μIso F S Q).inv ≫ (F.obj S ◁ t)) ≫ d.hom =
        F.map (λ_ Q).hom ≫ t := by
      dsimp [d, S]
      simp only [
        tensorHom_id, Category.assoc]
      rw [MonoidalCategory.whisker_exchange_assoc]
      rw [MonoidalCategory.leftUnitor_naturality]
      rw [Functor.Monoidal.map_leftUnitor]
      rfl
    have hsquare : (mS.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F S Q).inv ≫ (F.obj S ◁ t)) i) ≫
          HomologicalComplex.homologyMap d.hom i =
        (extendScalars (algebraMap (A ⊗[R] B) C)).map e.hom ≫
          (m.localizedComparison i ≫ HomologicalComplex.homologyMap t i) := by
      rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, hchain,
        HomologicalComplex.homologyMap_comp, ← Category.assoc, he, Category.assoc]
    have := h i
    have : IsIso ((mS.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F S Q).inv ≫ (F.obj S ◁ t)) i) ≫
          HomologicalComplex.homologyMap d.hom i) := by
      rw [hsquare]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (HomologicalComplex.homologyMap d.hom i)
  intro U hU0 hU mU i
  obtain ⟨eU⟩ := hU0
  obtain ⟨e, d, hsquare⟩ := exists_localizedTensorComparison_representative_square
    R A B C Q N t hQ U S hU hS (eU ≪≫ hsingle) mU mS i
  have := hunit i
  have : IsIso ((mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) ≫ d.hom) := by
    rw [hsquare]
    infer_instance
  exact IsIso.of_isIso_comp_right _ d.hom

end ModuleCat
