/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteCoefficientRealization
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-! # The specified finite-coefficient realization on hearts

## References

* Stacks Tags 03ET and 00YV
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private def finiteConstants (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)) ⟶
      (Profinite.continuousMapRingSheaf.{u} A).obj where
  app S := RingCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
      map_zero' := rfl
      map_one' := rfl
      map_add' _ _ := rfl
      map_mul' _ _ := rfl }
  naturality _ _ _ := rfl

private instance finiteConstants_surjective (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u}) (finiteConstants.{u} A) where
  imageSieve_mem {S} s := by
    let f : C(S, A) := s.down
    have hclosed (a : A) : IsClosed {x : S | f x = a} :=
      isClosed_singleton.preimage f.continuous
    let (a : A) : CompactSpace {x : S // f x = a} :=
      isCompact_iff_compactSpace.mp (hclosed a).isCompact
    let U (a : A) : Profinite.{u} := Profinite.of {x : S // f x = a}
    let incl (a : A) : U a ⟶ S := CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
    have hι : EffectiveEpiFamily U incl :=
      Profinite.effectiveEpiFamily_of_jointly_surjective U incl
        (fun x ↦ ⟨f x, ⟨x, rfl⟩, rfl⟩)
    refine coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨A, inferInstance, U, incl, hι, ?_⟩
    intro a
    refine ⟨ULift.up a, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact x.property.symm

private instance finiteConstants_injective (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u}) (finiteConstants.{u} A) where
  equalizerSieve_mem {S} a b h := by
    by_cases hab : a = b
    · subst b
      exact (coherentTopology Profinite).superset_covering
        (fun _ _ _ ↦ rfl) ((coherentTopology Profinite).top_mem _)
    · have : IsEmpty S.unop := ⟨fun x ↦ hab (ULift.ext (congrArg
        (fun t : ULift.{u + 1} C(S.unop, A) ↦ t.down x) h))⟩
      let U : PEmpty → Profinite.{u} := PEmpty.elim
      let incl : ∀ i, U i ⟶ S.unop := fun i ↦ i.elim
      have hι : EffectiveEpiFamily U incl :=
        Profinite.effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ isEmptyElim x)
      exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
        ⟨PEmpty, inferInstance, U, incl, hι, fun i ↦ i.elim⟩

/-- The actual scalar map is invertible, rather than just admitting an abstract ring
isomorphism. -/
theorem finiteScalarMap_isIso (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    IsIso (finiteScalarMap.{u} X A) := by
  let J := coherentTopology Profinite.{u}
  have h : J.W (A := RingCat.{u + 1}) (finiteConstants.{u} A) :=
    J.W_of_isLocallyBijective _
  have : IsIso ((presheafToSheaf J RingCat.{u + 1}).map (finiteConstants.{u} A)) :=
    (J.W_iff _).mp h
  have heq : constantToContinuous.{u} A =
      ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
        (CommRingCat.of (ULift.{u + 1} A))).hom ≫
      (presheafToSheaf J RingCat.{u + 1}).map (finiteConstants.{u} A) ≫
        (sheafificationAdjunction J RingCat.{u + 1}).counit.app
          (Profinite.continuousMapRingSheaf.{u} A) := rfl
  have : IsIso (constantToContinuous.{u} A) := by rw [heq]; infer_instance
  unfold finiteScalarMap finiteScalarPointMap
  infer_instance

attribute [-instance] integralModel_coefficientMonObj in
/-- Scalar extension along the specified finite constant-function map is an equivalence. -/
theorem finiteScalarExtension_isEquivalence (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    (Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (finiteScalarMap X A)).IsEquivalence := by
  have := finiteScalarMap_isIso X A
  let e := Mod.comapEquivalenceOfIsIso (finiteScalarMap X A)
  have : (Mod.comap (asIso (finiteScalarMap X A)).inv).IsEquivalence :=
    e.isEquivalence_inverse
  exact Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv (finiteScalarMap X A)).symm

attribute [-instance] integralModel_coefficientMonObj in
/-- The literal heart composite whose derived functors define finiteRealization. -/
def finiteHeartRealization (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :=
  Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (finiteScalarMap X A) ⋙ integralModelIntrinsicRealization X A

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded
