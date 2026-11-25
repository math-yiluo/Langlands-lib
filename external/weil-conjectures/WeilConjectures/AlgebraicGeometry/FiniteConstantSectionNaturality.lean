/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantSections
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantSections

/-! # Coefficient naturality of normalized finite constant sections -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The normalized comparison for finite constant sections commutes with a ring map.
Source: blueprint Compatible isomorphisms, reduction of finite coefficient entries.
(blueprint: lem-pe-finite-constant-section-coefficient-naturality).
Proof: assemble the normalized section comparisons into morphisms of ring presheaves,
using their restriction naturality. The two composites to continuous B-valued functions
agree on the constant presheaf, by normalization and the sheafification unit's naturality.
The continuous-function presheaf is a sheaf, so sheafification uniqueness identifies the
composites. Evaluate the equality at V, the section s and the point x. -/
theorem proEtale_finite_constant_sections_coefficient
    (X : Scheme.{u}) (A B : Type (u + 1)) [CommRing A] [CommRing B]
    [Finite A] [Finite B] [TopologicalSpace A] [TopologicalSpace B]
    [DiscreteTopology A] [DiscreteTopology B] (g : A →+* B)
    (V : X.ProEt)
    (s : (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
      (RingCat.of A)).obj.obj (op V))) (x : V.left) :
    (proEtale_finite_constant_sections X B).choose V
        (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).map
          (RingCat.ofHom g)).hom.app (op V) s) x =
      g ((proEtale_finite_constant_sections X A).choose V s x) := by
  let J := Scheme.ProEt.topology X
  let θA := (proEtale_finite_constant_sections X A).choose
  let θB := (proEtale_finite_constant_sections X B).choose
  have hA := (proEtale_finite_constant_sections X A).choose_spec
  have hB := (proEtale_finite_constant_sections X B).choose_spec
  let α : ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of A)).obj ⟶
      continuousRingPresheaf X A :=
    { app := fun U ↦ RingCat.ofHom (θA U.unop).toRingHom
      naturality := by
        intro U Z f
        apply RingCat.hom_ext
        ext z
        exact hA.2 f.unop z }
  let β : ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of B)).obj ⟶
      continuousRingPresheaf X B :=
    { app := fun U ↦ RingCat.ofHom (θB U.unop).toRingHom
      naturality := by
        intro U Z f
        apply RingCat.hom_ext
        ext z
        exact hB.2 f.unop z }
  let γ : continuousRingPresheaf X A ⟶ continuousRingPresheaf X B :=
    { app := fun U ↦ RingCat.ofHom (g.compLeftContinuous U.unop.left
        (continuous_of_discreteTopology))
      naturality := by intros; ext; rfl }
  let δ := ((constantSheaf J RingCat.{u + 1}).map (RingCat.ofHom g)).hom
  have h : δ ≫ β = α ≫ γ := by
    apply sheafify_hom_ext J _ _ (continuousRingPresheaf_isSheaf X B)
    ext U a
    have hn := congrArg (fun k ↦ k.app U a)
      (toSheafify_naturality J ((Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom g)))
    change θB U.unop (δ.app U ((toSheafify J
      ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app U a)) =
        (g.compLeftContinuous U.unop.left continuous_of_discreteTopology)
          (θA U.unop ((toSheafify J
            ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app U a))
    change ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of B))).app U)
      (g a) = δ.app U (((toSheafify J
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app U) a) at hn
    erw [← hn]
    rw [hB.1, hA.1]
    rfl
  have hf := congrArg (fun k ↦ k.app (op V) s) h
  change θB V (δ.app (op V) s) =
    (g.compLeftContinuous V.left continuous_of_discreteTopology) (θA V s) at hf
  exact congrArg (fun f : C(V.left, B) ↦ f x) hf

namespace ProEtale.FiniteDiscreteOrdinary

/-- The canonical constant-to-continuous coefficient map respects a morphism whose
constant functions have the specified images.
Source: blueprint Compatible isomorphisms, coefficient reduction of scalar sections.
(blueprint: lem-pe-finite-constant-section-coefficient-naturality).
Proof: the point comparison is the adjoint transpose of pointConstants, so its
naturality follows from the two Hom-equivalence naturality identities. Apply inverse
image and move the constant map across constantSchemeIso by naturality. -/
theorem canonicalAbelianMap_coefficient
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (T : Scheme.{u})
    (g : AddCommGrpCat.of (ULift.{u + 1} A) ⟶ AddCommGrpCat.of (ULift.{u + 1} B))
    (φ : coefficient A ⟶ coefficient B)
    (h : pointConstants A ≫ φ.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map g ≫ pointConstants B) :
    (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map g ≫
        canonicalAbelianMap B T =
      canonicalAbelianMap A T ≫ (upperStarFromPoint T).map φ := by
  let adj := sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}
  let a := (adj.homEquiv _ (coefficient A)).symm (pointConstants A)
  let b := (adj.homEquiv _ (coefficient B)).symm (pointConstants B)
  have hab : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map g ≫ b =
      a ≫ φ := by
    change (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      ((Functor.const Profinite.{u}ᵒᵖ).map g) ≫ b = a ≫ φ
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    change _ ≫ (adj.homEquiv _ _ ((adj.homEquiv _ _).symm _)) =
      (adj.homEquiv _ _ ((adj.homEquiv _ _).symm _)) ≫ _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h.symm
  change _ ≫ ((constantSchemeIso T).hom.app _ ≫ (upperStarFromPoint T).map b) =
    ((constantSchemeIso T).hom.app _ ≫ (upperStarFromPoint T).map a) ≫ _
  rw [← Category.assoc, (constantSchemeIso T).hom.naturality g]
  simp only [Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp, hab, Functor.map_comp]

end ProEtale.FiniteDiscreteOrdinary
end AlgebraicGeometry
