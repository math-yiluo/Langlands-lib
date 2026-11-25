/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties

import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# An integral-base model of a pointed clopen piece

Source: Stacks Project, Tag 055N, reduction to the reduced closure of a point.
(blueprint: lem-sbc-pointed-clopen-integral-model)
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

/-- Realize a relatively clopen piece as a finite type family over an integral base,
with the prescribed generic fibre and a rational point on that fibre. No connectedness
or persistence of connectedness is asserted.

Source: Stacks Project, Tag 055N, reduction to the induced reduced closed subscheme.
Proof: put the reduced closed subscheme structure on the closure of `y` and restrict
it to the inverse image of `V`. This is a nonempty open of an integral scheme, with
generic point mapping to `y`. Base change `g` to it. The projection is a locally
closed immersion, hence identifies its underlying space
with the inverse image of `V ∩ closure {y}`. Pull back `A` under this identification
and take its open subscheme. It is also closed, so its inclusion is quasi-compact:
its intersection with any quasi-compact open is closed in that open. The resulting
morphism `f` is locally of finite type and quasi-compact by base change and composition.
The base inclusion gives the open embedding `j` into the closure of `y`. Closed base
change preserves residue fields, so the fibre homeomorphisms followed by restriction
to `A` give the displayed homeomorphisms. The base-changed section at the generic
point belongs to this open subscheme by `hpoint`; its factorization yields the
rational point `r`, and the section equation yields the final equality.

(blueprint: lem-sbc-pointed-clopen-integral-model) -/
theorem exists_pointed_clopen_integral_model {P T : Scheme.{u}}
    (g : P ⟶ T) [LocallyOfFiniteType g] [QuasiCompact g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (y : T) (V : Set T) (A : Set P)
    (hV : IsOpen V) (hyV : y ∈ V)
    (hA : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A})
    (hpoint : σ y ∈ A) :
    ∃ (S X : Scheme.{u}) (_ : IsIntegral S) (f : X ⟶ S)
      (_ : LocallyOfFiniteType f) (_ : QuasiCompact f) (j : S → closure {y}),
      IsOpenEmbedding j ∧ (j (genericPoint S)).val = y ∧
      ∃ (_ : ∀ s : S, ↥(f.fiber s) ≃ₜ ↥(g ⁻¹' {(j s).val} ∩ A))
        (r : Spec (S.residueField (genericPoint S)) ⟶ f.fiber (genericPoint S)),
        r ≫ f.fiberToSpecResidueField (genericPoint S) = 𝟙 _ := by
  classical
  let Z : TopologicalSpace.Closeds T := ⟨closure {y}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let S₀ := I.subscheme
  let i₀ : S₀ ⟶ T := I.subschemeι
  let j₀ : S₀ ≃ₜ closure {y} := Homeomorph.setCongr
    (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)
  have : IrreducibleSpace ↥(closure ({y} : Set T)) :=
    isIrreducible_iff_irreducibleSpace.mp isIrreducible_singleton.closure
  have : IrreducibleSpace S₀ := j₀.irreducibleSpace_iff.mpr inferInstance
  have : IsIntegral S₀ := isIntegral_of_irreducibleSpace_of_isReduced S₀
  let W : S₀.Opens := i₀ ⁻¹ᵁ ⟨V, hV⟩
  let z : S₀ := j₀.symm ⟨y, subset_closure (Set.mem_singleton y)⟩
  have hz : i₀ z = y := by
    exact congrArg Subtype.val
      (j₀.apply_symm_apply ⟨y, subset_closure (Set.mem_singleton y)⟩)
  have hzW : z ∈ W := by
    change i₀ z ∈ V
    rw [hz]
    exact hyV
  have : Nonempty W.toScheme := ⟨⟨z, hzW⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let S := W.toScheme
  let i : S ⟶ T := W.ι ≫ i₀
  let j : S → closure {y} := fun s ↦ j₀ (W.ι s)
  have hj : IsOpenEmbedding j := j₀.isOpenEmbedding.comp W.ι.isOpenEmbedding
  have hi (s : S) : i s = (j s).val := rfl
  have hη : (j (genericPoint S)).val = y := by
    have hiz : i (⟨z, hzW⟩ : S) = y := hz
    have h₁ : i (genericPoint S) ⤳ i (⟨z, hzW⟩ : S) :=
      (genericPoint_specializes (α := S) (⟨z, hzW⟩ : S)).map i.continuous
    have h₂ : y ⤳ (j (genericPoint S)).val :=
      specializes_iff_mem_closure.mpr (j (genericPoint S)).property
    have h₁' : (j (genericPoint S)).val ⤳ y := by
      simpa only [hiz, hi] using h₁
    exact (h₁'.antisymm h₂).eq
  let D := pullback g i
  let p : D ⟶ P := pullback.fst g i
  let q : D ⟶ S := pullback.snd g i
  have hp (d : D) : g (p d) = i (q d) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hprange (d : D) : p d ∈ g ⁻¹' (V ∩ closure {y}) := by
    change g (p d) ∈ V ∩ closure {y}
    rw [hp, hi]
    exact ⟨(q d).property, (j (q d)).property⟩
  let a : D → g ⁻¹' (V ∩ closure {y}) := fun d ↦ ⟨p d, hprange d⟩
  have ha : Continuous a := p.continuous.subtype_mk _
  have hC : IsClopen (p ⁻¹' A) := hA.preimage ha
  let C : D.Opens := ⟨p ⁻¹' A, hC.isOpen⟩
  let X := C.toScheme
  let f : X ⟶ S := C.ι ≫ q
  have : QuasiCompact C.ι := by
    have : IsClosedImmersion C.ι := .of_isPreimmersion C.ι (by
      rw [Scheme.Opens.range_ι]
      exact hC.isClosed)
    infer_instance
  refine ⟨S, X, inferInstance, f, inferInstance, inferInstance, j, hj, hη, ?_⟩
  have hef (s : S) :
      Nonempty (↥(f.fiber s) ≃ₜ ↥(g ⁻¹' {(j s).val} ∩ A)) := by
    let k : ↥(f ⁻¹' {s}) → P := fun x ↦ p (C.ι x.val)
    have hk : IsEmbedding k :=
      (p.isEmbedding.comp C.ι.isEmbedding).comp IsEmbedding.subtypeVal
    have hkrange : Set.range k = g ⁻¹' {(j s).val} ∩ A := by
      ext x
      constructor
      · rintro ⟨w, rfl⟩
        have hw : f w.val = s := w.property
        have hw' : q (C.ι w.val) = s := by
          simpa only [f, Scheme.Hom.comp_apply] using hw
        exact ⟨by change g (p (C.ι w.val)) = (j s).val; rw [hp, hw', hi],
          w.val.property⟩
      · intro hx
        obtain ⟨d, hdx, hds⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := g) (g := i) x s (hx.1.trans (hi s).symm)
        have hdC : d ∈ C := by
          change p d ∈ A
          rw [hdx]
          exact hx.2
        let w : X := ⟨d, hdC⟩
        have hw : w ∈ f ⁻¹' {s} := by
          change q (C.ι w) = s
          exact hds
        exact ⟨⟨w, hw⟩, hdx⟩
    exact ⟨(f.fiberHomeo s).trans (hk.toHomeomorph.trans (.setCongr hkrange))⟩
  let b := S.fromSpecResidueField (genericPoint S)
  let r₀ : Spec (S.residueField (genericPoint S)) ⟶ D :=
    pullback.lift (b ≫ i ≫ σ) b (by simp [Category.assoc, hσ])
  have hr₀p : r₀ ≫ p = b ≫ i ≫ σ := pullback.lift_fst _ _ _
  have hr₀q : r₀ ≫ q = b := pullback.lift_snd _ _ _
  have hrange : Set.range r₀ ⊆ Set.range C.ι := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    change p (r₀ v) ∈ A
    rw [← Scheme.Hom.comp_apply, hr₀p, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hi, hη]
    exact hpoint
  let r₁ := IsOpenImmersion.lift C.ι r₀ hrange
  have hr₁ : r₁ ≫ f = b := by
    change r₁ ≫ (C.ι ≫ q) = b
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hr₀q]
  let r : Spec (S.residueField (genericPoint S)) ⟶ f.fiber (genericPoint S) :=
    pullback.lift r₁ (𝟙 _) (by simpa using hr₁)
  exact ⟨fun s ↦ (hef s).some, r, pullback.lift_snd _ _ _⟩

end AlgebraicGeometry
