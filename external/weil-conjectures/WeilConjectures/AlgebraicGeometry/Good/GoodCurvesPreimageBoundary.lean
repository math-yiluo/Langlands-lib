/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ProperCoproduct
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.PiProd
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesBoundaryQuasiFinite

/-!
# Geometric compactification of the inverse image of a good-curves open

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`, proof after
replacing the dense open by its inverse image under the finite good-curves cover.
(blueprint: lem-weil-pbc-good-curves-preimage-boundary)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open CategoryTheory.Limits

attribute [local instance high] instHasColimitOfHasColimitsOfShape
  hasColimitsOfShape_discrete

private theorem proper_sigma_desc
    {I : Type} [Finite I] {B : Scheme.{u}} (C : I → Scheme.{u})
    (c : ∀ i, C i ⟶ B) (hc : ∀ i, IsProper (c i)) : IsProper (Sigma.desc c) := by
  refine Finite.induction_empty_option (P := fun I ↦ ∀ [Finite I] (C : I → Scheme.{u})
    (c : ∀ i, C i ⟶ B), (∀ i, IsProper (c i)) → IsProper (Sigma.desc c))
    ?_ ?_ ?_ I C c hc
  · intro A D e hA _ C c hc
    have : Finite A := Finite.of_equiv _ e.symm
    have := hA (fun a ↦ C (e a)) (fun a ↦ c (e a)) fun a ↦ hc (e a)
    have he : (Sigma.whiskerEquiv e fun a ↦ Iso.refl (C (e a))).hom ≫ Sigma.desc c =
        Sigma.desc fun a ↦ c (e a) := by
      ext a
      simp
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper
      (Sigma.whiskerEquiv e fun a ↦ Iso.refl (C (e a))).hom, he]
    infer_instance
  · intro _ C c _
    have : IsEmpty ↥(∐ C) := isInitial_iff_isEmpty.mp
      ⟨IsInitial.ofUniqueHom (fun _ ↦ Sigma.desc fun i ↦ i.elim)
        fun _ _ ↦ Sigma.hom_ext _ _ fun i ↦ i.elim⟩
    infer_instance
  · intro A _ hA _ C c hc
    have := hA (fun a ↦ C (some a)) (fun a ↦ c (some a)) fun a ↦ hc (some a)
    have := hc none
    have hb := (proper_coproduct_two (c none) (Sigma.desc fun a ↦ c (some a))).2.2.2
    have : IsProper (coprod.desc (c none) (Sigma.desc fun a ↦ c (some a))) := hb
    have he : Sigma.desc c =
        (sigmaOptionIso C).hom ≫ coprod.desc (c none) (Sigma.desc fun a ↦ c (some a)) := by
      ext (_ | a) <;> simp
    rw [he]
    infer_instance

/-- The inverse image of a fibrewise dense open has a quasi-finite boundary in the
finite disjoint union of proper good-curve models.

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`, the second
boundary Zprime. (blueprint: lem-weil-pbc-good-curves-preimage-boundary)

Proof: Pullback distributes over the finite disjoint union Y. On each component
its inverse image W_i is an open of Y_i. Composing its open immersion with j_i gives
an open immersion into Ybar_i. Their disjoint union identifies the pullback with an
open O in the disjoint union C of the Ybar_i. The compatibility hcomm gives the
stated equality of the two maps to V. Each p_i followed by t_i is proper, since t_i
is finite, so C to V is proper by finite coproducts. It is of finite type over the
Noetherian V; hence C is Noetherian. Surjectivity of Y_i to T_i makes each fibre
nonempty, and hWi makes its open W_i fibre nonempty. A smooth geometrically connected
fibre of p_i is regular and connected, hence irreducible, so this open is dense
in that fibre. The good-curves-boundary quasi-finiteness theorem now applies to the
open component inclusions W_i into Ybar_i. Take Z with its embedding i to be the
canonical reduced closed complement of O. Its image is the complement of O. This
proves quasi-finiteness of its map to V, including empty families and
zero-dimensional fibres. -/
theorem goodCurvesPreimage_boundary
    {X V : Scheme.{u}} [IsNoetherian X] [IsNoetherian V]
    (f : X ⟶ V) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
    (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i) (p : ∀ i, Ybar i ⟶ T i)
    (ν : (∐ Y) ⟶ X) [IsFinite ν] [Surjective ν]
    (hcomm : ∀ i, Limits.Sigma.ι Y i ≫ ν ≫ f = j i ≫ p i ≫ t i)
    (ht : ∀ i, IsFinite (t i) ∧ AlgebraicGeometry.Etale (t i))
    (hj : ∀ i, IsOpenImmersion (j i))
    (hjp : ∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i))
    (hp : ∀ i, Smooth (p i) ∧ IsProper (p i) ∧
      ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
        topologicalKrullDim ((p i).fiber s) ≤ 1)
    (W : X.Opens)
    (hWi : ∀ (i : Fin n) (s : T i),
      Dense (((j i ≫ p i).fiberι s ≫ Limits.Sigma.ι Y i ≫ ν) ⁻¹' (W : Set X)))
    : IsNoetherian (∐ Ybar) ∧
      IsProper (Limits.Sigma.desc fun i ↦ p i ≫ t i) ∧
      ∃ (O : (∐ Ybar : Scheme.{u}).Opens)
        (e : Limits.pullback ν W.ι ≅ O.toScheme)
        (Z : Scheme.{u}) (i : Z ⟶ (∐ Ybar)),
        IsClosedImmersion i ∧ Set.range i.base = (O : Set (∐ Ybar : Scheme.{u}))ᶜ ∧
        e.hom ≫ O.ι ≫ (Limits.Sigma.desc fun k ↦ p k ≫ t k) =
          Limits.pullback.snd ν W.ι ≫ W.ι ≫ f ∧
        (i ≫ (Limits.Sigma.desc fun k ↦ p k ≫ t k)).IsQuasiFinite := by
  classical
  have : ∀ i, IsFinite (t i) := fun i ↦ (ht i).1
  have : ∀ i, AlgebraicGeometry.Etale (t i) := fun i ↦ (ht i).2
  have : ∀ i, IsOpenImmersion (j i) := hj
  have : ∀ i, Smooth (p i) := fun i ↦ (hp i).1
  have : ∀ i, IsProper (p i) := fun i ↦ (hp i).2.1
  have : ∀ i, Surjective (j i ≫ p i) := fun i ↦ (hjp i).2
  let c : (∐ Ybar) ⟶ V := Sigma.desc fun i ↦ p i ≫ t i
  have hc : IsProper c := proper_sigma_desc Ybar _ (fun i ↦ inferInstance)
  have : IsLocallyNoetherian (∐ Ybar) := LocallyOfFiniteType.isLocallyNoetherian c
  have : CompactSpace (∐ Ybar : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace c
  have hN : IsNoetherian (∐ Ybar) := {}
  let a : (∐ Y) ⟶ (∐ Ybar) := Sigma.desc fun i ↦ j i ≫ Sigma.ι Ybar i
  have ha : IsOpenImmersion a := by
    apply isOpenImmersion_sigmaDesc
    intro i k hik
    apply Set.disjoint_left.mpr
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    exact Set.disjoint_left.mp
      (TopologicalSpace.Opens.coe_disjoint.mpr (disjoint_opensRange_sigmaι Ybar i k hik))
      ⟨j i y, rfl⟩ ⟨j k z, by simpa [Scheme.Hom.comp_apply] using hz⟩
  have hac : a ≫ c = ν ≫ f := by
    apply Sigma.hom_ext
    intro i
    simpa [a, c] using (hcomm i).symm
  let q := pullback.fst ν W.ι ≫ a
  let O := q.opensRange
  let U : (i : Fin n) → (Y i).Opens := fun i ↦ (Sigma.ι Y i ≫ ν) ⁻¹ᵁ W
  let D : Fin n → Scheme.{u} := fun i ↦ (U i).toScheme
  let v : ∀ i, D i ⟶ Ybar i := fun i ↦ (U i).ι ≫ j i
  have hD : ∀ i s, Nonempty ((v i ≫ p i).fiber s) := by
    intro i s
    obtain ⟨y, hy⟩ := (hjp i).2.surj s
    have : Nonempty ((j i ≫ p i).fiber s) :=
      ⟨((j i ≫ p i).fiberHomeo s).symm ⟨y, hy⟩⟩
    obtain ⟨z, hz⟩ := (hWi i s).nonempty
    let w : D i := ⟨(j i ≫ p i).fiberι s z, hz⟩
    apply ((v i ≫ p i).fiberHomeo s).nonempty_congr.mpr
    exact ⟨⟨w, by
      change (j i ≫ p i) ((j i ≫ p i).fiberι s z) = s
      exact ((j i ≫ p i).fiberHomeo s z).2⟩⟩
  have hC : ∀ i s, Nonempty ((p i).fiber s) ∧
      GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
      topologicalKrullDim ((p i).fiber s) ≤ 1 := by
    intro i s
    obtain ⟨y, hy⟩ := (hjp i).2.surj s
    exact ⟨⟨((p i).fiberHomeo s).symm ⟨j i y, hy⟩⟩, (hp i).2.2 s⟩
  have hO : (⨆ i, (v i ≫ Sigma.ι Ybar i).opensRange) = O := by
    apply TopologicalSpace.Opens.ext
    ext x
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, Scheme.Hom.coe_opensRange]
    constructor
    · rintro ⟨i, y, rfl⟩
      change (v i ≫ Sigma.ι Ybar i) y ∈ Set.range q
      have hy : Sigma.ι Y i ((U i).ι y) ∈ Set.range (pullback.fst ν W.ι) := by
        rw [Scheme.Pullback.range_fst]
        exact ⟨⟨(ν (Sigma.ι Y i ((U i).ι y))), y.2⟩, rfl⟩
      obtain ⟨z, hz⟩ := hy
      refine ⟨z, ?_⟩
      change a (pullback.fst ν W.ι z) = _
      rw [hz]
      simp only [v, Category.assoc, Scheme.Hom.comp_apply]
      change (Sigma.ι Y i ≫ a) _ = _
      simp only [a, Sigma.ι_comp_desc, Scheme.Hom.comp_apply]
      rfl
    · rintro ⟨z, rfl⟩
      obtain ⟨i, y, hy⟩ := (sigmaOpenCover Y).exists_eq (pullback.fst ν W.ι z)
      change Sigma.ι Y i y = pullback.fst ν W.ι z at hy
      have hw : y ∈ U i := by
        change (Sigma.ι Y i ≫ ν) y ∈ W
        rw [Scheme.Hom.comp_apply, hy]
        have he := congrArg (fun g ↦ g z) (pullback.condition (f := ν) (g := W.ι))
        change ν (pullback.fst ν W.ι z) = W.ι (pullback.snd ν W.ι z) at he
        rw [he]
        exact (pullback.snd ν W.ι z).2
      refine ⟨i, ⟨y, hw⟩, ?_⟩
      change (v i ≫ Sigma.ι Ybar i) ⟨y, hw⟩ = a (pullback.fst ν W.ι z)
      rw [← hy]
      simp only [v, Category.assoc, Scheme.Hom.comp_apply]
      change _ = (Sigma.ι Y i ≫ a) _
      simp only [a, Sigma.ι_comp_desc, Scheme.Hom.comp_apply]
      rfl
  let T' : ULift.{u} (Fin n) → Scheme.{u} := fun i ↦ T i.down
  let C' : ULift.{u} (Fin n) → Scheme.{u} := fun i ↦ Ybar i.down
  let D' : ULift.{u} (Fin n) → Scheme.{u} := fun i ↦ D i.down
  let t' : ∀ i, T' i ⟶ V := fun i ↦ t i.down
  let p' : ∀ i, C' i ⟶ T' i := fun i ↦ p i.down
  let v' : ∀ i, D' i ⟶ C' i := fun i ↦ v i.down
  let E : (∐ C') ≅ (∐ Ybar) :=
    Sigma.whiskerEquiv Equiv.ulift (fun _ ↦ Iso.refl _)
  have hE (i : ULift.{u} (Fin n)) : Sigma.ι C' i ≫ E.hom = Sigma.ι Ybar i.down := by
    simp only [E, Sigma.whiskerEquiv_hom, Sigma.ι_comp_map', Iso.refl_inv]
    exact Category.id_comp _
  have hEc : E.hom ≫ c = Sigma.desc fun i ↦ p' i ≫ t' i := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, hE, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
  have hvE (i : ULift.{u} (Fin n)) :
      (v' i ≫ Sigma.ι C' i) ≫ E.hom = v i.down ≫ Sigma.ι Ybar i.down := by
    rw [Category.assoc, hE]
  let O' := ⨆ i, (v' i ≫ Sigma.ι C' i).opensRange
  have hO' : E.hom ''ᵁ O' = O := by
    rw [← hO]
    apply TopologicalSpace.Opens.ext
    ext x
    simp only [Scheme.Hom.coe_image, O', TopologicalSpace.Opens.coe_iSup,
      Set.mem_image, Set.mem_iUnion, Scheme.Hom.coe_opensRange]
    constructor
    · rintro ⟨y, ⟨i, z, rfl⟩, rfl⟩
      refine ⟨i.down, z, ?_⟩
      exact (congrArg (fun g ↦ g z) (hvE i)).symm
    · rintro ⟨i, z, rfl⟩
      refine ⟨(v' ⟨i⟩ ≫ Sigma.ι C' ⟨i⟩) z, ⟨⟨i⟩, z, rfl⟩, ?_⟩
      exact congrArg (fun g ↦ g z) (hvE ⟨i⟩)
  have hb := good_curves_boundary_quasiFinite V T' C' D' t' p' v'
    (fun i ↦ hC i.down) (fun i ↦ hD i.down)
  let K := Scheme.IdealSheafData.vanishingIdeal O'.compl
  let z : K.subscheme ⟶ (∐ Ybar) := K.subschemeι ≫ E.hom
  refine ⟨hN, hc, O, q.isoOpensRange, K.subscheme, z,
    inferInstance, ?_, ?_, ?_⟩
  · change Set.range (K.subschemeι ≫ E.hom) = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    have hr : Set.range K.subschemeι = (O' : Set (∐ C' : Scheme.{u}))ᶜ :=
      (Scheme.IdealSheafData.reduced_induced_closed_subscheme _ O'.compl).2.2.2.2.2.1
    rw [hr]
    change (Scheme.homeoOfIso E) '' (O' : Set (∐ C' : Scheme.{u}))ᶜ = _
    rw [(Scheme.homeoOfIso E).image_compl]
    exact congrArg Set.compl (congrArg
      (fun U : (∐ Ybar : Scheme.{u}).Opens ↦ (U : Set (∐ Ybar : Scheme.{u}))) hO')
  · rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    change (pullback.fst ν W.ι ≫ a) ≫ c = _
    rw [Category.assoc, hac, ← Category.assoc, pullback.condition]
    simp
  · change ((K.subschemeι ≫ E.hom) ≫ c).IsQuasiFinite
    rw [Category.assoc, hEc]
    exact hb.2.1

end AlgebraicGeometry.Etale
