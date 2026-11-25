/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction
import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricPointsDetect
import WeilConjectures.AlgebraicGeometry.EtaleFieldPointMapLocal
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The geometric-point functor for étale schemes over a field

Source: Stacks Project, Tag 03QR.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] etaleFieldDiscreteForget₂ etaleFieldActionForget₂

variable (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep]

/-- The continuous discrete action on the geometric points of an étale scheme. -/
noncomputable def etaleFieldPointObject
    (X : Scheme.Etale (Spec (CommRingCat.of K))) :
    DiscreteContAction (Type u) (Gal(Ksep/K)) :=
  ⟨⟨etaleFieldGeometricAction K Ksep X,
    etaleFieldGeometricAction_continuous K Ksep X⟩, by
      change DiscreteTopology (TopCat.discrete.obj (etaleFieldGeometricAction K Ksep X).V)
      infer_instance⟩

/-- Geometric points, with their Galois action; maps act by postcomposition. -/
noncomputable def etaleFieldPointFunctor :
    Scheme.Etale (Spec (CommRingCat.of K)) ⥤
      DiscreteContAction (Type u) (Gal(Ksep/K)) where
  obj := etaleFieldPointObject K Ksep
  map f := ⟨⟨
    { hom := ↾(fun x ↦ x ≫ (Scheme.Etale.forget _).map f)
      comm := by
        intro g
        apply ConcreteCategory.hom_ext
        intro x
        change (etaleFieldPointAutomorphism K Ksep g ≫ x) ≫
          (Scheme.Etale.forget _).map f =
            etaleFieldPointAutomorphism K Ksep g ≫ (x ≫ (Scheme.Etale.forget _).map f)
        exact Category.assoc _ _ _ }⟩⟩
  map_id X := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.hom_ext
    intro x
    change x ≫ (Scheme.Etale.forget _).map (𝟙 X) = x
    simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.hom_ext
    intro x
    change x ≫ (Scheme.Etale.forget _).map (f ≫ g) =
      (x ≫ (Scheme.Etale.forget _).map f) ≫ (Scheme.Etale.forget _).map g
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The geometric-point functor is full and faithful.
Source: Stacks Project, Tag 03QR, the equivalence assertion
(blueprint: lem-exc-etale-field-point-functor-fully-faithful).

Proof: By Morphisms, Tag 02GL, an étale K-scheme is the disjoint union of spectra of
finite separable extensions. On a component Spec L its geometric points are the
K-embeddings L → Ksep, a nonempty finite transitive Galois set. An equivariant map
from such a transitive set lands in one target orbit. The finite Galois classification
identifies maps between these orbits with unique K-morphisms of the corresponding
spectra. The coproduct universal property assembles these maps, proving fullness.
Uniqueness on every component proves faithfulness. The empty source has a unique map;
a nonempty source cannot map to the empty target on either side of the correspondence. -/
theorem etaleFieldPointFunctor_fullyFaithful :
    (etaleFieldPointFunctor K Ksep).Full ∧ (etaleFieldPointFunctor K Ksep).Faithful := by
  classical
  refine ⟨?_, ?_⟩
  · constructor
    intro X Y φ
    let qX : X.left ⟶ Spec (CommRingCat.of K) := X.hom
    let qY : Y.left ⟶ Spec (CommRingCat.of K) := Y.hom
    have : Etale qX := inferInstance
    let ψ : etaleFieldGeometricAction K Ksep X ⟶ etaleFieldGeometricAction K Ksep Y :=
      φ.hom.hom
    choose U hx f hf hφ using etaleFieldPointMap_local K Ksep X Y ψ
    change ∀ i, f i ≫ qY = (U i).ι ≫ qX at hf
    change ∀ i p hp, p ≫ f i = (ψ.hom (Over.homMk (p ≫ (U i).ι) hp)).left at hφ
    let 𝒰 : X.left.OpenCover := {
      I₀ := X.left
      X x := (U x).toScheme
      f x := (U x).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x ↦ ⟨x, ⟨x, hx x⟩, rfl⟩, inferInstance⟩ }
    have hcompat : ∀ i j, Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i =
        Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j := by
      intro i j
      let a := Limits.pullback.fst (𝒰.f i) (𝒰.f j)
      let b := Limits.pullback.snd (𝒰.f i) (𝒰.f j)
      let W := Scheme.Etale.mk (a ≫ (U i).ι ≫ qX)
      apply etaleFieldGeometricPoints_detect K Ksep W
      intro p
      have hpi : (p.left ≫ a) ≫ ((U i).ι ≫ qX) =
          (etaleFieldBasePoint K Ksep).hom := by
        change p.left ≫ (a ≫ (U i).ι ≫ qX) = _
        exact Over.w p
      have hc : a ≫ (U i).ι = b ≫ (U j).ι := Limits.pullback.condition
      have hpj : (p.left ≫ b) ≫ ((U j).ι ≫ qX) =
          (etaleFieldBasePoint K Ksep).hom := by
        change ((p.left ≫ b) ≫ (U j).ι) ≫ qX = _
        rw [Category.assoc p.left b (U j).ι, ← hc]
        simpa only [Category.assoc] using hpi
      have hi := hφ i (p.left ≫ a) hpi
      have hj := hφ j (p.left ≫ b) hpj
      have heq : Over.homMk ((p.left ≫ a) ≫ (U i).ι) hpi =
          Over.homMk ((p.left ≫ b) ≫ (U j).ι) hpj := by
        apply Over.OverMorphism.ext
        change (p.left ≫ a) ≫ (U i).ι = (p.left ≫ b) ≫ (U j).ι
        simpa only [Category.assoc] using congrArg (p.left ≫ ·) hc
      simpa only [Category.assoc] using hi.trans ((congrArg (fun q ↦ (ψ.hom q).left)
        heq).trans hj.symm)
    let l := 𝒰.glueMorphisms f hcompat
    have hl : ∀ i, (U i).ι ≫ l = f i := 𝒰.ι_glueMorphisms f hcompat
    have hb : l ≫ qY = qX := by
      apply 𝒰.hom_ext
      intro i
      rw [← Category.assoc, hl i, hf i]
    let lift : X ⟶ Y := MorphismProperty.Over.homMk l hb
    refine ⟨lift, ?_⟩
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.hom_ext
    intro p
    let x := p.left (default : Spec (CommRingCat.of Ksep))
    let pp : Spec (CommRingCat.of Ksep) ⟶ X.left := p.left
    have hr : Set.range pp ⊆ Set.range (U x).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      change pp t ∈ U x
      rw [Subsingleton.elim t (default : Spec (CommRingCat.of Ksep))]
      exact hx x
    let q := IsOpenImmersion.lift (U x).ι p.left hr
    have hq : q ≫ (U x).ι = p.left := IsOpenImmersion.lift_fac _ _ _
    have hqp : q ≫ ((U x).ι ≫ qX) = (etaleFieldBasePoint K Ksep).hom := by
      rw [← Category.assoc, hq]
      exact Over.w p
    apply Over.OverMorphism.ext
    change p.left ≫ l = (ψ.hom p).left
    rw [← hq, Category.assoc, hl x]
    have hh := hφ x q hqp
    have heq : Over.homMk (q ≫ (U x).ι) (by cat_disch) = p := by
      apply Over.OverMorphism.ext
      exact hq
    simpa only [heq] using hh
  · constructor
    intro X Y f g h
    apply (Scheme.Etale.forget _).map_injective
    apply Over.OverMorphism.ext
    apply etaleFieldGeometricPoints_detect K Ksep X
    intro p
    have hp := congrArg (fun t ↦ (t.hom.hom.hom p).left) h
    exact hp

end AlgebraicGeometry
