/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# The Galois action on geometric points of an étale scheme

Source: Stacks Project, Tag 03QR.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

local instance etaleFieldDiscreteForget₂ : HasForget₂ (Type u) TopCat :=
  ⟨TopCat.discrete, rfl⟩

local instance etaleFieldActionForget₂ (G : Type*) [Monoid G] [TopologicalSpace G] :
    HasForget₂ (DiscreteContAction (Type u) G) (Type u) :=
  HasForget₂.trans (DiscreteContAction (Type u) G) (ContAction (Type u) G) (Type u)

variable (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]

/-- The geometric point of `Spec K` defined by the field extension `Ksep / K`. -/
noncomputable def etaleFieldBasePoint : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))

/-- A Galois automorphism acts on the geometric point over `Spec K`. -/
noncomputable def etaleFieldPointAutomorphism (g : Gal(Ksep/K)) :
    etaleFieldBasePoint K Ksep ⟶ etaleFieldBasePoint K Ksep :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    dsimp [etaleFieldBasePoint]
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact g.commutes a)

/-- The action by precomposition on geometric points, with the discrete topology. -/
noncomputable def etaleFieldGeometricAction (X : Scheme.Etale (Spec (CommRingCat.of K))) :
    Action (Type u) (Gal(Ksep/K)) where
  V := etaleFieldBasePoint K Ksep ⟶ (Scheme.Etale.forget _).obj X
  ρ :=
    { toFun := fun g ↦ End.of (↾(fun x ↦ etaleFieldPointAutomorphism K Ksep g ≫ x))
      map_one' := by
        apply End.ext
        apply ConcreteCategory.hom_ext
        intro x
        change etaleFieldPointAutomorphism K Ksep 1 ≫ x = x
        have h : etaleFieldPointAutomorphism K Ksep 1 = 𝟙 _ := by
          apply Over.OverMorphism.ext
          change Spec.map (𝟙 (CommRingCat.of Ksep)) = 𝟙 _
          exact Spec.map_id _
        rw [h, Category.id_comp]
      map_mul' := by
        intro g h
        apply End.ext
        apply ConcreteCategory.hom_ext
        intro x
        change etaleFieldPointAutomorphism K Ksep (g * h) ≫ x =
          etaleFieldPointAutomorphism K Ksep g ≫
            (etaleFieldPointAutomorphism K Ksep h ≫ x)
        rw [← Category.assoc]
        congr 1
        apply Over.OverMorphism.ext
        change Spec.map (CommRingCat.ofHom (g * h).toRingHom) =
          Spec.map (CommRingCat.ofHom g.toRingHom) ≫
            Spec.map (CommRingCat.ofHom h.toRingHom)
        rw [← Spec.map_comp]
        rfl }

private theorem finiteType_embedding_stabilizer_open [IsSepClosure K Ksep]
    (R : Type u) [CommRing R] [Algebra K R] [Algebra.FiniteType K R]
    (σ : R →ₐ[K] Ksep) :
    IsOpen {g : Gal(Ksep/K) | g.toAlgHom.comp σ = σ} := by
  classical
  let : Algebra.IsSeparable K Ksep := IsSepClosure.separable
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := K) (A := R)
  have heq : {g : Gal(Ksep/K) | g.toAlgHom.comp σ = σ} =
      ⋂ a ∈ s, {g : Gal(Ksep/K) | g (σ a) = σ a} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h a _
      exact DFunLike.congr_fun h a
    · intro h
      apply AlgHom.ext_of_adjoin_eq_top hs
      exact h
  rw [heq]
  apply isOpen_biInter_finset
  intro a _
  exact stabilizer_isOpen_of_isIntegral (K := K) (L := Ksep) (σ a)

/-- The geometric-point action is continuous for the discrete topology.
Source: Stacks Project, Tag 03QR, first paragraph
(blueprint: lem-exc-etale-field-geometric-action-continuous).

Proof: Factor a geometric point through an affine open neighborhood Spec R. The map
Spec R → Spec K is locally of finite type, so R is a finitely generated K-algebra.
The geometric point corresponds to a K-algebra map R → Ksep. Choose finitely many
algebra generators. A Galois automorphism fixes this map exactly when it fixes the
images of all generators. Each such image has open stabilizer in the Krull topology,
since Ksep/K is algebraic. Thus the map's stabilizer is a finite intersection of open
sets. The open immersion Spec R → X is a monomorphism, so this is also the stabilizer
of the original geometric point. An action on a discrete space is continuous exactly
when every point stabilizer is open. The empty scheme has no points to check. -/
theorem etaleFieldGeometricAction_continuous [IsSepClosure K Ksep]
    (X : Scheme.Etale (Spec (CommRingCat.of K))) :
    (etaleFieldGeometricAction K Ksep X).IsContinuous := by
  classical
  let A := etaleFieldGeometricAction K Ksep X
  change ContinuousSMul (Gal(Ksep/K)) ((forget₂ (Action (Type u) (Gal(Ksep/K))) TopCat).obj A)
  have : DiscreteTopology ((forget₂ (Action (Type u) (Gal(Ksep/K))) TopCat).obj A) := by
    change DiscreteTopology (TopCat.discrete.obj A.V)
    infer_instance
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  obtain ⟨R, j, hj, hjx, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := X.left) (x := x.left (default : Spec (CommRingCat.of Ksep)))
    (U := ⊤) trivial
  let := hj
  have hr : Set.range x.left ⊆ Set.range j := by
    rintro _ ⟨t, rfl⟩
    have ht : t = (default : Spec (CommRingCat.of Ksep)) :=
      Subsingleton.elim (α := Spec (CommRingCat.of Ksep)) _ _
    rw [ht]
    exact hjx
  let l := IsOpenImmersion.lift j x.left hr
  have hl : l ≫ j = x.left := IsOpenImmersion.lift_fac _ _ _
  let b := Spec.homEquiv (j ≫ X.hom)
  let σ := Spec.homEquiv l
  let := b.hom.toAlgebra
  have hb : Spec.map b = j ≫ X.hom := Spec.homEquiv.symm_apply_apply _
  have hσ : Spec.map σ = l := Spec.homEquiv.symm_apply_apply _
  have hbase : b ≫ σ = CommRingCat.ofHom (algebraMap K Ksep) := by
    apply Spec.homEquiv.symm.injective
    change Spec.map (b ≫ σ) = Spec.map (CommRingCat.ofHom (algebraMap K Ksep))
    rw [Spec.map_comp, hb, hσ, ← Category.assoc, hl]
    exact Over.w x
  let a : R →ₐ[K] Ksep :=
    { σ.hom with
      commutes' := fun k ↦ DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hbase) k }
  have : LocallyOfFiniteType (Spec.map b) := by rw [hb]; infer_instance
  have : Algebra.FiniteType K R := HasRingHomProperty.Spec_iff.mp this
  have ha := finiteType_embedding_stabilizer_open K Ksep R a
  have heq : (MulAction.stabilizer (Gal(Ksep/K)) x : Set (Gal(Ksep/K))) =
      {g : Gal(Ksep/K) | g.toAlgHom.comp a = a} := by
    ext g
    change etaleFieldPointAutomorphism K Ksep g ≫ x = x ↔ g.toAlgHom.comp a = a
    constructor
    · intro h
      have hleft := congrArg Over.Hom.left h
      change Spec.map (CommRingCat.ofHom g.toRingHom) ≫ x.left = x.left at hleft
      rw [← hl] at hleft
      have hg : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ l = l := by
        apply (cancel_mono j).mp
        exact hleft
      apply AlgHom.ext
      intro r
      have hring := congrArg (fun f ↦ (Spec.homEquiv f).hom r) hg
      simpa [a, ← hσ, ← Spec.map_comp] using hring
    · intro h
      apply Over.OverMorphism.ext
      have hg : σ ≫ CommRingCat.ofHom g.toRingHom = σ := by
        ext r
        exact DFunLike.congr_fun h r
      change Spec.map (CommRingCat.ofHom g.toRingHom) ≫ x.left = x.left
      rw [← hl]
      rw [← hσ, ← Category.assoc, ← Spec.map_comp, hg]
  rw [heq]
  exact ha

end AlgebraicGeometry
