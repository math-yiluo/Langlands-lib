/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension
import WeilConjectures.AlgebraicGeometry.Sites.FieldInvariantGermRepresentative

/-!
# Sections over finite separable fields and geometric stalk invariants

## References

* Stacks Project, Etale Cohomology, Tags 04JM and 03QW

## Implementation details

In `fieldSections_stalkInvariants`, sections over a finite separable `L` are identified with
invariant germs by enlarging a germ representative to a finite Galois extension `E / L` and
applying finite Galois descent for sections; naturality comes from the lift-change action.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

private theorem closureAut_ext
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [Algebra.IsAlgebraic K Ω]
    (τ τ' : Ω ≃ₐ[K] Ω)
    (h : τ.toRingHom.comp (algebraMap Ks Ω) =
      τ'.toRingHom.comp (algebraMap Ks Ω)) : τ = τ' := by
  have : IsSepClosed Ks := IsSepClosure.sep_closed K
  have : Algebra.IsAlgebraic Ks Ω := Algebra.IsAlgebraic.tower_top (K := K) Ks
  have := IsPurelyInseparable.injective_comp_algebraMap Ks Ω Ω h
  ext a
  exact congrArg (fun f : Ω →+* Ω ↦ f a) this

private noncomputable def closureAut
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] (g : Gal(Ks/K)) : Ω ≃ₐ[K] Ω :=
  Classical.choose (exists_algEquiv_extending_separableClosure K Ks Ω g)

private theorem closureAut_spec_base
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (τ : Ω ≃ₐ[K] Ω) : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ s = s := by
  subst s
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact τ.commutes a

private noncomputable def changeLift
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (τ : Ω ≃ₐ[K] Ω) (X : (Spec (.of K)).Etale)
    (x : (pointSmallEtale s).fiber.obj X) : (pointSmallEtale s).fiber.obj X :=
  Over.homMk (Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left) (by
    rw [Category.assoc, Over.w x]
    exact closureAut_spec_base K Ks Ω s hs τ)

private noncomputable def changeGerm
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (τ : Ω ≃ₐ[K] Ω)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v))) :
    (pointSmallEtale s).sheafFiber.obj F → (pointSmallEtale s).sheafFiber.obj F :=
  (pointSmallEtale s).presheafFiberDesc
    (fun X x ↦ (pointSmallEtale s).toPresheafFiber X
      (changeLift K Ks Ω s hs τ X x) F.obj) (by
        intro X Y f x
        rw [GrothendieckTopology.Point.toPresheafFiber_w]
        congr 1)

private theorem closureAut_restrict
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (g : Gal(Ks/K)) :
    (closureAut K Ks Ω g).toRingHom.comp (algebraMap Ks Ω) =
      (algebraMap Ks Ω).comp g.toRingHom :=
  (Classical.choose_spec (exists_algEquiv_extending_separableClosure K Ks Ω g)).symm

private theorem closureAut_one
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] : closureAut K Ks Ω 1 = 1 := by
  apply closureAut_ext K Ks Ω
  rw [closureAut_restrict]
  rfl

private theorem closureAut_mul
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (g h : Gal(Ks/K)) :
    closureAut K Ks Ω (g * h) = closureAut K Ks Ω g * closureAut K Ks Ω h := by
  apply closureAut_ext K Ks Ω
  rw [closureAut_restrict]
  change (algebraMap Ks Ω).comp (g.toRingHom.comp h.toRingHom) =
    ((closureAut K Ks Ω g).toRingHom.comp (closureAut K Ks Ω h).toRingHom).comp _
  ext a
  have ht (k : Gal(Ks/K)) (b : Ks) :
      closureAut K Ks Ω k (algebraMap Ks Ω b) = algebraMap Ks Ω (k b) :=
    congrArg (fun f : Ks →+* Ω ↦ f b) (closureAut_restrict K Ks Ω k)
  change algebraMap Ks Ω (g (h a)) =
    closureAut K Ks Ω g (closureAut K Ks Ω h (algebraMap Ks Ω a))
  rw [ht, ht]

private theorem changeGerm_germ
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (τ : Ω ≃ₐ[K] Ω)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (X : (Spec (.of K)).Etale) (x : (pointSmallEtale s).fiber.obj X)
    (z : F.obj.obj (op X)) :
    changeGerm K Ks Ω s hs τ F ((pointSmallEtale s).toPresheafFiber X x F.obj z) =
      (pointSmallEtale s).toPresheafFiber X (changeLift K Ks Ω s hs τ X x) F.obj z := by
  have h := (pointSmallEtale s).toPresheafFiber_presheafFiberDesc
    (φ := fun Y y ↦ (pointSmallEtale s).toPresheafFiber Y
      (changeLift K Ks Ω s hs τ Y y) F.obj)
    (hφ := by
      intro Y Z f y
      rw [GrothendieckTopology.Point.toPresheafFiber_w]
      congr 1) X x
  exact congrArg (fun f ↦ f z) h

@[instance_reducible]
private noncomputable def stalkAction
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v))) :
    MulAction Gal(Ks/K) ((pointSmallEtale s).sheafFiber.obj F) where
  smul g := changeGerm K Ks Ω s hs (closureAut K Ks Ω g) F
  one_smul m := by
    obtain ⟨X, x, z, rfl⟩ := (pointSmallEtale s).toPresheafFiber_jointly_surjective
      (P := F.obj) m
    change changeGerm K Ks Ω s hs (closureAut K Ks Ω 1) F
      ((pointSmallEtale s).toPresheafFiber X x F.obj z) = _
    rw [closureAut_one, changeGerm_germ]
    have hx : changeLift K Ks Ω s hs 1 X x = x := by
      apply Over.OverMorphism.ext
      change Spec.map (𝟙 (CommRingCat.of Ω)) ≫ x.left = x.left
      rw [Spec.map_id, Category.id_comp]
    rw [hx]
  mul_smul g h m := by
    obtain ⟨X, x, z, rfl⟩ := (pointSmallEtale s).toPresheafFiber_jointly_surjective
      (P := F.obj) m
    change changeGerm K Ks Ω s hs (closureAut K Ks Ω (g * h)) F
      ((pointSmallEtale s).toPresheafFiber X x F.obj z) =
      changeGerm K Ks Ω s hs (closureAut K Ks Ω g) F
        (changeGerm K Ks Ω s hs (closureAut K Ks Ω h) F
          ((pointSmallEtale s).toPresheafFiber X x F.obj z))
    rw [changeGerm_germ, changeGerm_germ, changeGerm_germ, closureAut_mul]
    have hx : changeLift K Ks Ω s hs
        (closureAut K Ks Ω g * closureAut K Ks Ω h) X x =
        changeLift K Ks Ω s hs (closureAut K Ks Ω g) X
          (changeLift K Ks Ω s hs (closureAut K Ks Ω h) X x) := by
      apply Over.OverMorphism.ext
      simp only [changeLift, Over.homMk_left, ← Category.assoc, ← Spec.map_comp]
      rfl
    rw [hx]

private theorem fieldGerm_injective
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (x : (pointSmallEtale s).fiber.obj (etaleSpec K L)) :
    Function.Injective ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) x F.obj) := by
  intro z z' h
  obtain ⟨Y, f, y, _, hf⟩ :=
    ((pointSmallEtale s).toPresheafFiber_eq_iff' (P := F.obj) _ x z z').mp h
  have hcov : Sieve.ofArrows _ (fun _ : Unit ↦ f) ∈
      (Spec (.of K)).smallEtaleTopology (etaleSpec K L) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext a
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨(), y.left (default : Spec (.of Ω)),
      @Subsingleton.elim (Spec (.of L)) _ _ _⟩
  have hsheaf : Presieve.IsSheafFor F.obj (Presieve.singleton f) := by
    rw [← Presieve.ofArrows_pUnit.{0}, Presieve.isSheafFor_iff_generate]
    exact ((isSheaf_iff_isSheaf_of_type _ _).mp F.property) _ hcov
  exact (Presieve.isSeparatedFor_singleton.mp hsheaf.isSeparatedFor) hf

/-- There is a Galois action on geometric stalks, characterized by changing lifts through
automorphisms of the algebraic closure. At every finite separable intermediate field, the
canonical germ map identifies sections with the elements fixed by its Galois subgroup. These
maps commute with sheaf morphisms and field embeddings, independently of the extending
automorphism. -/
theorem fieldSections_stalkInvariants
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    ∃ (lift : ∀ (L : IntermediateField K Ks)
        [FiniteDimensional K L] [Algebra.IsSeparable K L],
          (pointSmallEtale s).fiber.obj (etaleSpec K L))
      (action : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)),
        MulAction Gal(Ks/K) ((pointSmallEtale s).sheafFiber.obj F)),
      (∀ (L : IntermediateField K Ks) [FiniteDimensional K L]
        [Algebra.IsSeparable K L],
        (lift L).left = Spec.map
          (CommRingCat.ofHom ((algebraMap Ks Ω).comp L.subtype))) ∧
      (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v))),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
          (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω) →
          ∀ (X : (Spec (.of K)).Etale)
          (x x' : (pointSmallEtale s).fiber.obj X),
          x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
          ∀ (z : F.obj.obj (op X)),
          (action F).smul g ((pointSmallEtale s).toPresheafFiber X x F.obj z) =
            (pointSmallEtale s).toPresheafFiber X x' F.obj z) ∧
        (∀ (L : IntermediateField K Ks) [FiniteDimensional K L]
          [Algebra.IsSeparable K L],
          Set.BijOn
            ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj)
            Set.univ
            {m | ∀ g ∈ L.fixingSubgroup, (action F).smul g m = m}) ∧
        (∀ (L L' : IntermediateField K Ks) [FiniteDimensional K L]
          [FiniteDimensional K L'] [Algebra.IsSeparable K L]
          [Algebra.IsSeparable K L']
          (j : L →ₐ[K] L') (g : Gal(Ks/K)),
          g.toAlgHom.comp L.val = L'.val.comp j →
          ∀ (z : F.obj.obj (op (etaleSpec K L))),
          (pointSmallEtale s).toPresheafFiber (etaleSpec K L') (lift L') F.obj
              (F.obj.map (etaleSpecMap j).op z) =
            (action F).smul g
              ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj z)) ∧
        (∀ (L L' : IntermediateField K Ks) [FiniteDimensional K L]
          [FiniteDimensional K L'] [Algebra.IsSeparable K L]
          [Algebra.IsSeparable K L']
          (j : L →ₐ[K] L') (g g' : Gal(Ks/K)),
          g.toAlgHom.comp L.val = L'.val.comp j →
          g'.toAlgHom.comp L.val = L'.val.comp j →
          ∀ (m : (pointSmallEtale s).sheafFiber.obj F),
          (∀ h ∈ L.fixingSubgroup, (action F).smul h m = m) →
          (∀ h ∈ L'.fixingSubgroup,
            (action F).smul h ((action F).smul g m) = (action F).smul g m) ∧
          (action F).smul g m = (action F).smul g' m)) ∧
      (∀ (F F' : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
        (φ : F ⟶ F'),
        (∀ (L : IntermediateField K Ks) [FiniteDimensional K L]
          [Algebra.IsSeparable K L] (z : F.obj.obj (op (etaleSpec K L))),
          (pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F'.obj
              (φ.hom.app _ z) =
            (pointSmallEtale s).sheafFiber.map φ
              ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj z)) ∧
        (∀ (g : Gal(Ks/K)) (m : (pointSmallEtale s).sheafFiber.obj F),
          (pointSmallEtale s).sheafFiber.map φ ((action F).smul g m) =
            (action F').smul g ((pointSmallEtale s).sheafFiber.map φ m))) := by
  classical
  let lift (L : IntermediateField K Ks) [FiniteDimensional K L]
      [Algebra.IsSeparable K L] : (pointSmallEtale s).fiber.obj (etaleSpec K L) :=
    Over.homMk (Spec.map
      (CommRingCat.ofHom ((algebraMap Ks Ω).comp L.subtype))) (by
        change Spec.map _ ≫ Spec.map _ = s
        rw [← Spec.map_comp, hs]
        congr 1
        ext a
        exact (IsScalarTower.algebraMap_apply K Ks Ω a).symm)
  let action := stalkAction.{u, v} K Ks Ω s hs
  have hlift (L : IntermediateField K Ks) [FiniteDimensional K L]
      [Algebra.IsSeparable K L] : (lift L).left = Spec.map
        (CommRingCat.ofHom ((algebraMap Ks Ω).comp L.subtype)) := rfl
  have haction
      (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
      (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale) (x x' : (pointSmallEtale s).fiber.obj X)
      (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : F.obj.obj (op X)) :
      (action F).smul g ((pointSmallEtale s).toPresheafFiber X x F.obj z) =
        (pointSmallEtale s).toPresheafFiber X x' F.obj z := by
    have hτ' : closureAut K Ks Ω g = τ :=
      closureAut_ext K Ks Ω _ _ ((closureAut_restrict K Ks Ω g).trans hτ)
    change changeGerm K Ks Ω s hs (closureAut K Ks Ω g) F _ = _
    rw [hτ', changeGerm_germ]
    have hx' : changeLift K Ks Ω s hs τ X x = x' :=
      Over.OverMorphism.ext hx.symm
    rw [hx']
  have hbij
      (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
      (L : IntermediateField K Ks) [FiniteDimensional K L]
      [Algebra.IsSeparable K L] :
      Set.BijOn ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj)
        Set.univ {m | ∀ g ∈ L.fixingSubgroup, (action F).smul g m = m} := by
    refine ⟨?_, (fieldGerm_injective K Ks Ω s F L (lift L)).injOn, ?_⟩
    · intro z _ g hg
      obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ks Ω g
      have hx : (lift L).left =
          Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ (lift L).left := by
        rw [hlift]
        rw [← Spec.map_comp]
        congr 1
        ext a
        have ht := congrArg (fun f : Ks →+* Ω ↦ f (L.val a)) hτ
        have hg' := (IntermediateField.mem_fixingSubgroup_iff L g).mp hg a a.property
        change algebraMap Ks Ω (L.val a) = τ (algebraMap Ks Ω (L.val a))
        exact (congrArg (algebraMap Ks Ω) hg').symm.trans ht
      exact haction F g τ hτ _ (lift L) (lift L) hx z
    · intro m hm
      obtain ⟨z, hz⟩ := exists_fieldSection_of_invariant_germ K Ks Ω s hs F
        (action F) (haction F) L (lift L) (hlift L) m hm
      exact ⟨z, Set.mem_univ _, hz⟩
  have hemb
      (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
      (L L' : IntermediateField K Ks) [FiniteDimensional K L]
      [FiniteDimensional K L'] [Algebra.IsSeparable K L] [Algebra.IsSeparable K L']
      (j : L →ₐ[K] L') (g : Gal(Ks/K))
      (hg : g.toAlgHom.comp L.val = L'.val.comp j)
      (z : F.obj.obj (op (etaleSpec K L))) :
      (pointSmallEtale s).toPresheafFiber (etaleSpec K L') (lift L') F.obj
          (F.obj.map (etaleSpecMap j).op z) =
        (action F).smul g
          ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj z) := by
    obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ks Ω g
    let x' := (pointSmallEtale s).fiber.map (etaleSpecMap j) (lift L')
    have hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ (lift L).left := by
      change (lift L').left ≫ (etaleSpecMap j).left = _
      rw [hlift, hlift]
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      have ht := congrArg (fun f : Ks →+* Ω ↦ f (L.val a)) hτ
      have hg' := congrArg (fun f : L →ₐ[K] Ks ↦ f a) hg
      change algebraMap Ks Ω (L'.val (j a)) = τ (algebraMap Ks Ω (L.val a))
      exact (congrArg (algebraMap Ks Ω) hg').symm.trans ht
    rw [GrothendieckTopology.Point.toPresheafFiber_w_apply]
    exact (haction F g τ hτ _ (lift L) x' hx z).symm
  refine ⟨lift, action, hlift, ?_, ?_⟩
  · intro F
    refine ⟨?_, hbij F, ?_, ?_⟩
    · intro g τ hτ X x x' hx z
      exact haction F g τ hτ X x x' hx z
    · intro L L' _ _ _ _ j g hg z
      exact hemb F L L' j g hg z
    · intro L L' _ _ _ _ j g g' hg hg' m hm
      obtain ⟨z, _, hz⟩ := (hbij F L).surjOn hm
      subst m
      rw [← hemb F L L' j g hg, ← hemb F L L' j g' hg']
      exact ⟨(hbij F L').mapsTo (Set.mem_univ _), rfl⟩
  · intro F F' φ
    refine ⟨?_, ?_⟩
    · intro L _ _ z
      exact ((pointSmallEtale s).toPresheafFiber_naturality_apply φ.hom _ _ z).symm
    · intro g m
      obtain ⟨X, x, z, rfl⟩ := (pointSmallEtale s).toPresheafFiber_jointly_surjective
        (P := F.obj) m
      change (pointSmallEtale s).presheafFiber.map φ.hom
        (changeGerm K Ks Ω s hs (closureAut K Ks Ω g) F _) =
          changeGerm K Ks Ω s hs (closureAut K Ks Ω g) F'
            ((pointSmallEtale s).presheafFiber.map φ.hom _)
      rw [changeGerm_germ,
        GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
        GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
        changeGerm_germ]

end AlgebraicGeometry.Scheme
