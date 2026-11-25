/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction
import WeilConjectures.AlgebraicGeometry.EtaleFieldPointFunctorEssSurj
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Étale schemes over a field and continuous G-sets

Source: Stacks Project, Tags 03QR and 03QS (blueprint: lem-exc-etale-field-gsets).
-/

@[expose] public section

universe u w

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] etaleFieldDiscreteForget₂ etaleFieldActionForget₂

/-- Stacks Project, Tags 03QR and 03QS (blueprint: lem-exc-etale-field-gsets).
The geometric-point functor carries the Galois action by precomposition. An étale scheme
over a field is a coproduct of spectra of finite separable extensions. Their geometric
points are finite transitive Galois sets, with open stabilizers, giving continuity.
The finite Galois correspondence identifies maps between components, proving full
faithfulness. Decomposing any discrete continuous Galois set into orbits and taking
the coproduct of the spectra of their fixed fields proves essential surjectivity.
Finally, every geometric point over a point of an étale scheme lifts through a
surjective étale family, and every point has a geometric point. Thus a family is
a cover exactly when its image under this functor is jointly surjective. -/
theorem etaleFieldGsets
    (K : Type u) [Field K]
    (Ksep : Type u) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] :
    ∃ (E : Scheme.Etale (Spec (CommRingCat.of K)) ≌
        DiscreteContAction (Type u) (Gal(Ksep / K)))
      (points : ∀ X : Scheme.Etale (Spec (CommRingCat.of K)),
        ((forget₂ _ (Type u)).obj (E.functor.obj X)) ≃
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ksep))) ⟶
            (Scheme.Etale.forget _).obj X)),
      (∀ (X Y : Scheme.Etale (Spec (CommRingCat.of K))) (f : X ⟶ Y)
          (x : (forget₂ _ (Type u)).obj (E.functor.obj X)),
        points Y ((forget₂ _ (Type u)).map (E.functor.map f) x) =
          points X x ≫ (Scheme.Etale.forget _).map f) ∧
      (∀ (X : Scheme.Etale (Spec (CommRingCat.of K))) (g : Gal(Ksep / K))
          (x : (forget₂ _ (Type u)).obj (E.functor.obj X)),
        (points X (((E.functor.obj X).obj.obj.ρ g) x)).left =
          Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (points X x).left) ∧
      (∀ {ι : Type w} (X : Scheme.Etale (Spec (CommRingCat.of K)))
          (U : ι → Scheme.Etale (Spec (CommRingCat.of K))) (f : ∀ i, U i ⟶ X),
        Sieve.ofArrows U f ∈ (Spec (CommRingCat.of K)).smallEtaleTopology X ↔
          ∀ x : (forget₂ _ (Type u)).obj (E.functor.obj X),
            ∃ (i : ι) (y : (forget₂ _ (Type u)).obj (E.functor.obj (U i))),
              (forget₂ _ (Type u)).map (E.functor.map (f i)) y = x) := by
  let F := etaleFieldPointFunctor K Ksep
  have h := etaleFieldPointFunctor_fullyFaithful K Ksep
  let := h.1
  let := h.2
  let := etaleFieldPointFunctor_essSurj K Ksep
  let : F.IsEquivalence := {}
  let : IsSepClosed Ksep := IsSepClosure.sep_closed K
  refine ⟨F.asEquivalence, fun X ↦ Equiv.refl _, ?_, ?_, ?_⟩
  · intro X Y f x
    rfl
  · intro X g x
    rfl
  · intro ι X U f
    change Sieve.ofArrows U f ∈ (Spec (CommRingCat.of K)).smallEtaleTopology X ↔
      ∀ x : etaleFieldBasePoint K Ksep ⟶ (Scheme.Etale.forget _).obj X,
        ∃ (i : ι) (y : etaleFieldBasePoint K Ksep ⟶
          (Scheme.Etale.forget _).obj (U i)), y ≫ (Scheme.Etale.forget _).map (f i) = x
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    constructor
    · intro hc x
      have hx : x.left (default : Spec (CommRingCat.of Ksep)) ∈
          ⋃ i, Set.range (f i).left := by rw [hc]; trivial
      simp only [Set.mem_iUnion, Set.mem_range] at hx
      obtain ⟨i, z, hz⟩ := hx
      obtain ⟨l, hl, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
        (f i).left x.left z hz
      refine ⟨i, Over.homMk l ?_, ?_⟩
      · change l ≫ (U i).hom = Spec.map (CommRingCat.ofHom (algebraMap K Ksep))
        have hf : (f i).left ≫ X.hom = (U i).hom := (f i).w
        rw [← hf, ← Category.assoc, hl]
        exact Over.w x
      · apply Over.OverMorphism.ext
        exact hl
    · intro hp
      ext z
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨x, hx⟩ := Scheme.pointSmallEtaleFiberObjToPreimage_surjective
        (Spec.map (CommRingCat.ofHom (algebraMap K Ksep))) rfl X
        ⟨z, by
          change (X.hom z : Spec (CommRingCat.of K)) = _
          exact Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _⟩
      obtain ⟨i, y, hy⟩ := hp x
      refine ⟨i, y.left (default : Spec (CommRingCat.of Ksep)), ?_⟩
      have he := congrArg (fun t ↦ t.left (default : Spec (CommRingCat.of Ksep))) hy
      have hz : x.left (default : Spec (CommRingCat.of Ksep)) = z := congrArg Subtype.val hx
      exact he.trans hz

end AlgebraicGeometry
