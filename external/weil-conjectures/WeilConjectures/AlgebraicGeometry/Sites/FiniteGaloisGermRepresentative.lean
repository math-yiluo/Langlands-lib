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
public import Mathlib.FieldTheory.Galois.GaloisClosure

import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Finite Galois representatives of geometric germs

## References

* Stacks Project, Tag 04JM, direct proof of Lemma 59.56.5
* Stacks 04JM, finite separable neighbourhood step
* Stacks 04JM and 02G8(1), together with the residue-field factorization of field points (Stacks
  01J5)
* Stacks Project, Tag 04JM, the finite Galois neighbourhood step
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

/-- A separable embedding into the algebraic closure factors through the given separable
closure. -/
private theorem factor_separable_embedding
    (K Ks Ω P : Type u) [Field K] [Field Ks] [Field Ω] [Field P]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [Algebra.IsAlgebraic K Ω]
    [Algebra K P] [Algebra.IsSeparable K P] (a : P →ₐ[K] Ω) :
    ∃ b : P →ₐ[K] Ks, (IsScalarTower.toAlgHom K Ks Ω).comp b = a := by
  classical
  have : IsSepClosed Ks := IsSepClosure.sep_closed K
  have : Algebra.IsAlgebraic Ks Ω := Algebra.IsAlgebraic.tower_top (K := K) Ks
  have hr (x : P) : ∃ y : Ks, algebraMap Ks Ω y = a x := by
    apply IsPurelyInseparable.inseparable Ks
    exact IsSeparable.tower_top Ks
      ((Algebra.IsSeparable.isSeparable K x).map a a.injective)
  choose b hb using hr
  have hinj := (algebraMap Ks Ω).injective
  let f : P →ₐ[K] Ks :=
    { toFun := b
      map_zero' := hinj (by simp only [hb, map_zero])
      map_one' := hinj (by simp only [hb, map_one])
      map_add' := fun x y ↦ hinj (by simp only [map_add, hb])
      map_mul' := fun x y ↦ hinj (by simp only [map_mul, hb])
      commutes' := fun x ↦ hinj (by rw [hb, a.commutes, IsScalarTower.algebraMap_apply K Ks Ω]) }
  exact ⟨f, AlgHom.ext hb⟩

set_option backward.isDefEq.respectTransparency false in
/-- The residue field of the image of a geometric lift gives a finite separable pointed
neighbourhood. -/
private theorem pointed_field_neighbourhood
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (X : (Spec (.of K)).Etale) (x : (pointSmallEtale s).fiber.obj X) :
    ∃ (P : IntermediateField K Ks) (_ : FiniteDimensional K P)
      (g : etaleSpec K P ⟶ X),
      Spec.map (CommRingCat.ofHom
        ((algebraMap Ks Ω).comp P.subtype)) ≫ g.left = x.left := by
  classical
  let Y : Scheme.{u} := X.left
  let f : Y ⟶ Spec (.of K) := X.hom
  have : Etale f := X.prop
  let t : Y := x.left (IsLocalRing.closedPoint Ω)
  let q := Y.fromSpecResidueField t ≫ f
  let i := Spec.homEquiv q
  let : Algebra K (Y.residueField t) := i.hom.toAlgebra
  have heq : Spec.map i = q := Spec.homEquiv.symm_apply_apply _
  have : IsClosedImmersion ((Spec (.of K)).fromSpecResidueField (f t)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete _)
  have : Surjective ((Spec (.of K)).fromSpecResidueField (f t)) :=
    ⟨fun z ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective
    ((Spec (.of K)).fromSpecResidueField (f t))
  have : Etale (Spec.map (f.residueFieldMap t)) :=
    HasRingHomProperty.Spec_iff.mpr (f.etale_residueFieldMap t)
  have : Etale q := by
    dsimp only [q]
    rw [← f.SpecMap_residueFieldMap_fromSpecResidueField t]
    infer_instance
  have : Etale (Spec.map i) := heq ▸ ‹Etale q›
  have : Algebra.Etale K (Y.residueField t) := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact HasRingHomProperty.Spec_iff.mp ‹Etale (Spec.map i)›
  have : Module.Finite K (Y.residueField t) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  have : Algebra.IsSeparable K (Y.residueField t) :=
    (Algebra.FormallyEtale.iff_isSeparable _ _).mp inferInstance
  let a := (SpecToEquivOfField Ω Y x.left).2
  have ha : Spec.map a ≫ Y.fromSpecResidueField t = x.left :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω Y x.left
  have hac : a.hom.comp (algebraMap K (Y.residueField t)) = algebraMap K Ω := by
    have hc : i ≫ a = CommRingCat.ofHom (algebraMap K Ω) := by
      apply Spec.map_injective
      rw [Spec.map_comp, heq]
      change Spec.map a ≫ (Y.fromSpecResidueField t ≫ f) = _
      rw [← Category.assoc, ha]
      exact (Over.w x).trans hs
    exact congrArg CommRingCat.Hom.hom hc
  let aa : Y.residueField t →ₐ[K] Ω :=
    { a.hom with commutes' := fun k ↦ congrArg (fun f : K →+* Ω ↦ f k) hac }
  obtain ⟨b, hb⟩ := factor_separable_embedding K Ks Ω _ aa
  let P := b.fieldRange
  let e := b.equivFieldRange
  have : FiniteDimensional K P := FiniteDimensional.of_surjective e.toLinearMap e.surjective
  let g : etaleSpec K P ⟶ X := MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y.fromSpecResidueField t) (by
      change _ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K P))
      rw [Category.assoc]
      change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q = _
      rw [← heq, ← Spec.map_comp]
      congr 1
      ext k
      exact congrArg Subtype.val (e.commutes k))
  refine ⟨P, inferInstance, g, ?_⟩
  have hc : CommRingCat.ofHom e.toRingHom ≫
      CommRingCat.ofHom ((algebraMap Ks Ω).comp P.subtype) = a := by
    ext p
    exact congrArg (fun f : Y.residueField t →ₐ[K] Ω ↦ f p) hb
  change Spec.map _ ≫ (Spec.map _ ≫ _) = x.left
  rw [← Category.assoc, ← Spec.map_comp, hc]
  exact ha

/-- Every germ `m` in the geometric fibre of `F` is represented by a section of `F` over
`Spec E` for a finite Galois extension `E` of `K` containing a given finite extension `L`. -/
theorem exists_finiteGalois_germ_representative
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (L : IntermediateField K Ks) [FiniteDimensional K L]
    (m : (pointSmallEtale s).sheafFiber.obj F) :
    ∃ E : FiniteGaloisIntermediateField K Ks,
      L ≤ E.toIntermediateField ∧
      ∃ y : (pointSmallEtale s).fiber.obj (etaleSpec K E),
        y.left = Spec.map
          (CommRingCat.ofHom ((algebraMap Ks Ω).comp E.toIntermediateField.subtype)) ∧
        ∃ z : F.obj.obj (op (etaleSpec K E)),
          (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z = m := by
  classical
  obtain ⟨X, x, z, rfl⟩ := (pointSmallEtale s).toPresheafFiber_jointly_surjective
    (P := F.obj) m
  obtain ⟨P, hP, g, hg⟩ := pointed_field_neighbourhood K Ks Ω s hs X x
  let E : FiniteGaloisIntermediateField K Ks :=
    { IntermediateField.normalClosure K (↥(P ⊔ L)) Ks with
      finiteDimensional := normalClosure.is_finiteDimensional K (↥(P ⊔ L)) Ks
      isGalois := IsGalois.normalClosure K (↥(P ⊔ L)) Ks }
  have hPE : P ≤ E.toIntermediateField :=
    le_sup_left.trans (IntermediateField.le_normalClosure (P ⊔ L))
  have hLE : L ≤ E.toIntermediateField :=
    le_sup_right.trans (IntermediateField.le_normalClosure (P ⊔ L))
  let a := (algebraMap Ks Ω).comp E.toIntermediateField.subtype
  let y : (pointSmallEtale s).fiber.obj (etaleSpec K E) :=
    Over.homMk (Spec.map (CommRingCat.ofHom a)) (by
      change Spec.map (CommRingCat.ofHom a) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K E)) = s
      rw [← Spec.map_comp, hs]
      congr 1
      ext k
      exact (IsScalarTower.algebraMap_apply K Ks Ω k).symm)
  let j : etaleSpec K E ⟶ etaleSpec K P := etaleSpecMap (IntermediateField.inclusion hPE)
  let f := j ≫ g
  have hy : (pointSmallEtale s).fiber.map f y = x := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom a) ≫ (j.left ≫ g.left) = x.left
    rw [← Category.assoc]
    change (Spec.map (CommRingCat.ofHom a) ≫
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hPE).toRingHom)) ≫
        g.left = x.left
    rw [← Spec.map_comp]
    have hc : CommRingCat.ofHom (IntermediateField.inclusion hPE).toRingHom ≫
        CommRingCat.ofHom a =
        CommRingCat.ofHom ((algebraMap Ks Ω).comp P.subtype) := by
      ext p
      rfl
    rw [hc]
    exact hg
  refine ⟨E, hLE, y, rfl, F.obj.map f.op z, ?_⟩
  rw [GrothendieckTopology.Point.toPresheafFiber_w_apply, hy]

end AlgebraicGeometry.Scheme
