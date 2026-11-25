/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Bijectivity of evaluation on the geometric stalk of units

Source: Stacks Project, Tags 03QU and Example 03QV (2).
(blueprint: lem-sc-etale-units-stalk-evaluation-overfield-bijective).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

-- The filtered colimit and residue-field refinements require additional elaboration work.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A stalk homomorphism satisfying the evaluation formula is bijective.

Source: Stacks Project, Tags 03QU and Example 03QV (2).
(blueprint: lem-sc-etale-units-stalk-evaluation-overfield-bijective).

Proof: For surjectivity, a separable-closure unit generates a finite separable
simple intermediate field L/K. Its spectrum is etale, and its given embedding in
Omega supplies the geometric lift. Apply the inverse global-sections isomorphism
of Spec L to the unit in L. The evaluation formula and naturality of the
isomorphism show that its germ has exactly the desired value; injectivity of
Ks into Omega removes the embedding.
For injectivity, use joint surjectivity of the filtered-colimit germ maps to
represent two stalk elements on a single pointed etale neighbourhood X. Let y
be the image of its lift. The canonical residue-field map Spec kappa(y) -> X
followed by X -> Spec K is etale: the structural residue-field map is etale,
and the residue-field spectrum at the point of Spec K is isomorphic to Spec K
(it is a reduced surjective closed immersion). Thus Spec kappa(y) is another
object of the small etale site. The original lift factors through it. Its field
embedding into Omega is injective. Naturality of the global-sections isomorphism
therefore makes equality of evaluated values imply equality of the restricted
unit sections. The filtered-colimit equality criterion identifies their germs.
No cofinality theorem or common finite compositum is needed for injectivity.
The proof includes imperfect base fields and transcendental overfields Omega.
No Galois equivariance is assumed or concluded. -/
theorem etaleUnits_stalk_evaluation_overfield_bijective
    (K Ω : Type u) [Field K] [Field Ω]
    [Algebra (SeparableClosure K) Ω] [Algebra K Ω]
    [IsScalarTower K (SeparableClosure K) Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ f : (p.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S.gmSheaf →+
        Additive (SeparableClosure K)ˣ,
      (∀ (X : S.Etale) (x : p.fiber.obj X) (z : S.gmSheaf.obj.obj (op X)),
        algebraMap (SeparableClosure K) Ω
            (Additive.toMul (f (p.toPresheafFiber X x S.gmSheaf.obj z)) :
              (SeparableClosure K)ˣ) =
          (ΓSpecIso (.of Ω)).hom
            (x.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)))) →
      Function.Bijective f := by
  classical
  dsimp only
  intro f hf
  let S := Spec (.of K)
  let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  constructor
  · intro v w hvw
    obtain ⟨X, x, z, z', rfl, rfl⟩ :=
      p.toPresheafFiber_jointly_surjective₂ (P := S.gmSheaf.obj) v w
    have heval := congrArg
      (fun t ↦ algebraMap (SeparableClosure K) Ω (Additive.toMul t : (SeparableClosure K)ˣ))
      hvw
    rw [hf, hf] at heval
    let y := x.left (IsLocalRing.closedPoint Ω)
    let q := X.hom y
    have : IsClosedImmersion (S.fromSpecResidueField q) :=
      isClosed_singleton_iff_isClosedImmersion.mp (by
        have : ({q} : Set S) = Set.univ :=
          Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
        rw [this]
        exact isClosed_univ)
    have : Surjective (S.fromSpecResidueField q) :=
      ⟨fun t ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
    have : IsIso (S.fromSpecResidueField q) := isIso_of_isClosedImmersion_of_surjective _
    let m := X.hom.residueFieldMap y
    have : Etale (Spec.map m) := HasRingHomProperty.Spec_iff.mpr
      (X.hom.etale_residueFieldMap y)
    have heq : Spec.map m ≫ S.fromSpecResidueField q =
        X.left.fromSpecResidueField y ≫ X.hom :=
      X.hom.SpecMap_residueFieldMap_fromSpecResidueField y
    have : Etale (X.left.fromSpecResidueField y ≫ X.hom) :=
      heq ▸ (inferInstance : Etale (Spec.map m ≫ S.fromSpecResidueField q))
    let Y : S.Etale := Scheme.Etale.mk (X.left.fromSpecResidueField y ≫ X.hom)
    let a : Y ⟶ X := MorphismProperty.Over.homMk (X.left.fromSpecResidueField y)
    let r := X.left.descResidueField (stalkClosedPointTo x.left)
    have hr : Spec.map r ≫ X.left.fromSpecResidueField y = x.left :=
      descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X.left x.left
    let xY : p.fiber.obj Y := Over.homMk (Spec.map r) (by
      change Spec.map r ≫ (X.left.fromSpecResidueField y ≫ X.hom) = _
      rw [← Category.assoc, hr]
      exact x.w)
    have hxY : p.fiber.map a xY = x := by
      apply Over.OverMorphism.ext
      exact hr
    have hsec : S.gmSheaf.obj.map a.op z = S.gmSheaf.obj.map a.op z' := by
      apply ULift.ext
      apply Additive.toMul.injective
      apply Units.ext
      change a.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)) =
        a.left.appTop ((Additive.toMul z'.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤))
      apply (ConcreteCategory.bijective_of_isIso (ΓSpecIso (X.left.residueField y)).hom).1
      apply r.hom.injective
      have hn := ΓSpecIso_naturality r
      have hvalue (t : Γ(X.left, ⊤)) :
          (ΓSpecIso (.of Ω)).hom (x.left.appTop t) =
            r ((ΓSpecIso (X.left.residueField y)).hom (a.left.appTop t)) := by
        have hmap := congrArg (fun l : Spec (.of Ω) ⟶ X.left ↦
          (ΓSpecIso (.of Ω)).hom (l.appTop t)) hr
        rw [Hom.comp_appTop] at hmap
        exact hmap.symm.trans (ConcreteCategory.congr_hom hn (a.left.appTop t))
      exact (hvalue _).symm.trans (heval.trans (hvalue _))
    exact (p.toPresheafFiber_eq_iff' X x z z').2 ⟨Y, a, xY, hxY, hsec⟩
  · intro t
    let a := (Additive.toMul t : (SeparableClosure K)ˣ)
    let L : IntermediateField K (SeparableClosure K) :=
      IntermediateField.adjoin K {(a : SeparableClosure K)}
    have : FiniteDimensional K L :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsSeparable.isIntegral K (a : SeparableClosure K))
    have : Algebra.Etale K L := Algebra.Etale.of_finite_of_isSeparable
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    let X : S.Etale := Scheme.Etale.mk
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    let r : L →+* Ω := (algebraMap (SeparableClosure K) Ω).comp L.subtype
    let x : p.fiber.obj X := Over.homMk (Spec.map (CommRingCat.ofHom r)) (by
      change Spec.map (CommRingCat.ofHom r) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) = _
      rw [← Spec.map_comp]
      congr 1
      ext k
      exact (IsScalarTower.algebraMap_apply K (SeparableClosure K) Ω k).symm)
    let aL : L := ⟨(a : SeparableClosure K),
      IntermediateField.mem_adjoin_simple_self K (a : SeparableClosure K)⟩
    have haL : aL ≠ 0 := by
      intro h
      exact a.ne_zero (congrArg Subtype.val h)
    let z : S.gmSheaf.obj.obj (op X) := ULift.up (Additive.ofMul
      (Units.map (ΓSpecIso (.of L)).inv.hom.toMonoidHom (Units.mk0 aL haL)))
    refine ⟨p.toPresheafFiber X x S.gmSheaf.obj z, ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    apply (algebraMap (SeparableClosure K) Ω).injective
    rw [hf]
    have hn := ConcreteCategory.congr_hom
      (ΓSpecIso_naturality (CommRingCat.ofHom r))
      ((ΓSpecIso (.of L)).inv aL)
    change (ΓSpecIso (.of Ω)).hom
      ((Spec.map (CommRingCat.ofHom r)).appTop ((ΓSpecIso (.of L)).inv aL)) = _
    exact hn.trans (congrArg r ((ΓSpecIso (.of L)).inv_hom_id_apply aL))

end AlgebraicGeometry.Scheme
