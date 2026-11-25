/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Values of functions on etale neighbourhoods are separable

Source: Stacks Project, Tags 03QU and Example 03QV (2).
(blueprint: lem-sc-etale-evaluation-separable).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Evaluation of an etale function at a geometric lift is separable over the base field.

Source: Stacks Project, Tags 03QU and Example 03QV (2).
(blueprint: lem-sc-etale-evaluation-separable).

Proof: Factor the geometric lift through the residue field of its image point.
The residue-field inclusion into Spec K is an isomorphism: it is a surjective closed
immersion into a reduced scheme. Hence its preimage under Spec is a ring isomorphism.
The residue-field extension induced by the etale structural morphism is finite
separable, so its composite with this ring isomorphism is etale, and in particular
separable. The embedding of the image residue field into the algebraic closure is
K-linear because the geometric lift lies over Spec K. Evaluate the global function
first in this residue field, then embed it. Naturality of the global sections of
Spec identifies the result with evaluation along the original lift. Separability
is preserved by the embedding. This argument needs no quasi-compactness of X. -/
theorem etale_evaluation_isSeparable (K : Type u) [Field K] :
    let Ω := AlgebraicClosure K
    let S := Spec (.of K)
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (X : S.Etale) (x : p.fiber.obj X) (z : Γ(X.left, ⊤)),
      IsSeparable K ((ΓSpecIso (.of Ω)).hom (x.left.appTop z)) := by
  classical
  dsimp only
  intro X x z
  let Ω := AlgebraicClosure K
  let S := Spec (.of K)
  let y := x.left (IsLocalRing.closedPoint Ω)
  let q := X.hom y
  have hq : IsClosed ({q} : Set S) := by
    have : ({q} : Set S) = Set.univ := Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
    rw [this]
    exact isClosed_univ
  have : IsClosedImmersion (S.fromSpecResidueField q) :=
    isClosed_singleton_iff_isClosedImmersion.mp hq
  have : Surjective (S.fromSpecResidueField q) :=
    ⟨fun t ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  have : IsIso (S.fromSpecResidueField q) :=
    isIso_of_isClosedImmersion_of_surjective _
  let b : CommRingCat.of K ⟶ S.residueField q :=
    Spec.preimage (S.fromSpecResidueField q)
  have : IsIso (Scheme.Spec.map b.op) := by
    change IsIso (Spec.map b)
    dsimp only [b]
    rw [Spec.map_preimage]
    infer_instance
  have : IsIso b.op := isIso_of_reflects_iso b.op Scheme.Spec
  have : IsIso b := isIso_of_op b
  let m := X.hom.residueFieldMap y
  let a := X.left.descResidueField (stalkClosedPointTo x.left)
  have hb : b.hom.Etale := RingHom.Etale.of_bijective
    (ConcreteCategory.bijective_of_isIso b)
  have hm : m.hom.Etale := X.hom.etale_residueFieldMap y
  let : Algebra K (X.left.residueField y) := (b ≫ m).hom.toAlgebra
  have : Algebra.Etale K (X.left.residueField y) := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact RingHom.Etale.stableUnderComposition _ _ hb hm
  have : Algebra.IsSeparable K (X.left.residueField y) :=
    (Algebra.FormallyEtale.iff_isSeparable K (X.left.residueField y)).mp inferInstance
  have hcomp : b ≫ m ≫ a = CommRingCat.ofHom (algebraMap K Ω) := by
    apply Spec.map_injective
    have hmfac : Spec.map m ≫ S.fromSpecResidueField q =
        X.left.fromSpecResidueField y ≫ X.hom :=
      X.hom.SpecMap_residueFieldMap_fromSpecResidueField y
    have hafac := descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X.left x.left
    calc
      Spec.map (b ≫ m ≫ a) = Spec.map a ≫ (Spec.map m ≫ Spec.map b) := by
        simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map a ≫ (Spec.map m ≫ S.fromSpecResidueField q) := by
        dsimp only [b]
        rw [Spec.map_preimage]
      _ = Spec.map a ≫ (X.left.fromSpecResidueField y ≫ X.hom) := by rw [hmfac]
      _ = x.left ≫ X.hom := by rw [← Category.assoc]; exact congrArg (· ≫ X.hom) hafac
      _ = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := x.w
  let a' : X.left.residueField y →ₐ[K] Ω :=
    { a.hom with
      commutes' r := by
        exact congrArg (fun t : CommRingCat.of K ⟶ CommRingCat.of Ω ↦ t r) hcomp }
  let w := (ΓSpecIso (X.left.residueField y)).hom
    ((X.left.fromSpecResidueField y).appTop z)
  have hw := (Algebra.IsSeparable.isSeparable K w).map a' a'.injective
  have heval : (ΓSpecIso (.of Ω)).hom (x.left.appTop z) = a' w := by
    have hf := descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X.left x.left
    rw [← hf, Hom.comp_appTop]
    exact congrArg (fun t ↦ t ((X.left.fromSpecResidueField y).appTop z))
      (ΓSpecIso_naturality a)
  rw [heval]
  exact hw

end AlgebraicGeometry.Scheme
