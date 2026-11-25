/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Normalization

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import WeilConjectures.AlgebraicGeometry.Morphisms.FieldTorsorGaloisComponents
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrGaloisComponentsRootCotangent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Nakayama

/-! # The index-one part of the DVR root calculation

## References

* Stacks Project, Tags 09EV, 09EB, 0BRM, 09E7, and 0307
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- Adjoining a group-order root of a DVR uniformizer kills the ramification of a torsor. -/
theorem dvr_root_normalization_maximalIdeal
    (B : CommRingCat.{u}) [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi)
    (G : Type (u + 1)) [Group G] [Finite G]
    (T : GaloisCover G (Spec (CommRingCat.of (FractionRing B))))
    (hn : IsUnit (Nat.card G : B)) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
    let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a := pullback.snd (T.π ≫ j) q
    ∀ (hqc : QuasiCompact a) (hqs : QuasiSeparated a),
    letI := hqc
    letI := hqs
    IsFinite a.fromNormalization →
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)} →
      let C := a.normalization.presheaf.stalk x
      let tau := (a.fromNormalization.stalkMap x).hom
        (AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x)
          (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)))
      IsLocalRing.maximalIdeal C = Ideal.span {tau} := by
  dsimp only
  intro hqc hqs
  let := hqc
  let := hqs
  intro hfinite x hx
  let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
  let a := pullback.snd (T.π ≫ j) q
  let y := a.fromNormalization x
  let C := a.normalization.presheaf.stalk x
  let tau := (a.fromNormalization.stalkMap x).hom
    (StructureSheaf.toStalk A y
      (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)))
  let m := IsLocalRing.maximalIdeal C
  obtain ⟨r, E, hE, aE, hfields, e, he⟩ :=
    field_torsor_galois_components (FractionRing B) G T
  let := hE
  let := aE
  have hcot : m ≤ Ideal.span {tau} ⊔ m * m :=
    dvr_galois_components_root_cotangent B pi hpi (Nat.card G) Nat.card_pos hn
      r E hfields T.P T.π e he hqc hqs x hx
  let := hfinite
  have : IsLocallyNoetherian a.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian a.fromNormalization
  have hle : m ≤ Ideal.span {tau} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m)
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal C))
      (by simpa only [Ideal.smul_eq_mul] using hcot)
  let : Algebra A (N.presheaf.stalk y) := (StructureSheaf.toStalk A y).hom.toAlgebra
  have : IsLocalization.AtPrime (N.presheaf.stalk y) y.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime
      ((AlgebraicGeometry.Spec.structureSheaf A).presheaf.stalk y) y.asIdeal)
  have hbase : IsLocalRing.maximalIdeal (N.presheaf.stalk y) = Ideal.span
      {StructureSheaf.toStalk A y
        (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi))} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (R := A) y.asIdeal
      (N.presheaf.stalk y), hx]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have hmem : tau ∈ m := by
    apply map_nonunit (a.fromNormalization.stalkMap x).hom
    rw [hbase]
    exact Ideal.mem_span_singleton_self _
  change m = Ideal.span {tau}
  exact le_antisymm hle (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem))

end AlgebraicGeometry.Scheme
