/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrGaloisComponentsStalkPrincipal
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrGaloisComponentsRootNotSquare
import WeilConjectures.RingTheory.PrincipalCotangentSpan

/-! # The first-order tame root calculation for Galois field components

## References

* Stacks Project, Tags 09EV, 09EB, 0BRM, 09E7 and 0307
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A root extension spanning all component degrees spans the normalized cotangent ideal. -/
theorem dvr_galois_components_root_cotangent
    (B : CommRingCat.{u}) [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (hn : IsUnit (n : B))
    (r : ℕ) (E : Fin r → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (FractionRing B) (E i)]
    (hE : ∀ i, FiniteDimensional (FractionRing B) (E i) ∧
      IsGalois (FractionRing B) (E i) ∧ Module.finrank (FractionRing B) (E i) ∣ n)
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of (FractionRing B)))
    (e : X ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing B) (E i)))) = p) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
    let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
    let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a := pullback.snd (p ≫ j) q
    ∀ (hqc : QuasiCompact a) (hqs : QuasiSeparated a),
    letI := hqc
    letI := hqs
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)} →
      let C := a.normalization.presheaf.stalk x
      let tau := (a.fromNormalization.stalkMap x).hom
        (StructureSheaf.toStalk A (a.fromNormalization x)
          (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)))
      let m := IsLocalRing.maximalIdeal C
      m ≤ Ideal.span {tau} ⊔ m * m := by
  dsimp
  intro hqc hqs x hx
  have hprincipal := dvr_galois_components_normalization_maximalIdeal_isPrincipal
    B pi hpi n hnpos r E (fun i ↦ ⟨(hE i).1, (hE i).2.1⟩) X p e he hqc hqs x hx
  have hnot := dvr_galois_components_root_not_mem_square
    B pi hpi n hnpos hn r E hE X p e he hqc hqs x hx
  exact (IsLocalRing.maximalIdeal_le_span_of_isPrincipal_of_not_mem_square
    _ hprincipal hnot).trans le_sup_left

end AlgebraicGeometry.Scheme
