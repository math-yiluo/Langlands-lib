/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictHenselizationResidueSeparableModel

/-! # Separability for compatible strict-henselization residues

Source: Stacks Project, Tags 04HX and 095T.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry
open Scheme Etale

/- The formerly arbitrary algebra structure must agree with the specified geometric
residue embedding. Without hAlgebra the statement is false. -/

private theorem residue_factorization_descends
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    (s : S) (q : Spec (.of K) ⟶ S) (b : Spec (.of L) ⟶ Spec (.of K))
    (a : S.residueField s →+* L)
    (h : Spec.map (CommRingCat.ofHom a) ≫ S.fromSpecResidueField s = b ≫ q) :
    ∃ c : S.residueField s →+* K, a = (Spec.preimage b).hom.comp c := by
  let t := SpecToEquivOfField K S q
  have ht : t.1 = s := by
    have hh := congrArg (fun f : Spec (.of L) ⟶ S ↦ f (IsLocalRing.closedPoint L)) h
    change S.fromSpecResidueField s
      (Spec.map (CommRingCat.ofHom a) (IsLocalRing.closedPoint L)) =
        q (b (IsLocalRing.closedPoint L)) at hh
    rw [Scheme.fromSpecResidueField_apply,
      Subsingleton.elim (b (IsLocalRing.closedPoint L)) (IsLocalRing.closedPoint K)] at hh
    exact hh.symm
  let c : S.residueField s ⟶ CommRingCat.of K := (S.residueFieldCongr ht).inv ≫ t.2
  have hc : Spec.map c ≫ S.fromSpecResidueField s = q := by
    dsimp only [c]
    rw [Spec.map_comp, Category.assoc]
    change Spec.map (t.2) ≫ Spec.map (S.residueFieldCongr ht.symm).hom ≫
      S.fromSpecResidueField s = q
    rw [Scheme.residueFieldCongr_fromSpecResidueField]
    exact (SpecToEquivOfField K S).symm_apply_apply q
  refine ⟨c.hom, ?_⟩
  change (CommRingCat.ofHom a).hom = (c ≫ Spec.preimage b).hom
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  apply (cancel_mono (S.fromSpecResidueField s)).1
  rw [Spec.map_comp, Spec.map_preimage, Category.assoc, hc]
  exact h

/-- The residue-field element induced by a compatible strict-henselization
point is separable over the second residue field.  This is the residue-field
comparison step from Stacks Tags 04HX and 095T; it is isolated here so that
the polynomial conclusion can be obtained independently by a minimal-polynomial
argument.

(blueprint: lem-weil-pbc-compatible-strict-henselization-residue-separability)

Proof: identify the first model's residue field as a separable extension of a
base residue field κ(s), preserving its closed-point structural map. This is the
single-model theorem `strictHenselization_residue_separable_model`. Compose the
factorization with ι and ρA. The equations hρA, hι and hρB identify the resulting
point with the second model's closed-point structural map followed by g. A field
point factors uniquely through its image's residue field, so the latter map gives
c : κ(s) → κB whose composite with the embedding ρB agrees with the image of κ(s)
in k'. Regard the map κA → k' as a κ(s)-algebra homomorphism; it preserves
separability. Finally enlarge the base from κ(s) to κB using the scalar tower.
The hypothesis hAlgebra ties that tower to the given geometric embedding. -/
theorem Etale.compatibleStrictHenselization_residue_isSeparable
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ)
    [Algebra (IsLocalRing.ResidueField B) k']
    (hAlgebra : algebraMap (IsLocalRing.ResidueField B) k' = (Spec.preimage ρB).hom) :
    ∀ x : IsLocalRing.ResidueField A,
      IsSeparable (IsLocalRing.ResidueField B)
        ((Spec.preimage (ι ≫ ρA)).hom x) := by
  obtain ⟨s, f, hsep, hf⟩ :=
    strictHenselization_residue_separable_model (ν ≫ ι ≫ σ) eA
  let a := (Spec.preimage (ι ≫ ρA)).hom
  let q := Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫ eB.hom ≫
    strictLocalizationToBase (ν ≫ τ) ≫ g
  have hfac : Spec.map (CommRingCat.ofHom (a.comp f)) ≫ S.fromSpecResidueField s =
      ρB ≫ q := by
    rw [show CommRingCat.ofHom (a.comp f) =
      CommRingCat.ofHom f ≫ Spec.preimage (ι ≫ ρA) from rfl,
      Spec.map_comp, Spec.map_preimage, Category.assoc, hf]
    simpa only [Category.assoc] using
      (congrArg (fun t ↦ ι ≫ t) hρA).trans
        (hι.trans (congrArg (fun t ↦ t ≫ g) hρB.symm))
  obtain ⟨c, hc⟩ := residue_factorization_descends s q ρB (a.comp f) hfac
  let : Algebra (S.residueField s) (IsLocalRing.ResidueField A) := f.toAlgebra
  let : Algebra (S.residueField s) k' := (a.comp f).toAlgebra
  let : Algebra (S.residueField s) (IsLocalRing.ResidueField B) := c.toAlgebra
  have : IsScalarTower (S.residueField s) (IsLocalRing.ResidueField B) k' := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change a (f r) = algebraMap (IsLocalRing.ResidueField B) k' (c r)
    rw [hAlgebra]
    exact DFunLike.congr_fun hc r
  let a' : IsLocalRing.ResidueField A →ₐ[S.residueField s] k' :=
    { a with commutes' := fun _ ↦ rfl }
  intro x
  exact ((hsep x).map a' a.injective).tower_top (IsLocalRing.ResidueField B)

end AlgebraicGeometry
