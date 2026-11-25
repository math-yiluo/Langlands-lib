/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover.Translation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.ArtinSchreier
import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.Mathlib.Algebra.CharP.Algebra

/-! # Geometric points of the Artin–Schreier cover

Over an algebraically closed field every geometric point of the base lifts to the
Artin–Schreier cover, and any two lifts differ by a unique translation. In particular the
cover is surjective.
Source: blueprint, lemma-artin-schreier-character-sheaf, step (4);
proposition-p-torsion-smooth-proper-curve--2.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

noncomputable section

namespace AlgebraicGeometry

variable {p : ℕ} {S : Scheme.{u}} {f : Γ(S, ⊤)} {P : Polynomial Γ(S, ⊤)}

/-- A morphism into the Artin–Schreier cover pulls back the coordinate to a solution of
`t ^ p - t = f`. -/
lemma appTop_adjoinRootCoverRoot_pow_sub (hP : P = X ^ p - X - C f) {Z : Scheme.{u}}
    (s : Z ⟶ (adjoinRootCover S P).left) :
    s.appTop (adjoinRootCoverRoot S P) ^ p - s.appTop (adjoinRootCoverRoot S P) =
      (s ≫ (adjoinRootCover S P).hom).appTop f := by
  have h := eval₂_appTop_adjoinRootCoverRoot s
  rw [eval₂_of_eq_artinSchreier hP] at h
  exact sub_eq_zero.mp h

variable [Fact p.Prime]

/-- **Geometric points of the Artin–Schreier cover.** Over an algebraically closed field,
every geometric point of `S` lifts to the cover, and two lifts differ by a unique
translation. -/
theorem artinSchreier_geometricPoints (hP : P = X ^ p - X - C f)
    (hchar : (p : Γ(S, ⊤)) = 0) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ S) :
    Nonempty {s : Spec (.of Ω) ⟶ (adjoinRootCover S P).left //
        s ≫ (adjoinRootCover S P).hom = x} ∧
      ∀ s t : {s : Spec (.of Ω) ⟶ (adjoinRootCover S P).left //
          s ≫ (adjoinRootCover S P).hom = x},
        ∃! a : ZMod p, t.val = s.val ≫ (artinSchreierAction hP hchar
          (Multiplicative.ofAdd a)).asIso.hom.left := by
  let e : Γ(Spec (.of Ω), ⊤) ≃+* Ω := (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv
  have : CharP Ω p :=
    CharP.of_ringHom_of_prime (e.toRingHom.comp x.appTop.hom) (Fact.out : p.Prime) hchar
  obtain ⟨hsurj, hker⟩ := IsAlgClosed.artinSchreier_surjective_and_kernel (k := Ω) p
  refine ⟨?_, fun s t ↦ ?_⟩
  · obtain ⟨r, hr⟩ := hsurj (e (x.appTop f))
    refine ⟨⟨adjoinRootCoverLift x (e.symm r) ?_, adjoinRootCoverLift_hom _ _ _⟩⟩
    have hr' : r ^ p - r = e (x.appTop f) := hr
    rw [eval₂_of_eq_artinSchreier hP, ← map_pow, ← map_sub, hr', RingEquiv.symm_apply_apply,
      sub_self]
  · have hs := appTop_adjoinRootCoverRoot_pow_sub hP s.val
    have ht := appTop_adjoinRootCoverRoot_pow_sub hP t.val
    rw [s.prop] at hs
    rw [t.prop] at ht
    generalize hu : s.val.appTop (adjoinRootCoverRoot S P) = u at hs
    generalize hv : t.val.appTop (adjoinRootCoverRoot S P) = v at ht
    have hd : (e v - e u) ^ p - (e v - e u) = 0 := by
      have h := FiniteField.sub_pow_card_eq_of_pow_card_sub_eq (ZMod.castHom (dvd_refl p) Ω)
        (x := e u) (y := e v) (by
          rw [ZMod.card, ← map_pow e u, ← map_pow e v, ← map_sub e, ← map_sub e, hs, ht])
      rw [ZMod.card] at h
      rw [h, sub_self]
    have hd' : e v - e u ∈ {x : Ω | x ^ p - x = 0} := hd
    rw [hker] at hd'
    obtain ⟨a, ha⟩ := hd'
    have key (b : ZMod p) : t.val = s.val ≫ (artinSchreierAction hP hchar
        (Multiplicative.ofAdd b)).asIso.hom.left ↔ ZMod.castHom (dvd_refl p) Ω b = e v - e u := by
      rw [artinSchreierAction_hom_left, ZMod.castHom_apply, ← ZMod.natCast_val]
      constructor
      · intro h
        rw [h, comp_artinSchreierTranslation_appTop_root, hu] at hv
        rw [← hv, map_add, map_natCast]
        ring
      · intro h
        refine adjoinRootCover_hom_ext (by rw [t.prop, Category.assoc,
          artinSchreierTranslation_hom, s.prop]) ?_
        rw [comp_artinSchreierTranslation_appTop_root, hu, hv]
        apply e.injective
        rw [map_add, map_natCast, h]
        ring
    refine ⟨a, (key a).2 ha, fun b hb ↦ ?_⟩
    exact (ZMod.castHom (dvd_refl p) Ω).injective (((key b).1 hb).trans ha.symm)

/-- The Artin–Schreier cover is surjective. -/
theorem surjective_adjoinRootCover_artinSchreier (hP : P = X ^ p - X - C f)
    (hchar : (p : Γ(S, ⊤)) = 0) : Surjective (adjoinRootCover S P).hom := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨⟨s, hs⟩⟩ := (artinSchreier_geometricPoints hP hchar
    (AlgebraicClosure (S.residueField x))
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x)
      (AlgebraicClosure (S.residueField x)))) ≫ S.fromSpecResidueField x)).1
  obtain ⟨q⟩ : Nonempty (Spec (.of (AlgebraicClosure (S.residueField x)))) := inferInstance
  refine ⟨s.base q, ?_⟩
  rw [← Scheme.Hom.comp_apply, hs, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

end AlgebraicGeometry
