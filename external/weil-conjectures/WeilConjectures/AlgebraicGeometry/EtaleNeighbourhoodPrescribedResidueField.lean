/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.Separable
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC
import WeilConjectures.Mathlib.RingTheory.Etale.ResidueField

/-!
# Étale neighbourhoods with a prescribed residue field

Source: Stacks Project, More on Morphisms, Lemma 02LF
(blueprint: lem-weil-pbc-etale-neighbourhood-prescribed-residue-field).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite separable extension of the residue field of a scheme point is realized by
an étale neighbourhood, compatibly with the induced residue-field map.
Source: Stacks Project, More on Morphisms, Lemma 02LF
(blueprint: lem-weil-pbc-etale-neighbourhood-prescribed-residue-field).

Proof:
1. Choose an affine open chart `Spec R → S` containing `s`, with corresponding prime `p`
   (`lem-weil-pbc-affine-open-spec-points`). Identify `κ(s)` with `κ(p)` using the open
   immersion's residue-field isomorphism and the affine residue-field identification
   (`lem-weil-pbc-residue-field-point-naturality`,
   `lem-weil-pbc-spec-residue-field-identification`). Call this composite `θ`.
2. Transport the extension `k/κ(s)` along `θ` to an extension `L/κ(p)`. A basis transports,
   so finiteness is preserved. The coefficientwise polynomial isomorphism transports
   minimal polynomials and preserves separability, so the extension remains separable.
3. Apply `lem-weil-pbc-etale-ring-map-prescribed-residue-field` (Stacks 00UD) to obtain an
   étale map `R → R'`, a prime `p'` over `p`, and an isomorphism `λ : κ(p') → L` compatible
   with the structure maps.
4. Set `U = Spec R'`, `u = p'`, and compose `Spec R' → Spec R → S` to obtain `φ`.
   It is étale by `definition-torsion-sheaves--3` and maps `u` to `s` by
   `lem-weil-pbc-spec-map-residue-field-naturality`.
5. Residue-field maps respect composition. The same Spec naturality lemma identifies
   the map for `Spec R' → Spec R` with `κ(p) → κ(p')`. Composing `λ⁻¹` with the inverse
   affine identification for `R'` gives `e : k → κ(u)`. Compatibility of `λ` shows that
   `e` composed with the structure map of `k` equals the residue-field map of `φ`.
-/
theorem Scheme.exists_etale_neighbourhood_prescribed_residueField
    (S : Scheme.{u}) (s : S) (k : Type v) [Field k]
    [Algebra (S.residueField s) k] [FiniteDimensional (S.residueField s) k]
    [Algebra.IsSeparable (S.residueField s) k] :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S), Etale φ ∧
      ∃ (u : U) (h : φ u = s) (e : k ≃+* U.residueField u),
        ∀ a : S.residueField s,
          e (algebraMap (S.residueField s) k a) =
            (φ.residueFieldMap u).hom ((S.residueFieldCongr h).inv.hom a) := by
  classical
  obtain ⟨R, ι, hι, ⟨p, hp⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := S) (U := ⊤) (x := s) trivial
  subst s
  have : IsOpenImmersion ι := hι
  let θ : S.residueField (ι p) ≃+* p.asIdeal.ResidueField :=
    ((asIso (ι.residueFieldMap p)) ≪≫
      Scheme.Spec.residueFieldIso R p).commRingCatIsoToRingEquiv
  let : Algebra p.asIdeal.ResidueField k :=
    ((algebraMap (S.residueField (ι p)) k).comp θ.symm.toRingHom).toAlgebra
  have htransport : (RingEquiv.refl k).toRingHom.comp
      (algebraMap (S.residueField (ι p)) k) =
      (algebraMap p.asIdeal.ResidueField k).comp θ.toRingHom := by
    ext x
    exact congrArg (algebraMap (S.residueField (ι p)) k) (θ.symm_apply_apply x).symm
  have : FiniteDimensional p.asIdeal.ResidueField k :=
    Module.Finite.of_equiv_equiv θ (RingEquiv.refl k) htransport.symm
  have : Algebra.IsSeparable p.asIdeal.ResidueField k :=
    Algebra.IsSeparable.of_equiv_equiv θ (RingEquiv.refl k) htransport.symm
  obtain ⟨A, hA, aA, heA, P, hP, hcomap, e, he⟩ :=
    Algebra.exists_etale_residueField_equiv p.asIdeal k
  let := hA
  let := aA
  let := heA
  let := hP
  let ψ : R ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap R A)
  let f := Spec.map ψ
  let q : Spec (CommRingCat.of A) := ⟨P, hP⟩
  have hfq : f q = p := by
    apply PrimeSpectrum.ext
    exact hcomap.symm
  subst p
  have : Etale f := by
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let ε : k ≃+* (Spec (CommRingCat.of A)).residueField q :=
    e.symm.trans
      (Scheme.Spec.residueFieldIso (CommRingCat.of A) q).commRingCatIsoToRingEquiv.symm
  refine ⟨Spec (CommRingCat.of A), f ≫ ι, inferInstance, q,
    rfl, ε, ?_⟩
  intro a
  apply (Scheme.Spec.residueFieldIso (CommRingCat.of A) q).commRingCatIsoToRingEquiv.injective
  apply e.injective
  have hnat := congrArg (fun m ↦ m.hom ((ι.residueFieldMap (f q)).hom a))
    (Spec.residueFieldMap_residueFieldIso_hom ψ q)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hnat
  change e ((Scheme.Spec.residueFieldIso (CommRingCat.of A) q).hom.hom
    (ε (algebraMap (S.residueField (ι (f q))) k a))) = _
  have hε (b : k) :
      (Scheme.Spec.residueFieldIso (CommRingCat.of A) q).hom.hom (ε b) = e.symm b :=
    (Scheme.Spec.residueFieldIso (CommRingCat.of A) q).commRingCatIsoToRingEquiv.apply_symm_apply
      (e.symm b)
  rw [hε, e.apply_symm_apply]
  rw [Scheme.residueFieldMap_comp]
  change algebraMap (S.residueField (ι (f q))) k a =
    e ((Scheme.Spec.residueFieldIso (CommRingCat.of A) q).hom.hom
      ((f.residueFieldMap q).hom ((ι.residueFieldMap (f q)).hom a)))
  rw [hnat]
  change algebraMap (S.residueField (ι (f q))) k a =
    e (Ideal.ResidueField.map (f q).asIdeal P (algebraMap R A) hcomap (θ a))
  rw [he]
  exact congrArg (algebraMap (S.residueField (ι (f q))) k) (θ.symm_apply_apply a).symm

end AlgebraicGeometry
