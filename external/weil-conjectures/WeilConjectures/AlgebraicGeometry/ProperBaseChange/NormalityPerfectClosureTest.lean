/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.ProperBaseChange.NormalAlgebraSeparableScalarExtension
import WeilConjectures.RingTheory.ProperBaseChange.NormalRingFieldExtensionDescent

/-!
# Testing geometric normality over a perfect purely inseparable extension

## References

* Stacks Project, Varieties, Tag 038O, equivalence (2) and (6), and Algebra, Tag 046W, uniqueness of
  the perfect closure
* Stacks Project, Varieties, Tag 038O, (2) iff (6), and Algebra, Tag 046W
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem normal_ring_equiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B)
    (h : ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal B) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  intro q hq
  let p := q.comap e.toRingHom
  let : p.IsPrime := Ideal.comap_isPrime _ q
  obtain ⟨hd, hi⟩ := h p
  let : IsDomain (Localization.AtPrime p) := hd
  let : IsIntegrallyClosed (Localization.AtPrime p) := hi
  let ep := Localization.localRingEquiv p q e rfl
  exact ⟨ep.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv ep⟩

private theorem separable_of_perfect (K M : Type u) [Field K] [Field M]
    [Algebra K M] [PerfectField K] : Algebra.IsSeparableExtension K M := by
  intro F hF
  let : Algebra.EssFiniteType K F := IntermediateField.essFiniteType_iff.mpr hF
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  exact ⟨s, hs, hsep⟩

private theorem normal_tensor_of_perfect
    (k K L A : Type u) [Field k] [Field K] [Field L] [CommRing A]
    [Algebra k K] [Algebra k L] [Algebra k A] [PerfectField K]
    (h : ∀ (p : Ideal (TensorProduct k A K)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal (TensorProduct k A L)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  obtain ⟨M, hM, hkM, i, j, _, _⟩ := Field.exists_common_extension k K L
  let := hM
  let := hkM
  let : Algebra K M := i.toRingHom.toAlgebra
  let : Algebra L M := j.toRingHom.toAlgebra
  let : IsScalarTower k K M := IsScalarTower.of_algHom i
  let : IsScalarTower k L M := IsScalarTower.of_algHom j
  let : Algebra K (TensorProduct k A K) := Algebra.TensorProduct.rightAlgebra
  let eK : TensorProduct K (TensorProduct k A K) M ≃+* TensorProduct k A M :=
    (Algebra.TensorProduct.comm K (TensorProduct k A K) M).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[K] M)
        (Algebra.TensorProduct.commRight k K A).symm).toRingEquiv.trans
          ((Algebra.TensorProduct.cancelBaseChange k K M M A).toRingEquiv.trans
            (Algebra.TensorProduct.comm k M A).toRingEquiv))
  have hMnorm := normal_ring_equiv eK
    (Algebra.isNormal_tensorProduct_of_separableExtension K (TensorProduct k A K) M
      (separable_of_perfect K M) h)
  let : Algebra L (TensorProduct k A L) := Algebra.TensorProduct.rightAlgebra
  let eL : TensorProduct L (TensorProduct k A L) M ≃+* TensorProduct k A M :=
    (Algebra.TensorProduct.comm L (TensorProduct k A L) M).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[L] M)
        (Algebra.TensorProduct.commRight k L A).symm).toRingEquiv.trans
          ((Algebra.TensorProduct.cancelBaseChange k L M M A).toRingEquiv.trans
            (Algebra.TensorProduct.comm k M A).toRingEquiv))
  exact Algebra.normal_ring_of_normal_tensor_field L M (TensorProduct k A L)
    (normal_ring_equiv eL.symm hMnorm)

private theorem normal_stalks_open {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g]
    (h : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x) := by
  intro x
  obtain ⟨hd, hi⟩ := h (g x)
  let : IsDomain (Y.presheaf.stalk (g x)) := hd
  let : IsIntegrallyClosed (Y.presheaf.stalk (g x)) := hi
  let e := (asIso (g.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩

private theorem normal_stalks_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y) :=
  normal_stalks_open e.inv h

private theorem normal_spec_iff (A : Type u) [CommRing A] :
    (∀ x : Spec (CommRingCat.of A),
      IsDomain ((Spec (CommRingCat.of A)).presheaf.stalk x) ∧
        IsIntegrallyClosed ((Spec (CommRingCat.of A)).presheaf.stalk x)) ↔
    ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  constructor
  · intro h p hp
    let x : PrimeSpectrum A := ⟨p, hp⟩
    obtain ⟨hd, hi⟩ := h x
    let : IsDomain ((Spec (CommRingCat.of A)).presheaf.stalk x) := hd
    let : IsIntegrallyClosed ((Spec (CommRingCat.of A)).presheaf.stalk x) := hi
    let e := (Spec.stalkIso (CommRingCat.of A) x).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩
  · intro h x
    obtain ⟨hd, hi⟩ := h x.asIdeal
    let : IsDomain (Localization.AtPrime x.asIdeal) := hd
    let : IsIntegrallyClosed (Localization.AtPrime x.asIdeal) := hi
    let e := (Spec.stalkIso (CommRingCat.of A) x).commRingCatIsoToRingEquiv.symm
    exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩

-- This common-overfield proof uses only perfectness; retain the assigned signature.
set_option linter.unusedVariables false in
/-- A scheme becomes normal over a perfect purely inseparable extension exactly when it
becomes normal over every field extension. Normality means that every stalk is an
integrally closed domain; the scheme need not be integral or nonempty. -/
theorem normal_stalks_perfectClosure_iff
    (k K : Type u) [Field k] [Field K] [Algebra k K] [PerfectField K]
    (hpower : ∀ a : K, ∃ n : ℕ, ∃ b : k, algebraMap k K b = a ^ (ringExpChar k ^ n))
    (T : Scheme.{u}) (f : T ⟶ Spec (CommRingCat.of k)) :
    (∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
      IsDomain ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x) ∧
      IsIntegrallyClosed
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x)) ↔
    ∀ (L : Type u) [Field L] [Algebra k L],
      ∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u}),
        IsDomain ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x) ∧
        IsIntegrallyClosed
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x) := by
  constructor
  · intro hK L _ _ x
    let gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let gL := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let C := T.affineOpenCover.openCover
    let CK := Scheme.Pullback.openCoverOfLeft C f gK
    let CL := Scheme.Pullback.openCoverOfLeft C f gL
    have hchart (i : C.I₀) :
        ∀ y : CL.X i, IsDomain ((CL.X i).presheaf.stalk y) ∧
          IsIntegrallyClosed ((CL.X i).presheaf.stalk y) := by
      let A := T.affineOpenCover.X i
      let a : CommRingCat.of k ⟶ A := Spec.homEquiv (C.f i ≫ f)
      let : Algebra k A := a.hom.toAlgebra
      have ha : Spec.map (CommRingCat.ofHom (algebraMap k A)) = C.f i ≫ f :=
        Spec.homEquiv.symm_apply_apply (C.f i ≫ f)
      have hKi := normal_stalks_open (CK.f i) hK
      have hAK : ∀ (p : Ideal (TensorProduct k A K)) [p.IsPrime],
          IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
        apply (normal_spec_iff (TensorProduct k A K)).mp
        apply normal_stalks_iso (pullbackSpecIso k A K)
        change ∀ y : (pullback (C.f i ≫ f) gK : Scheme.{u}),
          IsDomain ((pullback (C.f i ≫ f) gK).presheaf.stalk y) ∧
            IsIntegrallyClosed ((pullback (C.f i ≫ f) gK).presheaf.stalk y) at hKi
        rw [← ha] at hKi
        exact hKi
      have hAL := normal_tensor_of_perfect k K L A hAK
      have hLi := normal_stalks_iso (pullbackSpecIso k A L).symm
        ((normal_spec_iff (TensorProduct k A L)).mpr hAL)
      change ∀ y : (pullback (C.f i ≫ f) gL : Scheme.{u}),
        IsDomain ((pullback (C.f i ≫ f) gL).presheaf.stalk y) ∧
          IsIntegrallyClosed ((pullback (C.f i ≫ f) gL).presheaf.stalk y)
      rw [← ha]
      exact hLi
    obtain ⟨i, y, hy⟩ := CL.exists_eq x
    obtain ⟨hd, hi⟩ := hchart i y
    let : IsDomain ((CL.X i).presheaf.stalk y) := hd
    let : IsIntegrallyClosed ((CL.X i).presheaf.stalk y) := hi
    let e := (asIso ((CL.f i).stalkMap y)).commRingCatIsoToRingEquiv
    have hout : IsDomain ((pullback f gL).presheaf.stalk ((CL.f i) y)) ∧
        IsIntegrallyClosed ((pullback f gL).presheaf.stalk ((CL.f i) y)) :=
      ⟨e.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e.symm⟩
    change (CL.f i) y = x at hy
    rw [hy] at hout
    exact hout
  · intro h
    exact h K

end AlgebraicGeometry
