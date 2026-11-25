/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.KrullDimension.LocalRing
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.RingTheory.LocalDomainDimOnePrincipalLocalization

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The affine-local function-field square is a pullback of the diagonal, without
assuming separatedness.
Source: Stacks Project, Varieties Lemma 09NB, first paragraph of the proof
(blueprint: lem-sc-affine-local-function-field-diagonal-pullback).
Proof: Put A = Γ(X,U), B = O_{X,x}, and K = k(X). The stalk is a local domain
with fraction field K. A one-dimensional local domain B has just the zero prime
and its maximal ideal: a nonzero prime strictly below the maximal ideal would give
a chain of length two. Since x is outside U and the generic point is in every
nonempty open, the inverse image of U is precisely the zero prime. Choose a nonzero
element t of the maximal ideal (B cannot be a field since its dimension is one).
For every nonzero a in B, t lies in the radical of (a), so a divides a power of t.
The localization criterion therefore makes K a localization of B away from t,
and Spec K → Spec B is an open immersion. Its range is the zero prime, exactly
the inverse image of U: the closed point maps to x, while the unique point of
Spec K maps to the generic point. The open-immersion pullback criterion shows
that Spec K, with the germ and stalk-specialization maps, is Spec A ×_X Spec B.
The product Spec A × Spec B is
Spec (A ⊗[ℤ] B), since this tensor product is the coproduct of commutative rings.
Under this identification the map from Spec K is the spectrum of the tensor lift:
its compositions with the two projections are the germ map and the stalk map.
Finally the square from any fibre product Y ×_X Z to Y × Z and the diagonal
X → X × X is cartesian, by the universal properties of products and pullbacks.
These identifications give exactly the displayed square. No separatedness is
used in this calculation; it is the separate closedness step in the parent proof. -/
theorem Scheme.isPullback_affine_local_functionField_diagonal
    (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (x : X) (hx : x ∉ U)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    let A : Type u := Γ(X, U)
    let B : Type u := X.presheaf.stalk x
    let K : Type u := X.functionField
    let φ : TensorProduct ℤ A B →ₐ[ℤ] K :=
      Algebra.TensorProduct.lift
        (X.germToFunctionField U).hom.toIntAlgHom
        (algebraMap B K).toIntAlgHom
        (fun _ _ => Commute.all _ _)
    IsPullback (X.fromSpecStalk (genericPoint X))
      (Spec.map (CommRingCat.ofHom φ.toRingHom))
      (prod.lift (𝟙 X) (𝟙 X))
      (prod.lift
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct ℤ A B)) ≫
          hU.fromSpec)
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight.toRingHom : B →+* TensorProduct ℤ A B)) ≫
          X.fromSpecStalk x)) := by
  dsimp only
  let B := X.presheaf.stalk x
  let K := X.functionField
  let g := Spec.map (X.germToFunctionField U)
  let b := Spec.map (CommRingCat.ofHom (algebraMap B K))
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hg : g ≫ hU.fromSpec = X.fromSpecStalk (genericPoint X) :=
    hU.fromSpecStalk_eq_fromSpecStalk hη
  have hb : b ≫ X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)
  have hnot : ¬ IsField B :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hdim).1
  obtain ⟨t, ht, ht0⟩ : ∃ t : B, t ∈ IsLocalRing.maximalIdeal B ∧ t ≠ 0 := by
    have hm : IsLocalRing.maximalIdeal B ≠ ⊥ :=
      fun h => hnot (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    exact Submodule.exists_mem_ne_zero_of_ne_bot hm
  have : IsLocalization.Away t K :=
    (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers t)
      (S := K) (nonZeroDivisors B)
      (powers_le_nonZeroDivisors_of_noZeroDivisors ht0) (fun a ha => by
        have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha
        have hr := (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hdim).2 a ha0 ht
        obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hr
        exact ⟨t ^ n, ⟨n, rfl⟩, Ideal.mem_span_singleton.mp hn⟩)).mpr inferInstance
  have : IsOpenImmersion b := IsOpenImmersion.of_isLocalization t
  have hgeom : IsPullback g b hU.fromSpec (X.fromSpecStalk x) := by
    apply IsOpenImmersion.isPullback _ _ _ _ (hb.trans hg.symm)
    apply TopologicalSpace.Opens.ext
    apply Set.ext
    intro p
    change X.fromSpecStalk x p ∈ hU.fromSpec.opensRange ↔ p ∈ Set.range b
    rw [hU.opensRange_fromSpec]
    constructor
    · intro hp
      have hpbot : p.asIdeal = ⊥ := by
        by_contra hne
        have hmax : p.asIdeal.IsMaximal :=
          Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
            (Ring.krullDimLE_iff.mpr hdim.le) p.asIdeal hne p.isPrime
        have heq : p = IsLocalRing.closedPoint B :=
          PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
        rw [heq] at hp
        change X.fromSpecStalk x
          (IsLocalRing.closedPoint (X.presheaf.stalk x)) ∈ U at hp
        rw [Scheme.fromSpecStalk_closedPoint] at hp
        exact hx hp
      refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap B K) ⊥ = p.asIdeal
      rw [hpbot]
      change RingHom.ker (algebraMap B K) = ⊥
      exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective B K)
    · rintro ⟨q, rfl⟩
      have heq : X.fromSpecStalk x (b q) = genericPoint X := by
        change (b ≫ X.fromSpecStalk x) q = genericPoint X
        rw [hb]
        have hq : q = IsLocalRing.closedPoint
          (X.presheaf.stalk (genericPoint X)) := Subsingleton.elim _ _
        rw [hq]
        exact Scheme.fromSpecStalk_closedPoint
      rw [heq]
      exact hη
  let A := Γ(X, U)
  let T := CommRingCat.of (TensorProduct ℤ A B)
  let a : Spec T ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
  let c : Spec T ⟶ Spec B :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)
  have hprod : IsLimit (BinaryFan.mk a c) :=
    BinaryFan.isLimitMapConeEquiv (F := Scheme.Spec)
      (isLimitOfPreserves Scheme.Spec
        (BinaryCofan.IsColimit.op (CommRingCat.coproductCoconeIsColimit A B)))
  let φ : TensorProduct ℤ A B →ₐ[ℤ] K :=
    Algebra.TensorProduct.lift (X.germToFunctionField U).hom.toIntAlgHom
      (algebraMap B K).toIntAlgHom (fun _ _ => Commute.all _ _)
  let d := Spec.map (CommRingCat.ofHom φ.toRingHom)
  have hda : d ≫ a = g := by
    dsimp [d, a, g]
    rw [← Spec.map_comp]
    congr 1
    ext z
    simp [φ]
    rfl
  have hdc : d ≫ c = b := by
    dsimp [d, c, b]
    rw [← Spec.map_comp]
    congr 1
    ext z
    change φ (1 ⊗ₜ[ℤ] z) = (algebraMap B K) z
    simp only [φ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  let δ : X ⟶ X ⨯ X := prod.lift (𝟙 X) (𝟙 X)
  let q : Spec T ⟶ X ⨯ X := prod.lift (a ≫ hU.fromSpec) (c ≫ X.fromSpecStalk x)
  change IsPullback (X.fromSpecStalk (genericPoint X)) d δ q
  have comm : X.fromSpecStalk (genericPoint X) ≫ δ = d ≫ q := by
    apply prod.hom_ext
    · simp only [δ, q, Category.assoc, prod.lift_fst, Category.comp_id]
      rw [← Category.assoc, hda, hg]
    · simp only [δ, q, Category.assoc, prod.lift_snd, Category.comp_id]
      rw [← Category.assoc, hdc, hb]
  have hleft (s : PullbackCone δ q) : s.snd ≫ a ≫ hU.fromSpec = s.fst := by
    simpa [δ, q] using (congrArg (fun f => f ≫ prod.fst) s.condition).symm
  have hright (s : PullbackCone δ q) : s.snd ≫ c ≫ X.fromSpecStalk x = s.fst := by
    simpa [δ, q] using (congrArg (fun f => f ≫ prod.snd) s.condition).symm
  let l (s : PullbackCone δ q) :=
    hgeom.lift (s.snd ≫ a) (s.snd ≫ c)
      (by simpa only [Category.assoc] using (hleft s).trans (hright s).symm)
  have hla (s : PullbackCone δ q) : l s ≫ g = s.snd ≫ a := hgeom.lift_fst _ _ _
  have hlc (s : PullbackCone δ q) : l s ≫ b = s.snd ≫ c := hgeom.lift_snd _ _ _
  refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm l ?_ ?_ ?_⟩⟩
  · intro s
    rw [← hg, ← Category.assoc, hla, Category.assoc, hleft]
  · intro s
    apply BinaryFan.IsLimit.hom_ext hprod
    · simpa only [BinaryFan.mk_fst, Category.assoc, hda] using hla s
    · simpa only [BinaryFan.mk_snd, Category.assoc, hdc] using hlc s
  · intro s m hm hn
    apply hgeom.hom_ext
    · calc
        m ≫ g = (m ≫ d) ≫ a := by rw [Category.assoc, hda]
        _ = s.snd ≫ a := by rw [hn]
        _ = l s ≫ g := (hla s).symm
    · calc
        m ≫ b = (m ≫ d) ≫ c := by rw [Category.assoc, hdc]
        _ = s.snd ≫ c := by rw [hn]
        _ = l s ≫ b := (hlc s).symm

end AlgebraicGeometry
