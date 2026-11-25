/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian

public import Mathlib.NumberTheory.RamificationInertia.Galois

public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.CartierGenericStalkGaloisModelCore
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Galois models at generic Cartier DVR stalks

## References

* Stacks Project, Tags 0307 and 09EB
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite normalization of a pulled-back torsor over the complement of an integral
Cartier centre has a Galois integral-closure model at a DVR generic stalk. -/
theorem cartier_generic_stalk_galois_model
    {N U P : Scheme.{u}} [IsLocallyNoetherian N]
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (V : N.Opens) (κ : V.toScheme ⟶ U) (p : P ⟶ V.toScheme) [IsFinite p]
    (r : P ⟶ W.P) (hpb : IsPullback r p W.π κ) :
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∀ (hdom : IsDomain (N.presheaf.stalk (j η))),
      letI := hdom
      IsDiscreteValuationRing (N.presheaf.stalk (j η)) →
      ∀ (x : a.normalization), a.fromNormalization x = j η →
        ∃ (S : CommRingCat.{u}) (T : Subgroup G)
          (alg : Algebra (N.presheaf.stalk (j η)) S),
          letI := alg
          ∃ (act : MulSemiringAction T S),
          letI := act
          IsDomain (N.presheaf.stalk (j η)) ∧ IsDomain S ∧
          Module.Finite (N.presheaf.stalk (j η)) S ∧
          Module.Flat (N.presheaf.stalk (j η)) S ∧
          IsGaloisGroup T (N.presheaf.stalk (j η)) S ∧
          ∃ (q₀ : Ideal S), q₀.IsPrime ∧
            (letI := (a.fromNormalization.residueFieldMap x).hom.toAlgebra
             Module.finrank (N.residueField (a.fromNormalization x))
               (a.normalization.residueField x)) = q₀.inertiaDeg (N.presheaf.stalk (j η)) := by
  dsimp only
  intro hetale hfinite D j hD hj hV η hη hdom hdvr x hx
  let := hdom
  let := hdvr
  obtain ⟨S, T, alg, act, hS, hinj, hfiniteS, hfield, q₀, hq₀, e, f, hcomm⟩ :=
    cartier_generic_stalk_galois_model_core (N := N) G W V κ p r hpb
      hetale hfinite D j hD hj hV η hη hdom hdvr x hx
  let := alg
  let := act
  let := hS
  have : Module.IsTorsionFree (N.presheaf.stalk (j η)) S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  let := FractionRing.liftAlgebra (N.presheaf.stalk (j η)) (FractionRing S)
  let := IsFractionRing.mulSemiringAction T S (FractionRing S)
  let := hfiniteS
  let := hfield
  have hgalois : IsGaloisGroup T (N.presheaf.stalk (j η)) S :=
    IsGaloisGroup.of_isFractionRing T (N.presheaf.stalk (j η)) S
      (FractionRing (N.presheaf.stalk (j η))) (FractionRing S)
  have hflat : Module.Flat (N.presheaf.stalk (j η)) S := inferInstance
  let := hq₀
  let := Localization.AtPrime.algebraOfLiesOver
    (q₀.under (N.presheaf.stalk (j η))) q₀
  let := ((p ≫ V.ι).fromNormalization.residueFieldMap x).hom.toAlgebra
  have hfin := Algebra.finrank_eq_of_equiv_equiv e f hcomm
  refine ⟨S, T, alg, act, hdom, hS, hfiniteS, hflat, hgalois, q₀, hq₀, ?_⟩
  rw [Ideal.inertiaDeg_def]
  exact hfin

end AlgebraicGeometry.Scheme
