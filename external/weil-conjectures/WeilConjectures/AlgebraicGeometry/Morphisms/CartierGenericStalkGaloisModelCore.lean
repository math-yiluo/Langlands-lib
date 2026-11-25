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
import WeilConjectures.AlgebraicGeometry.Morphisms.CartierStalkNormalizationProduct
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkProductResidueComparison

/-! # Geometric factor and residue square at a Cartier DVR stalk

## References

* Stacks Project, Tags 0307 and 09EB
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Geometric local model with compatible residue-field isomorphisms. -/
theorem cartier_generic_stalk_galois_model_core
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
          ∃ (hS : IsDomain S),
          letI := hS
          ∃ (hinj : Function.Injective (algebraMap (N.presheaf.stalk (j η)) S)),
          letI : Module.IsTorsionFree (N.presheaf.stalk (j η)) S :=
            Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
          letI := FractionRing.liftAlgebra (N.presheaf.stalk (j η)) (FractionRing S)
          letI := IsFractionRing.mulSemiringAction T S (FractionRing S)
          Module.Finite (N.presheaf.stalk (j η)) S ∧
          IsGaloisGroup T (FractionRing (N.presheaf.stalk (j η))) (FractionRing S) ∧
          ∃ (q₀ : Ideal S) (hq₀ : q₀.IsPrime),
            letI := hq₀
            letI := Localization.AtPrime.algebraOfLiesOver
              (q₀.under (N.presheaf.stalk (j η))) q₀
            letI := (a.fromNormalization.residueFieldMap x).hom.toAlgebra
            ∃ (e : N.residueField (a.fromNormalization x) ≃+*
                (q₀.under (N.presheaf.stalk (j η))).ResidueField)
              (f : a.normalization.residueField x ≃+* q₀.ResidueField),
              (algebraMap (q₀.under (N.presheaf.stalk (j η))).ResidueField
                q₀.ResidueField).comp e.toRingHom =
                f.toRingHom.comp (algebraMap (N.residueField (a.fromNormalization x))
                  (a.normalization.residueField x)) := by
  dsimp only
  intro hetale hfinite D j hD hj hV η hη hdom hdvr x hx
  let := hdom
  let := hdvr
  let R := N.presheaf.stalk (j η)
  obtain ⟨n, E, hE, aE, T, act, hg, hf, c, hc⟩ :=
    cartier_stalk_normalization_product (N := N) G W V κ p r hpb
      hetale hfinite D j hD hj hV η hη hdom hdvr
  let := hE
  let := aE
  let (i : Fin n) : Algebra R (E i) :=
    ((algebraMap (FractionRing R) (E i)).comp
      (algebraMap R (FractionRing R))).toAlgebra
  let S (i : Fin n) : CommRingCat.{u} := CommRingCat.of (integralClosure R (E i))
  obtain ⟨i, q, hq, e, f, hcomm⟩ := stalk_product_residue_comparison
    (p ≫ V.ι).fromNormalization (j η) (Fin n) S (fun i ↦ inferInstance) c hc x hx
  let := act
  let : IsGaloisGroup (T i) (FractionRing R) (E i) := hg i
  let : IsScalarTower R (FractionRing R) (E i) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : SMulCommClass (T i) R (E i) := ⟨fun g r z ↦ by
    change g • (algebraMap (FractionRing R) (E i) (algebraMap R (FractionRing R) r) * z) =
      algebraMap (FractionRing R) (E i) (algebraMap R (FractionRing R) r) * (g • z)
    rw [smul_mul', smul_algebraMap]⟩
  let : MulSemiringAction (T i) (S i) :=
    inferInstanceAs (MulSemiringAction (T i) (integralClosure R (E i)))
  have hS : IsDomain (S i) := inferInstanceAs (IsDomain (integralClosure R (E i)))
  let := hS
  have hinj : Function.Injective (algebraMap R (S i)) := by
    intro r t h
    have h' := congrArg (algebraMap (S i) (E i)) h
    exact (IsFractionRing.injective R (FractionRing R))
      ((algebraMap (FractionRing R) (E i)).injective h')
  let : Module.IsTorsionFree R (S i) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  let : FiniteDimensional (FractionRing R) (E i) :=
    IsGaloisGroup.finiteDimensional (T i) (FractionRing R) (E i)
  let : IsFractionRing (S i) (E i) :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing R) (E i)
  have hring : IsGaloisGroup (T i) R (S i) :=
    IsGaloisGroup.of_isFractionRing (T i) R (S i) (FractionRing R) (E i)
  let := hring
  let := FractionRing.liftAlgebra R (FractionRing (S i))
  let := IsFractionRing.mulSemiringAction (T i) (S i) (FractionRing (S i))
  have hfield : IsGaloisGroup (T i) (FractionRing R) (FractionRing (S i)) :=
    IsGaloisGroup.to_isFractionRing (T i) R (S i) _ _
  exact ⟨S i, T i, inferInstance, inferInstance, hS, hinj, hf i, hfield,
    q, hq, e, f, hcomm⟩
end AlgebraicGeometry.Scheme
