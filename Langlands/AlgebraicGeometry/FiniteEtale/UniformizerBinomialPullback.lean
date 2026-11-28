import Langlands.AlgebraicGeometry.FiniteEtale.Definitions
import Langlands.CommutativeAlgebra.DvrUniformizerRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale

/-! # Pullback of a binomial cover at a uniformizer -/

noncomputable section

open Algebra TensorProduct CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

/-- Adjoin a root of the specified binomial, viewed as a morphism of affine schemes. -/
def binomialMorphism {B : Type u} [CommRing B] (b : B) (m : ℕ) :
    Spec (.of (AdjoinRoot (X ^ m - C b))) ⟶ Spec (.of B) := Spec.algebraMap _ _

/-- The binomial cover is finite étale when the degree and the constant term are units. -/
def binomialCover {B : Type u} [CommRing B] (b : B) {m : ℕ}
    (hm : m ≠ 0) (hunit : IsUnit (m : B)) (hb : IsUnit b) : Cover (Spec (.of B)) := by
  have hfin : IsFinite (binomialMorphism b m) := by
    apply (IsFinite.SpecMap_iff _).2
    exact RingHom.finite_algebraMap.mpr (monic_X_pow_sub_C b hm).finite_adjoinRoot
  have het : Etale (binomialMorphism b m) := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).2
    exact RingHom.etale_algebraMap.mpr (AdjoinRoot.etale_X_pow_sub_C hm hunit hb)
  exact cover (binomialMorphism b m)

/-- The binomial of positive degree with uniformizer as constant term is irreducible
in the fraction field of the DVR. -/
theorem irreducible_uniformizerBinomial (W : Type*) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] (L : Type*) [Field L] [Algebra W L] [IsFractionRing W L]
    {π : W} (hπ : Irreducible π) {m : ℕ} (hm : m ≠ 0) :
    Irreducible (X ^ m - C (algebraMap W L π)) := by
  let p : W[X] := X ^ m - C π
  have hp : p.Monic := monic_X_pow_sub_C π hm
  have hdom : IsDomain (AdjoinRoot p) :=
    (Langlands.CommutativeAlgebra.DvrUniformizerRoot.isDiscreteValuationRing_adjoinRoot
      hπ hm).choose
  have hprime : (Ideal.span {p}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hi : Irreducible p := ((Ideal.span_singleton_prime hp.ne_zero).mp hprime).irreducible
  simpa [p, Polynomial.map_sub, Polynomial.map_pow] using
    (hp.irreducible_iff_irreducible_map_fraction_map (K := L)).mp hi

/-- A positive-degree binomial cover remains connected after a field-valued pullback
sending its constant term to a uniformizer of a DVR in that field. -/
def UniformizerBinomialPullbackStatement : Prop :=
  ∀ (B W L : Type u) [CommRing B] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field L] [Algebra W L] [IsFractionRing W L] (θ : B →+* L) (b : B) (π : W),
    θ b = algebraMap W L π → Irreducible π → ∀ m : ℕ, m ≠ 0 →
      ConnectedSpace (pullback (binomialMorphism b m) (Spec.map (CommRingCat.ofHom θ)) : Scheme.{u})

/-- Adjoining a root commutes with base change, and the resulting binomial over the
fraction field is irreducible. -/
theorem uniformizerBinomialPullback : UniformizerBinomialPullbackStatement.{u} := by
  intro B W L _ _ _ _ _ _ _ θ b π hθ hπ m hm
  let : Algebra B L := θ.toAlgebra
  let p : B[X] := X ^ m - C b
  let q := p.map (Algebra.TensorProduct.includeRight : B →ₐ[B] L ⊗[B] B).toRingHom
  let r : L[X] := X ^ m - C (algebraMap W L π)
  let e := Algebra.TensorProduct.rid B L L
  have hqr : q.map e.toRingHom = r := by
    rw [show q = p.map (Algebra.TensorProduct.includeRight : B →ₐ[B] L ⊗[B] B).toRingHom
        from rfl, Polynomial.map_map]
    change (X ^ m - C b).map _ = r
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    change X ^ m - C (e (1 ⊗ₜ[B] b)) = r
    rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]
    exact congrArg (fun z : L ↦ X ^ m - C z) hθ
  let ε : L ⊗[B] AdjoinRoot p ≃ₐ[L] AdjoinRoot r :=
    (AdjoinRoot.tensorAlgEquiv p q rfl).trans
      (AdjoinRoot.mapAlgEquiv e q r (hqr ▸ Associated.refl r))
  have : Fact (Irreducible r) := ⟨irreducible_uniformizerBinomial W L hπ hm⟩
  let i := Scheme.Spec.mapIso ε.toRingEquiv.toCommRingCatIso.op
  let j := pullbackSymmetry (binomialMorphism b m) (Spec.map (CommRingCat.ofHom θ))
  let k := pullbackSpecIso B L (AdjoinRoot p)
  let ePull : pullback (binomialMorphism b m) (Spec.map (CommRingCat.ofHom θ)) ≅
      Spec (.of (AdjoinRoot r)) := j ≪≫ k ≪≫ i.symm
  exact (Scheme.homeoOfIso ePull).connectedSpace_iff.mpr inferInstance

end Langlands.AlgebraicGeometry.FiniteEtale
