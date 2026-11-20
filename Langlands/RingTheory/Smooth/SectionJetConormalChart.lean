import Langlands.RingTheory.Smooth.SectionJetConormalBaseChange
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.LocalRing.Module

/-! # Basic open charts of conormal generators -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Algebra.SectionJet

open Langlands.GroupScheme.CoordinateWeights
open _root_.TensorProduct

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  (ε : A →ₐ[R] R)

/-- The residue-field conormal dimension pulls back without a flatness hypothesis. -/
theorem finrank_residue_cotangent_baseChange (B : Type w) [CommRing B] [Algebra R B]
    (q : PrimeSpectrum B) :
    let p := q.comap (algebraMap R B)
    Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.Fiber (RingHom.ker (baseChangeAugmentation ε B)).Cotangent) =
    Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (RingHom.ker ε).Cotangent) := by
  dsimp only
  let p := q.comap (algebraMap R B)
  let κp := p.asIdeal.ResidueField
  let κq := q.asIdeal.ResidueField
  let M := (RingHom.ker ε).Cotangent
  let M' := (RingHom.ker (baseChangeAugmentation ε B)).Cotangent
  let f : κp →+* κq := Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R B) rfl
  let : Algebra κp κq := f.toAlgebra
  let : IsScalarTower R κp κq := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R κq r = f (algebraMap R κp r)
    rw [IsScalarTower.algebraMap_apply R B κq]
    exact (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal (algebraMap R B) rfl r).symm
  let e : κq ⊗[B] M' ≃ₗ[κq] κq ⊗[κp] (κp ⊗[R] M) :=
    AlgebraTensorModule.congr (.refl κq κq) (baseChangeConormalEquiv ε B).symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange R B κq κq M ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R κp κq κq M).symm
  change Module.finrank κq (κq ⊗[B] M') = Module.finrank κp (κp ⊗[R] M)
  rw [e.finrank_eq, Module.finrank_baseChange]

private theorem exists_localized_spanning_map {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : PrimeSpectrum R) (r : ℕ)
    (hr : Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) = r) :
    ∃ (a : R) (_ : a ∉ p.asIdeal) (φ : (Fin r →₀ R) →ₗ[R] M),
      Function.Surjective (LocalizedModule.map (Submonoid.powers a) φ) := by
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule.AtPrime p.asIdeal M
  let κp := p.asIdeal.ResidueField
  let : Module.Finite Rₚ Mₚ := inferInstance
  let e : κp ⊗[Rₚ] Mₚ ≃ₗ[κp] κp ⊗[R] M :=
    AlgebraTensorModule.congr (.refl κp κp) (LocalizedModule.equivTensorProduct _ M) ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange R Rₚ κp κp M
  let b : Module.Basis (Fin r) κp (κp ⊗[Rₚ] Mₚ) :=
    Module.finBasisOfFinrankEq κp _ (e.finrank_eq.trans hr)
  obtain ⟨v, hv⟩ := (TensorProduct.mk_surjective Rₚ Mₚ κp Ideal.Quotient.mk_surjective).comp_left b
  let g : (Fin r →₀ Rₚ) →ₗ[Rₚ] Mₚ := Finsupp.linearCombination Rₚ v
  have hg : Function.Surjective (g.restrictScalars R) := by
    change Function.Surjective g
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis v b (congr_fun hv)
  let i : (Fin r →₀ R) →ₗ[R] Fin r →₀ Rₚ := Finsupp.mapRange.linearMap (Algebra.linearMap R Rₚ)
  let j := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M
  obtain ⟨φ, -, -, hφ⟩ := Module.exists_localizedMap_surjective_of_surjective p.asIdeal.primeCompl i j hg
  obtain ⟨a, ha, hsurj⟩ := Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective
    p.asIdeal φ (by simpa [LocalizedModule.coe_map_eq i j] using hφ)
  exact ⟨a, ha, φ, hsurj⟩

/-- At a point of residue conormal dimension `r` on any affine test, its image
has a basic neighborhood where `r` lifts from the original augmentation ideal
span the conormal after localization. -/
def SectionJetConormalChartStatement : Prop :=
  ∀ (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [FiniteType R A] (ε : A →ₐ[R] R)
    (q : PrimeSpectrum B) (r : ℕ),
    Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.Fiber (RingHom.ker (baseChangeAugmentation ε B)).Cotangent) = r →
    ∃ (a : R) (_ : algebraMap R B a ∉ q.asIdeal) (z : Fin r → RingHom.ker ε),
      Submodule.span (Localization.Away a) (Set.range fun i =>
        AugmentedAlgebra.classMap (baseChangeAugmentation ε (Localization.Away a))
          ((1 : Localization.Away a) ⊗ₜ[R] (z i : A))) = ⊤

theorem sectionJetConormalChart : SectionJetConormalChartStatement.{u, v, w} := by
  intro R A B _ _ _ _ _ _ ε q r hr
  let M := (RingHom.ker ε).Cotangent
  let : Module.Finite R M := finite_cotangent_of_finiteType ε
  let p := q.comap (algebraMap R B)
  have hp : Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) = r :=
    (finrank_residue_cotangent_baseChange ε B q).symm.trans hr
  obtain ⟨a, ha, φ, hφ⟩ := exists_localized_spanning_map p r hp
  let S := Localization.Away a
  let εS := baseChangeAugmentation ε S
  let N := (RingHom.ker εS).Cotangent
  let s := Submonoid.powers a
  let c : LocalizedModule.Away a M ≃ₗ[S] N :=
    (LocalizedModule.equivTensorProduct s M).trans (baseChangeConormalEquiv ε S)
  let b : Module.Basis (Fin r) S (LocalizedModule.Away a (Fin r →₀ R)) :=
    ((Finsupp.basisSingleOne (R := R) (ι := Fin r)).baseChange S).map
      (LocalizedModule.equivTensorProduct s _).symm
  choose z hz using fun i : Fin r => (RingHom.ker ε).toCotangent_surjective (φ (Finsupp.single i 1))
  let g : LocalizedModule.Away a (Fin r →₀ R) →ₗ[S] N :=
    c.toLinearMap.comp (LocalizedModule.map s φ)
  let f : Fin r → N := fun i => AugmentedAlgebra.classMap εS ((1 : S) ⊗ₜ[R] (z i : A))
  have hf (i : Fin r) : g (b i) = f i := by
    have hb : b i = LocalizedModule.mk (Finsupp.single i (1 : R)) (1 : s) := by
      simp only [b, Module.Basis.map_apply, Module.Basis.baseChange_apply, Finsupp.coe_basisSingleOne]
      exact LocalizedModule.equivTensorProduct_symm_apply_tmul_one s _
    rw [hb]
    change c (LocalizedModule.map s φ (LocalizedModule.mk (Finsupp.single i 1) 1)) = f i
    rw [LocalizedModule.map_mk]
    change baseChangeConormalEquiv ε S (LocalizedModule.equivTensorProduct s M
      (LocalizedModule.mk (φ (Finsupp.single i 1)) 1)) = f i
    rw [LocalizedModule.equivTensorProduct_apply_mk, Localization.mk_one, ← hz i]
    have hclass : (RingHom.ker ε).toCotangent (z i) =
        AugmentedAlgebra.classMap ε (z i : A) := (AugmentedAlgebra.classMap_ideal ε (z i)).symm
    rw [hclass]
    exact baseChangeConormalEquiv_tmul_classMap ε S 1 (z i) (z i).property
  have hg : Function.Surjective g := c.surjective.comp hφ
  have hspan : Submodule.span S (Set.range f) = ⊤ := by
    rw [← show ⇑g ∘ ⇑b = f from funext hf, Set.range_comp, ← Submodule.map_span, b.span_eq,
      Submodule.map_top, LinearMap.range_eq_top.mpr hg]
  exact ⟨a, ha, z, hspan⟩

end Algebra.SectionJet
