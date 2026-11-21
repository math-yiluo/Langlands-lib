import Langlands.Algebra.NumberFieldReducedNormLocality
import Langlands.GroupScheme.Rational.CentralSimpleNormOneCocycle
import Langlands.GroupScheme.Rational.SimplyConnectedHasseAlmostSimple
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneProof
import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingGaloisReduction

/-! # Inner type A Hasse injectivity reduces to locality of reduced norms -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CentralSimpleUnits

/-- A finite field cover admits a common coefficient field finite Galois over the
new base, through the two compatible inclusions into a tensor quotient. -/
theorem exists_finiteGalois_over_baseChange
    (F K L : Type u) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [CharZero K] [FiniteDimensional F L] :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra K M)
      (_ : FiniteDimensional K M) (_ : IsGalois K M) (_ : Algebra F M)
      (_ : IsScalarTower F K M) (_ : Algebra L M), IsScalarTower F L M := by
  let D := K ⊗[F] L
  have : Nontrivial D := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F K L
    (algebraMap F K).injective (algebraMap F L).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal D
  let : Field (D ⧸ m) := Ideal.Quotient.field m
  have : FiniteDimensional K D := inferInstanceAs (Module.Finite K (K ⊗[F] L))
  have : FiniteDimensional K (D ⧸ m) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  obtain ⟨M, hfin, hgal, ⟨j⟩⟩ := exists_finite_galois_algHom K (D ⧸ m)
  let : Algebra F M := Algebra.compHom M (algebraMap F K)
  let : IsScalarTower F K M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e : L →ₐ[F] M :=
    (((j.comp (Ideal.Quotient.mkₐ K m))).restrictScalars F).comp
      Algebra.TensorProduct.includeRight
  let : Algebra L M := e.toRingHom.toAlgebra
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  exact ⟨M, inferInstance, inferInstance, hfin, hgal, inferInstance, inferInstance,
    inferInstance, inferInstance⟩

variable {F A L : Type u} [Field F] [NumberField F] [Ring A] [Algebra F A]
  [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A]
  [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

private theorem exists_relative_norm {K : Type u} [Field K] [Algebra F K]
    (ξ : Cocycle (normOne F A) (GaloisCocycle.cover F L))
    (b : (groupScheme F A).affinePoints (CommAlgCat.of F L)) (a : Fˣ)
    (hb : ∀ σ : L ≃ₐ[F] L,
      (normOne F A).affinePointsTarget (normOneι F A) (CommAlgCat.of F L) (GaloisCocycle.value ξ σ) =
        b * (GaloisPoint.conjugate F L (groupScheme F A) σ b)⁻¹)
    (ha : affineReducedNorm (CommAlgCat.of F L) b = Units.map (algebraMap F L) a)
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    Units.map (algebraMap F K).toMonoidHom a ∈ Set.range (reducedNormUnits F A K) := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  obtain ⟨M, _, _, _, _, _, _, _, _⟩ := exists_finiteGalois_over_baseChange F K L
  obtain ⟨r, hr⟩ := exists_affineReducedNorm_of_baseChange_isTrivial M ξ b a hb ha h
  exact ⟨FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (CommAlgCat.of F K) r, hr⟩

/-- Reduced-norm locality implies the Hasse kernel for the actual norm-one group. -/
theorem isTrivial_of_locallyTrivial_of_reducedNormLocality
    (hn : NumberFieldReducedNormLocalityStatement.{u})
    (ξ : Cocycle (normOne F A) (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial) :
    ξ.IsTrivial := by
  obtain ⟨b, a, hb, ha⟩ := exists_cocycle_primitive ξ
  have hl (v : Global.Place F) :
      Units.map (algebraMap F (Global.placeCompletion F v)).toMonoidHom a ∈
        Set.range (reducedNormUnits F A (Global.placeCompletion F v)) := by
    rcases v with v | v
    · exact exists_relative_norm (K := v.Completion) ξ b a hb ha (hξ (.inl v))
    · exact exists_relative_norm (K := v.adicCompletion F) ξ b a hb ha (hξ (.inr v))
  obtain ⟨r, hr⟩ := hn F A a hl
  let E := FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (CommAlgCat.of F F)
  have hE : affineReducedNorm (CommAlgCat.of F F) (E.symm r) = a := by
    change reducedNormUnits F A F (E (E.symm r)) = a
    rw [E.apply_symm_apply, hr]
  apply isTrivial_of_primitive_norm ξ b (E.symm r) hb
  rw [hE]
  exact ha

end CentralSimpleUnits

/-- The kernel of localization for simply connected absolutely almost-simple groups
whose Tits index has inner type A. -/
def NumberFieldInnerTypeASimplyConnectedGaloisHasseKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → d.HasInnerTypeA n →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- Inner type A reduces to the local-to-global principle for reduced norms. -/
theorem numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality
    (hn : NumberFieldReducedNormLocalityStatement.{u}) :
    NumberFieldInnerTypeASimplyConnectedGaloisHasseKernelStatement.{u} := by
  intro F _ _ G _ _ d n hG hs hd L _ _ _ _ ξ hξ
  obtain ⟨A, _, _, _, _, _, _, ⟨e⟩⟩ := innerTypeANormOne F G d n hG hs hd
  have ht := CentralSimpleUnits.isTrivial_of_locallyTrivial_of_reducedNormLocality hn
    (ξ.map e.hom) (hξ.map e.hom)
  obtain ⟨f, hf⟩ := ht.map e.inv
  refine ⟨f, fun a b => ?_⟩
  have key := hf a b
  change (ξ.toFun a b ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = _ at key
  rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id] at key
  exact key

end Langlands.GroupScheme
