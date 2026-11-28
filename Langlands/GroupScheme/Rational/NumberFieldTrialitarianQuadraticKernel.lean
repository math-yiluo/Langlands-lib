import Langlands.GroupScheme.Rational.NumberFieldCocycleComponentReduction
import Langlands.GroupScheme.Rational.NumberFieldCocycleCoverDescent
import Langlands.GroupScheme.Rational.NumberFieldTypeAOneHasseReduction
import Langlands.GroupScheme.Rational.NumberFieldQuadraticOppositeBorelTorusProof
import Langlands.GroupScheme.Rational.TrialitarianOppositeBorelFactorsProof

/-! # Reduction of the trialitarian Hasse kernel to a quadratic cover and rank one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- A locally trivial trialitarian cocycle split by a totally imaginary
quadratic quasi-splitting field is trivial. -/
theorem Cocycle.isTrivial_of_trialitarian_quadratic_quasiSplit
    {F L : Type u} [Field F] [NumberField F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (habs : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ∀ a : d.Vertex, e a ≠ 1 →
      ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a)
    (hnorm : Langlands.CentralSimple.NumberFieldReducedNormLocalityStatement.{u})
    (Q : IntermediateField F (SeparableClosure F)) [FiniteDimensional F Q] [IsGalois F Q]
    [NumberField.IsTotallyComplex Q] (hdeg : Module.finrank F Q = 2)
    (hqs : IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap F Q)).obj G))
    (ξ : Cocycle G (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial)
    (hsplit : (ξ.baseChangePullback (algebraBaseMap F Q)).IsTrivial) : ξ.IsTrivial := by
  let b := algebraBaseMap F Q
  obtain ⟨hb₁, hb₂, hb₃⟩ := fieldExtension_fpqc F Q
  let : Surjective b := hb₁
  let : Flat b := hb₂
  let : QuasiCompact b := hb₃
  obtain ⟨hL₁, hL₂, hL₃⟩ := fieldExtension_fpqc F L
  let : Surjective (GaloisCocycle.cover F L).hom := hL₁
  let : Flat (GaloisCocycle.cover F L).hom := hL₂
  let : QuasiCompact (GaloisCocycle.cover F L).hom := hL₃
  obtain ⟨ν, hν, hνξ⟩ := ξ.exists_locallyTrivial_of_baseChangePullback b hξ hsplit
  change Cocycle G (GaloisCocycle.cover F Q) at ν
  obtain ⟨T, t, ht, hlift⟩ := numberFieldQuadraticOppositeBorelTorus F Q hdeg G hsc.isSemisimple hqs
  obtain ⟨δ, hδν, hδ⟩ := hlift ν (fun w _ => hν (.inl w))
  have hδ : δ.RealLocallyTrivial := hδ
  obtain ⟨a, _, _, A, _, _, _, dA, H, _, _, dH, T₁, T₂, p₁, p₂, i, j, r, s, act,
    _, hscA, habsA, ⟨eA⟩, hscH, habsH, ⟨eH⟩, hscW, hact, hfixed, hprod⟩ :=
    trialitarianOppositeBorelFactors F G d e hsc habs hD hno Q T t ht
  let α := δ.map p₁
  let β := δ.map p₂
  let ξLeaf := β.map r
  let k := r ≫ s
  have hβ : (β.map k).IsTrivial := by
    have hLeaf : ξLeaf.LocallyTrivial := ((hδ.map p₂).map r).locallyTrivial_of_isSimplyConnected hscW
    have hLeafTriv := isTrivial_weilTypeAOne_of_reducedNormLocality hnorm hscA habsA dA eA ξLeaf hLeaf
    obtain ⟨f, hf⟩ := hLeafTriv.map s
    refine ⟨f, fun u v => ?_⟩
    change β.toFun u v ≫ k.hom.hom = _
    rw [show k.hom.hom = r.hom.hom ≫ s.hom.hom from rfl, ← Category.assoc]
    exact hf u v
  apply hνξ
  apply Cocycle.IsTrivial.of_cohomologous hδν
  refine Cocycle.isTrivial_of_component_cocycles i j k hscH act hact hfixed
    (δ.map t) α β
    (fun _ f _ ζ hζ =>
      isTrivial_typeAOneForm_of_reducedNormLocality hnorm hscH habsH dH eH f.toBaseChangeIso ζ hζ)
    (hδ.map p₁) hβ ?_
  intro Z u v
  exact hprod Z (δ.toFun u v)

end Langlands.GroupScheme
