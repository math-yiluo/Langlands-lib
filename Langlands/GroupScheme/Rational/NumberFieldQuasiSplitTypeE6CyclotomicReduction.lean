import Langlands.Global.Arithmetic.CyclotomicPrimePowerGalois
import Langlands.GroupScheme.Rational.NumberFieldAbelianCoverVanishing
import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexQuasiSplitTypeE6
import Langlands.GroupScheme.Rational.NumberFieldTorusCyclotomicSplitting
import Langlands.GroupScheme.Rational.NumberFieldTypeE6LeviReduction
import Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReductionProof
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormBaseChange
import Langlands.GroupScheme.Rational.SteinbergAssembly

/-! # Cyclotomic reduction for quasi-split type E6 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Cyclotomic IsMulCommutative

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 1400
set_option maxHeartbeats 1600000

private theorem prime_dvd_pow_two_mul_pow_three {q a b : ℕ} (hq : q.Prime)
    (h : q ∣ 2 ^ a * 3 ^ b) : q = 2 ∨ q = 3 := by
  rcases hq.dvd_mul.mp h with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h3))

private theorem prime_dvd_totient_two_three {N q : ℕ} (hN : 0 < N)
    (hSupport : ∀ p : ℕ, p.Prime → p ∣ N → p = 2 ∨ p = 3)
    (hq : q.Prime) (h : q ∣ N.totient) : q = 2 ∨ q = 3 := by
  rw [Nat.totient_eq_prod_factorization hN.ne', Nat.prod_factorization_eq_prod_primeFactors] at h
  obtain ⟨p, hp, hd⟩ := (hq.prime.dvd_finsetProd_iff _).mp h
  have hp' := hSupport p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  rcases hq.dvd_mul.mp hd with hn | hn
  · exact (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors hp)).mp
      (hq.dvd_of_dvd_pow hn) ▸ hp'
  · rcases hp' with rfl | rfl
    · exact (hq.not_dvd_one hn).elim
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hn)

private def eligible (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) : Prop :=
  IsTotallyComplex F ∧ IsQuasiSplit G ∧ IsAbsolutelyAlmostSimple G ∧
  ∃ hsc : IsSimplyConnected G,
    letI := hsc.isSemisimple.isConnectedReductive.isAffineHom
    letI := hsc.isSemisimple.isConnectedReductive.smooth
    ∃ (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
      ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)

private theorem eligible_baseChange
    (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (h : eligible F G) : eligible E ((GroupScheme.baseChange (algebraBaseMap F E)).obj G) := by
  obtain ⟨hF, hqs, habs, hsc, d, e, hcart⟩ := h
  let : IsTotallyComplex F := hF
  let : Smooth G.X.hom := hsc.isSemisimple.isConnectedReductive.smooth
  let G_E := (GroupScheme.baseChange (algebraBaseMap F E)).obj G
  have hscE : IsSimplyConnected G_E := isSimplyConnectedFieldExtension F E G hsc
  let : Smooth G_E.X.hom := hscE.isSemisimple.isConnectedReductive.smooth
  let : IsAffineHom G_E.X.hom := hscE.isSemisimple.isConnectedReductive.isAffineHom
  let φ : E →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let : Algebra E (SeparableClosure F) := φ.toRingHom.toAlgebra
  let : IsScalarTower F E (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  let : Algebra E (SeparableClosure E) := (separableClosure E (AlgebraicClosure E)).algebra
  let : IsSepClosure E (SeparableClosure F) :=
    ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable F E (SeparableClosure F)⟩
  let r := IsSepClosure.equiv E (SeparableClosure E) (SeparableClosure F)
  let : Algebra (SeparableClosure E) (SeparableClosure F) := r.toRingHom.toAlgebra
  let : IsScalarTower E (SeparableClosure E) (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq (fun x => (r.commutes x).symm)
  let Q := GaloisPinningData.rootDatumScalarExtension (E := E) d.pinning
  have hc : algebraBaseMap (SeparableClosure E) (SeparableClosure F) ≫
      algebraBaseMap E (SeparableClosure E) = algebraBaseMap E (SeparableClosure F) := by
    simp only [algebraBaseMap, ← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq E (SeparableClosure E) (SeparableClosure F)).symm
  have hT : IsTorus Q.pinning.torus.toGrp :=
    ⟨SeparableClosure F, inferInstance, inferInstance, Q.pinning.isSplitTorus⟩
  have hsplit := GaloisPinningData.isSplitTorus_separableClosure Q.pinning.torus hT
  obtain ⟨q, ε, hεb, _⟩ := StarActionFiniteStage.exists_stage Q.pinning hc hsplit
  obtain ⟨dE⟩ := titsIndexExistence E G_E hscE.isSemisimple
  obtain ⟨_, _, ζ, _, _, hζb, _⟩ :=
    StarActionIndependence.starActionIndependence E (SeparableClosure E) G_E q dE.pinning
  let f := ζ.comp (ε.symm.comp Q.rootEquiv)
  have hf (a : d.pinning.rootIndex) :
      a ∈ d.pinning.base.support ↔ f.indexEquiv a ∈ dE.pinning.base.support := by
    change a ∈ d.pinning.base.support ↔
      ζ.indexEquiv (ε.indexEquiv.symm (Q.rootEquiv.indexEquiv a)) ∈ dE.pinning.base.support
    have hmid := hεb (ε.indexEquiv.symm (Q.rootEquiv.indexEquiv a))
    simp only [Equiv.apply_symm_apply] at hmid
    exact (Q.base_eq a).trans (hmid.symm.trans (hζb _))
  let v : d.Vertex ≃ dE.Vertex := f.indexEquiv.subtypeEquiv hf
  refine ⟨isTotallyComplex_of_algebra F E, hqs.baseChange_of_algebraicExtension,
    habs.baseChange_of_algebraicExtension, hscE, dE, v.symm.trans e, ?_⟩
  intro a b
  have hv (x y : d.Vertex) : dE.cartan (v x) (v y) = d.cartan x y := f.toHom.pairing
  simpa only [Equiv.apply_symm_apply, Equiv.trans_apply] using
    (hv (v.symm a) (v.symm b)).trans (hcart (v.symm a) (v.symm b))

private theorem isTrivial_baseChangePullback_map_of_isTrivial
    {S S' : Scheme.{u}} {G H : GroupScheme S} {U : Over S}
    (ξ : Cocycle G U) (i : G ⟶ H) (b : S' ⟶ S)
    (h : (ξ.baseChangePullback b).IsTrivial) : ((ξ.map i).baseChangePullback b).IsTrivial := by
  refine (h.map ((GroupScheme.baseChange b).map i)).of_cohomologous
    (Cocycle.cohomologous_of_toFun_eq ?_)
  intro Z a c
  apply (baseChangePointsEquiv b H Z).injective
  change baseChangePointsEquiv b H Z ((ξ.baseChangePullback b).toFun a c ≫
    ((GroupScheme.baseChange b).map i).hom.hom) = _
  rw [baseChangePointsEquiv_comp]
  simp only [Cocycle.baseChangePullback, Cocycle.baseChange_toFun]
  rfl

/-- Quasi-split E6 vanishing from the maximal-torus order bound, cyclotomic
torus splitting and vanishing on covers of degree two or three. -/
def NumberFieldQuasiSplitTypeE6CyclotomicReductionStatement : Prop :=
  TypeE6MaximalTorusCocycleOrderStatement.{u} →
  NumberFieldTorusCocycleCyclotomicSplittingStatement.{u} →
  NumberFieldTotallyComplexQuasiSplitTypeE6PrimeCoverStatement.{u} →
  NumberFieldTotallyComplexQuasiSplitTypeE6VanishingStatement.{u}

open GaloisCocycle in
set_option synthInstance.maxHeartbeats 120000 in
theorem numberFieldQuasiSplitTypeE6CyclotomicReduction :
    NumberFieldQuasiSplitTypeE6CyclotomicReductionStatement.{u} := by
  classical
  intro hOrder hCyclo hPrime F _ _ hF G _ _ d e hsc habs hcart hqs L _ _ _ _ ξ
  let hred := hsc.isSemisimple.isConnectedReductive
  let : Smooth G.X.hom := hred.smooth
  obtain ⟨R⟩ := quasiSplitCocycleTorusReduction F G hsc.isSemisimple hqs L ξ
  let T₀ : CommGroupScheme (Spec (CommRingCat.of F)) := { R.torus with comm := R.isTorus.isCommMonObj }
  let j : T₀.toGrp ⟶ G := R.inclusion
  obtain ⟨T, i, f, hi, hf⟩ := EnvelopeInfiniteReduction.exists_isMaximalTorus_factor G j
    R.isTorus R.isClosedSubgroup
  let τ := R.torusCocycle.map f
  obtain ⟨a, b, hτ⟩ := hOrder F G d e hsc habs hcart T i hi R.carrier τ
  obtain ⟨N, hN, hSupport, hSplit⟩ := hCyclo F T hi.1 R.carrier τ (2 ^ a * 3 ^ b)
    (by positivity) hτ
  let : NeZero N := ⟨hN.ne'⟩
  let E := CyclotomicField N F
  let : FiniteDimensional F E := IsCyclotomicExtension.finiteDimensional {N} F E
  let : IsGalois F E := IsCyclotomicExtension.isGalois {N} F E
  let ζ := IsCyclotomicExtension.zeta_spec N F E
  let c := ζ.autToPow F
  let : IsMulCommutative (E ≃ₐ[F] E) := by
    refine ⟨⟨fun x y => ζ.autToPow_injective F ?_⟩⟩
    change c (x * y) = c (y * x)
    rw [map_mul, map_mul, mul_comm]
  have hdiv (q : ℕ) (hq : q.Prime) (hd : q ∣ Module.finrank F E) : q ∈ ({2, 3} : Set ℕ) := by
    have hd' := hd.trans (Langlands.Global.Arithmetic.CyclotomicPrimePowerGalois.finrank_dvd_totient
      (K := F) (L := E) (m := N))
    have h' := prime_dvd_totient_two_three hN
      (fun p hp hdN => prime_dvd_pow_two_mul_pow_three hp (hSupport p hp hdN)) hq hd'
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h'
  let ξ' := ξ.refine R.refinement
  have hrel : ξ'.Cohomologous (τ.map i) := by
    refine ⟨R.cochain, fun {Z} x y => ?_⟩
    have hm : IsClosedImmersion R.inclusion.hom.hom.left := R.isClosedSubgroup
    let : Mono R.inclusion.hom.hom := Over.mono_of_mono_left _
    change (R.torusCocycle.toFun x y ≫ f.hom.hom) ≫ i.hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
    exact Cocycle.lift_toFun _ R.inclusion R.factorization x y
  let cE := algebraBaseMap F E
  have hE : (ξ'.baseChangePullback cE).IsTrivial :=
    (isTrivial_baseChangePullback_map_of_isTrivial τ i cE (hSplit E _ ζ)).of_cohomologous
      (hrel.symm.baseChange cE _ _)
  obtain ⟨M, φR, φE, hMfin, hMgal⟩ := TypeE6HasseReduction.exists_common_galois F R.carrier E
  let : Algebra R.carrier M := φR.toRingHom.toAlgebra
  let : Algebra E M := φE.toRingHom.toAlgebra
  let : Module E M := Algebra.toModule
  let : Module R.carrier M := Algebra.toModule
  have : IsScalarTower F R.carrier M := IsScalarTower.of_algebraMap_eq (fun x => (φR.commutes x).symm)
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq (fun x => (φE.commutes x).symm)
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : QuasiCompact R.refinement.left := R.quasiCompact_refinement
  let : Flat R.refinement.left := R.flat_refinement
  let : Surjective R.refinement.left := R.surjective_refinement
  apply (ξ.isTrivial_refine_iff R.refinement).mp
  apply Cocycle.isTrivial_of_baseChange_isTrivial_of_kernel M ξ'
    (ξ'.locallyTrivial_of_totallyComplex hF hsc) hE
  intro θ _
  apply numberFieldAbelianCoverVanishing eligible ({2, 3} : Set ℕ) eligible_baseChange ?_ ?_
    F G ⟨hF, hqs, habs, hsc, d, e, hcart⟩ E hdiv θ
  · intro K _ _ H _ hH K' _ _ _ _ z
    obtain ⟨ht, _, _, hs, _⟩ := hH
    exact z.locallyTrivial_of_totallyComplex ht hs
  · intro K _ _ H _ hH K' _ _ _ _ _ hs z
    obtain ⟨ht, hq, ha, hc, dH, eH, hcartH⟩ := hH
    let : Smooth H.X.hom := hc.isSemisimple.isConnectedReductive.smooth
    exact hPrime K ht H dH eH hc ha hcartH hq K' hs z

end Langlands.GroupScheme
