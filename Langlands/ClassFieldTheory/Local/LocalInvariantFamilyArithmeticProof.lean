import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyLawsStatement
import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticProof
import Langlands.ClassFieldTheory.Local.UnramifiedInvariantInflationProof

/-! # Arithmetic normalization of the local invariant family

An arithmetic unramified coordinate forces the extension to be unramified,
and the absolute ramification index is invariant under isomorphisms of
p-adic fields. The image of the extension in the algebraic closure is then an
unramified stage, where the descended invariant is the finite unramified
invariant. Inflation along the isomorphism onto the image and the cyclic-class
formula give `1/n` on the class of a uniformizer.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

open IsLocalRing

namespace ArithmeticNormalizationProof

variable {p : ℕ} [Fact p.Prime]

section Invariance

variable {L E : PadicField.{u} p}

/-- The canonical norm is invariant under isomorphisms over `Padic p`. -/
theorem canonicalNorm_algEquiv (σ : L.Carrier ≃ₐ[Padic p] E.Carrier) (x : L.Carrier) :
    E.canonicalNorm (σ x) = L.canonicalNorm x := by
  simp only [PadicField.canonicalNorm, spectralNorm, minpoly.algEquiv_eq]

/-- An isomorphism over `Padic p` maps canonical integers onto canonical integers. -/
theorem integers_map (σ : L.Carrier ≃ₐ[Padic p] E.Carrier) :
    L.canonicalTopologicalData.Integers.map (σ.toRingEquiv : L.Carrier →+* E.Carrier) =
      E.canonicalTopologicalData.Integers := by
  ext y
  rw [Subring.mem_map_equiv,
    ← L.canonicalTopologicalData.canonicalNorm_le_one_iff_mem_integers,
    ← E.canonicalTopologicalData.canonicalNorm_le_one_iff_mem_integers,
    ← canonicalNorm_algEquiv σ]
  simp

/-- The induced isomorphism of canonical integer rings. -/
def integersEquiv (σ : L.Carrier ≃ₐ[Padic p] E.Carrier) :
    L.canonicalTopologicalData.Integers ≃+* E.canonicalTopologicalData.Integers :=
  (σ.toRingEquiv.subringMap (s := L.canonicalTopologicalData.Integers)).trans
    (RingEquiv.subringCongr (integers_map σ))

/-- The absolute ramification index is invariant under isomorphisms over `Padic p`. -/
theorem ramificationIndex_eq_of_algEquiv (σ : L.Carrier ≃ₐ[Padic p] E.Carrier) :
    L.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex := by
  have hcard : L.canonicalTopologicalData.residueCardinality =
      E.canonicalTopologicalData.residueCardinality :=
    Nat.card_congr (ResidueField.mapEquiv (integersEquiv σ)).toEquiv
  have hres : L.canonicalTopologicalData.residueDegree =
      E.canonicalTopologicalData.residueDegree := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    dsimp only
    rw [← L.canonicalTopologicalData.residueCardinality_eq_pow,
      ← E.canonicalTopologicalData.residueCardinality_eq_pow, hcard]
  have h := L.canonicalTopologicalData.ramificationIndex_mul_residueDegree
  rw [hres, σ.toLinearEquiv.finrank_eq,
    ← E.canonicalTopologicalData.ramificationIndex_mul_residueDegree] at h
  exact Nat.eq_of_mul_eq_mul_right E.canonicalTopologicalData.residueDegree_pos h

end Invariance

section Converse

variable (F E : PadicField.{u} p)

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : NormedAlgebra (Padic p) F.Carrier := F.canonicalNormedAlgebra
local instance : IsUltrametricDist F.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
local instance : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier

variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] [IsGalois F.Carrier E.Carrier]

local instance : Finite (ResidueField (LocalGalois.baseIntegers F.Carrier)) :=
  letI := F.canonicalTopologicalData.finite_residueField
  Finite.of_equiv F.canonicalTopologicalData.ResidueField
    (ArithmeticCoordinate.baseResidueEquiv F).symm.toEquiv

local instance :
    Finite (ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier)) :=
  letI := E.canonicalTopologicalData.finite_residueField
  Finite.of_equiv E.canonicalTopologicalData.ResidueField
    (ArithmeticCoordinate.extensionResidueEquiv F E).symm.toEquiv

/-- An injective residue action forces equal absolute ramification indices. -/
theorem ramificationIndex_eq_of_residueHom_injective
    (h : Function.Injective (LocalGalois.residueHom F.Carrier E.Carrier)) :
    F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex := by
  have hbij : Function.Bijective (LocalGalois.residueHom F.Carrier E.Carrier) :=
    ⟨h, LocalGalois.residueHom_surjective F.Carrier E.Carrier⟩
  have hgal : Module.finrank F.Carrier E.Carrier =
      Module.finrank (ResidueField (LocalGalois.baseIntegers F.Carrier))
        (ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier)) := by
    rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
    exact Nat.card_congr (Equiv.ofBijective _ hbij)
  have hcard : E.canonicalTopologicalData.residueCardinality =
      F.canonicalTopologicalData.residueCardinality ^
        Module.finrank F.Carrier E.Carrier := by
    change Nat.card E.canonicalTopologicalData.ResidueField =
      Nat.card F.canonicalTopologicalData.ResidueField ^ _
    rw [← Nat.card_congr (ArithmeticCoordinate.extensionResidueEquiv F E).toEquiv,
      ← Nat.card_congr (ArithmeticCoordinate.baseResidueEquiv F).toEquiv, hgal]
    exact Module.natCard_eq_pow_finrank
  have hdeg : E.canonicalTopologicalData.residueDegree =
      F.canonicalTopologicalData.residueDegree * Module.finrank F.Carrier E.Carrier := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    dsimp only
    rw [← E.canonicalTopologicalData.residueCardinality_eq_pow, hcard,
      F.canonicalTopologicalData.residueCardinality_eq_pow, ← pow_mul]
  have h1 := E.canonicalTopologicalData.ramificationIndex_mul_residueDegree
  rw [hdeg, ← (Module.finrank_mul_finrank (Padic p) F.Carrier E.Carrier),
    ← F.canonicalTopologicalData.ramificationIndex_mul_residueDegree, ← mul_assoc] at h1
  exact (Nat.eq_of_mul_eq_mul_right F.canonicalTopologicalData.residueDegree_pos
    (Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1)).symm

end Converse

section Inflation

variable {K L M : Type u} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Normal K L]

/-- Inflation along an isomorphism is transport along it. -/
theorem relativeInflation_eq_relativeH2Equiv (e : L ≃ₐ[K] M)
    (h : ∀ a : L, algebraMap L M a = e a) (x : relativeCohomology K L 2) :
    relativeInflation K L M 2 x = relativeH2Equiv e x := by
  have hpull : ∀ s : Gal(M/K),
      AlgEquiv.restrictNormalHom L s = relativeAutPullback e s := by
    intro s
    ext a
    change (s.restrictNormal L) a = e.symm (s (e a))
    apply (algebraMap L M).injective
    rw [AlgEquiv.restrictNormal_commutes, h, h, e.apply_symm_apply]
  induction x using groupCohomology.H2_induction_on with | h z =>
  rw [relativeInflation, groupCohomology.H2π_comp_map_apply, relativeH2Equiv_H2π]
  congr 1
  apply groupCohomology.cocycles₂_ext
  intro s t
  rw [relativeCocycleTransport_apply]
  change unitInclusionLinear L M
      (z (AlgEquiv.restrictNormalHom L s, AlgEquiv.restrictNormalHom L t)) = _
  rw [hpull, hpull]
  exact Units.ext (h _)

end Inflation

end ArithmeticNormalizationProof

open AbsoluteInvariantAssembly ArithmeticNormalizationProof Langlands.LocalClassField

/-- The local invariant family gives `1/n` on the cyclic class of a uniformizer
for every arithmetic unramified coordinate. -/
theorem localInvariantFamilyArithmetic : LocalInvariantFamilyArithmeticStatement.{u} := by
  intro hEx p _ F L _ _ _ _ n _ χ hχ a ha
  have hn : n = Module.finrank F.Carrier L := by
    rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr χ.toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  subst hn
  let : Algebra (Padic p) L :=
    ((algebraMap F.Carrier L).comp (algebraMap (Padic p) F.Carrier)).toAlgebra
  let : IsScalarTower (Padic p) F.Carrier L := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) L := FiniteDimensional.trans (Padic p) F.Carrier L
  let L' : PadicField.{u} p := ⟨L⟩
  have hFL : F.canonicalTopologicalData.ramificationIndex =
      L'.canonicalTopologicalData.ramificationIndex :=
    ramificationIndex_eq_of_residueHom_injective F L' hχ.1
  let f := closureEmbedding F.Carrier L
  let e := f.equivFieldRange
  let S₀ : FiniteIntermediateExtension F.Carrier := ⟨f.fieldRange, inferInstance⟩
  let E' : PadicField.{u} p := S₀.asPadicField
  let := E'.algebra
  let : IsScalarTower (Padic p) F.Carrier E'.Carrier := IsScalarTower.of_algebraMap_eq' rfl
  let σ : L'.Carrier ≃ₐ[Padic p] E'.Carrier :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun r => e.commutes _)
  have hFE : F.canonicalTopologicalData.ramificationIndex =
      E'.canonicalTopologicalData.ramificationIndex :=
    hFL.trans (ramificationIndex_eq_of_algEquiv σ)
  let S : Stage F := ⟨S₀, inferInstance, hFE⟩
  let : Algebra L E'.Carrier := e.toRingEquiv.toRingHom.toAlgebra
  let : IsScalarTower F.Carrier L E'.Carrier :=
    IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  have hinf : ∀ x : relativeCohomology F.Carrier L 2,
      relativeInflation F.Carrier L E'.Carrier 2 x = relativeH2Equiv e x :=
    relativeInflation_eq_relativeH2Equiv e (fun _ => rfl)
  have hstage := descendedHom_stage F hEx closureInflationTowerCompatibility
    unramifiedInvariantInflationCompatibility S
  have hcomp := unramifiedInvariantInflationCompatibility p F L' E' hFL hFE χ S.coordinate
    hχ S.coordinate_arithmetic (cyclicClass F.Carrier L χ.toMonoidHom a)
  rw [localInvariantFamily_relative, embeddedRelativeInvariant_apply]
  change descendedHom F hEx closureInflationTowerCompatibility
    unramifiedInvariantInflationCompatibility
      (closureInflation F.Carrier S.field 2 (relativeH2Equiv e _)) = _
  rw [hstage, ← hinf]
  change unramifiedH2Invariant F E' hFE S.coordinate _ = _
  refine hcomp.trans ((UnramifiedInflation.unramifiedH2Invariant_cyclicClass F L'
    cyclicClassNormNormalization hFL χ a).trans ?_)
  rw [ha, Int.cast_one, one_div]
  rfl

end Langlands.ClassFieldTheory.Local
