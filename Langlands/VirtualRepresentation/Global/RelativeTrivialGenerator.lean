import Langlands.Automorphic.ConstantSpectralPresentation
import Langlands.VirtualRepresentation.Global.RelativeImages
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers
import Langlands.Weil.Representation.UnitaryProof
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Correspondence.RankOneReciprocityBijection
import Langlands.Representation.Classification.TwoSupercuspidalTopDerivatives

/-! # The trivial relative Weil representation and the actual constant cusp line -/

noncomputable section
open scoped Classical

universe uF uW uP

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.FiniteRepresentation

variable {G : Type uF} [Group G]

/-- The standard positive form on complex scalars makes the lifted trivial line unitary. -/
theorem characterLine_one_isUnitary :
    (characterLine.{uF, uW} (1 : G →* ℂˣ)).IsUnitary := by
  apply isUnitary_of_equiv (characterLineEquiv (1 : G →* ℂˣ))
  refine ⟨InnerProductSpace.toCore, ?_⟩
  intro g x y
  change inner ℂ ((1 : ℂ) * x) ((1 : ℂ) * y) = inner ℂ x y
  simp only [one_mul]

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.RelativeGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality Langlands.Automorphic Langlands.Unramified

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] (c : FundamentalClass.ClassFamily.{uF})

/-- Supplied actual characterized local maps at every finite place above every place.
Existence of this data remains a separate class-field-theoretic obligation. -/
structure RelativeLocalMapFamily where
  reciprocity (v : FinitePlace F) (w : FinitePlacesAbove E v) :
    LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1)
  localMap (v : FinitePlace F) (w : FinitePlacesAbove E v) :
    Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E
  localMap_spec (v : FinitePlace F) (w : FinitePlacesAbove E v) :
    RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 (reciprocity v w) (localMap v w)

/-- The actual continuous trivial line, retaining an independent Weil carrier universe. -/
def trivialWeil : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E) :=
  FiniteRepresentation.characterLine 1

@[simp]
theorem trivialWeil_representation (g : RelativeWeilGroup c F E) :
    (trivialWeil.{uF, uW} F E c).representation g = 1 := by
  ext x
  change (1 : ℂ) • x = x
  exact one_smul ℂ x

theorem trivialWeil_isContinuous :
    (trivialWeil.{uF, uW} F E c).IsContinuous :=
  FiniteRepresentation.characterLine_isContinuous (1 : RelativeWeilGroup c F E →ₜ* ℂˣ)

theorem trivialWeil_isIrreducible :
    (trivialWeil.{uF, uW} F E c).IsIrreducible :=
  FiniteRepresentation.characterLine_isIrreducible 1

@[simp]
theorem trivialWeil_rank : (trivialWeil.{uF, uW} F E c).rank = 1 :=
  FiniteRepresentation.characterLine_rank 1

theorem trivialWeil_isUnitary :
    (trivialWeil.{uF, uW} F E c).IsUnitary :=
  FiniteRepresentation.characterLine_one_isUnitary

variable (v : FinitePlace F)

/-- Every restriction of the trivial line is the same actual trivial local line. -/
def trivialLocalEquiv
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    FiniteRepresentation.Equiv
      (RelativeWeilGroup.localComponent (trivialWeil.{uF, uW} F E c) ι)
      (FiniteRepresentation.characterLine
        (1 : Weil.Local.localWeilGroup (padicField v) →* ℂˣ)) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' _ := by
    ext x
    rfl

theorem trivialWeil_localUnramified
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    (RelativeWeilGroup.localComponent (trivialWeil.{uF, uW} F E c) ι).IsUnramified
      (Weil.Local.localInertia (padicField v)) := by
  intro i
  exact trivialWeil_representation F E c (ι i)

@[simp]
theorem trivialWeil_localEulerPolynomial
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    RelativeWeilGroup.localEulerPolynomial (trivialWeil.{uF, uW} F E c) ι =
      1 - Polynomial.X := by
  change LocalFactor.eulerPolynomial
    ((trivialWeil.{uF, uW} F E c).representation
      (ι (Weil.Local.localGeometricFrobenius (padicField v)))) = _
  rw [trivialWeil_representation]
  apply Polynomial.funext
  intro z
  rw [LocalFactor.eulerPolynomial_eval]
  have hlin : (1 : Module.End ℂ (ULift.{uW} ℂ)) - z • 1 = (1 - z) • 1 := by
    simpa only [one_smul] using
      (sub_smul (1 : ℂ) z (1 : Module.End ℂ (ULift.{uW} ℂ))).symm
  rw [hlin, LinearMap.det_smul]
  simp only [map_one, mul_one, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X]
  change (1 - z) ^ Module.finrank ℂ (ULift.{uW} ℂ) = 1 - z
  rw [ConstantFunctions.liftedScalar_finrank, pow_one]

/-- The actual unitary rank-one local trivial Weil class. -/
def trivialLocalWeilBasis : LocalWeil.UnitaryBasis.{uF, uW} (padicField v) :=
  LocalWeil.unitaryBasisClass
    (FiniteRepresentation.characterLine
      (1 : Weil.Local.localWeilGroup (padicField v) →* ℂˣ))
    (FiniteRepresentation.characterLine_isContinuous 1)
    (FiniteRepresentation.characterLine_isIrreducible 1)
    FiniteRepresentation.characterLine_one_isUnitary 1
    (FiniteRepresentation.characterLine_rank 1)

/-- The multiplicity-one unitary lattice element of the local trivial line. -/
def trivialLocalWeilElement : LocalWeil.UnitaryLattice.{uF, uW} (padicField v) :=
  generator (trivialLocalWeilBasis.{uF, uW} F v)

@[simp]
theorem trivialLocalWeil_include :
    LocalWeil.includeUnitary (padicField v) (trivialLocalWeilElement.{uF, uW} F v) =
      LocalWeil.ofRepresentation
        (FiniteRepresentation.characterLine
          (1 : Weil.Local.localWeilGroup (padicField v) →* ℂˣ))
        (FiniteRepresentation.characterLine_isContinuous 1)
        (FiniteRepresentation.characterLine_isIrreducible 1) 1
        (FiniteRepresentation.characterLine_rank 1) := by
  simp [trivialLocalWeilElement, trivialLocalWeilBasis, LocalWeil.includeUnitary,
    Weil.includeUnitary, includeSubset, VirtualRepresentation.map, generator,
    LocalWeil.unitaryBasisClass, Weil.unitaryBasisClass, LocalWeil.ofRepresentation,
    LocalWeil.basisClass]

theorem trivialLocalWeil_effective :
    trivialLocalWeilElement.{uF, uW} F v ∈ effective := by
  intro b
  classical
  simp only [trivialLocalWeilElement, generator, Finsupp.single_apply]
  split <;> norm_num

/-- Restriction of the trivial global line has this exact full local expansion. -/
theorem trivialWeil_localExactExpansion
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    LocalWeil.ExactExpansion (padicField v)
      (localExactClass F E c v (trivialWeil.{uF, uW} F E c)
        (trivialWeil_isContinuous F E c) ι)
      (LocalWeil.includeUnitary (padicField v) (trivialLocalWeilElement F v)) := by
  rw [LocalWeil.exactExpansion_iff, trivialLocalWeil_include,
    LocalWeil.realizeExact_ofRepresentation]
  exact ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _
    (trivialLocalEquiv.{uF, uW} F E c v ι).symm

@[simp]
theorem trivialLocalWeil_include_rankOne
    (e : Correspondence.ReciprocityCandidate (padicField v)) :
    LocalWeil.includeUnitary (padicField v) (trivialLocalWeilElement.{uF, uW} F v) =
      generator (⟨1, Correspondence.rankOneWeilCharacterClass.{uF, uW}
        (padicField v) e 1⟩ : LocalWeil.Basis.{uF, uW} (padicField v)) := by
  have he : LocalFactor.RankOne.weilCharacter (padicField v) e 1 = 1 := by
    ext g
    rfl
  rw [trivialLocalWeil_include]
  simp only [LocalWeil.ofRepresentation, LocalWeil.basisClass, Weil.basisClass,
    Correspondence.rankOneWeilCharacterClass, he,
    FiniteRepresentation.continuousIrreducibleCharacterClass]
  rfl

variable [CompactSpace (AdeleQuotient F)]

/-- With actual local-map data, the constructed constant spectrum is weakly associated
with the actual trivial relative Weil representation. -/
theorem trivialWeil_weaklyAssociated
    (M : RelativeLocalMapFamily F E c) :
    RelativeWeilGroup.IsWeaklyAssociated (trivialWeil.{uF, uW} F E c)
      (ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).spectralSystem := by
  refine ⟨trivialWeil_isContinuous F E c, trivialWeil_rank F E c, ?_⟩
  apply Filter.Eventually.of_forall
  intro v
  refine ⟨by simp [CuspidalSpectralPresentation.spectralSystem,
    ConstantFunctions.rankOneSpectralPresentation], ?_⟩
  intro w
  refine ⟨⟨M.reciprocity v w, M.localMap v w, M.localMap_spec v w⟩, ?_⟩
  intro e ι _hι
  refine ⟨trivialWeil_localUnramified F E c v ι, ?_⟩
  rw [trivialWeil_localEulerPolynomial]
  exact (rankOneTrivialSpectrum_eulerPolynomial).symm

local instance relativeTrivialGeneratorAddCommGroup : AddCommGroup (RationalInvariantFunctions F 1) := Submodule.addCommGroup _
local instance relativeTrivialGeneratorAddCommGroup2 : AddCommGroup (ContinuousRationalFunctions F 1) := Submodule.addCommGroup _
local instance relativeTrivialGeneratorAddCommGroup3 : AddCommGroup (FiniteSmoothRationalFunctions F 1) := Submodule.addCommGroup _
local instance relativeTrivialGeneratorAddCommGroup4 : AddCommGroup (AutomorphicForms F 1) := Submodule.addCommGroup _
local instance relativeTrivialGeneratorAddCommGroup5 (S : LocalRealization F 1 v) : AddCommGroup S.Space := Submodule.addCommGroup _

local instance trivialFieldTopology : TopologicalSpace (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.topology
local instance trivialGLTopology (n : ℕ) : TopologicalSpace (FiniteLocalGL F n v) :=
  (padicField v).canonicalGeneralLinearTopology n

omit [CompactSpace (AdeleQuotient F)] in
/-- The constructed GL₁ trivial object has an invariant positive form. -/
theorem trivialLocalAutomorphic_isUnitarizable :
    Langlands.IsUnitarizable
      (Correspondence.rankOneSupercuspidalObject.{uF, uF} (padicField v) 1).obj.representation := by
  change Langlands.IsUnitarizable
    (FiniteRepresentation.characterLine.{uF, uF}
      (Correspondence.determinantQuasiCharacter (padicField v) 1 1)).representation
  have hdet : Correspondence.determinantQuasiCharacter (padicField v) 1 1 = 1 := by
    ext g
    rfl
  rw [hdet]
  exact (FiniteRepresentation.isUnitary_iff_isUnitarizable _).mp
    FiniteRepresentation.characterLine_one_isUnitary

/-- The actual unitary rank-one cuspidal datum of the trivial field character. -/
def trivialLocalAutomorphicDatum :
    PadicField.TopologicalData.UnitaryCuspidalDatum.{uF, uF}
      (padicField v).canonicalTopologicalData :=
  ⟨⟨1, Nat.one_pos,
    (Correspondence.rankOneSupercuspidalObject.{uF, uF} (padicField v) 1).isoClass⟩,
    trivialLocalAutomorphic_isUnitarizable F v⟩

/-- Its singleton unitary support, in the universe of actual automorphic forms. -/
def trivialLocalAutomorphicElement :
    PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v) :=
  (padicField v).canonicalTopologicalData.unitarySupportLattice
    {trivialLocalAutomorphicDatum F v}

omit [CompactSpace (AdeleQuotient F)] in
@[simp]
theorem trivialLocalAutomorphic_include :
    PadicSupercuspidal.includeUnitary (padicField v) (trivialLocalAutomorphicElement F v) =
      generator (⟨1, Correspondence.rankOneSupercuspidalClass.{uF, uF} (padicField v) 1⟩ :
        PadicSupercuspidal.Basis.{uF, uF} (padicField v)) := by
  let := (padicField v).canonicalTopologicalData.topology
  change Supercuspidal.includeUnitary (padicField v).Carrier
    ((padicField v).canonicalTopologicalData.unitarySupportLattice
      {trivialLocalAutomorphicDatum F v}) = _
  rw [(padicField v).canonicalTopologicalData.includeUnitary_unitarySupportLattice]
  simp only [Multiset.map_singleton,
    (padicField v).canonicalTopologicalData.supportLattice_singleton]
  rfl

/-- The actual constant local component is the trivial GL₁ object, across the
independent tensor-factor universe. -/
def trivialLocalAutomorphicEquiv :
    (Correspondence.rankOneSupercuspidalObject.{uF, uF} (padicField v) 1).obj.representation.Equiv
      ((ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).localComponent v).representation := by
  let e :
      (Correspondence.rankOneSupercuspidalObject.{uF, uF} (padicField v) 1).obj.representation.Equiv
        (ConstantFunctions.tensorLocalModel.{uF, uP} F 1 v) :=
    Representation.Equiv.mk
      ((ULift.moduleEquiv : ULift.{uF} ℂ ≃ₗ[ℂ] ℂ).trans
        (ULift.moduleEquiv : ULift.{uP} ℂ ≃ₗ[ℂ] ℂ).symm)
      (fun _g => by
        apply LinearMap.ext
        intro x
        change ULift.up ((1 : ℂ) * x.down) = ULift.up x.down
        simp only [one_mul])
  exact e.trans
    ((ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).presentation.localComponentEquiv
      (ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).finiteSlice.nonzero v)

theorem trivialLocalAutomorphic_support :
    PadicSupercuspidal.IsUnitaryLatticeSupport (padicField v)
      (((ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).localComponent v).padicObject
        (((ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).presentation.localComponent_isIrreducible_iff
          (ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).finiteSlice.nonzero v).mpr
          (ConstantFunctions.tensorLocalModel_isIrreducible F 1 v))
        (((ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).presentation.localComponent_isAdmissible_iff
          (ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).finiteSlice.nonzero v).mpr
          (ConstantFunctions.tensorLocalModel_isAdmissible F 1 v))).obj
      (trivialLocalAutomorphicElement F v) := by
  let T := (padicField v).canonicalTopologicalData
  let := T.topology
  let A := Correspondence.rankOneSupercuspidalObject.{uF, uF} (padicField v) 1
  have hs := Classification.TwoSupercuspidalTopDerivatives.supercuspidal_singleton_support
    T Nat.one_pos A
  have hu : T.IsUnitaryLatticeSupport A.obj (trivialLocalAutomorphicElement F v) := by
    refine ⟨{trivialLocalAutomorphicDatum F v}, ?_, rfl⟩
    simpa only [Multiset.map_singleton, trivialLocalAutomorphicDatum, A] using hs
  exact hu.of_iso (Langlands.SmoothRep.mkIso (trivialLocalAutomorphicEquiv.{uF, uP} F v))

/-- A fully witnessed trivial generator, constructed from supplied actual local maps.
Only the existence of the local-map family remains an external input. -/
def trivialWitnessedGenerator (M : RelativeLocalMapFamily F E c) :
    WitnessedGenerator.{uF, uW, uP} F E c v := by
  let w : FinitePlacesAbove E v := Classical.choice inferInstance
  exact
    { rankIndex := 0
      weil := trivialWeil F E c
      weil_irreducible := trivialWeil_isIrreducible F E c
      weil_unitary := trivialWeil_isUnitary F E c
      cuspidal := ConstantFunctions.rankOneCuspidal F
      presentation := ConstantFunctions.rankOneSpectralPresentation F
      associated := trivialWeil_weaklyAssociated F E c M
      placeOver := w
      reciprocity := M.reciprocity v w
      localMap := M.localMap v w
      localMap_spec := M.localMap_spec v w
      local_irreducible :=
        ((ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).presentation.localComponent_isIrreducible_iff
          (ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).finiteSlice.nonzero v).mpr
            (ConstantFunctions.tensorLocalModel_isIrreducible F 1 v)
      local_admissible :=
        ((ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).presentation.localComponent_isAdmissible_iff
          (ConstantFunctions.rankOneSpectralPresentation.{uF, uP} F).finiteSlice.nonzero v).mpr
            (ConstantFunctions.tensorLocalModel_isAdmissible F 1 v)
      weilElement := trivialLocalWeilElement F v
      weil_effective := trivialLocalWeil_effective F v
      weil_expansion := trivialWeil_localExactExpansion F E c v (M.localMap v w)
      automorphicElement := trivialLocalAutomorphicElement F v
      automorphic_support := trivialLocalAutomorphic_support F v }

@[simp]
theorem trivialWitnessedGenerator_weilElement (M : RelativeLocalMapFamily F E c) :
    (trivialWitnessedGenerator.{uF, uW, uP} F E c v M).weilElement =
      trivialLocalWeilElement F v := rfl

@[simp]
theorem trivialWitnessedGenerator_automorphicElement (M : RelativeLocalMapFamily F E c) :
    (trivialWitnessedGenerator.{uF, uW, uP} F E c v M).automorphicElement =
      trivialLocalAutomorphicElement F v := rfl

/-- The Weil element is the rank-one class of the trivial field character for every
supplied reciprocity candidate, without a normalization restriction on that candidate. -/
theorem trivialWitnessedGenerator_weil_include (M : RelativeLocalMapFamily F E c)
    (e : Correspondence.ReciprocityCandidate (padicField v)) :
    LocalWeil.includeUnitary (padicField v)
        (trivialWitnessedGenerator.{uF, uW, uP} F E c v M).weilElement =
      generator (⟨1, Correspondence.rankOneWeilCharacterClass.{uF, uW}
        (padicField v) e 1⟩ : LocalWeil.Basis.{uF, uW} (padicField v)) :=
  trivialLocalWeil_include_rankOne F v e

/-- The automorphic element is exactly the rank-one trivial supercuspidal class. -/
theorem trivialWitnessedGenerator_automorphic_include (M : RelativeLocalMapFamily F E c) :
    PadicSupercuspidal.includeUnitary (padicField v)
        (trivialWitnessedGenerator.{uF, uW, uP} F E c v M).automorphicElement =
      generator (⟨1, Correspondence.rankOneSupercuspidalClass.{uF, uF} (padicField v) 1⟩ :
        PadicSupercuspidal.Basis.{uF, uF} (padicField v)) :=
  trivialLocalAutomorphic_include F v

end Langlands.VirtualRepresentation.RelativeGlobal
