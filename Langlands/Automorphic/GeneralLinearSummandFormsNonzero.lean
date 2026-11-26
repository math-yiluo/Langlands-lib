import Langlands.Automorphic.GeneralLinearSummandCenterAnnihilation
import Langlands.Automorphic.GeneralLinearSummandCompactFinite
import Langlands.Automorphic.GeneralLinearSummandFormsDenseReduction
import Langlands.Automorphic.FullOperatorAction
import Langlands.Automorphic.GroupSchemeFullAEL2ContinuousCuspidality
import Langlands.Automorphic.GeneralLinearParabolicCuspidalEquivalence
import Langlands.Automorphic.GeneralLinearQuotientJointRecovery

/-! # Nonzero cuspidal forms attached to irreducible cuspidal summands of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set Topology Filter
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.FiniteVectors

private local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _

private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "K∞" => standardInfiniteCompact F (r + 1)
local notation "m" => GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)

section Level

/-- The open subgroup of finite adelic matrices corresponding to an open subgroup of the
finite adelic points of the group scheme. -/
def matrixLevel (K : OpenSubgroup (FiniteAdelicGroupPoints F GLs)) :
    OpenSubgroup (FiniteAdelicGL F (r + 1)) :=
  OpenSubgroup.comap (GeneralLinearGroupPoints.finiteHomeomorph F (r + 1)).symm.toMulEquiv.toMonoidHom
    (GeneralLinearGroupPoints.finiteHomeomorph F (r + 1)).symm.continuous K

theorem adelicHomeomorph_symm_ofFinite (l : FiniteAdelicGL F (r + 1)) :
    (m).symm (AdelicGL.ofFinite F (r + 1) l) = AdelicGroupPoints.ofFinite F GLs
      ((GeneralLinearGroupPoints.finiteHomeomorph F (r + 1)).symm l) := by
  apply (m).injective
  rw [ContinuousMulEquiv.apply_symm_apply, GeneralLinearGroupPoints.adelicHomeomorph_ofFinite,
    ContinuousMulEquiv.apply_symm_apply]

variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))

/-- Invariance under an open subgroup of finite adelic points is invariance under the
corresponding open subgroup of finite adelic matrices. -/
theorem IsFiniteInvariant.matrixLevel {h : C(PositiveRationalQuotient F GLs T i, ℂ)}
    {K : OpenSubgroup (FiniteAdelicGroupPoints F GLs)}
    (hh : IsFiniteInvariant F GLs T i h K.toSubgroup) :
    ∀ l : (matrixLevel F r K).toSubgroup, ∀ q,
      h (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F GLs T i)
        ((m).symm (AdelicGL.ofFinite F (r + 1) l)) q) = h q := by
  intro l q
  rw [adelicHomeomorph_symm_ofFinite]
  exact hh _ l.property q

end Level

variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "μQ" => positiveRationalQuotientHaarMeasure F GLs T i
local notation "ρ" => haarQuotientL2BoundedRightAction F GLs T i hi I e hc
local notation "hG" => GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))

section CompactTransfer

/-- The standard archimedean compact subgroup acting on matrix-model continuous functions by
right translation. -/
def compactFunctionAction : Representation ℂ K∞ (Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)) :=
  (Langlands.Automorphic.continuousRightAction F (r + 1)).comp
    ((AdelicGL.ofInfinite F (r + 1)).toMonoidHom.comp (standardInfiniteCompact F (r + 1)).subtype)

include hi I e hc in
/-- Right translation by a compact element acts on `L²` classes by the quotient action. -/
theorem IsGeneralLinearFormClass.compactFunctionAction
    {φ : Lp ℂ 2 μQ} {f : Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)}
    (hφ : IsGeneralLinearFormClass F r T i φ f) (k : K∞) :
    IsGeneralLinearFormClass F r T i (compactAction F r T i hi I e hc k φ)
      (compactFunctionAction F r k f) := by
  have h := hφ.rightTranslate (haarQuotientMeasureRightInvariant F GLs T i hi I e hc)
    ((m).symm (AdelicGL.ofInfinite F (r + 1) k.val))
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  exact h

/-- Matrix-model continuous functions with an `L²` class, as a representation of the standard
compact subgroup. -/
def classSubrepresentation : Subrepresentation (compactFunctionAction F r) where
  toSubmodule :=
    { carrier := {g | ∃ ψ, IsGeneralLinearFormClass F r T i ψ g}
      zero_mem' := ⟨0, isGeneralLinearFormClass_zero F r T i⟩
      add_mem' := fun ⟨ψ, hψ⟩ ⟨χ, hχ⟩ => ⟨ψ + χ, hψ.add hχ⟩
      smul_mem' := fun c _ ⟨ψ, hψ⟩ => ⟨c • ψ, hψ.smul c⟩ }
  apply_mem_toSubmodule k _ := fun ⟨_, hψ⟩ =>
    ⟨_, IsGeneralLinearFormClass.compactFunctionAction F r T i hi I e hc hψ k⟩

/-- The `L²` class map, intertwining the compact actions. -/
def classMap :
    (classSubrepresentation F r T i hi I e hc).toRepresentation.IntertwiningMap
      (compactAction F r T i hi I e hc) where
  toLinearMap :=
    { toFun := fun g => Classical.choose g.property
      map_add' := fun g g' => (Classical.choose_spec (g + g').property).unique
        ((Classical.choose_spec g.property).add (Classical.choose_spec g'.property))
      map_smul' := fun c g => (Classical.choose_spec (c • g).property).unique
        ((Classical.choose_spec g.property).smul c) }
  isIntertwining' k := by
    apply LinearMap.ext
    intro g
    exact (Classical.choose_spec
      ((classSubrepresentation F r T i hi I e hc).toRepresentation k g).property).unique
      (IsGeneralLinearFormClass.compactFunctionAction F r T i hi I e hc
        (Classical.choose_spec g.property) k)

theorem classMap_spec (g : (classSubrepresentation F r T i hi I e hc).toSubmodule) :
    IsGeneralLinearFormClass F r T i (classMap F r T i hi I e hc g) g :=
  Classical.choose_spec g.property

theorem classMap_injective : Function.Injective (classMap F r T i hi I e hc) := by
  intro g g' hgg'
  apply Subtype.ext
  have h' := classMap_spec F r T i hi I e hc g'
  rw [← hgg'] at h'
  exact generalLinearFormClass_form_eq F r T i hi I e hc (classMap_spec F r T i hi I e hc g) h'

/-- The inclusion of the class subrepresentation. -/
def classInclusion :
    (classSubrepresentation F r T i hi I e hc).toRepresentation.IntertwiningMap
      (compactFunctionAction F r) where
  toLinearMap := (classSubrepresentation F r T i hi I e hc).toSubmodule.subtype
  isIntertwining' _ := rfl

/-- **Compact finiteness descends from classes.** If the `L²` class of a matrix-model
continuous function is `K∞`-finite, that is, its orbit under the standard compact subgroup
spans a finite-dimensional space, then the function is `K∞`-finite (`IsInfiniteFinite`). -/
theorem isInfiniteFinite_of_isGeneralLinearFormClass {φ : Lp ℂ 2 μQ}
    {f : Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)} (hφ : IsGeneralLinearFormClass F r T i φ f)
    (hfin : IsFiniteVector (compactAction F r T i hi I e hc) φ) :
    Langlands.Automorphic.IsInfiniteFinite F (r + 1) K∞ f := by
  let g : (classSubrepresentation F r T i hi I e hc).toSubmodule := ⟨f, φ, hφ⟩
  have hg : classMap F r T i hi I e hc g = φ := (classMap_spec F r T i hi I e hc g).unique hφ
  have h1 : IsFiniteVector (classSubrepresentation F r T i hi I e hc).toRepresentation g :=
    (isFiniteVector_map_iff (classMap F r T i hi I e hc) (classMap_injective F r T i hi I e hc)
      g).mp (hg ▸ hfin)
  exact h1.map (classInclusion F r T i hi I e hc)

end CompactTransfer

omit [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant] in
/-- The slice of the smooth inclusion is the finite-smooth slice. -/
theorem smoothInfiniteSlice_finiteSmoothInclusion (b : FiniteAdelicGL F (r + 1))
    (f : Langlands.Automorphic.FiniteSmoothRationalFunctions F (r + 1)) :
    Langlands.Automorphic.smoothInfiniteSlice F (r + 1) b
        (Langlands.Automorphic.finiteSmoothInclusion F (r + 1) f) =
      Langlands.Automorphic.finiteSmoothSlice F (r + 1) b f := rfl

include hi I e hc in
/-- A finite-smooth function whose enveloping derivative by a central element has zero class
is killed by that central element on every slice. -/
theorem centerAction_slice_eq_zero (f : Langlands.Automorphic.FiniteSmoothRationalFunctions F (r + 1))
    (z : ArchimedeanGL.EnvelopingCenter F (r + 1))
    (hz : IsGeneralLinearFormClass F r T i 0 (Langlands.Automorphic.finiteSmoothEnvelopingAction
      F (r + 1) (ArchimedeanGL.centerInclusion F (r + 1) z) f).val)
    (b : FiniteAdelicGL F (r + 1)) :
    ArchimedeanGL.centerAction F (r + 1) z (Langlands.Automorphic.smoothInfiniteSlice F (r + 1) b
      (Langlands.Automorphic.finiteSmoothInclusion F (r + 1) f)) = 0 := by
  have h0 := generalLinearFormClass_form_eq F r T i hi I e hc hz (isGeneralLinearFormClass_zero F r T i)
  rw [ArchimedeanGL.centerAction_apply, smoothInfiniteSlice_finiteSmoothInclusion]
  apply Subtype.ext
  funext a
  rw [← Langlands.Automorphic.evaluate_finiteSmoothEnvelopingAction, h0]
  rfl


section Construction

variable [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))]
  (ν : Measure (InfiniteAdelicGL F (r + 1))) [ν.IsHaarMeasure]
  [SecondCountableTopology (InfiniteAdelicGL F (r + 1))]


/-- **A nonzero attached form from a regular compact-finite vector.** Let `P` be a nonzero closed
invariant subspace of the full almost-everywhere cuspidal space, minimal among such subspaces.
A regular vector of `P`, invariant under a compact open subgroup and `K∞`-finite (its orbit
under the standard archimedean compact subgroup spans a finite-dimensional space), gives a
nonzero stable cuspidal form with class in `P`: smooth it at infinity by a kernel invariant under
conjugation by `K∞`. -/
theorem summandForms_ne_bot_of_regular [CompactSpace (AdeleQuotient F)]
    (hPD : ParabolicDynamicStatement.{u})
    (P : Submodule ℂ (fullAEL2CuspidalSubmodule F GLs hPD hG T i hi I e hc))
    (hPinv : ∀ a, ∀ x ∈ P, fullAEL2CuspidalBoundedRightAction F GLs hPD hG T i hi I e hc a x ∈ P)
    (hPne : P ≠ ⊥) (hPc : IsClosed (P : Set (fullAEL2CuspidalSubmodule F GLs hPD hG T i hi I e hc)))
    (hPmin : ∀ P' : Submodule ℂ (fullAEL2CuspidalSubmodule F GLs hPD hG T i hi I e hc), P' ≤ P →
      IsClosed (P' : Set (fullAEL2CuspidalSubmodule F GLs hPD hG T i hi I e hc)) →
      (∀ a, ∀ x ∈ P', fullAEL2CuspidalBoundedRightAction F GLs hPD hG T i hi I e hc a x ∈ P') →
        P' = ⊥ ∨ P' = P)
    (hν : ∀ k : K∞, Measure.map (· * k.val) ν = ν)
    {K : OpenSubgroup (FiniteAdelicGroupPoints F GLs)} {u : Lp ℂ 2 μQ}
    (hu : IsRegularVector F GLs T i hi I e hc (summandSubmodule F r hPD T i hi I e hc P)
      K.toSubgroup u)
    (hfin : IsFiniteVector (compactAction F r T i hi I e hc) u) :
    summandForms F r T i (summandSubmodule F r hPD T i hi I e hc P) ≠ ⊥ := by
  obtain ⟨κ, hκ, hne⟩ := exists_smoothedClass_ne_zero F r T i hi I e hc ν hu.ne_zero
  obtain ⟨h, S₀, C₀, hS₀, hC₀, hae, hMB, hL⟩ := hu.rep
  have hL' := IsFiniteInvariant.matrixLevel F r T i hL
  obtain ⟨f, hf⟩ := exists_finiteSmooth_smoothing F r T i ν κ h (matrixLevel F r K) hL'
  have hf1 : f.val = continuousGeneralLinearEquiv F (r + 1)
      (positiveQuotientContinuousPullback F GLs T i (smoothedQuotientFunction F r T i ν 1 κ h)) := by
    have := hf 1
    rwa [map_one, Module.End.one_apply] at this
  have hcls : IsGeneralLinearFormClass F r T i (smoothedClass F r T i ν hi I e hc 1 κ u) f.val := by
    rw [hf1]
    exact isGeneralLinearFormClass_smoothedClass F r T i ν hi I e hc 1 κ u h hae
  have hA := isClosed_summandSubmodule F r hPD T i hi I e hc P hPc
  have hAinv := summandSubmodule_invariant F r hPD T i hi I e hc P hPinv
  have hmemA : smoothedClass F r T i ν hi I e hc 1 κ u ∈ summandSubmodule F r hPD T i hi I e hc P :=
    smoothedClass_mem F r T i ν hi I e hc _ hA hAinv 1 κ hu.mem
      (integrable_smoothingOrbit F r T i ν hi I e hc 1 κ u h hae)
  obtain ⟨J, hJ, hJy⟩ :=
    exists_ideal_smoothedClass_eq_zero F r hPD T i hi I e hc ν P hPinv hPne hPc hPmin
  have hauto : f ∈ Langlands.Automorphic.automorphicSubrepresentation F (r + 1) := by
    rw [Langlands.Automorphic.mem_automorphicSubrepresentation,
      Langlands.Automorphic.isAutomorphicForm_iff_source_conditions]
    refine ⟨(Langlands.Automorphic.hasFiniteLevel_iff_mem_finiteSmooth F (r + 1) f.val).mpr
      f.property.2, ?_, ⟨J, hJ, fun z hz b => ?_⟩, fun b => ?_⟩
    · exact isInfiniteFinite_of_isGeneralLinearFormClass F r T i hi I e hc hcls
        (isFiniteVector_smoothedClass F r T i hi I e hc ν κ hκ hν hfin)
    · apply centerAction_slice_eq_zero F r T i hi I e hc f z
      have h0 := hJy κ u hu.mem h hae (matrixLevel F r K) hL' z hz
      have hz' := isGeneralLinearFormClass_smoothedClass F r T i ν hi I e hc
        (ArchimedeanGL.centerInclusion F (r + 1) z) κ u h hae
      rw [h0, ← hf] at hz'
      exact hz'
    · have hMB3 := quotientMassBound_weightedQuotientOrbitIntegral F GLs T i hi I e hc ν
        (archimedeanAdelicPoint F r) (smoothingWeight F r 1 κ)
        (smoothingWeight_hasCompactSupport F r 1 κ) h hS₀ hC₀ hMB
      obtain ⟨C', hC', hb⟩ := QuotientMassBound.sliceGrowth F (r + 1) T i hi I e hc
        (isCompact_conjugateSet F GLs ((smoothingWeight_hasCompactSupport F r 1 κ).isCompact.image
          (archimedeanAdelicPoint F r).continuous) hS₀) (mul_nonneg hC₀ (sq_nonneg _)) hMB3 b
      refine ⟨C', hC', Module.finrank ℝ (ArchimedeanMatrix F (r + 1)), fun a => ?_⟩
      change ‖Langlands.Automorphic.ContinuousRationalFunctions.evaluate F (r + 1) f.val
        (AdelicGL.pair F (r + 1) a b)‖ ≤ _
      rw [hf1, evaluate_pullback]
      exact hb a
  let fS : Langlands.Automorphic.StableAutomorphicFunctions F (r + 1) := ⟨f, by
    change f ∈ (Langlands.Automorphic.automorphicOperatorCore F (r + 1)).toSubmodule
    rw [Langlands.Automorphic.automorphicOperatorCore_eq]
    exact hauto⟩
  have hfS : stableToContinuous F (r + 1) fS = f.val := rfl
  have hS : (smoothedClass F r T i ν hi I e hc 1 κ u) ∈
      fullAEL2CuspidalSubmodule F GLs hPD hG T i hi I e hc := by
    obtain ⟨x, -, hx⟩ := hmemA
    rw [← hx]
    exact x.property
  have hae3 := (groupSchemeQuotientL2IntegratedRepresentative F GLs T i hi I e hc ν
    (archimedeanAdelicPoint F r) (smoothingWeight F r 1 κ)
    (smoothingWeight_hasCompactSupport F r 1 κ) u h hae).2
  have hcusp : Langlands.Automorphic.IsCuspidal F (r + 1) (stableToContinuous F (r + 1) fS) := by
    rw [hfS, hf1]
    exact (mem_normalizedGeneralLinearParabolicCuspidal_iff F (r + 1) hPD hG _).mp
      ((groupSchemeFullAEL2ContinuousCuspidality F GLs hPD hG T i hi I e hc _ _ hae3).mp hS)
  intro hbot
  have hmem : fS ∈ summandForms F r T i (summandSubmodule F r hPD T i hi I e hc P) :=
    ⟨hcusp, _, hmemA, hcls⟩
  rw [hbot, Submodule.mem_bot] at hmem
  have h0 : f.val = 0 := by
    have := congrArg (stableToContinuous F (r + 1)) hmem
    rwa [map_zero] at this
  rw [h0] at hcls
  exact hne (hcls.unique (isGeneralLinearFormClass_zero F r T i))

end Construction

/-- The same construction with the Borel Haar measure of the archimedean group, which is right
invariant under the standard compact subgroup. -/
theorem summandForms_ne_bot_of_compactFinite [CompactSpace (AdeleQuotient F)]
    (hPD : ParabolicDynamicStatement.{u})
    (P : Submodule ℂ (fullAEL2CuspidalSubmodule F GLs hPD hG T i hi I e hc))
    (hPinv : ∀ a, ∀ x ∈ P, fullAEL2CuspidalBoundedRightAction F GLs hPD hG T i hi I e hc a x ∈ P)
    (hPne : P ≠ ⊥) (hPc : IsClosed (P : Set (fullAEL2CuspidalSubmodule F GLs hPD hG T i hi I e hc)))
    (hPmin : ∀ P' : Submodule ℂ (fullAEL2CuspidalSubmodule F GLs hPD hG T i hi I e hc), P' ≤ P →
      IsClosed (P' : Set (fullAEL2CuspidalSubmodule F GLs hPD hG T i hi I e hc)) →
      (∀ a, ∀ x ∈ P', fullAEL2CuspidalBoundedRightAction F GLs hPD hG T i hi I e hc a x ∈ P') →
        P' = ⊥ ∨ P' = P)
    {K : OpenSubgroup (FiniteAdelicGroupPoints F GLs)} {u : Lp ℂ 2 μQ}
    (hu : IsRegularVector F GLs T i hi I e hc (summandSubmodule F r hPD T i hi I e hc P)
      K.toSubgroup u)
    (hfin : IsFiniteVector (compactAction F r T i hi I e hc) u) :
    summandForms F r T i (summandSubmodule F r hPD T i hi I e hc P) ≠ ⊥ := by
  let : MeasurableSpace (InfiniteAdelicGL F (r + 1)) := borel _
  have : BorelSpace (InfiniteAdelicGL F (r + 1)) := ⟨rfl⟩
  have := secondCountableTopology_infiniteAdelicGL F r
  exact summandForms_ne_bot_of_regular F r T i hi I e hc Measure.haar hPD P hPinv hPne hPc hPmin
    (fun k => Langlands.Analysis.NormalizedAverage.map_mul_right_eq_self_of_isCompact _ _
      (isCompact_standardInfiniteCompact F (r + 1)) k.property) hu hfin


set_option maxHeartbeats 1000000 in
/-- **Nonzero attached forms.** Given the continuous-representative theorem for compact
convolution on the positive rational quotient, every nonzero closed invariant subspace of the
full almost-everywhere cuspidal space of `GL_{r+1}`, minimal among such subspaces, has a nonzero
stable cuspidal form whose class lies in it. -/
theorem generalLinearSummandFormsNonzero_of_representative
    (hrep : GroupSchemeQuotientL2ContinuousRepresentativeStatement.{u}) :
    GeneralLinearSummandFormsNonzeroStatement.{u} := by
  intro F _ _ _ r hPD T i hi _ I _ e hc _ hG₀ S πc P ⟨hPne, hPc, hPinv, hPmin⟩
  have hA := isClosed_summandSubmodule F r hPD T i hi I e hc P hPc
  have hAinv := summandSubmodule_invariant F r hPD T i hi I e hc P hPinv
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPne
  have hx0' : (x : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) T i)) ≠ 0 :=
    fun h => hx0 (Subtype.ext h)
  obtain ⟨u₀, hu₀⟩ := exists_isRegularVector_convolution F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) T i hi I e hc hrep _ hA hAinv
    ⟨x, hxP, rfl⟩ hx0'
  obtain ⟨K, -, u₁, hu₁⟩ := exists_isRegularVector_level F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) T i hi I e hc _ hA hAinv hu₀
  obtain ⟨u₂, hu₂, hfin⟩ := exists_isRegularVector_compactFinite F r T i hi I e hc _ hA hAinv hu₁
  exact summandForms_ne_bot_of_compactFinite F r T i hi I e hc hPD P hPinv hPne hPc hPmin hu₂ hfin

/-- **Density of attached form classes.** Given the continuous-representative theorem for
compact convolution on the positive rational quotient, the classes of the stable cuspidal forms
attached to an irreducible cuspidal summand of `GL_{r+1}` are dense in it. -/
theorem generalLinearSummandFormsDense_of_representative
    (hrep : GroupSchemeQuotientL2ContinuousRepresentativeStatement.{u}) :
    GeneralLinearSummandFormsDenseStatement.{u} :=
  generalLinearSummandFormsDenseOfNonzero (generalLinearSummandFormsNonzero_of_representative hrep)

end Langlands.Automorphic.GroupSchemeFunctions
