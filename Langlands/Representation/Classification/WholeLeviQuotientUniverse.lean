import Langlands.Representation.Classification.RegularLanglandsHeadAdapters
import Langlands.Representation.Category.UniverseLiftPadic
import Langlands.Representation.Induction.InnerLeviTransport
import Langlands.Representation.Tensor.ProductFiltration

/-!
# Cross-universe transport of whole-Levi standard modules and weak quotients

Lift supplied tempered block factors of a whole-Levi representation, and an
arbitrary irreducible quotient of its twisted normalized induction, to one
common carrier universe. The whole-Levi factorization is supplied data. Only
actual equivalences and surjections are constructed; no factorization
existence, head or classification result is assumed or proved.
-/

noncomputable section

open CategoryTheory

namespace Langlands.WholeLeviQuotientUniverse

universe uF uV uW uJ uK uX

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section Blocks

variable {n : ℕ} (B : GeneralLinear.BlockShape n)
  (A : letI := T.topology
    ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))

-- `uJ` and `uX` enter only through the common carrier universe `max uF uV uJ uX`.
set_option linter.checkUnivs false in
/-- The block factors with carriers lifted to `max uF uV uJ uX`. -/
def liftedBlocks :
    letI := T.topology
    ∀ i, SmoothRep.{0, uF, max uF uV uJ uX} ℂ (GeneralLinear (B.size i) F.Carrier) :=
  letI := T.topology
  fun i => SmoothRep.universeLift.{max uF uJ uX} (A i)

@[simp]
theorem liftedBlocks_representation (i : Fin B.length) :
    letI := T.topology
    (liftedBlocks.{uF, uV, uJ, uX} T B A i).representation =
      universeLiftRepresentation.{max uF uJ uX} (A i).representation :=
  rfl

/-- The factor lift `v ↦ ULift.up v`. -/
def blockLiftEquiv (i : Fin B.length) :
    letI := T.topology
    (A i).representation.Equiv (liftedBlocks.{uF, uV, uJ, uX} T B A i).representation :=
  letI := T.topology
  SmoothRep.universeLiftEquiv.{max uF uJ uX} (A i)

@[simp]
theorem blockLiftEquiv_apply (i : Fin B.length) (v : letI := T.topology; A i) :
    letI := T.topology
    blockLiftEquiv.{uF, uV, uJ, uX} T B A i v = ULift.up v :=
  rfl

theorem liftedBlocks_isIrreducible_iff (i : Fin B.length) :
    letI := T.topology
    Representation.IsIrreducible (liftedBlocks.{uF, uV, uJ, uX} T B A i).representation ↔
      Representation.IsIrreducible (A i).representation :=
  letI := T.topology
  SmoothRep.isIrreducible_universeLift_iff (A i)

theorem liftedBlocks_isTempered_iff (i : Fin B.length) :
    letI := T.topology
    T.IsTempered (liftedBlocks.{uF, uV, uJ, uX} T B A i).representation ↔
      T.IsTempered (A i).representation :=
  letI := T.topology
  T.isTempered_universeLift_iff (A i).representation

/-- The untwisted block tensors are equivalent, by the tensor of the factor lifts. -/
def tensorLiftEquiv :
    letI := T.topology
    (B.blockTensor (fun i => (A i).representation)).Equiv
      (B.blockTensor (fun i => (liftedBlocks.{uF, uV, uJ, uX} T B A i).representation)) :=
  letI := T.topology
  FiniteTensorFiltration.externalCongr (blockLiftEquiv.{uF, uV, uJ, uX} T B A)

@[simp]
theorem tensorLiftEquiv_tprod (v : letI := T.topology; ∀ i, A i) :
    letI := T.topology
    tensorLiftEquiv.{uF, uV, uJ, uX} T B A (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => blockLiftEquiv.{uF, uV, uJ, uX} T B A i (v i)) :=
  PiTensorProduct.congr_tprod _ _

/-- A supplied factorization of the whole-Levi representation, followed by the
factor lifts. -/
def leviLiftEquiv (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (eσ : letI := T.topology
      σ.ρ.Equiv (B.blockTensor (fun i => (A i).representation))) :
    letI := T.topology
    σ.ρ.Equiv (B.blockTensor (fun i => (liftedBlocks.{uF, uV, uJ, uX} T B A i).representation)) :=
  letI := T.topology
  eσ.trans (tensorLiftEquiv T B A)

@[simp]
theorem leviLiftEquiv_apply (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (eσ : letI := T.topology
      σ.ρ.Equiv (B.blockTensor (fun i => (A i).representation))) (v : σ.V) :
    letI := T.topology
    leviLiftEquiv.{uF, uV, uJ, uX} T B A σ eσ v = tensorLiftEquiv T B A (eσ v) :=
  rfl

/-- Whole-Levi analytic temperedness is unchanged by passing to the lifted tensor. -/
theorem isLeviTempered_liftedTensor_iff (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (eσ : letI := T.topology
      σ.ρ.Equiv (B.blockTensor (fun i => (A i).representation))) :
    letI := T.topology
    RelativeRegularComparison.IsLeviTempered T B σ ↔
      RelativeRegularComparison.IsLeviTempered T B
        (Rep.of (B.blockTensor (fun i => (liftedBlocks.{uF, uV, uJ, uX} T B A i).representation))) :=
  letI := T.topology
  T.isLeviTempered_iff_of_equiv B (leviLiftEquiv T B A σ eσ)

variable (hA : letI := T.topology
    ∀ i, Representation.IsIrreducible (A i).representation)
  (hT : letI := T.topology; ∀ i, T.IsTempered (A i).representation)
  (t : Fin B.length → ℝ) (ht : StrictAnti t)

-- `uJ` and `uX` enter only through the common carrier universe `max uF uV uJ uX`.
set_option linter.checkUnivs false in
/-- The lifted tempered Langlands datum: shape `B`, lifted blocks and exponent `t`. -/
def liftedDatum : T.TemperedLanglandsDatum.{max uF uV uJ uX, uF} n where
  shape := B
  blocks := liftedBlocks.{uF, uV, uJ, uX} T B A
  irreducible i := (liftedBlocks_isIrreducible_iff T B A i).mpr (hA i)
  tempered i := (liftedBlocks_isTempered_iff T B A i).mpr (hT i)
  exponent := t
  strictAnti := ht

@[simp]
theorem liftedDatum_shape :
    (liftedDatum.{uF, uV, uJ, uX} T B A hA hT t ht).shape = B :=
  rfl

@[simp]
theorem liftedDatum_exponent :
    (liftedDatum.{uF, uV, uJ, uX} T B A hA hT t ht).exponent = t :=
  rfl

@[simp]
theorem liftedDatum_blocks :
    (liftedDatum.{uF, uV, uJ, uX} T B A hA hT t ht).blocks = liftedBlocks.{uF, uV, uJ, uX} T B A :=
  rfl

/-- The lifted standard module is equivalent to normalized induction of the
real twist of the original whole-Levi representation. -/
def standardModuleEquiv (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (eσ : letI := T.topology
      σ.ρ.Equiv (B.blockTensor (fun i => (A i).representation))) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (liftedDatum.{uF, uV, uJ, uX} T B A hA hT t ht).standardModule.representation.Equiv
      (T.normalizedParabolicInduced B (T.leviRealPowerTwist B t σ.ρ)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  (RegularHeadExistence.standardModuleLeviTwistEquiv T
      (liftedDatum.{uF, uV, uJ, uX} T B A hA hT t ht)).trans
    (T.normalizedParabolicInducedEquiv B
      (twistEquiv (T.leviRealPowerCharacter B t)
        (leviLiftEquiv.{uF, uV, uJ, uX} T B A σ eσ).symm))

/-- Pointwise, the standard-module equivalence is the inverse of the lifted
whole-Levi factorization applied to function values. -/
@[simp]
theorem standardModuleEquiv_eval (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (eσ : letI := T.topology
      σ.ρ.Equiv (B.blockTensor (fun i => (A i).representation)))
    (f : letI := T.topology
      (liftedDatum.{uF, uV, uJ, uX} T B A hA hT t ht).standardModule)
    (g : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ (standardModuleEquiv.{uF, uV, uJ, uX} T B A hA hT t ht σ eσ f) g =
      (leviLiftEquiv.{uF, uV, uJ, uX} T B A σ eσ).symm (Induction.eval _ _ f g) :=
  rfl

end Blocks

section Quotient

variable {n : ℕ}

/-- A quotient of a smooth representation by a surjective intertwiner is smooth.
Here the source is any normalized parabolic induction. -/
theorem isSmooth_of_surjective_induced (B : GeneralLinear.BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
    (q : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      (T.normalizedParabolicInduced B ρ).IntertwiningMap J.ρ)
    (hq : Function.Surjective q) :
    letI := T.topology
    IsSmooth J.ρ :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  isSmooth_of_surjective q hq (T.isSmooth_normalizedParabolicInduced B ρ)

-- `uV` and `uX` enter only through the common carrier universe `max uF uV uJ uX`.
set_option linter.checkUnivs false in
/-- The smooth lift of an ambient representation `J` to carrier universe
`max uF uV uJ uX`. -/
def quotientLift (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
    (hJ : letI := T.topology; IsSmooth J.ρ) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV uJ uX} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  SmoothRep.universeLift.{max uF uV uX} (SmoothRep.of J.ρ hJ)

@[simp]
theorem quotientLift_representation (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
    (hJ : letI := T.topology; IsSmooth J.ρ) :
    letI := T.topology
    (quotientLift.{uF, uV, uJ, uX} T J hJ).representation =
      universeLiftRepresentation.{max uF uV uX} J.ρ :=
  rfl

/-- The lift `v ↦ ULift.up v` of `J`. -/
def quotientLiftEquiv (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
    (hJ : letI := T.topology; IsSmooth J.ρ) :
    letI := T.topology
    J.ρ.Equiv (quotientLift.{uF, uV, uJ, uX} T J hJ).representation :=
  letI := T.topology
  SmoothRep.universeLiftEquiv.{max uF uV uX} (SmoothRep.of J.ρ hJ)

@[simp]
theorem quotientLiftEquiv_apply (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
    (hJ : letI := T.topology; IsSmooth J.ρ) (v : J.V) :
    letI := T.topology
    quotientLiftEquiv.{uF, uV, uJ, uX} T J hJ v = ULift.up v :=
  rfl

theorem quotientLift_isIrreducible_iff (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
    (hJ : letI := T.topology; IsSmooth J.ρ) :
    letI := T.topology
    Representation.IsIrreducible (quotientLift.{uF, uV, uJ, uX} T J hJ).representation ↔
      Representation.IsIrreducible J.ρ :=
  letI := T.topology
  SmoothRep.isIrreducible_universeLift_iff (SmoothRep.of J.ρ hJ)

/-- Equivalent ambient representations have isomorphic smooth lifts once the
auxiliary universes are chosen so that both carriers lie in
`max uF uV uW uJ uK uX`. -/
def quotientLiftIso (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
    (K : Rep.{uK} ℂ (GeneralLinear n F.Carrier))
    (hJ : letI := T.topology; IsSmooth J.ρ) (hK : letI := T.topology; IsSmooth K.ρ)
    (e : J.ρ.Equiv K.ρ) :
    letI := T.topology
    quotientLift.{uF, uV, uJ, max uW uK uX} T J hJ ≅
      quotientLift.{uF, uW, uK, max uV uJ uX} T K hK :=
  letI := T.topology
  SmoothRep.mkIso
    (((quotientLiftEquiv.{uF, uV, uJ, max uW uK uX} T J hJ).symm.trans e).trans
      (quotientLiftEquiv.{uF, uW, uK, max uV uJ uX} T K hK))

@[simp]
theorem quotientLiftIso_hom_apply (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
    (K : Rep.{uK} ℂ (GeneralLinear n F.Carrier))
    (hJ : letI := T.topology; IsSmooth J.ρ) (hK : letI := T.topology; IsSmooth K.ρ)
    (e : J.ρ.Equiv K.ρ) (v : J.V) :
    letI := T.topology
    SmoothRep.hom (quotientLiftIso.{uF, uV, uW, uJ, uK, uX} T J K hJ hK e).hom (ULift.up v) =
      ULift.up (e v) :=
  rfl

variable (B : GeneralLinear.BlockShape n)
  (A : letI := T.topology
    ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
  (hA : letI := T.topology
    ∀ i, Representation.IsIrreducible (A i).representation)
  (hT : letI := T.topology; ∀ i, T.IsTempered (A i).representation)
  (t : Fin B.length → ℝ) (ht : StrictAnti t)
  (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
  (eσ : letI := T.topology
    σ.ρ.Equiv (B.blockTensor (fun i => (A i).representation)))
  (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
  (q : letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced B (T.leviRealPowerTwist B t σ.ρ)).IntertwiningMap J.ρ)
  (hq : Function.Surjective q)

/-- The transported quotient map: the standard-module equivalence, then `q`,
then the lift of `J`. -/
def quotientMap :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (liftedDatum.{uF, uV, uJ, uX} T B A hA hT t ht).standardModule.representation.IntertwiningMap
      (quotientLift.{uF, uV, uJ, uX} T J
        (isSmooth_of_surjective_induced T B _ J q hq)).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  (quotientLiftEquiv.{uF, uV, uJ, uX} T J
      (isSmooth_of_surjective_induced T B _ J q hq)).toIntertwiningMap.comp
    (q.comp (standardModuleEquiv.{uF, uV, uJ, uX} T B A hA hT t ht σ eσ).toIntertwiningMap)

@[simp]
theorem quotientMap_apply
    (f : letI := T.topology
      (liftedDatum.{uF, uV, uJ, uX} T B A hA hT t ht).standardModule) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    quotientMap.{uF, uV, uJ, uX} T B A hA hT t ht σ eσ J q hq f =
      ULift.up (q (standardModuleEquiv.{uF, uV, uJ, uX} T B A hA hT t ht σ eσ f)) :=
  rfl

theorem quotientMap_surjective :
    Function.Surjective (quotientMap.{uF, uV, uJ, uX} T B A hA hT t ht σ eσ J q hq) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  (quotientLiftEquiv.{uF, uV, uJ, uX} T J
      (isSmooth_of_surjective_induced T B _ J q hq)).surjective.comp
    (hq.comp (standardModuleEquiv.{uF, uV, uJ, uX} T B A hA hT t ht σ eσ).surjective)

include eσ in
/-- The lift of an arbitrary irreducible quotient of the original twisted
induction is a weak Langlands quotient of the lifted datum. -/
theorem isLanglandsQuotient_quotientLift (hJ : letI := T.topology
    Representation.IsIrreducible J.ρ) :
    (liftedDatum.{uF, uV, uJ, uX} T B A hA hT t ht).IsLanglandsQuotient
      (quotientLift.{uF, uV, uJ, uX} T J (isSmooth_of_surjective_induced T B _ J q hq)) :=
  letI := T.topology
  ⟨(quotientLift_isIrreducible_iff T J _).mpr hJ,
    quotientMap.{uF, uV, uJ, uX} T B A hA hT t ht σ eσ J q hq,
    quotientMap_surjective T B A hA hT t ht σ eσ J q hq⟩

include eσ in
/-- Existential form: if some surjective intertwiner from the original twisted
induction onto an irreducible `J` exists, then the lift of `J`, for any proof of
its smoothness, is a weak Langlands quotient of the lifted datum. -/
theorem isLanglandsQuotient_quotientLift_of_exists
    (hJs : letI := T.topology; IsSmooth J.ρ)
    (hJ : letI := T.topology; Representation.IsIrreducible J.ρ)
    (h : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ∃ q : (T.normalizedParabolicInduced B (T.leviRealPowerTwist B t σ.ρ)).IntertwiningMap J.ρ,
        Function.Surjective q) :
    (liftedDatum.{uF, uV, uJ, uX} T B A hA hT t ht).IsLanglandsQuotient
      (quotientLift.{uF, uV, uJ, uX} T J hJs) := by
  obtain ⟨q, hq⟩ := h
  exact isLanglandsQuotient_quotientLift T B A hA hT t ht σ eσ J q hq hJ

end Quotient

end Langlands.WholeLeviQuotientUniverse
