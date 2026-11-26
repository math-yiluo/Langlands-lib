import Langlands.BaseChange.TwistedPaleyWiener
import Langlands.LocalField.CharZeroPadicRealization
import Langlands.Representation.Classification.ConstituentAutomorphismTransport
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.Classification.RegularLanglandsDataUniquenessProof
import Langlands.Representation.Classification.RegularLanglandsExhaustionProof

/-! # Stable Langlands data for an irreducible σ-stable representation -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe u v z

section Continuous

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E]

/-- The entrywise action as a continuous multiplicative equivalence. -/
def entrywiseContinuousAut (σ : E ≃ₐ[F] E) (n : ℕ) :
    GeneralLinear n E ≃ₜ* GeneralLinear n E where
  toMulEquiv := entrywiseAut σ n
  continuous_toFun := continuous_entrywiseAut_of_isModuleTopology σ n
  continuous_invFun := continuous_entrywiseAut_of_isModuleTopology σ.symm n

end Continuous

section Padic

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)
  (hModule : letI := T.topology; IsModuleTopology F E.Carrier)
  (σ : E.Carrier ≃ₐ[F] E.Carrier)

include hModule

/-- Entrywise field automorphisms preserve the determinant power characters. -/
theorem determinantPowerCharacter_entrywiseAut (n : ℕ) (s : ℝ) (g : GeneralLinear n E.Carrier) :
    T.determinantPowerCharacter n s (entrywiseAut σ n g) = T.determinantPowerCharacter n s g := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  have h : T.determinantNorm n (entrywiseAut σ n g) = T.determinantNorm n g :=
    determinantNorm_entrywiseAut σ n g
  exact congrArg (positiveUnitsToComplex.comp (Units.map (NNReal.rpowMonoidHom s))) h

/-- Pullback of a normalized product is the normalized product of the pullbacks.
This uses the section transport along the entrywise field automorphism. -/
def normalizedProductEntrywisePullbackEquiv {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type z} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) E.Carrier) (V i)) :
    Representation.Equiv
      (T.normalizedProductInduced B (fun i => (ρ i).comp (entrywiseAut σ (B.size i)).toMonoidHom))
      ((T.normalizedProductInduced B ρ).comp (entrywiseAut σ n).toMonoidHom) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  let ρ' := fun i => (ρ i).comp (entrywiseAut σ (B.size i)).toMonoidHom
  have hTensor : B.blockTensor ρ' = (B.blockTensor ρ).comp (leviAut σ B).toMonoidHom := by
    apply MonoidHom.ext
    intro m
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    change B.blockTensor ρ' m (PiTensorProduct.tprod ℂ w) =
      B.blockTensor ρ (leviAut σ B m) (PiTensorProduct.tprod ℂ w)
    rw [BlockShape.blockTensor_tprod, BlockShape.blockTensor_tprod]
    rfl
  refine Induction.transportSmoothEquiv (B.parabolic E.Carrier) (entrywiseAut σ n)
    (continuous_entrywiseAut σ n) (continuous_entrywiseAut_symm σ n)
    (parabolicAut σ B) (fun _ => rfl) (LinearEquiv.refl ℂ (PiTensorProduct ℂ V)) ?_
  intro q w
  have hMod : T.parabolicHalfModulus B (parabolicAut σ B q) = T.parabolicHalfModulus B q :=
    parabolicHalfModulus_parabolicAut σ B q
  change (T.parabolicHalfModulus B q : ℂ) • B.blockTensor ρ' (B.leviProjection E.Carrier q) w =
    (T.parabolicHalfModulus B (parabolicAut σ B q) : ℂ) •
      B.blockTensor ρ (B.leviProjection E.Carrier (parabolicAut σ B q)) w
  rw [hMod, hTensor, leviProjection_parabolicAut]
  rfl

/-- Pull back every tempered block along the field automorphism, retaining
the ordered block shape and real exponents. -/
def entrywisePullbackLanglandsDatum {n : ℕ} (d : T.TemperedLanglandsDatum.{z} n) :
    T.TemperedLanglandsDatum.{z} n := by
  let := T.topology
  let := T.localField
  let := T.valuativeRel
  let := hModule
  let a (i : Fin d.shape.length) := entrywiseContinuousAut σ (d.shape.size i)
  exact
    { shape := d.shape
      blocks := fun i => SmoothRep.pullback (a i) (d.blocks i)
      irreducible := fun i =>
        (isIrreducible_comp_continuousMulEquiv_iff _ (a i)).mpr (d.irreducible i)
      tempered := fun i => T.isTempered_comp_continuousMulEquiv _ (a i) (d.tempered i)
      exponent := d.exponent
      strictAnti := d.strictAnti }

omit hModule in
private def productEntrywisePullbackBundledEquiv {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type z} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) E.Carrier) (V i))
    (hρ : letI := T.topology; ∀ i, IsSmooth (ρ i))
    (hτ : letI := T.topology; ∀ i, IsSmooth (τ i))
    (e : Representation.Equiv (T.normalizedProductInduced B ρ)
      ((T.normalizedProductInduced B τ).comp (entrywiseAut σ n).toMonoidHom)) :
    letI := T.topology
    Representation.Equiv
      (((T.normalizedProductInductionFunctor B).obj
        (fun i => SmoothRep.of (ρ i) (hρ i))).representation)
      (((T.normalizedProductInductionFunctor B).obj
        (fun i => SmoothRep.of (τ i) (hτ i))).representation.comp
          (entrywiseAut σ n).toMonoidHom) := e

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The standard module of the pulled-back data is the pullback of the original
standard module, using the invariance of the real determinant characters. -/
def entrywisePullbackStandardModuleEquiv {n : ℕ} (d : T.TemperedLanglandsDatum.{z} n) :
    letI := T.topology
    Representation.Equiv
      (entrywisePullbackLanglandsDatum T hModule σ d).standardModule.representation
      (d.standardModule.representation.comp (entrywiseAut σ n).toMonoidHom) := by
  let := T.topology
  let d' := entrywisePullbackLanglandsDatum T hModule σ d
  let θ (i : Fin d.shape.length) := (entrywiseAut σ (d.shape.size i)).toMonoidHom
  let χ (i : Fin d.shape.length) := T.determinantPowerCharacter (d.shape.size i) (d.exponent i)
  let π (i : Fin d.shape.length) := twist (χ i) (d.blocks i).representation
  let π' (i : Fin d.shape.length) := twist (χ i) ((d.blocks i).representation.comp (θ i))
  have h (i : Fin d.shape.length) :
      π' i = (π i).comp (θ i) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro x
    change (T.determinantPowerCharacter (d.shape.size i) (d.exponent i) g : ℂ) •
      (d.blocks i).representation (entrywiseAut σ (d.shape.size i) g) x =
      (T.determinantPowerCharacter (d.shape.size i) (d.exponent i)
        (entrywiseAut σ (d.shape.size i) g) : ℂ) •
        (d.blocks i).representation (entrywiseAut σ (d.shape.size i) g) x
    rw [determinantPowerCharacter_entrywiseAut T hModule σ (d.shape.size i) (d.exponent i) g]
  let S (ξ : ∀ i, Representation ℂ (GeneralLinear (d.shape.size i) E.Carrier) (d.blocks i)) :=
    Representation.Equiv (T.normalizedProductInduced d.shape ξ)
      ((T.normalizedProductInduced d.shape π).comp (entrywiseAut σ n).toMonoidHom)
  have eraw : S π' := Eq.mpr (congrArg S (funext h))
    (normalizedProductEntrywisePullbackEquiv T hModule σ d.shape π)
  have hπ (i : Fin d.shape.length) : IsSmooth (π i) :=
    (T.twistedBlocks d.shape d.blocks d.exponent i).isSmooth
  have hπ' (i : Fin d.shape.length) : IsSmooth (π' i) :=
    (T.twistedBlocks d'.shape d'.blocks d'.exponent i).isSmooth
  let e := productEntrywisePullbackBundledEquiv T σ d.shape π' π hπ' hπ eraw
  have hsource : (T.normalizedProductInductionFunctor d.shape).obj
      (fun i => SmoothRep.of (π' i) (hπ' i)) = d'.standardModule := by
    apply congrArg (T.normalizedProductInductionFunctor d.shape).obj
    rfl
  have htarget : (T.normalizedProductInductionFunctor d.shape).obj
      (fun i => SmoothRep.of (π i) (hπ i)) = d.standardModule := by
    apply congrArg (T.normalizedProductInductionFunctor d.shape).obj
    rfl
  let comparison (A B : SmoothRep.{0,v,max v z} ℂ (GeneralLinear n E.Carrier)) :=
    Representation.Equiv A.representation
      (B.representation.comp (entrywiseAut σ n).toMonoidHom)
  exact Eq.mp (congrArg₂ comparison hsource htarget) e

end Padic

/-- An irreducible admissible σ-stable representation of positive-rank GL
has ordered tempered Langlands head data with each block σ-stable. -/
def SigmaStableTemperedLanglandsHeadStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
    (E : PadicField.{v} p) [Algebra F E.Carrier] (T : E.TopologicalData),
    (letI := T.topology; IsModuleTopology F E.Carrier) →
    ∀ (σ : E.Carrier ≃ₐ[F] E.Carrier) (n : ℕ), 0 < n →
      letI := T.topology
      ∀ (π : SmoothRep.{0,v,max v z} ℂ (GeneralLinear n E.Carrier)),
        π.representation.IsIrreducible → π.IsAdmissible →
        IsSigmaStable σ n π.representation →
        ∃ d : T.TemperedLanglandsDatum.{max v z} n, d.IsLanglandsHead π ∧
          ∀ i, IsSigmaStable σ (d.shape.size i) (d.blocks i).representation

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordered tempered Langlands data of a stable irreducible admissible
representation have stable blocks, so their standard module has an induced
twisting isomorphism. -/
theorem exists_sigmaStable_temperedLanglandsHead :
    SigmaStableTemperedLanglandsHeadStatement.{u,v,z} := by
  intro F _ _ p _ E _ T hModule σ n hn
  let := T.topology
  let := T.localField
  let := T.valuativeRel
  let := hModule
  intro π hπ hAdm ⟨A⟩
  obtain ⟨d, hd⟩ := glRegularLanglandsExhaustion.{v,z} p E T n hn π hπ hAdm
  refine ⟨d, hd, ?_⟩
  let d' := entrywisePullbackLanglandsDatum T hModule σ d
  let π' := SmoothRep.pullback (entrywiseContinuousAut σ n) π
  have hd' : d'.IsLanglandsHead π' :=
    (hd.comp_mulEquiv (entrywiseAut σ n)).of_equiv
      (entrywisePullbackStandardModuleEquiv T hModule σ d).symm
  let e : π ≅ π' := SmoothRep.mkIso A
  obtain ⟨a, ha, hb⟩ := glRegularLanglandsDataUniqueness.{v,z} p E T n hn d d' π π'
    hd.isLanglandsQuotient hd'.isLanglandsQuotient ⟨e⟩
  change Fin d.shape.length ≃o Fin d.shape.length at a
  have he : a = OrderIso.refl _ := Subsingleton.elim _ _
  subst a
  intro i
  obtain ⟨eᵢ⟩ := (hb i).2
  exact ⟨SmoothRep.equivOfIso eᵢ⟩

section CharZero

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [CharZero E] [IsModuleTopology F E]

/-- Use the same result over a characteristic-zero local field with its
specified topology, via the Library's realization as a p-adic field. -/
theorem exists_sigmaStable_temperedLanglandsHead_of_charZero
    (σ : E ≃ₐ[F] E) {n : ℕ} (hn : 0 < n)
    (π : SmoothRep.{0,v,max v z} ℂ (GeneralLinear n E))
    (hπ : π.representation.IsIrreducible) (hAdm : π.IsAdmissible)
    (hσ : IsSigmaStable σ n π.representation) :
    letI : TopologicalSpace (CharZeroLocalField.padicField E).Carrier := ‹TopologicalSpace E›
    ∃ d : (CharZeroLocalField.topologicalData E).TemperedLanglandsDatum.{max v z} n,
      d.IsLanglandsHead π ∧ ∀ i, IsSigmaStable σ (d.shape.size i) (d.blocks i).representation := by
  let : Algebra F (CharZeroLocalField.padicField E).Carrier := ‹Algebra F E›
  exact exists_sigmaStable_temperedLanglandsHead.{u,v,z} F (CharZeroLocalField.residueChar E)
    (CharZeroLocalField.padicField E) (CharZeroLocalField.topologicalData E)
    (inferInstanceAs (IsModuleTopology F E)) σ n hn π hπ hAdm hσ

end CharZero

end Langlands.BaseChange
