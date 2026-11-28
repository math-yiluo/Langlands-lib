import Langlands.TraceFormula.SigmaDiscreteTwistedGlobalizationStatement
import Langlands.TraceFormula.SigmaEllipticTwistedTraceGlobalizationStatement
import Langlands.BaseChange.GenericSigmaEllipticDiscreteStatement
import Langlands.BaseChange.TwistedCuspidalPseudoCoefficientExistenceStatement
import Langlands.BaseChange.CyclicGlobalizationPlaceComparison
import Langlands.BaseChange.AutomorphicObjectFieldPullback
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.Automorphic.CuspidalUnitaryLocalGenericity
import Langlands.Automorphic.CuspidalPresentationUniverse
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof

/-!
# The twisted globalization of a σ-discrete series: a reduction

The module proves that `SigmaDiscreteTwistedGlobalizationStatement` (Henniart–Lemaire 2011,
II.6.16; Arthur–Clozel 1989, Chapter 1, §6.3 (b)) follows from three statements:

* `SigmaEllipticTwistedTraceGlobalizationStatement`, the global trace-formula step: a test
  function at `v` whose σ-orbital integrals vanish off the σ-elliptic set and whose twisted
  trace on some representation with central character `χ` is nonzero is seen by a σ-stable
  unitary cusp, supercuspidal above `v₁` and `v₂`, with central character `χ` at `w`;
* `TwistedCuspidalPseudoCoefficientExistenceStatement` (Henniart–Lemaire 2011, II.5.13 and
  II.5.14, Proposition 2), applied to the cyclic algebra `F_v ⊗_F E` over `F_v`;
* `GenericSigmaEllipticDiscreteStatement` (Henniart–Lemaire 2011, II.5.8 and II.5.15,
  Proposition 1), applied to the same algebra.

The pseudo-coefficient of the given σ-discrete series `ρ` is the test function at `v`; the
component at `w` of the cusp is generic and has nonzero twisted trace at it, hence is a
σ-discrete series, and the separation property of the pseudo-coefficient makes it isomorphic
to `ρ` (Henniart–Lemaire 2011, II.6.16, printed p. 132).

Auxiliary results: the base change `K ⊗_F E` of a cyclic separable algebra along a field
extension `K/F` is cyclic for `id ⊗ σ` (`isCyclicAlgebra_tensorCongr`); genericity is carried
along a bicontinuous ring isomorphism (`isGeneric_of_ringEquiv`); a tempered representation
has a unitary central character (`IsTemperedRep.nonempty_unitaryCentralCharacter`); and a
commutative ring satisfying `IsField` carries a field structure extending its given ring
structure (`fieldOfIsField`). See the paired Markdown.
-/

noncomputable section

universe uF uE uR uW

open NumberField IsDedekindDomain MeasureTheory
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic Langlands.BaseChange Langlands.HarmonicAnalysis
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.TraceFormula

/-! ## The base change of a cyclic algebra -/

section Cyclic

variable {F : Type*} {E : Type*} {K : Type*} [Field F] [Field E] [Algebra F E] [Field K]
  [Algebra F K]

/-- `τ ↦ id ⊗ τ` as a group homomorphism `Aut(E/F) →* Aut_K(K ⊗_F E)`. -/
def tensorCongrHom : (E ≃ₐ[F] E) →* (K ⊗[F] E ≃ₐ[K] K ⊗[F] E) where
  toFun τ := Algebra.TensorProduct.congr AlgEquiv.refl τ
  map_one' := Algebra.TensorProduct.congr_refl
  map_mul' σ τ := by
    change Algebra.TensorProduct.congr (AlgEquiv.refl.trans AlgEquiv.refl) (τ.trans σ) =
      (Algebra.TensorProduct.congr AlgEquiv.refl τ).trans
        (Algebra.TensorProduct.congr AlgEquiv.refl σ)
    exact Algebra.TensorProduct.congr_trans _ _ _ _

theorem tensorCongrHom_injective :
    Function.Injective (tensorCongrHom (F := F) (E := E) (K := K)) := by
  intro σ τ h
  ext y
  have hy := congrArg (fun ρ : K ⊗[F] E ≃ₐ[K] K ⊗[F] E => ρ ((1 : K) ⊗ₜ[F] y)) h
  change (1 : K) ⊗ₜ[F] σ y = (1 : K) ⊗ₜ[F] τ y at hy
  exact Algebra.TensorProduct.includeRight_injective (A := K)
    (algebraMap F K).injective hy

/-- If `σ` presents `E/F` as a cyclic algebra of degree `l` and `E/F` is separable, then
`id ⊗ σ` presents `K ⊗_F E` as a cyclic `K`-algebra of degree `l`, for every field
extension `K` of `F`. -/
theorem isCyclicAlgebra_tensorCongr [Algebra.IsSeparable F E] (σ : E ≃ₐ[F] E) (l : ℕ)
    (h : IsCyclicAlgebra σ l) :
    IsCyclicAlgebra (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) σ) l := by
  obtain ⟨hfin, hrank, -, hord, hfix⟩ := h
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Module.finrank_baseChange, hrank]
  · have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
    exact Algebra.FormallyUnramified.isReduced_of_field K _
  · rw [← hord]
    exact orderOf_injective _ (tensorCongrHom_injective (K := K)) σ
  · intro x hx
    let f : F →ₗ[F] E := Algebra.linearMap F E
    let g : E →ₗ[F] E := σ.toLinearMap - LinearMap.id
    have hexact : Function.Exact f g := by
      intro y
      constructor
      · intro hy
        have : σ y = y := sub_eq_zero.mp hy
        obtain ⟨c, rfl⟩ := hfix y this
        exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩
        change σ (algebraMap F E c) - algebraMap F E c = 0
        rw [AlgEquiv.commutes, sub_self]
    have hexact' := Module.Flat.lTensor_exact K hexact
    have hσ : ∀ z : K ⊗[F] E, σ.toLinearMap.lTensor K z =
        (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) σ z : K ⊗[F] E) := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b => rfl
      | add z w hz hw =>
        rw [map_add, hz, hw]
        exact (map_add (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) σ) z w).symm
    have hlin : ∀ z : K ⊗[F] E, g.lTensor K z = σ.toLinearMap.lTensor K z - z := by
      intro z
      rw [LinearMap.lTensor_sub, LinearMap.lTensor_id, LinearMap.sub_apply, LinearMap.id_apply]
    have hkey : ∀ y : K ⊗[F] F, f.lTensor K y =
        (algebraMap K (K ⊗[F] E) (TensorProduct.rid F K y) : K ⊗[F] E) := by
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul a b =>
        rw [TensorProduct.rid_tmul, LinearMap.lTensor_tmul]
        change a ⊗ₜ[F] algebraMap F E b = (b • a) ⊗ₜ[F] (1 : E)
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      | add z w hz hw => rw [map_add, hz, hw, map_add, map_add]
    have hg : g.lTensor K x = 0 := (hlin x).trans (sub_eq_zero.mpr ((hσ x).trans hx))
    obtain ⟨y, hy⟩ := (hexact' x).mp hg
    exact ⟨_, (hkey y).symm.trans hy⟩

end Cyclic

/-! ## Genericity along a bicontinuous ring isomorphism -/

section Generic

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
  [TopologicalSpace S]

private theorem generalLinearRingEquiv_mem_upperUnipotent_iff (e : R ≃+* S)
    (he : Continuous e) (he' : Continuous e.symm) (r : ℕ) (g : GeneralLinear (r + 1) R) :
    generalLinearRingEquiv e he he' g ∈ GeneralLinear.upperUnipotent (r + 1) S ↔
      g ∈ GeneralLinear.upperUnipotent (r + 1) R := by
  change ((generalLinearRingEquiv e he he' g).val.IsUpperTriangular ∧
      ∀ i, generalLinearRingEquiv e he he' g i i = 1) ↔
    (g.val.IsUpperTriangular ∧ ∀ i, g i i = 1)
  simp only [generalLinearRingEquiv_apply_apply]
  constructor
  · rintro ⟨hT, hD⟩
    refine ⟨fun i j hij => e.injective ?_, fun i => e.injective ?_⟩
    · simpa using hT hij
    · simpa using hD i
  · rintro ⟨hT, hD⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · change e (g i j) = 0
      rw [show g i j = 0 from hT hij, map_zero]
    · rw [hD i, map_one]

/-- Genericity is carried along a bicontinuous ring isomorphism `e : R ≃+* S`: if `π` is
generic for `ψ`, then the pullback of `π` through the entrywise isomorphism
`GL_{r+1}(R) ≃ GL_{r+1}(S)` is generic for `ψ ∘ e`. -/
theorem isGeneric_of_ringEquiv (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm)
    {r : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) S) V)
    (π' : Representation ℂ (GeneralLinear (r + 1) R) V)
    (hπ' : ∀ g, π' g = π (generalLinearRingEquiv e he he' g))
    (ψ : UnitaryAdditiveCharacter S) (h : Whittaker.IsGeneric ψ r π) :
    Whittaker.IsGeneric (ψ.comapSurjective e.toAddMonoidHom he e.surjective) r π' := by
  let κ := generalLinearRingEquiv (n := r + 1) e he he'
  have hEq : π' = π.comp κ.toMulEquiv.toMonoidHom := MonoidHom.ext hπ'
  subst hEq
  obtain ⟨hI, hA, ℓ, hℓ⟩ := h
  refine ⟨(isIrreducible_comp_continuousMulEquiv_iff π κ).mpr hI,
    (isAdmissible_comp_continuousMulEquiv_iff π κ).mpr hA, ?_⟩
  have hN := generalLinearRingEquiv_mem_upperUnipotent_iff e he he' r
  have hθ (u : GeneralLinear.upperUnipotent (r + 1) R) :
      Whittaker.standardCharacter ψ r ⟨κ u, (hN u).2 u.2⟩ =
        Whittaker.standardCharacter (ψ.comapSurjective e.toAddMonoidHom he e.surjective) r u := by
    apply Units.ext
    have h1 : (∑ i : Fin r, (κ u.val) i.castSucc i.succ) =
        e (∑ i : Fin r, u.val i.castSucc i.succ) := by
      rw [map_sum]
      rfl
    exact congrArg (fun x : S => ((ψ x : Circle) : ℂ)) h1
  have hfun := Whittaker.functionals_comp κ.toMulEquiv hN hθ π
  exact ⟨⟨ℓ.val, (congrArg (fun T => ℓ.val ∈ T) hfun).mpr ℓ.property⟩, hℓ⟩

end Generic

/-! ## The central character of a tempered representation -/

section Tempered

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A tempered representation of a locally compact group has a unitary central character. -/
theorem IsTemperedRep.nonempty_unitaryCentralCharacter {ρ : Representation ℂ G V}
    (h : IsTemperedRep ρ) : Nonempty (UnitaryCentralCharacter ρ) := by
  let _ : MeasurableSpace (G ⧸ Subgroup.center G) := borel _
  have _ : BorelSpace (G ⧸ Subgroup.center G) := ⟨rfl⟩
  obtain ⟨-, c, -⟩ := h (Measure.haarMeasure (Classical.arbitrary _))
  exact ⟨c⟩

end Tempered

/-! ## A field structure extending a given commutative ring structure -/

/-- The field structure on a commutative ring `R` satisfying `IsField R`, built so that its
underlying commutative ring is the given instance (unlike `IsField.toField`, which starts from
the ring structure only). -/
noncomputable abbrev fieldOfIsField {R : Type*} [inst : CommRing R] (h : IsField R) : Field R :=
  { inst, h.toSemifield with
    qsmul := _
    qsmul_def := fun _ _ => rfl }

theorem fieldOfIsField_toCommRing {R : Type*} [inst : CommRing R] (h : IsField R) :
    (fieldOfIsField h).toCommRing = inst := by
  with_reducible_and_instances rfl

/-! ## The reduction -/

local instance sigmaDiscreteReductionRationalAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance sigmaDiscreteReductionContinuousAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance sigmaDiscreteReductionSmoothAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance sigmaDiscreteReductionFormsAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance sigmaDiscreteReductionLocalSpaceAddCommGroup {F : Type*} [Field F]
    [NumberField F] {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- **Reduction of the twisted globalization of a σ-discrete series.** The twisted
globalization `SigmaDiscreteTwistedGlobalizationStatement` follows from

* the global trace-formula step `SigmaEllipticTwistedTraceGlobalizationStatement` (a σ-stable
  unitary cusp, supercuspidal above `v₁` and `v₂`, whose component at `w` has central
  character `χ` and nonzero twisted trace at a test function with σ-orbital integrals
  supported on the σ-elliptic set),
* the existence of twisted pseudo-coefficients of σ-discrete series
  `TwistedCuspidalPseudoCoefficientExistenceStatement` (Henniart–Lemaire 2011, II.5.13), and
* `GenericSigmaEllipticDiscreteStatement` (a generic σ-stable representation with unitary
  central character and nonzero twisted trace at such a test function is a σ-discrete series),

the last two applied to the cyclic algebra `F_v ⊗_F E` over `F_v`, which is a field because
there is only one place of `E` above `v`. -/
def SigmaDiscreteTwistedGlobalizationReductionStatement : Prop :=
  SigmaEllipticTwistedTraceGlobalizationStatement.{uF, uE, uR, uW} →
    TwistedCuspidalPseudoCoefficientExistenceStatement.{uF, max uF uE, uR} →
    GenericSigmaEllipticDiscreteStatement.{uF, max uF uE, uE} →
    SigmaDiscreteTwistedGlobalizationStatement.{uF, uE, uR, uW}

set_option maxHeartbeats 1600000 in
/-- The three statements of `SigmaDiscreteTwistedGlobalizationReductionStatement` imply the
twisted globalization of a σ-discrete series. -/
theorem sigmaDiscreteTwistedGlobalizationReduction :
    SigmaDiscreteTwistedGlobalizationReductionStatement.{uF, uE, uR, uW} := by
  intro hG hPC hGSED F E _ _ _ _ _ _ _ σ l hcyc hinf v w hw v₁ v₂ v₃ h12 h13 h23 h1v h2v h3v
    hs1 hs2 hs3 r
  let : TopologicalSpace (v.adicCompletion F ⊗[F] E) :=
    moduleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)
  have : IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (v.adicCompletion F ⊗[F] E) :=
    IsModuleTopology.isTopologicalRing (v.adicCompletion F) _
  intro σv W _ _ ρ hρ
  have hρ' := hρ
  obtain ⟨hadm, hirr, htemp, ⟨A⟩, -⟩ := hρ'
  let e := tensorUniqueCompletion v w hw
  let : Field (v.adicCompletion F ⊗[F] E) :=
    fieldOfIsField (e.toRingEquiv.toMulEquiv.isField (Field.toIsField _))
  let : ValuativeRel (v.adicCompletion F) := (CompletionPadic.topologicalData v).valuativeRel
  have : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    (CompletionPadic.topologicalData v).localField
  have : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have : Algebra.IsSeparable F E := inferInstance
  have hcycv : IsCyclicAlgebra σv l := isCyclicAlgebra_tensorCongr σ l hcyc
  have : Module.Finite (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := hcycv.1
  have := generalLinear_t2Space_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  have := generalLinear_locallyCompactSpace_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  have := generalLinear_totallyDisconnectedSpace_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  let : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) := borel _
  have : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) := ⟨rfl⟩
  obtain ⟨c⟩ := IsTemperedRep.nonempty_unitaryCentralCharacter htemp
  let χ := c.character
  have hχ : HasCentralCharacterRep ρ χ := c.acts
  let μ : Measure (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) :=
    Measure.haarMeasure (Classical.arbitrary _)
  have hμ : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  obtain ⟨φ, hpc, -, hell, -⟩ := hPC (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) σv l
    hcycv (r + 1) (Nat.succ_pos r) W ρ hadm hρ χ hχ A μ
  obtain ⟨T, P, hU, hstab, hsc1, hsc2, hI, hA, hχP, hP, A', htr⟩ :=
    hG F E σ l hcyc hinf v w hw v₁ v₂ v₃ h12 h13 h23 h1v h2v h3v hs1 hs2 hs3 r χ
      c.norm_eq_one μ φ hell W ρ hadm hirr hχ A (by rw [hpc.2.1]; exact one_ne_zero)
  refine ⟨T, P, hU, hstab, hsc1, hsc2, hI, hA, ?_⟩
  obtain ⟨he, he'⟩ := tensorUniqueCompletion_bicontinuous v w hw
  obtain ⟨ψ, hgen⟩ := P.exists_generic_at_completion hU w.1 hI hA
  let κ : GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E) →* FiniteLocalGL E (r + 1) w.1 :=
    Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun q : FinitePlacesAbove E v => q.1.adicCompletion E) w).comp
        (finiteTensorMap v).toRingHom)
  let PiV := (P.localComponent w.1).representation.comp κ
  have hgenD := isGeneric_of_ringEquiv e.toRingEquiv he he'
    (P.localComponent w.1).representation PiV (fun _ => rfl) ψ hgen
  have hds := hGSED (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) σv l r hcycv PiV hP _
    hgenD χ hχP c.norm_eq_one A' μ φ hell htr
  obtain ⟨σ', -, ⟨f⟩⟩ := exists_small_finiteLocalFactor.{uE, uE, uR} (r + 1) w.1
    (P.localComponent w.1).smoothRepresentation hI
  let τ' := σ'.representation.comp κ
  let fτ : Representation.Equiv PiV τ' := Representation.Equiv.mk f.toLinearEquiv
    (fun g => f.toIntertwiningMap.isIntertwining' (κ g))
  by_contra hne
  have hne' : IsEmpty (Representation.Equiv τ' ρ) := ⟨fun g => hne ⟨fτ.trans g⟩⟩
  have h0 := hpc.2.2 _ τ' (isAdmissible_of_equiv fτ hP)
    ((isIrreducible_iff_of_equiv fτ).mp hds.2.1) ((isTemperedRep_iff_of_equiv fτ).mp hds.2.2.1)
    (hχP.of_equiv fτ) hne' (A'.transport fτ)
  have heq := twistedDistribution_eq_of_equivalent μ hP (isAdmissible_of_equiv fτ hP) fτ
    A'.toLinearMap
  exact htr ((LinearMap.congr_fun heq φ).symm.trans h0)

end Langlands.TraceFormula
