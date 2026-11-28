import Langlands.BaseChange.TwistedCharacter.UnramifiedTraceFamily
import Langlands.BaseChange.TwistedCharacter.GLInducedTest
import Langlands.BaseChange.TwistedCharacter.GeneralLinearUnimodular
import Langlands.BaseChange.ExternalTensorTwistedCharacter
import Langlands.HarmonicAnalysis.SchwartzBruhatPiTensor
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.BaseChange.TwistedCharacter.ExternalSlotExpansion

/-! # Unramified families of normalized inductions of induced blocks -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear Geometric HarmonicAnalysis MeasureTheory

universe u v w

section Nested

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) {r : ℕ}
  (g : ∀ i, Fin (S i).length → Fin r)
  {V : ∀ i, Fin (S i).length → Type w} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module ℂ (V i j)]
  (R : ∀ i j, Representation ℂ (GeneralLinear ((S i).size j) E) (V i j))
  (A : ∀ i j, SigmaIntertwiner σ ((S i).size j) (R i j))

/-- The normalizing half modulus of an inner block shape. -/
abbrev innerHalfModulus (i : Fin B.length) : (S i).Levi E →* ℂˣ :=
  (LocalFieldData.ofInstances E).leviHalfModulus (S i)

theorem isOpen_ker_innerHalfModulus (i : Fin B.length) :
    IsOpen ((innerHalfModulus (E := E) B S i).ker : Set ((S i).Levi E)) :=
  (LocalFieldData.ofInstances E).isOpen_ker_leviHalfModulus (S i)

/-- The inner representation of the nested family in block `i`: the unnormalized induction of
the unramified twist of the normalized inducing representation of the inner blocks. -/
abbrev nestedInnerRep (z : Fin r → ℂˣ) (i : Fin B.length) :=
  Induction.smoothInduced ((S i).parabolic E)
    ((twist (leviUnramified E (S i) (g i) z)
      (familyInducing (S i) (R i) (innerHalfModulus B S i))).comp ((S i).leviProjection E))

/-- The induced σ-intertwiner of the inner representation in block `i`. -/
abbrev nestedInnerIntertwiner (z : Fin r → ℂˣ) (i : Fin B.length) :
    SigmaIntertwiner σ (B.size i) (nestedInnerRep B S g R z i) :=
  TwistedPaleyWiener.inducedSigmaIntertwiner σ (S i)
    (twist (leviUnramified E (S i) (g i) z)
      (familyInducing (S i) (R i) (innerHalfModulus B S i)))
    (twistTwistedIntertwiner (leviAut σ (S i)) (leviUnramified E (S i) (g i) z)
      (leviUnramified_leviAut E (S i) (g i) σ z)
      (familyInducingIntertwiner σ (S i) (R i) (A i) (innerHalfModulus B S i)
        (leviHalfModulus_leviAut σ (S i))))

/-- The normalized parabolic induction of an admissible Levi representation is admissible. -/
theorem isAdmissible_normalizedParabolicInduced {X : Type w} [AddCommGroup X] [Module ℂ X]
    (Ξ : Representation ℂ (B.Levi E) X) (hΞ : IsAdmissible Ξ) :
    IsAdmissible ((LocalFieldData.ofInstances E).normalizedParabolicInduced B Ξ) := by
  let T := LocalFieldData.ofInstances E
  let : CompactSpace (Induction.LeftQuotient (B.parabolic E)) :=
    AllField.Parabolic.parabolicQuotientCompact E T B
  have hX : IsAdmissible (twist (T.leviHalfModulus B) Ξ) :=
    (isAdmissible_twist_iff _ _ (T.isOpen_ker_leviHalfModulus B)).mpr hΞ
  exact Induction.smoothInduced_isAdmissible_of_compactSpace _ _
    ((AllField.Parabolic.leviInflationAdmissibility E T B _ _).mpr hX)

theorem isAdmissible_nestedInnerRep (hR : ∀ i j, IsAdmissible (R i j)) (z : Fin r → ℂˣ)
    (i : Fin B.length) : IsAdmissible (nestedInnerRep B S g R z i) :=
  isAdmissible_familyInduced (S i) (g i) (R i) (innerHalfModulus B S i)
    (isOpen_ker_innerHalfModulus B S i) (hR i) z

theorem isAdmissible_nestedRep (hR : ∀ i j, IsAdmissible (R i j)) (z : Fin r → ℂˣ) :
    IsAdmissible ((LocalFieldData.ofInstances E).normalizedParabolicInduced B
      (B.blockTensor (nestedInnerRep B S g R z))) :=
  isAdmissible_normalizedParabolicInduced B _
    (FiniteTensor.isAdmissible_external _ (isAdmissible_nestedInnerRep B S g R hR z))

variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  (μ : Measure (GeneralLinear n E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- The nested family: the twisted trace of the normalized induction from the outer blocks of
the inner unramified families, with all intertwiners induced from the block intertwiners. -/
def nestedTrace (hR : ∀ i j, IsAdmissible (R i j)) (z : Fin r → ℂˣ) :
    Distribution (GeneralLinear n E) :=
  twistedDistribution μ _ (isAdmissible_nestedRep B S g R hR z)
    (normalizedParabolicSigmaIntertwiner σ B (B.blockTensor (nestedInnerRep B S g R z))
      (leviTensorIntertwiner σ B (nestedInnerIntertwiner σ B S g R A z))).toLinearMap

set_option maxHeartbeats 1600000 in
/-- Every test function evaluates the nested family to a Laurent polynomial. -/
theorem nestedTrace_regular {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1)
    (hR : ∀ i j, IsAdmissible (R i j)) (hirr : ∀ i j, (R i j).IsIrreducible)
    (f : SchwartzBruhat (GeneralLinear n E)) :
    ∃ q : AddMonoidAlgebra ℂ (Fin r → ℤ), ∀ z,
      nestedTrace σ B S g R A μ hR z f = Plancherel.finiteLaurentEvaluation z q := by
  classical
  let H (i : Fin B.length) := GeneralLinear (B.size i) E
  let _ (i : Fin B.length) : MeasurableSpace (H i) := borel _
  have _ (i : Fin B.length) : BorelSpace (H i) := ⟨rfl⟩
  let _ (i : Fin B.length) : T2Space (H i) := LocalFieldTopology.generalLinear_t2Space E _
  let _ (i : Fin B.length) : LocallyCompactSpace (H i) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace E _
  let _ (i : Fin B.length) : TotallyDisconnectedSpace (H i) :=
    LocalFieldTopology.generalLinear_totallyDisconnectedSpace E _
  let _ (i : Fin B.length) : SecondCountableTopology (H i) :=
    LocalFieldTopology.generalLinear_secondCountableTopology E _
  let μi (i : Fin B.length) : Measure (H i) := Measure.haar
  have _ (i : Fin B.length) : (μi i).IsMulRightInvariant :=
    generalLinear_isMulRightInvariant E _ (μi i)
  let ν : Measure (B.Levi E) := Measure.pi μi
  let κB := (LocalFieldData.ofInstances E).leviHalfModulus B
  have hκB : IsOpen (κB.ker : Set (B.Levi E)) :=
    (LocalFieldData.ofInstances E).isOpen_ker_leviHalfModulus B
  obtain ⟨fM, hfM⟩ := sigmaInducedTest.{u,v,max v w} σ B μ ν hd hσ f
  let f' := characterMultiplyTest κB hκB fM
  have hspan : f' ∈ Submodule.span ℂ (Set.range (SchwartzBruhat.piTensor (X := H))) := by
    rw [SchwartzBruhat.span_piTensor]
    trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
  choose q hq using fun (i : Fin B.length) (φ : SchwartzBruhat (H i)) =>
    unramifiedFamilyTrace_regular σ (S i) (g i) (R i) (A i) (innerHalfModulus B S i)
      (isOpen_ker_innerHalfModulus B S i) (leviHalfModulus_leviAut σ (S i)) (μi i) hd hσ
      (hR i) (hirr i) φ
  refine ⟨c.sum (fun φ a => a • ∏ i, q i (φ i)), fun z => ?_⟩
  let Ξ := B.blockTensor (nestedInnerRep B S g R z)
  have hΞ : IsAdmissible Ξ :=
    FiniteTensor.isAdmissible_external _ (isAdmissible_nestedInnerRep B S g R hR z)
  have hΞ' : IsAdmissible (twist κB Ξ) := (isAdmissible_twist_iff _ _ hκB).mpr hΞ
  let AΞ := leviTensorIntertwiner σ B (nestedInnerIntertwiner σ B S g R A z)
  have h1 := hfM _ (twist κB Ξ) hΞ'
    (twistTwistedIntertwiner (leviAut σ B) κB (leviHalfModulus_leviAut σ B) AΞ)
    (isAdmissible_nestedRep B S g R hR z)
  change nestedTrace σ B S g R A μ hR z f = _ at h1
  rw [h1, twistedDistribution_twist_eq_comp ν Ξ hΞ _ κB hκB hΞ', LinearMap.comp_apply]
  change twistedDistribution ν Ξ hΞ AΞ.toLinearMap f' = _
  rw [← hc, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun φ _ => ?_
  rw [map_smul, map_smul, map_prod]
  congr 1
  have h2 := twistedDistribution_external_piTensor μi (nestedInnerRep B S g R z)
    (isAdmissible_nestedInnerRep B S g R hR z)
    (fun i => (nestedInnerIntertwiner σ B S g R A z i).toLinearMap) φ
  change twistedDistribution (Measure.pi μi) (FiniteTensor.external (nestedInnerRep B S g R z))
      (FiniteTensor.isAdmissible_external _ (isAdmissible_nestedInnerRep B S g R hR z))
      (PiTensorProduct.map (fun i => (nestedInnerIntertwiner σ B S g R A z i).toLinearMap))
      (SchwartzBruhat.piTensor φ) = _
  rw [h2]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact hq i (φ i) z

omit [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)] in
/-- If `σ ^ d = 1` and the inner block intertwiners have order dividing `d`, the induced
intertwiner of the nested family has order dividing `d`. Both hypotheses are needed: the
induced operator also moves functions on `GL_n(E)` by `entrywiseAut σ n`. -/
theorem nestedIntertwiner_pow {d : ℕ} (hσ : σ ^ d = 1) (hA : ∀ i j, (A i j).toLinearMap ^ d = 1)
    (z : Fin r → ℂˣ) :
    (normalizedParabolicSigmaIntertwiner σ B (B.blockTensor (nestedInnerRep B S g R z))
      (leviTensorIntertwiner σ B (nestedInnerIntertwiner σ B S g R A z))).toLinearMap ^ d = 1 := by
  have hθ : (entrywiseAut σ n) ^ d = 1 := by
    change (entrywiseAutHom n) σ ^ d = 1
    rw [← map_pow, hσ, map_one]
  unfold normalizedParabolicSigmaIntertwiner TwistedPaleyWiener.inducedSigmaIntertwiner
  exact inducedTwistedIntertwiner_pow_eq_one _ _ _ _ _ _ _ _ _ _ hθ
    (leviTensorIntertwiner_pow σ B (nestedInnerRep B S g R z) (nestedInnerIntertwiner σ B S g R A z)
      (fun i => familyIntertwiner_pow σ (S i) (g i) (R i) (A i) (innerHalfModulus B S i)
        (leviHalfModulus_leviAut σ (S i)) hσ (hA i) z))

variable {C : BlockShape n} {h : Fin C.length → Fin r}
  {W : Fin C.length → Type (max v w)} [∀ k, AddCommGroup (W k)] [∀ k, Module ℂ (W k)]
  {Q : ∀ k, Representation ℂ (GeneralLinear (C.size k) E) (W k)}
  {AQ : ∀ k, SigmaIntertwiner σ (C.size k) (Q k)}
  {κ : C.Levi E →* ℂˣ} (hκ : IsOpen (κ.ker : Set (C.Levi E)))
  (hκσ : ∀ m, κ (leviAut σ C m) = κ m)

/-- The nested family is one root of unity times an unramified family on a single shape, once
their unitary specializations are irreducible and equivalent. -/
theorem nestedTrace_comparison {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1)
    (hR : ∀ i j, IsAdmissible (R i j)) (hirr : ∀ i j, (R i j).IsIrreducible)
    (hA : ∀ i j, (A i j).toLinearMap ^ d = 1)
    (hQ : ∀ k, IsAdmissible (Q k)) (hQirr : ∀ k, (Q k).IsIrreducible)
    (hAQ : ∀ k, (AQ k).toLinearMap ^ d = 1)
    (hunit : ∀ z : Fin r → ℂˣ, (∀ k, ‖(z k : ℂ)‖ = 1) →
      (Induction.smoothInduced (C.parabolic E)
        ((twist κ (C.blockTensor (fun k =>
          twist (determinantUnramified E (C.size k) (z (h k))) (Q k)))).comp
            (C.leviProjection E))).IsIrreducible ∧
      Nonempty ((Induction.smoothInduced (C.parabolic E)
        ((twist κ (C.blockTensor (fun k =>
          twist (determinantUnramified E (C.size k) (z (h k))) (Q k)))).comp
            (C.leviProjection E))).Equiv
        ((LocalFieldData.ofInstances E).normalizedParabolicInduced B
          (B.blockTensor (nestedInnerRep B S g R z))))) :
    ∃ c : ℂ, c ^ d = 1 ∧ ∀ z,
      nestedTrace σ B S g R A μ hR z =
        c • unramifiedFamilyTrace σ C h Q AQ κ hκ hκσ μ hQ z := by
  let u : (Fin r → Circle) → (Fin r → ℂˣ) := fun z i => Circle.toUnits (z i)
  have hu (z : Fin r → Circle) (k : Fin r) : ‖((u z k : ℂˣ) : ℂ)‖ = 1 := Circle.norm_coe (z k)
  let ρ (z : Fin r → Circle) := Induction.smoothInduced (C.parabolic E)
    ((twist (leviUnramified E C h (u z)) (familyInducing C Q κ)).comp (C.leviProjection E))
  let π (z : Fin r → Circle) := (LocalFieldData.ofInstances E).normalizedParabolicInduced B
    (B.blockTensor (nestedInnerRep B S g R (u z)))
  have hρirr (z) : (ρ z).IsIrreducible := by
    obtain ⟨e⟩ := nonempty_familyInduced_equiv C h Q κ (u z)
    exact (isIrreducible_iff_of_equiv e).mpr (hunit (u z) (hu z)).1
  have he (z) : Nonempty ((ρ z).Equiv (π z)) := by
    obtain ⟨e⟩ := nonempty_familyInduced_equiv C h Q κ (u z)
    exact ⟨e.trans (hunit (u z) (hu z)).2.some⟩
  exact regularTwistedDistributionComparison μ (entrywiseAut σ n) hd
    (nestedTrace σ B S g R A μ hR)
    (unramifiedFamilyTrace σ C h Q AQ κ hκ hκσ μ hQ)
    (nestedTrace_regular σ B S g R A μ hd hσ hR hirr)
    (unramifiedFamilyTrace_regular σ C h Q AQ κ hκ hκσ μ hd hσ hQ hQirr)
    _ _ ρ π (fun z => isAdmissible_familyInduced C h Q κ hκ hQ (u z))
    (fun z => isAdmissible_nestedRep B S g R hR (u z)) hρirr (fun z => (he z).some)
    _ _ (fun z => familyIntertwiner_pow σ C h Q AQ κ hκσ hσ hAQ (u z))
    (fun z => nestedIntertwiner_pow σ B S g R A hσ hA (u z)) (fun _ => rfl) (fun _ => rfl)

end Nested

section Reparametrization

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) {r : ℕ}
  (g : ∀ i, Fin (S i).length → Fin r)
  {V : ∀ i, Fin (S i).length → Type w} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module ℂ (V i j)]
  (R : ∀ i j, Representation ℂ (GeneralLinear ((S i).size j) E) (V i j))
  (A : ∀ i j, SigmaIntertwiner σ ((S i).size j) (R i j))
  [∀ i, MeasurableSpace (GeneralLinear (B.size i) E)] [∀ i, BorelSpace (GeneralLinear (B.size i) E)]
  [∀ i, T2Space (GeneralLinear (B.size i) E)] [∀ i, LocallyCompactSpace (GeneralLinear (B.size i) E)]
  [∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) E)]
  [∀ i, SecondCountableTopology (GeneralLinear (B.size i) E)]
  (μi : ∀ i, Measure (GeneralLinear (B.size i) E)) [∀ i, SigmaFinite (μi i)]
  [∀ i, IsFiniteMeasureOnCompacts (μi i)] [∀ i, (μi i).IsMulLeftInvariant]

/-- The twisted distribution of the external tensor product of the inner family
representations, with the tensor product of their intertwiners, depends on the global
parameters only through the parameters of the inner blocks: it equals the twisted distribution
of the external tensor product of the inner families at those parameters. -/
theorem external_nestedInner_reparam (hR : ∀ i j, IsAdmissible (R i j)) (z : Fin r → ℂˣ)
    (w : ∀ i, Fin (S i).length → ℂˣ) (hw : ∀ i j, z (g i j) = w i j) :
    twistedDistribution (Measure.pi μi) (FiniteTensor.external (nestedInnerRep B S g R z))
        (FiniteTensor.isAdmissible_external _ (isAdmissible_nestedInnerRep B S g R hR z))
        (PiTensorProduct.map (fun i => (nestedInnerIntertwiner σ B S g R A z i).toLinearMap)) =
      twistedDistribution (Measure.pi μi)
        (FiniteTensor.external (fun i => Induction.smoothInduced ((S i).parabolic E)
          ((twist (leviUnramified E (S i) id (w i))
            (familyInducing (S i) (R i) (innerHalfModulus B S i))).comp
              ((S i).leviProjection E))))
        (FiniteTensor.isAdmissible_external _ (fun i => isAdmissible_familyInduced (S i) id (R i)
          (innerHalfModulus B S i) (isOpen_ker_innerHalfModulus B S i) (hR i) (w i)))
        (PiTensorProduct.map (fun i => (TwistedPaleyWiener.inducedSigmaIntertwiner σ (S i)
          (twist (leviUnramified E (S i) id (w i))
            (familyInducing (S i) (R i) (innerHalfModulus B S i)))
          (twistTwistedIntertwiner (leviAut σ (S i)) (leviUnramified E (S i) id (w i))
            (leviUnramified_leviAut E (S i) id σ (w i))
            (familyInducingIntertwiner σ (S i) (R i) (A i) (innerHalfModulus B S i)
              (leviHalfModulus_leviAut σ (S i))))).toLinearMap)) := by
  apply distribution_ext_piTensor
  intro φ
  rw [twistedDistribution_external_piTensor, twistedDistribution_external_piTensor]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hz : (fun j => z (g i j)) = w i := funext (hw i)
  change unramifiedFamilyTrace σ (S i) id (R i) (A i) (innerHalfModulus B S i)
      (isOpen_ker_innerHalfModulus B S i) (leviHalfModulus_leviAut σ (S i)) (μi i) (hR i)
      (fun j => z (g i j)) (φ i) =
    unramifiedFamilyTrace σ (S i) id (R i) (A i) (innerHalfModulus B S i)
      (isOpen_ker_innerHalfModulus B S i) (leviHalfModulus_leviAut σ (S i)) (μi i) (hR i)
      (w i) (φ i)
  rw [hz]

end Reparametrization

end Langlands.BaseChange
