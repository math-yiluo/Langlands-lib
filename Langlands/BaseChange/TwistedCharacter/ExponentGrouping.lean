import Langlands.BaseChange.TwistedCharacter.StandardTraceFamily
import Langlands.Representation.Classification.OrderedExponentGroupingProof
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Parabolic.WholeLeviConjugacyProof
import Langlands.Representation.Classification.TwistedProductCharacterTwistProof
import Langlands.Representation.Classification.TemperedInductionProof
import Langlands.Representation.Classification.BlockTensorTemperedProof
import Langlands.Representation.Classification.TwoSegmentSocleCommutationProof
import Langlands.Representation.Induction.FiniteProductTensorBijectiveProof
import Mathlib.Data.Fin.Tuple.Sort

/-! # Grouping σ-stable tempered blocks by real exponent into a standard datum -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory GeneralLinear HarmonicAnalysis MeasureTheory PadicField.TopologicalData

universe u v w

section NormalizedPower

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
  {W : Fin B.length → Type w} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i)}

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- If `σ ^ d = 1` and the block intertwiners have order dividing `d`, the normalized induced
σ-intertwiner has order dividing `d`. Both hypotheses are needed: the induced operator also
moves functions on `GL_n(E)` by `entrywiseAut σ n`. -/
theorem inducedSigmaIntertwiner_pow (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i)) {d : ℕ}
    (hσ : σ ^ d = 1) (hA : ∀ i, (A i).toLinearMap ^ d = 1) :
    (inducedSigmaIntertwiner σ B A).toLinearMap ^ d = 1 := by
  have hθ : (entrywiseAut σ n) ^ d = 1 := by
    change (entrywiseAutHom n) σ ^ d = 1
    rw [← map_pow, hσ, map_one]
  exact inducedTwistedIntertwiner_pow_eq_one (entrywiseAut σ n)
    (continuous_entrywiseAut_of_isModuleTopology σ n)
    (TwistedPaleyWiener.continuous_entrywiseAut_symm σ n) (B.parabolic E)
    (entrywiseAut_mem_parabolic_iff σ B) (B.leviProjection E) (leviAut σ B)
    (leviProjection_entrywiseAut σ B)
    (twist ((LocalFieldData.ofInstances E).leviHalfModulus B) (B.blockTensor P))
    (twistTwistedIntertwiner (leviAut σ B) ((LocalFieldData.ofInstances E).leviHalfModulus B)
      (leviHalfModulus_leviAut σ B) (leviTensorIntertwiner σ B A)) hθ
    (leviTensorIntertwiner_pow σ B P A hA)

end NormalizedPower

section Padic

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)

/-- A normalized product of irreducible tempered blocks is irreducible and tempered. -/
theorem normalizedProduct_irreducible_tempered {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (τ : letI := T.topology; ∀ k, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (B.size k) E.Carrier))
    (hirr : letI := T.topology; ∀ k, (τ k).representation.IsIrreducible)
    (htemp : letI := T.topology; ∀ k, T.IsTempered (τ k).representation) :
    letI := T.topology
    (T.normalizedProductInduced B (fun k => (τ k).representation)).IsIrreducible ∧
      T.IsTempered (T.normalizedProductInduced B (fun k => (τ k).representation)) := by
  let := T.topology
  have hunit (k : Fin B.length) : IsUnitarizable (τ k).representation :=
    glTemperedUnitarity.{v, max v w} p E T (B.size k) (B.positive k) _ (τ k).representation
      (hirr k) (htemp k)
  have hIrr := (Classification.bernsteinUnitaryProductIrreducibility.{v,w} E T n B τ
    fun k => ⟨hirr k, hunit k⟩).1
  rw [T.normalizedProductInductionFunctor_obj] at hIrr
  refine ⟨hIrr, ?_⟩
  let := T.leviTopology B
  have := T.leviTopologicalGroup B
  let := borel (B.Levi E.Carrier ⧸ Subgroup.center (B.Levi E.Carrier))
  have : BorelSpace (B.Levi E.Carrier ⧸ Subgroup.center (B.Levi E.Carrier)) := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient B
  have hadm (k : Fin B.length) : IsAdmissible (τ k).representation := (htemp k).isAdmissible
  have hL := (glBlockTensorTempered.{v, max v w} p E T n hn B _ (fun k => (τ k).representation)
    hirr hadm).mp htemp μ
  have hLirr : (B.blockTensor (fun k => (τ k).representation)).IsIrreducible := by
    let (k : Fin B.length) : (τ k).representation.IsIrreducible := hirr k
    exact FiniteTensor.isIrreducible_external _
      (fun k f => (admissibleSchur_scalarEndomorphism _ (hadm k) inferInstance f).exists)
  have h := (glTemperedInduction.{v, max v w} p E T n hn B μ _ _ hLirr hL).2.2
  rw [T.normalizedProductInduced_eq]
  exact h

/-- Equal unramified parameters give equal twists, as an equivalence. -/
def twistDeterminantUnramifiedEquiv {m : ℕ} {V : Type w} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear m E.Carrier) V) {c c' : ℂˣ} (hc : c = c') :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (twist (determinantUnramified E.Carrier m c) ρ).Equiv
      (twist (determinantUnramified E.Carrier m c') ρ) := by
  subst hc
  exact Representation.Equiv.refl _

theorem cast_twist_determinantUnramified {m m' : ℕ} (hm : m = m')
    (Y : letI := T.topology; SmoothRep.{0,v,w} ℂ (GeneralLinear m E.Carrier)) (c : ℂˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    hm ▸ (Y.twist (determinantUnramified E.Carrier m c)
      (isOpen_ker_determinantUnramified E.Carrier m c)) =
      (hm ▸ Y).twist (determinantUnramified E.Carrier m' c)
        (isOpen_ker_determinantUnramified E.Carrier m' c) := by
  subst hm
  rfl

/-- The unramified character `z ^ ord(det)` as a smooth character of the units. -/
def unramifiedSmoothCharacter (c : ℂˣ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ E.Carrierˣ :=
  letI := T.topology
  ⟨T.unramifiedCharacter c, T.isOpen_ker_unramifiedCharacter c⟩

/-- Equal characters give equal twists, as an equivalence. -/
def twistEquivOfEq {G : Type*} [Group G] {V : Type w} [AddCommGroup V] [Module ℂ V]
    {χ χ' : G →* ℂˣ} (hχ : χ = χ') (ρ : Representation ℂ G V) :
    (twist χ ρ).Equiv (twist χ' ρ) := by
  subst hχ
  exact Representation.Equiv.refl _

theorem unramifiedSmoothCharacter_comp_determinant (m : ℕ) (c : ℂˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (unramifiedSmoothCharacter T c).toMonoidHom.comp
        (determinant : GeneralLinear m E.Carrier →* E.Carrierˣ) =
      determinantUnramified E.Carrier m c := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply MonoidHom.ext
  intro g
  rfl

/-- Equal smooth representations are equivalent. -/
def smoothRepEquivOfEq {G : Type v} [Group G] [TopologicalSpace G]
    {A B : SmoothRep.{0,v,w} ℂ G} (hAB : A = B) : A.representation.Equiv B.representation := by
  subst hAB
  exact Representation.Equiv.refl _

/-- A rank cast of a twisted block is the twist of the rank cast. -/
def castTwistEquiv {a b : ℕ} (hp : a = b)
    (Y : letI := T.topology; SmoothRep.{0,v,w} ℂ (GeneralLinear a E.Carrier)) {c c' : ℂˣ}
    (hc : c = c') :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (hp ▸ (Y.twist (determinantUnramified E.Carrier a c)
      (isOpen_ker_determinantUnramified E.Carrier a c))).representation.Equiv
      (twist (determinantUnramified E.Carrier b c') (hp ▸ Y).representation) := by
  subst hp
  subst hc
  exact Representation.Equiv.refl _

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- An inner normalized product of blocks, each equivalent to the twist of a fixed block
family by one unramified character, is the twist of the inner product. -/
def groupBlockEquiv {m : ℕ} (S' : BlockShape m)
    (G' : letI := T.topology; ∀ k, SmoothRep.{0,v,w} ℂ (GeneralLinear (S'.size k) E.Carrier))
    (ib : letI := T.topology; ∀ k, SmoothRep.{0,v,w} ℂ (GeneralLinear (S'.size k) E.Carrier))
    (c : ℂˣ)
    (hG : letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      ∀ k, (G' k).representation.Equiv
        (twist (determinantUnramified E.Carrier (S'.size k) c) (ib k).representation)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup m
    ((T.normalizedProductInductionFunctor S').obj G').representation.Equiv
      (twist (determinantUnramified E.Carrier m c)
        (T.normalizedProductInduced S' (fun k => (ib k).representation))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup m
  let χS := unramifiedSmoothCharacter T c
  let ob1 : ((T.normalizedProductInductionFunctor S').obj G').representation.Equiv
      (T.normalizedProductInduced S' (fun k =>
        twist (determinantUnramified E.Carrier (S'.size k) c) (ib k).representation)) :=
    T.normalizedProductInducedEquiv S' hG
  let ob2 : (T.normalizedProductInduced S' (fun k =>
        twist (determinantUnramified E.Carrier (S'.size k) c) (ib k).representation)).Equiv
      (T.normalizedProductInduced S' (fun k =>
        twist (χS.toMonoidHom.comp determinant) (ib k).representation)) :=
    T.normalizedProductInducedEquiv S' (fun k =>
      twistEquivOfEq (unramifiedSmoothCharacter_comp_determinant T _ c).symm (ib k).representation)
  let ob3 :=
    (T.normalizedProductDeterminantTwistEquiv S' χS (fun k => (ib k).representation)).symm
  let ob4 := twistEquivOfEq (unramifiedSmoothCharacter_comp_determinant T m c)
    (T.normalizedProductInduced S' (fun k => (ib k).representation))
  exact ob1.trans (ob2.trans (ob3.trans ob4))

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- At unitary parameters constant on runs, the normalized product of twisted blocks is
equivalent to the normalized product, over the runs, of the twisted normalized products of
the blocks of each run. -/
theorem nonempty_unitaryGrouping_equiv {n : ℕ} (hn : 0 < n) (L : BlockShape n)
    (e : Equiv.Perm (Fin L.length)) (D : BlockShape n) (q' : Fin L.length → Fin D.length)
    (S : ∀ j, BlockShape (D.size j)) (e' : ∀ j, Fin (S j).length ≃ {i // q' i = j})
    (h : ∀ j k, (S j).size k = (L.permute e).size (e' j k).val)
    (hc : ∀ j k (x : Fin ((S j).size k)),
      D.index j ((S j).index k x) = (L.permute e).index (e' j k).val (Fin.cast (h j k) x))
    (δ : letI := T.topology; ∀ k, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (L.size k) E.Carrier))
    (hirr : letI := T.topology; ∀ k, (δ k).representation.IsIrreducible)
    (htemp : letI := T.topology; ∀ k, T.IsTempered (δ k).representation)
    (ib : letI := T.topology
      ∀ j k, SmoothRep.{0,v,max v w} ℂ (GeneralLinear ((S j).size k) E.Carrier))
    (hib : ∀ j k, ib j k = (h j k).symm ▸ δ (e (e' j k).val))
    (P : letI := T.topology; ∀ j, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (D.size j) E.Carrier))
    (hP : letI := T.topology; ∀ j, P j = SmoothRep.of
      (T.normalizedProductInduced (S j) (fun k => (ib j k).representation))
      (T.isSmooth_normalizedProductInduced (S j) _))
    (z : Fin D.length → ℂˣ) (hz : ∀ j, ‖(z j : ℂ)‖ = 1) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup n
    Nonempty ((T.normalizedProductInduced L (fun k =>
        twist (determinantUnramified E.Carrier (L.size k) (z (q' (e.symm k))))
          (δ k).representation)).Equiv
      (T.normalizedProductInduced D (fun j =>
        twist (determinantUnramified E.Carrier (D.size j) (z j)) (P j).representation))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  have hunit (k : Fin L.length) : IsUnitarizable (δ k).representation :=
    glTemperedUnitarity.{v, max v w} p E T (L.size k) (L.positive k) _ (δ k).representation
      (hirr k) (htemp k)
  let δz (k : Fin L.length) : SmoothRep.{0,v,max v w} ℂ (GeneralLinear (L.size k) E.Carrier) :=
    (δ k).twist (determinantUnramified E.Carrier (L.size k) (z (q' (e.symm k))))
      (isOpen_ker_determinantUnramified E.Carrier _ _)
  have hδzirr (k : Fin L.length) : (δz k).representation.IsIrreducible :=
    (isIrreducible_twist_iff _ _).mpr (hirr k)
  have hδzadm (k : Fin L.length) : (δz k).IsAdmissible :=
    (isAdmissible_twist_iff _ _ (isOpen_ker_determinantUnramified E.Carrier _ _)).mpr
      (htemp k).isAdmissible
  -- the two irreducible orderings
  have hX1 := normalizedProduct_unitaryTwist T L δ hirr hunit (fun k => q' (e.symm k)) z hz
  have hX2 := normalizedProduct_unitaryTwist T (L.permute e) (fun k => δ (e k)) (fun k => hirr _)
    (fun k => hunit _) (fun k => q' (e.symm (e k))) z hz
  have hJH := Parabolic.WholeLeviConjugacyProof.permutedProducts.{v, max v w} E T hn L e δz hδzirr hδzadm
  -- identify the two orderings
  let a1 : (T.normalizedProductInduced L (fun k => (δz k).representation)).Equiv
      (T.normalizedProductInduced L (fun k =>
        twist (determinantUnramified E.Carrier (L.size k) (z (q' (e.symm k))))
          (δ k).representation)) :=
    T.normalizedProductInducedEquiv L (fun k => Representation.Equiv.refl _)
  let a2 : (T.normalizedProductInduced (L.permute e) (fun k => (δz (e k)).representation)).Equiv
      (T.normalizedProductInduced (L.permute e) (fun k =>
        twist (determinantUnramified E.Carrier ((L.permute e).size k) (z (q' (e.symm (e k)))))
          (δ (e k)).representation)) :=
    T.normalizedProductInducedEquiv (L.permute e) (fun k => Representation.Equiv.refl _)
  have hirr1 : (T.normalizedProductInduced L (fun k => (δz k).representation)).IsIrreducible :=
    (isIrreducible_iff_of_equiv a1).mpr hX1.1
  have hirr2 : (T.normalizedProductInduced (L.permute e)
      (fun k => (δz (e k)).representation)).IsIrreducible :=
    (isIrreducible_iff_of_equiv a2).mpr hX2.1
  have hi1 : (Rep.of (T.normalizedProductInduced L (fun k => (δz k).representation))).ρ.IsIrreducible :=
    hirr1
  have hi2 : (Rep.of (T.normalizedProductInduced (L.permute e)
      (fun k => (δz (e k)).representation))).ρ.IsIrreducible := hirr2
  have hJH' : HaveSameJordanHolderFactors
      (Rep.of (T.normalizedProductInduced L (fun k => (δz k).representation)))
      (Rep.of (T.normalizedProductInduced (L.permute e) (fun k => (δz (e k)).representation))) :=
    hJH
  have b12 := nonempty_equiv_of_isIrreducible_of_sameFactors
    (Rep.of (T.normalizedProductInduced L (fun k => (δz k).representation)))
    (Rep.of (T.normalizedProductInduced (L.permute e) (fun k => (δz (e k)).representation)))
    hi1 hi2 hJH'
  let f12 : (T.normalizedProductInduced L (fun k => (δz k).representation)).Equiv
      (T.normalizedProductInduced (L.permute e) (fun k => (δz (e k)).representation)) :=
    b12.some
  -- regrouping
  let E' : ((j : Fin D.length) × Fin (S j).length) ≃ Fin (L.permute e).length :=
    (Equiv.sigmaCongrRight e').trans (Equiv.sigmaFiberEquiv q')
  have hreg := Parabolic.orderedProductRegrouping.{v, max v w} E T n (L.permute e) D S E'
    (fun a => h a.1 a.2) hc (fun k => δz (e k))
  let f23 := SmoothRep.equivOfIso hreg.some
  let f13 := a1.symm.trans f12
  have hzj (j : Fin D.length) (k : Fin (S j).length) :
      z (q' (e.symm (e (E' ⟨j, k⟩)))) = z j := by
    rw [Equiv.symm_apply_apply]
    exact congrArg z (e' j k).property
  exact ⟨f13.trans (f23.trans (T.normalizedProductInducedEquiv D (fun j =>
    (groupBlockEquiv T (S j) _ (ib j) (z j) (fun k => (castTwistEquiv T _ _ (hzj j k)).trans
      (twistEquiv _ (smoothRepEquivOfEq (hib j k).symm)))).trans
      (twistEquiv _ (smoothRepEquivOfEq (hP j).symm)))))⟩

variable (σ : E.Carrier ≃ₐ[F] E.Carrier)

/-- Transport a σ-intertwiner along an equality of ranks. -/
def castSigmaIntertwiner {m m' : ℕ} (h : m = m')
    (δ : letI := T.topology; SmoothRep.{0,v,w} ℂ (GeneralLinear m E.Carrier))
    (A : letI := T.topology; SigmaIntertwiner σ m δ.representation) :
    letI := T.topology
    SigmaIntertwiner σ m' (h ▸ δ).representation := by
  subst h
  exact A

omit [TopologicalSpace F] in
theorem castSigmaIntertwiner_pow {m m' : ℕ} (h : m = m')
    (δ : letI := T.topology; SmoothRep.{0,v,w} ℂ (GeneralLinear m E.Carrier))
    (A : letI := T.topology; SigmaIntertwiner σ m δ.representation) {d : ℕ} (hA : A.toLinearMap ^ d = 1) :
    (castSigmaIntertwiner T σ h δ A).toLinearMap ^ d = 1 := by
  subst h
  exact hA

variable (hModule : letI := T.topology; IsModuleTopology F E.Carrier)

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
include hModule in
/-- Sorting σ-stable irreducible tempered blocks by their real exponents and inducing each
maximal run of equal exponents gives a σ-stable tempered standard datum. At unitary
unramified parameters, constant on runs, the two normalized products are equivalent. -/
theorem exists_groupedTemperedDatum {n : ℕ} (hn : 0 < n) (L : BlockShape n)
    (δ : letI := T.topology; ∀ k, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (L.size k) E.Carrier))
    (hirr : letI := T.topology; ∀ k, (δ k).representation.IsIrreducible)
    (htemp : letI := T.topology; ∀ k, T.IsTempered (δ k).representation)
    (A : letI := T.topology; ∀ k, SigmaIntertwiner σ (L.size k) (δ k).representation)
    {d : ℕ} (hσ : σ ^ d = 1) (hA : ∀ k, (A k).toLinearMap ^ d = 1) (x : Fin L.length → ℝ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∃ (t : T.TemperedLanglandsDatum.{max v w} n)
      (A' : ∀ j, SigmaIntertwiner σ (t.shape.size j) (t.blocks j).representation)
      (q : Fin L.length → Fin t.shape.length),
      (∀ j, (A' j).toLinearMap ^ d = 1) ∧ (∀ k, x k = t.exponent (q k)) ∧
      ∀ z : Fin t.shape.length → ℂˣ, (∀ j, ‖(z j : ℂ)‖ = 1) →
        letI := T.generalLinearTopologicalGroup n
        Nonempty ((T.normalizedProductInduced L (fun k =>
            twist (determinantUnramified E.Carrier (L.size k) (z (q k))) (δ k).representation)).Equiv
          (T.normalizedProductInduced t.shape (fun j =>
            twist (determinantUnramified E.Carrier (t.shape.size j) (z j))
              (t.blocks j).representation))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  let e := Tuple.sort (fun k => -x k)
  have hanti : Antitone (fun k => x (e k)) := by
    intro a b hab
    have h := Tuple.monotone_sort (fun k => -x k) hab
    simp only [Function.comp_apply, neg_le_neg_iff] at h
    exact h
  obtain ⟨D, b, q', hb, hq', hsurj, ha, S, e', h, he, hc⟩ :=
    Classification.orderedExponentGrouping n (L.permute e) (fun k => x (e k)) hanti
  let τ (j : Fin D.length) (k : Fin (S j).length) :
      SmoothRep.{0,v,max v w} ℂ (GeneralLinear ((S j).size k) E.Carrier) :=
    (h j k).symm ▸ δ (e (e' j k).val)
  have hτ (j : Fin D.length) (k : Fin (S j).length) :
      (τ j k).representation.IsIrreducible ∧ T.IsTempered (τ j k).representation := by
    have transport (r s : ℕ) (hr : r = s)
        (Y : SmoothRep.{0,v,max v w} ℂ (GeneralLinear s E.Carrier))
        (hY : Y.representation.IsIrreducible ∧ T.IsTempered Y.representation) :
        (hr.symm ▸ Y).representation.IsIrreducible ∧ T.IsTempered (hr.symm ▸ Y).representation := by
      cases hr
      exact hY
    exact transport _ _ (h j k) _ ⟨hirr _, htemp _⟩
  let Pi (j : Fin D.length) : SmoothRep.{0,v,max v w} ℂ (GeneralLinear (D.size j) E.Carrier) :=
    SmoothRep.of (T.normalizedProductInduced (S j) (fun k => (τ j k).representation))
      (T.isSmooth_normalizedProductInduced (S j) _)
  have hPi (j : Fin D.length) :
      (Pi j).representation.IsIrreducible ∧ T.IsTempered (Pi j).representation := by
    have h := normalizedProduct_irreducible_tempered T (D.positive j) (S j) (τ j)
      (fun k => (hτ j k).1) (fun k => (hτ j k).2)
    let e0 : (Pi j).representation.Equiv
        (T.normalizedProductInduced (S j) (fun k => (τ j k).representation)) :=
      Representation.Equiv.refl _
    exact ⟨(isIrreducible_iff_of_equiv e0).mpr h.1, (T.isTempered_iff_of_equiv e0).mpr h.2⟩
  let t : T.TemperedLanglandsDatum.{max v w} n :=
    { shape := D
      blocks := Pi
      irreducible := fun j => (hPi j).1
      tempered := fun j => (hPi j).2
      exponent := b
      strictAnti := hb }
  let Aτ (j : Fin D.length) (k : Fin (S j).length) :
      SigmaIntertwiner σ ((S j).size k) (τ j k).representation :=
    castSigmaIntertwiner T σ (h j k).symm (δ (e (e' j k).val)) (A _)
  let A' (j : Fin D.length) : SigmaIntertwiner σ (D.size j) (Pi j).representation :=
    inducedSigmaIntertwiner σ (S j) (Aτ j)
  refine ⟨t, A', fun k => q' (e.symm k), fun j => ?_, fun k => ?_, fun z hz => ?_⟩
  · exact inducedSigmaIntertwiner_pow σ (S j) (Aτ j) hσ
      (fun k => castSigmaIntertwiner_pow T σ _ _ _ (hA _))
  · have hk := ha (e.symm k)
    simp only [Equiv.apply_symm_apply] at hk
    exact hk
  · let := T.generalLinearTopologicalGroup n
    exact nonempty_unitaryGrouping_equiv T hn L e D q' S e' h hc δ hirr htemp τ
      (fun _ _ => rfl) Pi (fun _ => rfl) z hz

end Padic

end Langlands.BaseChange
