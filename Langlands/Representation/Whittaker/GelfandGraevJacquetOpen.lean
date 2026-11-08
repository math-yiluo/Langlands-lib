import Langlands.Representation.Whittaker.GelfandGraevJacquetOpenStatement
import Langlands.Representation.Whittaker.OpenStabilizer
import Langlands.Representation.Parabolic.LeviBridges
import Langlands.Representation.Induction.SplitStagesComparison
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Derivative.TopLocalizationData
import Langlands.Group.GL.BlockModulusHaarProof
import Langlands.HarmonicAnalysis.HaarConjugacy
import Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.Parabolic.UnipotentFiniteContainment
import Langlands.Representation.Whittaker.GelfandGraevJacquet

/-!
# The open orbit piece of the Jacquet module of a Gelfand–Graev representation

Let `w` be the block-reversal matrix, `N` the upper unipotent subgroup and `P` the upper block
parabolic with Levi `M`, unipotent radical `U`, Levi projection `r` and Levi section `s`. The
stabilizer `H = P ∩ w N w⁻¹` is `s(N_M)`, and `ψ_N ∘ Ad(w⁻¹)` is `ψ_M ∘ r` on it. Compact
induction in stages through `r⁻¹(N_M)` and integration over `U` identify the `U`-coinvariants of
`c-Ind_H^P (ψ_N ∘ Ad(w⁻¹))` with `c-Ind_{N_M}^M ψ_M`. The Haar ratio and the normalizing
character are trivial on `N_M`, which proves `GelfandGraevOpenPieceStatement`.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear Geometric HarmonicAnalysis Induction MeasureTheory MeasureTheory.Measure
open QuotientIntegration
open scoped NNReal _root_.Topology

universe uF uV

section Stabilizer

variable {n : ℕ} (B : BlockShape n) (K : Type uF) [Field K]

/-- Conjugation by `w⁻¹` sends the open piece stabilizer `P ∩ w N w⁻¹` into the Library's open
stabilizer `N ∩ w⁻¹ P w`. -/
def openPieceToOpenStabilizer
    (x : orbitStabilizer (upperUnipotent n K) (B.parabolic K) (B.reverseMatrix K)) :
    openStabilizer B K :=
  ⟨stabilizerToInducing (upperUnipotent n K) (B.parabolic K) (B.reverseMatrix K) x, by
    change MulAut.conj (B.reverseMatrix K)⁻¹⁻¹
      (MulAut.conj (B.reverseMatrix K)⁻¹ ((x : B.parabolic K) : GeneralLinear n K)) ∈
        B.parabolic K
    simp [MulAut.conj_apply, mul_assoc]⟩

theorem openPieceToOpenStabilizer_inducing
    (x : orbitStabilizer (upperUnipotent n K) (B.parabolic K) (B.reverseMatrix K)) :
    stabilizerToInducing (B.parabolic K) (upperUnipotent n K) (B.reverseMatrix K)⁻¹
      (openPieceToOpenStabilizer B K x) = x := by
  apply Subtype.ext
  change MulAut.conj (B.reverseMatrix K)⁻¹⁻¹
      (MulAut.conj (B.reverseMatrix K)⁻¹ ((x : B.parabolic K) : GeneralLinear n K)) = _
  simp [MulAut.conj_apply, mul_assoc]

theorem openStabilizerEquiv_openPieceToOpenStabilizer
    (x : orbitStabilizer (upperUnipotent n K) (B.parabolic K) (B.reverseMatrix K)) :
    (fun i => (openStabilizerEquiv B K (openPieceToOpenStabilizer B K x) i).val) =
      B.leviProjection K x := by
  funext i
  rw [openStabilizerEquiv_apply_val, openPieceToOpenStabilizer_inducing]

/-- The Levi projection of an element of the open piece stabilizer is upper unitriangular in every
block. -/
theorem openPiece_leviProjection_mem
    (x : orbitStabilizer (upperUnipotent n K) (B.parabolic K) (B.reverseMatrix K))
    (i : Fin B.length) :
    B.leviProjection K x i ∈ upperUnipotent (B.size i) K := by
  rw [← openStabilizerEquiv_openPieceToOpenStabilizer B K x]
  exact (openStabilizerEquiv B K (openPieceToOpenStabilizer B K x) i).property

/-- An element of the open piece stabilizer is the Levi section of its Levi projection. -/
theorem openPiece_eq_leviInParabolic
    (x : orbitStabilizer (upperUnipotent n K) (B.parabolic K) (B.reverseMatrix K)) :
    (x : B.parabolic K) = B.leviInParabolic K (B.leviProjection K x) := by
  have h := openStabilizerEquiv_symm_apply_val B K
    (openStabilizerEquiv B K (openPieceToOpenStabilizer B K x))
  rw [MulEquiv.symm_apply_apply, openStabilizerEquiv_openPieceToOpenStabilizer] at h
  apply Subtype.ext
  rw [B.leviInParabolic_val]
  change MulAut.conj (B.reverseMatrix K)⁻¹ ((x : B.parabolic K) : GeneralLinear n K) = _ at h
  rw [MulAut.conj_apply, inv_inv] at h
  exact mul_left_cancel (mul_right_cancel h)

/-- The Levi section of an element of `N_M` lies in the open piece stabilizer. -/
theorem leviInParabolic_mem_openPiece (l : B.Levi K)
    (hl : ∀ i, l i ∈ upperUnipotent (B.size i) K) :
    B.leviInParabolic K l ∈
      orbitStabilizer (upperUnipotent n K) (B.parabolic K) (B.reverseMatrix K) := by
  let y := (openStabilizerEquiv B K).symm (fun i => ⟨l i, hl i⟩)
  have h := openStabilizerEquiv_symm_apply_val B K (fun i => ⟨l i, hl i⟩)
  change MulAut.conj (B.reverseMatrix K)⁻¹ (B.leviEmbedding K l) ∈ upperUnipotent n K
  rw [MulAut.conj_apply, inv_inv]
  have hy : (y.val.val : GeneralLinear n K) ∈ upperUnipotent n K := y.val.property
  rw [h] at hy
  exact hy

/-- On the open piece stabilizer, the Gelfand–Graev character conjugated by the block reversal
is the Levi Whittaker character of the Levi projection. -/
theorem openPiece_character (ψ : AddChar K ℂ)
    (x : orbitStabilizer (upperUnipotent n K) (B.parabolic K) (B.reverseMatrix K))
    (i : ∀ j : Fin B.length, upperUnipotent (B.size j) K)
    (hi : ∀ j, (i j : GeneralLinear (B.size j) K) = B.leviProjection K x j) :
    entrywiseCharacter ψ n
        (stabilizerToInducing (upperUnipotent n K) (B.parabolic K) (B.reverseMatrix K) x) =
      ∏ j, entrywiseCharacter ψ (B.size j) (i j) := by
  have h := openStabilizerEquiv_character B K ψ (openPieceToOpenStabilizer B K x)
  have he : openStabilizerEquiv B K (openPieceToOpenStabilizer B K x) = i := by
    funext j
    apply Subtype.ext
    rw [hi j]
    exact congrFun (openStabilizerEquiv_openPieceToOpenStabilizer B K x) j
  rw [he] at h
  exact h

end Stabilizer


section Transport

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Compact induction from two equal subgroups, with the coefficients identified along the
inclusion. -/
def compactInducedCongrSubgroup {K K' : Subgroup G} (h : K = K')
    {κ : Representation ℂ K V} {κ' : Representation ℂ K' W}
    (e : κ.Equiv (κ'.comp (Subgroup.inclusion h.le))) :
    (Induction.compactInduced K κ).Equiv (Induction.compactInduced K' κ') := by
  subst h
  exact Induction.compactInducedEquiv K e

/-- The coinvariants of a trivial action are the space itself. -/
def coinvariantsTrivialEquiv {H : Type*} [Group H] (σ : Representation ℂ H V)
    (hσ : ∀ h, σ h = 1) : Representation.Coinvariants σ ≃ₗ[ℂ] V where
  toLinearMap := Representation.Coinvariants.lift σ LinearMap.id fun h => by
    rw [hσ h]
    rfl
  invFun := Representation.Coinvariants.mk σ
  left_inv z := by
    induction z using Representation.Coinvariants.induction_on with
    | h v => rfl
  right_inv _ := rfl

@[simp] theorem coinvariantsTrivialEquiv_mk {H : Type*} [Group H] (σ : Representation ℂ H V)
    (hσ : ∀ h, σ h = 1) (v : V) :
    coinvariantsTrivialEquiv σ hσ (Representation.Coinvariants.mk σ v) = v := rfl

/-- A linear identification with `ℂ` along which every element acts by a character is an
equivalence with the character representation. -/
def characterRepresentationEquiv {K : Type*} [Group K] (κ : Representation ℂ K V)
    (e : V ≃ₗ[ℂ] ℂ) (θ : K →* ℂˣ) (h : ∀ k v, e (κ k v) = (θ k : ℂ) • e v) :
    κ.Equiv (characterRepresentation θ) where
  toLinearEquiv := e
  isIntertwining' k := LinearMap.ext fun v => by
    change e (κ k v) = (θ k : ℂ) • e v
    exact h k v

end Transport

section Normalized

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (B : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The normalized Jacquet module of a representation of the parabolic is the unnormalized Levi
action on the radical coinvariants twisted by `δ_P^(-1/2)`. -/
theorem parabolicNormalizedJacquet_eq_twist (ρ : Representation ℂ (B.parabolic F.Carrier) V) :
    parabolicNormalizedJacquet T B ρ =
      twist (Jacquet.inverseHalfCharacter (T.leviModulus B)) (Parabolic.leviCoinvariants B ρ) := by
  apply MonoidHom.ext
  intro m
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective ρ (B.unipotentRadical F.Carrier) v
  change Jacquet.normalizedActionOfModulus ρ (B.unipotentRadical F.Carrier) ⊤
      B.top_le_normalizer_unipotentRadical (B.topModulus (T.leviModulus B)) (B.leviToTop m)
      (Jacquet.mk ρ _ w) =
    (Jacquet.inverseHalfCharacter (T.leviModulus B) m : ℂ) •
      Parabolic.leviCoinvariants B ρ m (Jacquet.mk ρ _ w)
  rw [Jacquet.normalizedActionOfModulus_mk, B.topModulus_leviToTop,
    Jacquet.inverseHalfCharacter_apply]
  rfl

/-- The same identification as an equivalence of representations. -/
def parabolicNormalizedJacquetTwistEquiv (ρ : Representation ℂ (B.parabolic F.Carrier) V) :
    (parabolicNormalizedJacquet T B ρ).Equiv
      (twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
        (Parabolic.leviCoinvariants B ρ)) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' m := by
    rw [parabolicNormalizedJacquet_eq_twist]
    rfl

/-- The block modulus is trivial on the product of the block upper unipotent subgroups. -/
theorem leviModulus_eq_one_of_upperUnipotent (l : B.Levi F.Carrier)
    (hl : ∀ i, l i ∈ upperUnipotent (B.size i) F.Carrier) : T.leviModulus B l = 1 :=
  T.normOneLevi_le_ker_leviModulus B ((T.mem_normOneLevi B l).mpr fun i =>
    Derivative.TopLocalization.determinantNorm_upper T ⟨l i, hl i⟩)

end Normalized

set_option maxHeartbeats 800000 in
/-- The normalized Jacquet module of the open orbit piece of the Gelfand–Graev representation is
the Gelfand–Graev representation of the Levi. -/
theorem gelfandGraevOpenPiece : GelfandGraevOpenPieceStatement.{uF} := by
  intro p hp F ψ n B
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.generalLinearNonarchimedean (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := T.generalLinearT2Space (n + 1)
  let := T.upperUnipotentNonarchimedean (n + 1)
  let := B.parabolicLocallyCompactSpace F.Carrier
  let := T.leviTopologicalGroup B
  let N := upperUnipotent (n + 1) F.Carrier
  let G := B.parabolic F.Carrier
  let L := B.Levi F.Carrier
  let U := B.unipotentRadical F.Carrier
  let w := B.reverseMatrix F.Carrier
  let r := B.leviProjection F.Carrier
  let s := B.leviInParabolic F.Carrier
  have hrs : ∀ l, r (s l) = l := B.leviProjection_section F.Carrier
  have hr : Continuous r := (B.leviProjectionContinuous F.Carrier).continuous
  have hs : Continuous s := (B.leviInParabolicContinuous F.Carrier).continuous
  let NM := leviUpperUnipotent (F := F.Carrier) B
  let Q := NM.comap r
  let H := orbitStabilizer N G w
  -- The coefficient character on the stabilizer is smooth.
  let σ := (gelfandGraevCharacterRepresentation ψ n).comp (stabilizerToInducing N G w)
  have hstab : Continuous (stabilizerToInducing N G w) := by
    apply continuous_induced_rng.mpr
    change Continuous fun q : H => w⁻¹ * ((q : G) : Langlands.GeneralLinear (n + 1) F.Carrier) *
      w⁻¹⁻¹
    exact (continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
      continuous_const
  have hσ : IsSmooth σ :=
    isSmooth_comp _ hstab (isSmooth_characterRepresentation_of_isOpen_ker _
      (isOpen_ker_of_continuous_complex_character _ (standardCharacterContinuous ψ n).continuous))
  -- The groups of the compact induction in stages.
  have hNM : IsClosed (NM : Set L) := by
    change IsClosed ((Subgroup.pi Set.univ fun i => upperUnipotent (B.size i) F.Carrier :
      Subgroup L) : Set L)
    rw [Subgroup.coe_pi]
    exact isClosed_set_pi fun i _ => UpperUnipotent.isClosed
  have hQ : IsClosed (Q : Set G) := hNM.preimage hr
  have hker : r.ker ≤ Q := fun x hx => by
    change r x ∈ NM
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem _
  have hHQ : H ≤ Q := fun x hx => by
    change r x ∈ NM
    exact (Subgroup.mem_pi _).mpr fun i _ => openPiece_leviProjection_mem B F.Carrier ⟨x, hx⟩ i
  have hH : IsClosed (H : Set G) := isClosed_orbitStabilizer N G w UpperUnipotent.isClosed
  have hsH : ∀ l : Q.comap s, s l ∈ H := fun l => by
    apply leviInParabolic_mem_openPiece
    intro i
    have hl : r (s l) ∈ NM := l.property
    rw [hrs] at hl
    exact (Subgroup.mem_pi _).mp hl i (Set.mem_univ i)
  have hK : Q.comap s = NM := by
    ext l
    change r (s l) ∈ NM ↔ l ∈ NM
    rw [hrs]
  -- Measure data on the kernel of the retraction.
  let rP := splitStagesRetraction r s hrs Q hker
  let eK : rP.ker ≃ₜ* U := splitStagesKernelContinuousEquiv r s hrs Q hker
  let : LocallyCompactSpace U := T.unipotentRadicalLocallyCompactSpace B
  let : LocallyCompactSpace rP.ker := eK.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : MeasurableSpace rP.ker := borel _
  let : BorelSpace rP.ker := ⟨rfl⟩
  let : MeasurableSpace U := borel _
  let : BorelSpace U := ⟨rfl⟩
  let I := (H.subgroupOf Q).comap rP.ker.subtype
  let : MeasurableSpace I := borel _
  let : BorelSpace I := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient I) := borel _
  let : BorelSpace (QuotientIntegration.LeftQuotient I) := ⟨rfl⟩
  have hI : IsClosed (I : Set rP.ker) :=
    (hH.preimage continuous_subtype_val).preimage continuous_subtype_val
  let : LocallyCompactSpace I := hI.locallyCompactSpace
  have hcover : ∀ x : rP.ker, ∃ C : OpenSubgroup rP.ker, IsCompact (C : Set rP.ker) ∧ x ∈ C := by
    intro x
    obtain ⟨C, hC, hx⟩ := Parabolic.unipotentFiniteContainment F T B {eK x}
    exact ⟨OpenSubgroup.comap eK.toMonoidHom eK.continuous C,
      eK.toHomeomorph.isClosedEmbedding.isCompact_preimage hC,
      hx (eK x) (Finset.mem_singleton_self _)⟩
  have hu := Haar.compactOpenCoverUnimodularity hcover
  let μN : Measure rP.ker := haar
  let μI : Measure I := haar
  let : IsMulRightInvariant μN := hu.1 μN
  let : IsMulRightInvariant μI := hu.2 I hI μI
  obtain ⟨ν, hν⟩ := compatibleMeasureExists I hI μN μI
  let : ν.Regular := hν.regular
  have hKB : ∀ O : Set rP.ker, IsOpen O → (1 : rP.ker) ∈ O →
      ∃ C : OpenSubgroup rP.ker, IsCompact (C : Set rP.ker) ∧ (C : Set rP.ker) ⊆ O := by
    intro O hO h1
    have hneigh : eK.symm ⁻¹' O ∈ 𝓝 (1 : U) :=
      (hO.preimage eK.symm.continuous).mem_nhds (by simpa using h1)
    let C := T.unipotentRadicalCompactOpen B (eK.symm ⁻¹' O) hneigh
    refine ⟨OpenSubgroup.comap eK.toMonoidHom eK.continuous C.val,
      eK.toHomeomorph.isClosedEmbedding.isCompact_preimage C.property.1, ?_⟩
    intro x hx
    have := C.property.2 hx
    change eK.symm (eK x) ∈ O at this
    simpa only [eK.symm_apply_apply] using this
  have hB : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ C : OpenSubgroup G, IsCompact (C : Set G) ∧ (C : Set G) ⊆ O :=
    fun O hO h1 => ⟨(T.parabolicCompactOpen B O (hO.mem_nhds h1)).val,
      (T.parabolicCompactOpen B O (hO.mem_nhds h1)).property⟩
  have hN : IsClosed (r.ker : Set G) := B.isClosed_unipotentRadical F.Carrier
  -- Compact induction in stages and integration over the kernel.
  let E1 := splitStagesCompactEquiv r s hrs hr hs Q H hker hHQ hQ hH hsH σ hσ ν hKB μN μI hν
    hN hB
  -- The coefficient of the result: the kernel intersection is trivial.
  let K := Q.comap s
  let sP := s.subgroupComap Q
  let HP := H.subgroupOf Q
  have hSI : ∀ l, sP l ∈ HP := fun l => hsH l
  have hHPc : IsClosed (HP : Set Q) := hH.preimage continuous_subtype_val
  let σP := σ.comp (Subgroup.subgroupOfEquivOfLe hHQ).toMonoidHom
  let σI := σP.comp (rP.ker.subtype.subgroupComap HP)
  let χ := Jacquet.complexCharacter (splitKernelHaarRatio rP sP HP hSI hHPc)
  let κ := twist χ (splitKernelCoefficientAction rP sP HP hSI σP)
  have hItriv : ∀ i : I, i = 1 := by
    intro i
    have hk : r (((i : rP.ker) : Q) : G) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp (i : rP.ker).property)
    have hx := openPiece_eq_leviInParabolic B F.Carrier ⟨((i : rP.ker) : Q), i.property⟩
    change ((i : rP.ker) : Q) = s (r (((i : rP.ker) : Q) : G)) at hx
    rw [hk, map_one] at hx
    exact Subtype.ext (Subtype.ext (Subtype.ext hx))
  have : Subsingleton I := ⟨fun i j => (hItriv i).trans (hItriv j).symm⟩
  have hσI : ∀ i, σI i = 1 := fun i => by rw [hItriv i, map_one]
  let lin := coinvariantsTrivialEquiv σI hσI
  -- The Haar ratio and the normalizing character are trivial on `N_M`.
  have hmod : ∀ l : K, T.leviModulus B (l : L) = 1 := fun l =>
    leviModulus_eq_one_of_upperUnipotent T B (l : L) fun i =>
      (Subgroup.mem_pi _).mp (hK.le l.property) i (Set.mem_univ i)
  have hden : ∀ l : K, mulEquivHaarChar (splitKernelConjugation rP sP l) = 1 := by
    intro l
    let b : U ≃ₜ* U := splitKernelConjugation r s (l : L)
    rw [haarChar_eq_of_conjugacy eK (splitKernelConjugation rP sP l) b (fun u => Subtype.ext rfl),
      mulEquivHaarChar_eq haar b]
    have hb : (b : U → U) = B.leviAction F.Carrier (l : L)⁻¹ := by
      funext u
      apply Subtype.ext
      change (s l)⁻¹ * (u : G) * s l = s (l : L)⁻¹ * (u : G) * (s (l : L)⁻¹)⁻¹
      rw [map_inv, inv_inv]
    have hmap : (haar : Measure U).map b = haar := by
      rw [hb, glBlockModulusHaar p F T (n + 1) B haar ((l : L)⁻¹), map_inv, hmod l, inv_one,
        Units.val_one, inv_one, one_smul]
    simp only [hmap, haarScalarFactor_self]
  have hχ : ∀ l : K, (χ l : ℂ) = 1 := by
    intro l
    have hratio : (splitKernelHaarRatio rP sP HP hSI hHPc l : ℝ≥0) = 1 := by
      rw [splitKernelHaarRatio_apply, mulEquivHaarChar_eq_one_of_compactSpace, hden l, div_one]
    rw [Jacquet.complexCharacter_apply, hratio]
    simp
  let δ' := Jacquet.inverseHalfCharacter (T.leviModulus B)
  have hδ : ∀ l : K, (δ' (l : L) : ℂ) = 1 := by
    intro l
    have hl : (l : L) ∈ δ'.ker := by
      rw [Jacquet.inverseHalfCharacter_ker]
      exact hmod l
    rw [MonoidHom.mem_ker.mp hl, Units.val_one]
  have hδopen : IsOpen (δ'.ker : Set L) :=
    Jacquet.isOpen_ker_inverseHalfCharacter _ (T.isOpen_ker_leviModulus B)
  -- On `N_M` the coefficient action is the Levi Whittaker character.
  have hc : ∀ (l : K) (v : ℂ), σP (splitKernelSection sP HP hSI l) v =
      (leviWhittakerCharacter B ψ.complex (Subgroup.inclusion hK.le l) : ℂ) • v := by
    intro l v
    have hl : ∀ j, (l : L) j ∈ upperUnipotent (B.size j) F.Carrier := fun j =>
      (Subgroup.mem_pi _).mp (hK.le l.property) j (Set.mem_univ j)
    have hpc := openPiece_character B F.Carrier ψ.complex ⟨s l, hsH l⟩
      (fun j => ⟨(l : L) j, hl j⟩) fun j => (congrFun (hrs l) j).symm
    change (entrywiseCharacter ψ.complex (n + 1)
        (stabilizerToInducing N G w ⟨s l, hsH l⟩) : ℂ) • v = _
    rw [hpc, leviWhittakerCharacter_apply]
    rfl
  have hact : ∀ (l : K) (x : Representation.Coinvariants σI),
      coinvariantsTrivialEquiv σI hσI (twist (δ'.comp K.subtype) κ l x) =
        (((leviWhittakerCharacter B ψ.complex).comp (Subgroup.inclusion hK.le)) l : ℂ) •
          coinvariantsTrivialEquiv σI hσI x := by
    intro l x
    induction x using Representation.Coinvariants.induction_on with
    | h v =>
      have h1 : twist (δ'.comp K.subtype) κ l (Representation.Coinvariants.mk σI v) =
          Representation.Coinvariants.mk σI (σP (splitKernelSection sP HP hSI l) v) := by
        change (δ' (l : L) : ℂ) • ((χ l : ℂ) • splitKernelCoefficientAction rP sP HP hSI σP l
            (Representation.Coinvariants.mk σI v)) = _
        simp only [hδ l, hχ l, one_smul]
        rfl
      exact (congrArg (coinvariantsTrivialEquiv σI hσI) h1).trans (hc l v)
  let e5 := characterRepresentationEquiv (twist (δ'.comp K.subtype) κ)
    (coinvariantsTrivialEquiv σI hσI) _ hact
  exact ⟨(parabolicNormalizedJacquetTwistEquiv T B _).trans
    (((twistEquiv δ' E1).trans (compactInductionTwistEquiv K ⟨δ', hδopen⟩ κ)).trans
      (compactInducedCongrSubgroup hK e5))⟩

/-- The normalized Jacquet module of the Gelfand–Graev representation of `GL_(n+1)(F)` along a
standard block parabolic is the Gelfand–Graev representation of the Levi. -/
theorem gelfandGraevJacquet :
    RankinSelberg.SupercuspidalCompleteness.GelfandGraevJacquetStatement.{uF} :=
  gelfandGraevJacquet_of_openPiece gelfandGraevOpenPiece

end Langlands.Whittaker
