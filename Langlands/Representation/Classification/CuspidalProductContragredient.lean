import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Classification.SupercuspidalContragredient
import Langlands.Representation.Classification.SupercuspidalContragredientProof
import Langlands.Representation.Parabolic.NaturalInductionDualityProof
import Langlands.Representation.Tensor.SmoothDualInjectivityProof
import Langlands.Representation.Tensor.SmoothDualSurjectivityProof
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Induction.BlockCharacterAbsorption
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Twist.SmoothPartDefinitions
import Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof

/-!
# Contragredients and determinant twists of cuspidal products

For a product `A_1 × ⋯ × A_r` of supercuspidal representatives, the twist by
`|det|^t` of its smooth contragredient is equivalent to the product of the
representatives `|det|^t Ã_i` of the data `ν^t ρ̃_i`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.CuspidalProductContragredient

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

section Data

/-- The class `[ρ̃]` of the smooth contragredient. It is irreducible so that
unification never unfolds it while comparing data. -/
@[irreducible]
def dualClass (ρ : T.CuspidalDatum.{uV, uF}) :
    letI := T.topology
    GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := ρ.rank) :=
  T.supercuspidalClassContragredient supercuspidalContragredient.{uF, uV} ρ.rank ρ.cls

theorem dualClass_def (ρ : T.CuspidalDatum.{uV, uF}) :
    dualClass ρ =
      T.supercuspidalClassContragredient supercuspidalContragredient.{uF, uV} ρ.rank ρ.cls := by
  unfold dualClass
  rfl

/-- The cuspidal datum `ρ̃` of the smooth contragredient. -/
def dualDatum (ρ : T.CuspidalDatum.{uV, uF}) : T.CuspidalDatum.{uV, uF} where
  rank := ρ.rank
  rank_pos := ρ.rank_pos
  cls := dualClass ρ

@[simp]
theorem dualDatum_rank (ρ : T.CuspidalDatum.{uV, uF}) : (dualDatum ρ).rank = ρ.rank := rfl

theorem dualDatum_cls (ρ : T.CuspidalDatum.{uV, uF}) :
    (dualDatum ρ).cls =
      T.supercuspidalClassContragredient supercuspidalContragredient.{uF, uV} ρ.rank ρ.cls :=
  dualClass_def ρ

theorem dualDatum_dualDatum (ρ : T.CuspidalDatum.{uV, uF}) : dualDatum (dualDatum ρ) = ρ := by
  obtain ⟨r, hr, a⟩ := ρ
  change CuspidalDatum.mk r hr (dualClass (dualDatum ⟨r, hr, a⟩)) = _
  rw [dualClass_def]
  change CuspidalDatum.mk r hr
    (T.supercuspidalClassContragredient supercuspidalContragredient.{uF, uV} r
      (dualClass ⟨r, hr, a⟩)) = _
  rw [dualClass_def]
  exact congrArg (CuspidalDatum.mk r hr)
    (T.supercuspidalClassContragredient_involutive supercuspidalContragredient.{uF, uV} r a)

/-- Dualizing a supercuspidal class commutes with `ν^s ↦ ν^(-s)`. -/
theorem classContragredient_realPowerTwist (n : ℕ) (s : ℝ)
    (a : letI := T.topology
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n)) :
    T.supercuspidalClassContragredient supercuspidalContragredient.{uF, uV} n
        (T.supercuspidalClassRealPowerTwist n s a) =
      T.supercuspidalClassRealPowerTwist n (-s)
        (T.supercuspidalClassContragredient supercuspidalContragredient.{uF, uV} n a) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  unfold PadicField.TopologicalData.supercuspidalClassContragredient
    PadicField.TopologicalData.supercuspidalClassRealPowerTwist
  rw [SupercuspidalClass.contragredient_twist]
  exact SupercuspidalClass.twist_congr (by
    rw [PadicField.TopologicalData.determinantPowerCharacter,
      PadicField.TopologicalData.determinantPowerCharacter, realPowerCharacter_neg]) _ _ _ _ _

/-- `(ν^s ρ)~ = ν^(-s) ρ̃`. -/
theorem dualDatum_twist (s : ℝ) (ρ : T.CuspidalDatum.{uV, uF}) :
    dualDatum (ρ.twist s) = (dualDatum ρ).twist (-s) := by
  obtain ⟨r, hr, a⟩ := ρ
  change CuspidalDatum.mk r hr (dualClass ((⟨r, hr, a⟩ : T.CuspidalDatum.{uV, uF}).twist s)) =
    CuspidalDatum.mk r hr
    (T.supercuspidalClassRealPowerTwist r (-s) (dualClass ⟨r, hr, a⟩))
  rw [dualClass_def, dualClass_def]
  exact congrArg (CuspidalDatum.mk r hr) (classContragredient_realPowerTwist r s a)

/-- The family `ν^t ρ̃_i`. -/
def twistedDualData (t : ℝ) {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF}) :
    Fin r → T.CuspidalDatum.{uV, uF} :=
  fun i => (dualDatum (ρ i)).twist t

theorem twistedDualData_rank (t : ℝ) {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (i : Fin r) : (twistedDualData t ρ i).rank = (ρ i).rank := rfl

theorem sum_twistedDualData_rank (t : ℝ) {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    {n : ℕ} (h : ∑ i, (ρ i).rank = n) : ∑ i, (twistedDualData t ρ i).rank = n := h

theorem ofFn_twistedDualData (t : ℝ) {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF}) :
    (List.ofFn (twistedDualData t ρ) : Multiset T.CuspidalDatum.{uV, uF}) =
      (List.ofFn ρ : Multiset T.CuspidalDatum.{uV, uF}).map
        (fun x => (dualDatum x).twist t) := by
  rw [Multiset.map_coe, List.map_ofFn]
  rfl

/-- If `s̃ ≤ ν ρ̃` as multisets, then `ν s ≤ ρ`. -/
theorem twist_le_of_dual_le {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF})
    (s : Multiset T.CuspidalDatum.{uV, uF})
    (h : s.map dualDatum ≤ (List.ofFn (twistedDualData 1 ρ) : Multiset _)) :
    s.map (CuspidalDatum.twist 1) ≤ (List.ofFn ρ : Multiset T.CuspidalDatum.{uV, uF}) := by
  have key := Multiset.map_le_map (f := fun x => (dualDatum x).twist 1) h
  rw [ofFn_twistedDualData, Multiset.map_map, Multiset.map_map] at key
  have hl : ((fun x => (dualDatum x).twist 1) ∘ dualDatum) =
      (CuspidalDatum.twist 1 : T.CuspidalDatum.{uV, uF} → _) := by
    funext x
    simp [dualDatum_dualDatum]
  have hr : ((fun x => (dualDatum x).twist 1) ∘ fun x => (dualDatum x).twist 1) =
      (id : T.CuspidalDatum.{uV, uF} → _) := by
    funext x
    simp only [Function.comp_apply, dualDatum_twist, dualDatum_dualDatum,
      CuspidalDatum.twist_twist, id]
    norm_num
  rw [hl, hr, Multiset.map_id] at key
  exact key

end Data

section Products

variable (T)

/-- The determinant of an upper block parabolic element is the product of the
determinants of its diagonal blocks (the argument of Worker 264's
`TwistedProductCharacterTwistProof`). -/
theorem determinant_parabolic {R : Type*} [CommRing R] {n : ℕ} (B : BlockShape n)
    (g : B.parabolic R) :
    determinant g.val = ∏ i, determinant (B.leviProjection R g i) := by
  let M : Matrix B.Index B.Index R := g.val.val.submatrix B.indexEquiv B.indexEquiv
  have hM : M.BlockTriangular Sigma.fst := g.property
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_submatrix_equiv_self B.indexEquiv]
  change M.det = _
  rw [hM.det_fintype, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro i _
  let e : Fin (B.size i) ≃ {a : B.Index // a.1 = i} :=
    Equiv.ofBijective (fun a => ⟨⟨i, a⟩, rfl⟩) (by
      constructor
      · intro a b h
        exact Sigma.mk.inj_iff.mp (congrArg Subtype.val h) |>.2 |> eq_of_heq
      · rintro ⟨⟨j, a⟩, h⟩
        dsimp only at h
        subst j
        exact ⟨a, rfl⟩)
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

/-- `|det|^t` of a block-diagonal element is the product over the blocks. -/
theorem determinantPowerCharacter_leviEmbedding {n : ℕ} (B : BlockShape n) (t : ℝ)
    (m : B.Levi F.Carrier) :
    T.determinantPowerCharacter n t (B.leviEmbedding F.Carrier m) =
      ∏ i, T.determinantPowerCharacter (B.size i) t (m i) := by
  let f : F.Carrierˣ →* ℂˣ :=
    (positiveUnitsToComplex.comp (Units.map (NNReal.rpowMonoidHom t))).comp T.normalizedAbsUnits
  change f (determinant (B.leviEmbedding F.Carrier m)) = ∏ i, f (determinant (m i))
  rw [Parabolic.FlattenedModulusCalculation.determinant_leviEmbedding, map_prod]

/-- `|det|^t` of an upper block parabolic element is the product over its Levi blocks. -/
theorem determinantPowerCharacter_parabolic {n : ℕ} (B : BlockShape n) (t : ℝ)
    (g : B.parabolic F.Carrier) :
    T.determinantPowerCharacter n t g.val =
      ∏ i, T.determinantPowerCharacter (B.size i) t (B.leviProjection F.Carrier g i) := by
  let f : F.Carrierˣ →* ℂˣ :=
    (positiveUnitsToComplex.comp (Units.map (NNReal.rpowMonoidHom t))).comp T.normalizedAbsUnits
  change f (determinant g.val) = ∏ i, f (determinant (B.leviProjection F.Carrier g i))
  rw [determinant_parabolic, map_prod]

/-- Twisting by `|det|^t` commutes with normalized block products:
`|det|^t (σ_1 × ⋯ × σ_r) ≅ (|det|^t σ_1) × ⋯ × (|det|^t σ_r)`. -/
theorem nonempty_twist_productEquiv {n : ℕ} (B : BlockShape n) (t : ℝ)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Nonempty ((twist (T.determinantPowerCharacter n t) (T.normalizedProductInduced B σ)).Equiv
      (T.normalizedProductInduced B
        (fun i => twist (T.determinantPowerCharacter (B.size i) t) (σ i)))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let χn : Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier) :=
    ⟨T.determinantPowerCharacter n t, T.isOpen_ker_determinantPowerCharacter n t⟩
  let χL : Induction.SmoothCharacter ℂ (B.Levi F.Carrier) :=
    ⟨(T.determinantPowerCharacter n t).comp (B.leviEmbedding F.Carrier),
      (T.isOpen_ker_determinantPowerCharacter n t).preimage
        (T.blockLeviEmbedding B).continuous⟩
  have hcoord (i : Fin B.length) :
      (χL.coordinate i).toMonoidHom = T.determinantPowerCharacter (B.size i) t := by
    apply MonoidHom.ext
    intro g
    change T.determinantPowerCharacter n t (B.leviEmbedding F.Carrier (Pi.mulSingle i g)) = _
    rw [determinantPowerCharacter_leviEmbedding, Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.mulSingle_eq_of_ne hji]
    · simp
  have htensor : B.blockTensor (fun i => twist (T.determinantPowerCharacter (B.size i) t) (σ i)) =
      twist χL.toMonoidHom (B.blockTensor σ) := by
    simpa only [hcoord] using χL.external_coordinate_twist σ
  let ρ := twist (T.parabolicHalfModulus B)
    ((B.blockTensor σ).comp (B.leviProjection F.Carrier))
  have hτ : twist (χn.toMonoidHom.comp (B.parabolic F.Carrier).subtype) ρ =
      twist (T.parabolicHalfModulus B)
        ((B.blockTensor (fun i => twist (T.determinantPowerCharacter (B.size i) t) (σ i))).comp
          (B.leviProjection F.Carrier)) := by
    rw [htensor]
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    change (T.determinantPowerCharacter n t g.val : ℂ) •
        ((T.parabolicHalfModulus B g : ℂ) • B.blockTensor σ (B.leviProjection F.Carrier g) v) =
      (T.parabolicHalfModulus B g : ℂ) •
        ((T.determinantPowerCharacter n t
          (B.leviEmbedding F.Carrier (B.leviProjection F.Carrier g)) : ℂ) •
            B.blockTensor σ (B.leviProjection F.Carrier g) v)
    rw [determinantPowerCharacter_parabolic, determinantPowerCharacter_leviEmbedding]
    exact smul_comm _ _ _
  exact ⟨(Induction.smoothInductionTwistEquiv (B.parabolic F.Carrier) χn ρ).trans
    (Induction.smoothInducedEquiv _ (equivOfRepresentationEq hτ))⟩

/-- Smooth duality of a normalized block product of admissible blocks:
`(σ_1 × ⋯ × σ_r)~ ≅ σ̃_1 × ⋯ × σ̃_r` (the argument of Worker 264's
`TwistedProductOrdinaryDualProof`, without exponents). -/
theorem nonempty_contragredient_productEquiv {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hτ : letI := T.topology
      ∀ i, letI := T.generalLinearTopologicalGroup (B.size i); IsAdmissible (τ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
    Nonempty ((smoothContragredient (T.normalizedProductInduced B τ)).Equiv
      (T.normalizedProductInduced B (fun i => smoothContragredient (τ i)))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
  let := T.leviTopologicalGroup B
  let σ : Rep.{uV} ℂ (B.Levi F.Carrier) := Rep.of (B.blockTensor τ)
  have hσ : IsAdmissible σ.ρ := FiniteTensor.isAdmissible_external τ hτ
  obtain ⟨EI, -⟩ := Parabolic.naturalNormalizedInductionDuality.{uF, uV}.1 p F T n B
  have hbij : Function.Bijective (FiniteTensor.smoothDualTensorMap τ) :=
    ⟨FiniteTensor.smoothDualTensorInjectivity.{0, uF, uV} (Fin B.length) _ _ τ,
      FiniteTensor.smoothDualTensorMap_surjective τ hτ
      (fun i => GeneralLinear.compactOpen_cofinal F T (B.size i))⟩
  let e2 : (FiniteTensor.external (fun i => smoothContragredient (τ i))).Equiv
      (smoothContragredient (FiniteTensor.external τ)) :=
    Representation.Equiv.mk (LinearEquiv.ofBijective _ hbij)
      (FiniteTensor.smoothDualTensorIntertwiner τ).isIntertwining'
  exact ⟨(EI σ hσ).trans (T.normalizedParabolicInducedEquiv B e2.symm)⟩

end Products

section Representatives

variable (T)

/-- The smooth contragredient `Ã` of a supercuspidal representative `A`. -/
def dualRep {n : ℕ}
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n)) :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  SupercuspidalRep.contragredient (compactOpen_cofinal F T n)
    (T.supercuspidalContragredientClosed supercuspidalContragredient.{uF, uV} n) A

@[simp]
theorem dualRep_obj {n : ℕ}
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n)) :
    (dualRep T A).obj =
      (letI := T.topology; letI := T.generalLinearTopologicalGroup n; A.obj.contragredient) :=
  rfl

/-- The representative `|det|^t Ã` of `ν^t ρ̃`. -/
def twistedDualRep (t : ℝ) {n : ℕ}
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n)) :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n) :=
  letI := T.topology
  SupercuspidalRep.twist (T.determinantPowerCharacter n t)
    (T.isOpen_ker_determinantPowerCharacter n t)
    (T.ker_determinant_le_ker_determinantPowerCharacter n t) (dualRep T A)

variable {T}

theorem dualRep_represents {ρ : T.CuspidalDatum.{uV, uF}}
    {A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank)}
    (hA : ρ.IsRepresentedBy A) : (dualDatum ρ).IsRepresentedBy (dualRep T A) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup ρ.rank
  change _ = (dualDatum ρ).cls
  rw [dualDatum_cls, ← show A.isoClass = ρ.cls from hA]
  rfl

theorem twistedDualRep_represents (t : ℝ) {ρ : T.CuspidalDatum.{uV, uF}}
    {A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank)}
    (hA : ρ.IsRepresentedBy A) :
    ((dualDatum ρ).twist t).IsRepresentedBy (twistedDualRep T t A) := by
  let := T.topology
  change _ = T.supercuspidalClassRealPowerTwist ρ.rank t (dualDatum ρ).cls
  rw [← show (dualRep T A).isoClass = (dualDatum ρ).cls from dualRep_represents hA]
  rfl

/-- The product of the representatives `Ã_i` of `ρ̃_i`, written over the block shape
of the `ρ_i`. -/
theorem cuspidalProductInduced_dualDatum {r : ℕ}
    (ρ : Fin r → T.CuspidalDatum.{uV, uF}) {n : ℕ} (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    T.cuspidalProductInduced (fun i => dualDatum (ρ i)) h (fun i => dualRep T (A i)) =
      (T.normalizedProductInductionFunctor (T.cuspidalShape ρ h)).obj
        (fun i => (dualRep T (A i)).obj) :=
  rfl

/-- The product of the representatives `|det|^t Ã_i` of `ν^t ρ̃_i`, written over the
block shape of the `ρ_i`. -/
theorem cuspidalProductInduced_twistedDualData (t : ℝ) {r : ℕ}
    (ρ : Fin r → T.CuspidalDatum.{uV, uF}) {n : ℕ} (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    T.cuspidalProductInduced (twistedDualData t ρ) h (fun i => twistedDualRep T t (A i)) =
      (T.normalizedProductInductionFunctor (T.cuspidalShape ρ h)).obj
        (fun i => (twistedDualRep T t (A i)).obj) :=
  rfl

/-- `(ρ_1 × ⋯ × ρ_r)~ ≅ ρ̃_1 × ⋯ × ρ̃_r` on actual representatives. -/
theorem nonempty_contragredient_cuspidalProductIso {r : ℕ}
    (ρ : Fin r → T.CuspidalDatum.{uV, uF}) {n : ℕ} (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Nonempty ((T.cuspidalProductInduced ρ h A).contragredient ≅
      T.cuspidalProductInduced (fun i => dualDatum (ρ i)) h (fun i => dualRep T (A i))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  rw [cuspidalProductInduced_dualDatum]
  obtain ⟨e⟩ := nonempty_contragredient_productEquiv T (T.cuspidalShape ρ h)
    (fun i => (A i).obj.representation) (fun i => (A i).property.2.1)
  exact ⟨SmoothRep.mkIso e⟩

/-- `ν^t ρ̃_1 × ⋯ × ν^t ρ̃_r ≃ |det|^t (ρ_1 × ⋯ × ρ_r)~` on actual representatives. -/
theorem nonempty_twistedDual_cuspidalProductEquiv (t : ℝ) {r : ℕ}
    (ρ : Fin r → T.CuspidalDatum.{uV, uF}) {n : ℕ} (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Nonempty ((T.cuspidalProductInduced (twistedDualData t ρ) h
        (fun i => twistedDualRep T t (A i))).representation.Equiv
      (twist (T.determinantPowerCharacter n t)
        (smoothContragredient (T.cuspidalProductInduced ρ h A).representation))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  rw [cuspidalProductInduced_twistedDualData]
  obtain ⟨e⟩ := nonempty_contragredient_productEquiv T (T.cuspidalShape ρ h)
    (fun i => (A i).obj.representation) (fun i => (A i).property.2.1)
  let : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
    fun k => T.generalLinearTopologicalGroup k
  obtain ⟨e'⟩ := nonempty_twist_productEquiv T (T.cuspidalShape ρ h) t
    (fun (i : Fin r) => smoothContragredient (A i).obj.representation)
  exact ⟨((twistEquiv (T.determinantPowerCharacter n t) e).trans e').symm⟩

end Representatives

section Subquotients

universe uR uG uW

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- A subrepresentation `B ↪ C` of a quotient `A ↠ C` is a subquotient of `A`: it
is the quotient of the preimage of `B` in `A`. -/
theorem isSubquotient_of_injective_of_surjective {A B C : SmoothRep.{uR, uG, uW} R G}
    (i : B ⟶ C) (hi : Function.Injective (SmoothRep.hom i)) (r : A ⟶ C)
    (hr : Function.Surjective (SmoothRep.hom r)) : SmoothRep.IsSubquotient B A := by
  let S : Subrepresentation A.representation :=
    { toSubmodule := (LinearMap.range (SmoothRep.hom i).toLinearMap).comap
        (SmoothRep.hom r).toLinearMap
      apply_mem_toSubmodule := fun g v hv => by
        obtain ⟨b, hb⟩ := hv
        refine ⟨B.representation g b, ?_⟩
        change SmoothRep.hom i (B.representation g b) =
          SmoothRep.hom r (A.representation g v)
        rw [Representation.IntertwiningMap.isIntertwining,
          Representation.IntertwiningMap.isIntertwining]
        exact congrArg _ hb }
  let D := SmoothRep.subrepresentation A S
  let e := LinearEquiv.ofInjective (SmoothRep.hom i).toLinearMap hi
  let q₀ : D →ₗ[R] B := e.symm.toLinearMap ∘ₗ
    (((SmoothRep.hom r).toLinearMap.comp S.toSubmodule.subtype).codRestrict
      (LinearMap.range (SmoothRep.hom i).toLinearMap) (fun v => v.property))
  have hq₀ (v : D) : SmoothRep.hom i (q₀ v) = SmoothRep.hom r v.val := by
    exact congrArg Subtype.val (e.apply_symm_apply
      (((SmoothRep.hom r).toLinearMap.comp S.toSubmodule.subtype).codRestrict
        (LinearMap.range (SmoothRep.hom i).toLinearMap) (fun v => v.property) v))
  let q : D ⟶ B := SmoothRep.ofHom
    { toLinearMap := q₀
      isIntertwining' := fun g => by
        ext v
        apply hi
        change SmoothRep.hom i (q₀ (D.representation g v)) =
          SmoothRep.hom i (B.representation g (q₀ v))
        rw [hq₀, Representation.IntertwiningMap.isIntertwining, hq₀,
          ← Representation.IntertwiningMap.isIntertwining]
        rfl }
  refine SmoothRep.isSubquotient_iff_exists.mpr
    ⟨D, SmoothRep.subtype A S, q, SmoothRep.subtype_injective A S, ?_⟩
  intro b
  obtain ⟨a, ha⟩ := hr (SmoothRep.hom i b)
  let d : D := ⟨a, Submodule.mem_comap.mpr ⟨b, ha.symm⟩⟩
  refine ⟨d, hi ?_⟩
  change SmoothRep.hom i (q₀ d) = _
  rw [hq₀]
  exact ha

end Subquotients

section Support

/-- If `σ` is an irreducible subquotient of `ρ_1 × ⋯ × ρ_r`, then `σ̃` is an
irreducible subquotient of `ρ̃_1 × ⋯ × ρ̃_r`. -/
theorem isCuspidalConstituent_contragredient {r : ℕ} {ρ : Fin r → T.CuspidalDatum.{uV, uF}}
    {n : ℕ}
    {σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hσ : T.IsCuspidalConstituent ρ σ) :
    T.IsCuspidalConstituent (fun i => dualDatum (ρ i))
      (letI := T.topology; letI := T.generalLinearTopologicalGroup n; σ.contragredient) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  obtain ⟨h, A, hA, hirr, hsub⟩ := hσ
  have hadm : σ.IsAdmissible :=
    (CuspidalSupport.cuspidalEmbedding.{uF, max uF uV} F T n σ hirr).1
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hsub
  obtain ⟨e⟩ := nonempty_contragredient_cuspidalProductIso ρ h A
  refine ⟨h, fun i => dualRep T (A i), fun i => dualRep_represents (hA i),
    (SmoothRep.isIrreducible_contragredient_iff (compactOpen_cofinal F T n) σ hadm).mpr hirr,
    SmoothRep.IsSubquotient.of_iso_right ?_ e⟩
  exact isSubquotient_of_injective_of_surjective (SmoothRep.contragredientHom q)
    (contragredientMap_injective_of_surjective _ hq) (SmoothRep.contragredientHom i)
    (contragredientMap_surjective_of_injective_of_compact_cofinal (compactOpen_cofinal F T n)
      C.isSmooth (T.cuspidalProductInduced ρ h A).isSmooth _ hi)

/-- If `s` is a supercuspidal support of `σ`, then `s̃` is one of `σ̃`. -/
theorem isSupercuspidalSupport_contragredient {n : ℕ}
    {σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset T.CuspidalDatum.{uV, uF}} (hs : T.IsSupercuspidalSupport σ s) :
    T.IsSupercuspidalSupport
      (letI := T.topology; letI := T.generalLinearTopologicalGroup n; σ.contragredient)
      (s.map dualDatum) := by
  obtain ⟨k, ρ, rfl, hρ⟩ := hs
  refine ⟨k, fun i => dualDatum (ρ i), ?_, isCuspidalConstituent_contragredient hρ⟩
  rw [Multiset.map_coe, List.map_ofFn]
  rfl

end Support

end Langlands.Classification.CuspidalProductContragredient
