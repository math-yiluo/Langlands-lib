import Langlands.Global.Arithmetic.HarrisProposition48MackeyStepStatement
import Langlands.Global.Arithmetic.HarrisMackeyReciprocity
import Langlands.Global.Arithmetic.HarrisProposition48MackeyChildProblem
import Langlands.Global.Arithmetic.HarrisProposition48MackeyFiniteProof
import Langlands.ClassField.Global.CohomologyMaps
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof

/-! # The arithmetic Mackey step in Harris's Proposition 4.8 -/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField AdelicFunctoriality LocalClassField LocalFactor.CommonClosure
open GeneralPosition Weil.Local Langlands.ClassField.Global
open scoped FiniteExtension Pointwise

private theorem doubleCosetCard {G : Type*} [Group G] (H K : Subgroup G) [hH : H.Normal] :
    Nat.card (DoubleCoset.Quotient (H : Set G) K) = (H ⊔ K).index := by
  change Nat.card (DoubleCoset.Quotient (H : Set G) K) = Nat.card (G ⧸ (H ⊔ K))
  apply Nat.card_congr
  apply Quotient.congrRight
  intro x y
  rw [DoubleCoset.rel_iff, QuotientGroup.leftRel_apply]
  change (∃ h ∈ H, ∃ k ∈ K, y = h * x * k) ↔ x⁻¹ * y ∈ (↑(H ⊔ K) : Set G)
  rw [Subgroup.normal_mul]
  constructor
  · rintro ⟨h, hh, k, hk, rfl⟩
    refine ⟨x⁻¹ * h * x, ?_, k, hk, by simp [mul_assoc]⟩
    change x⁻¹ * h * x ∈ H
    simpa only [inv_inv] using hH.conj_mem h hh x⁻¹
  · rintro ⟨h, hh, k, hk, hxy⟩
    refine ⟨x * h * x⁻¹, hH.conj_mem h hh x, k, hk, ?_⟩
    calc
      y = x * (x⁻¹ * y) := by simp
      _ = x * h * x⁻¹ * x * k := by simp [hxy, mul_assoc]

namespace Proposition48Problem

private theorem mackeyIndex_card (Q : Proposition48Problem.{uF}) [IsGalois Q.E Q.L]
    (D : IntermediateField Q.E Q.L) (hD : Q.IsPrimeCyclicStep D) :
    Nat.card (Q.MackeyIndex D) = 1 ∨ Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D := by
  let : IsGalois Q.E D := hD.1
  unfold MackeyIndex
  rw [doubleCosetCard]
  apply hD.2.2.eq_one_or_self_of_dvd
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  exact Subgroup.index_dvd_of_le le_sup_left

set_option maxHeartbeats 600000 in
private theorem exists_compatibleWeilLift (Q : Proposition48Problem.{uF})
    [IsGalois Q.E Q.L] (hP : Q.Ps.IsCompatible) (hUnique : HasUniquePlaceAbove Q.L Q.Ps.v)
    (a : Q.L ≃ₐ[Q.E] Q.L) :
    ∃ (σ : FiniteCompletion Q.L Q.Ps.vTilde ≃+* FiniteCompletion Q.L Q.Ps.vTilde)
      (g : localWeilGroup Q.F),
      Continuous σ ∧
      (∀ y : Q.L, σ (algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) y) =
        algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) (a.symm y)) ∧
      ∀ y, (Q.Ps.isoTilde (σ y) : AlgebraicClosure Q.F.Carrier) =
        (localProjection Q.F g).symm (Q.Ps.isoTilde y) := by
  let e := MackeyCompletion.autEquiv Q.Ps.v Q.Ps.vTilde hUnique
  let σ := e.symm a.symm
  let M := galoisClosure Q.F Q.F'
  let : CharZero Q.F.Carrier := Algebra.charZero_of_charZero (Padic Q.p) Q.F.Carrier
  let : IsGalois Q.F.Carrier M.field := by
    change IsGalois Q.F.Carrier
      (IntermediateField.normalClosure Q.F.Carrier Q.F'.field (AlgebraicClosure Q.F.Carrier))
    infer_instance
  let s : Gal(M.field/Q.F.Carrier) :=
    { (Q.Ps.isoTilde.symm.trans σ.toRingEquiv).trans Q.Ps.isoTilde with
      commutes' := fun x => by
        obtain ⟨y, rfl⟩ := Q.Ps.iso.surjective x
        rw [← hP.1 y]
        change Q.Ps.isoTilde (σ (Q.Ps.isoTilde.symm (Q.Ps.isoTilde
          (algebraMap (FiniteCompletion Q.E Q.Ps.v) (FiniteCompletion Q.L Q.Ps.vTilde) y)))) = _
        rw [Q.Ps.isoTilde.symm_apply_apply, σ.commutes]
        rfl }
  have hSurj : Function.Surjective (fun w : localWeilGroup Q.F =>
      (localProjection Q.F w).restrictNormal M.field) :=
    denseRange_discrete.mp <|
      (AlgEquiv.restrictNormalHom_surjective (K₁ := M.field)
        (AlgebraicClosure Q.F.Carrier)).denseRange.comp (localProjection_denseRange Q.F)
        (InfiniteGalois.restrictNormalHom_continuous M.field)
  obtain ⟨w, hw⟩ := hSurj s
  refine ⟨σ.toRingEquiv, w⁻¹, continuous_localAut Q.Ps.v Q.Ps.vTilde σ, ?_, ?_⟩
  · intro y
    have h := (MackeyCompletion.autEquiv_apply Q.Ps.v Q.Ps.vTilde hUnique σ y).symm
    change σ (algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) y) =
      algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) (e (e.symm a.symm) y) at h
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  · intro y
    have h := AlgEquiv.restrictNormal_commutes (localProjection Q.F w) M.field (Q.Ps.isoTilde y)
    change (localProjection Q.F w).restrictNormal M.field = s at hw
    rw [hw] at h
    calc
      _ = (s (Q.Ps.isoTilde y) : AlgebraicClosure Q.F.Carrier) := by
        change (Q.Ps.isoTilde (σ y) : AlgebraicClosure Q.F.Carrier) =
          Q.Ps.isoTilde (σ (Q.Ps.isoTilde.symm (Q.Ps.isoTilde y)))
        rw [Q.Ps.isoTilde.symm_apply_apply]
      _ = (show Gal(AlgebraicClosure Q.F.Carrier/Q.F.Carrier) from
        localProjection Q.F w) (Q.Ps.isoTilde y) := h
      _ = _ := by rw [map_inv]; rfl

set_option maxHeartbeats 800000 in
private theorem exists_child_of_tower (Q : Proposition48Problem.{uF}) [IsGalois Q.E Q.L]
    (D : IntermediateField Q.E Q.L) (a : Q.L ≃ₐ[Q.E] Q.L) (T : Extension Q.F)
    (A : MackeyChild.CompletedBase Q D T) (hP : Q.Ps.IsCompatible)
    (hUnique : HasUniquePlaceAbove Q.L Q.Ps.v) (hPrime : (Module.finrank Q.E D).Prime)
    {b : ℕ} (hParent : Q.IsAuxiliaryValidAtParity b) (he : NormalizedReciprocity Q.F Q.e)
    (hχ : Q.Ps.HasComponent Q.ξ Q.χs)
    {n : ℕ} (S : Fin (n + 1) → Extension Q.F)
    (hT : ∀ i, T.field ≤ (S i).field)
    (htop : (S 0).field = (galoisClosure Q.F Q.F').field)
    (hbot : S (Fin.last n) = T)
    (hstep : ∀ i : Fin n, IsCyclicPrimeStep Q.F (S i.succ) (S i.castSucc))
    (hirr : ∀ (i : Fin (n + 1)) (g : localWeilGroup Q.F),
      (mackeyConstituent (weilSubgroup Q.F Q.F') (weilSubgroup Q.F (S i))
        (FiniteRepresentation.characterLine.{uF, 0}
          (weilCharacter Q.F Q.e Q.F' Q.χs).toMonoidHom) g).IsIrreducible) :
    ∃ R : Proposition48Problem.{uF}, Q.IsAuxiliaryMackeyChild D a R ∧
      R.IsAuxiliaryValidAtParity b ∧ Module.finrank R.E R.E' = Q.mackeyRank D a ∧
      R.inductionDegree < Q.inductionDegree := by
  obtain ⟨σ, g, hσ, hσa, hστ⟩ := Q.exists_compatibleWeilLift hP hUnique a
  let τ := localProjection Q.F g
  let TP := T.asPadicField (p := Q.p)
  let C := A.localInducing a
  let U : Extension Q.F := ⟨T.field ⊔ (Q.F'.conj τ).field, inferInstance⟩
  have hU : A.parentInducingField a = U.field :=
    A.parentInducingField_eq a hUnique hP τ σ hσ hσa hστ
  let f := A.parentInducingEquivTo a U hU
  have hf (x : C.field) : (f x : AlgebraicClosure Q.F.Carrier) =
      intermediateClosureEquiv Q.F T (x : AlgebraicClosure T.field) :=
    A.parentInducingEquiv_apply a x
  have hle : (Q.F'.conj τ).field ≤ U.field := le_sup_right
  let η := mackeyFieldCharacter Q.F T U C f hf Q.F' g hle Q.χs
  have hη := mackeyFieldCharacter_apply Q.F T U C f hf Q.F' g hle Q.χs
  have hComponent := A.place_hasComponent a hUnique hP τ σ hσ hσa hστ U hU hle hχ η hη
  obtain ⟨e, heT⟩ := commonClosureReciprocityExistence Q.p TP TP.canonicalTopologicalData
  have hC := embeddedWeil_mem_conjugate Q.F T U C f hf Q.F' g rfl
  have hM : (galoisClosure TP C).field ≤ (rebase Q.F T (S 0) (hT 0)).field := by
    intro x hx
    obtain ⟨y, hy⟩ := (A.place a hUnique).isoTilde.surjective ⟨x, hx⟩
    have hy' : ((A.place a hUnique).isoTilde y : AlgebraicClosure T.field) = x :=
      congrArg Subtype.val hy
    have hImage := (A.place_isoTilde_apply a hUnique y).symm.trans hy'
    rw [← hImage]
    apply (mem_rebase Q.F T (S 0) (hT 0) _).mpr
    rw [htop]
    change intermediateClosureEquiv Q.F T ((intermediateClosureEquiv Q.F T).symm
      (↑(Q.Ps.isoTilde _) : AlgebraicClosure Q.F.Carrier)) ∈ _
    rw [AlgEquiv.apply_symm_apply]
    exact Subtype.property _
  have hGeneral := isInGeneralPosition_of_mackey_tower Q.F Q.F' T C g
    (weilCharacter Q.F Q.e Q.F' Q.χs) (weilCharacter TP e C η) hC
    (fun w => weilCharacter_mackey Q.F T U C f hf Q.F' g Q.e he e heT Q.χs η hle hη w _ rfl)
    S hT hbot hstep hM hirr
  exact A.exists_auxiliaryMackeyChild a hUnique hPrime hParent e η heT hGeneral hComponent

end Proposition48Problem

set_option maxHeartbeats 600000 in
/-- Harris's arithmetic Mackey step, using one tower stage for every actual raw child. -/
theorem proposition48MackeyStep : Proposition48MackeyStepStatement.{uF} := by
  intro Q hParent hn
  have hParent' := hParent
  obtain ⟨he, -, hTower, hNormal, -, hP, hUnique, -, hGeneral, -, -, -, hχ⟩ := hParent'
  let : IsScalarTower Q.E Q.E' Q.L := hTower
  let : IsGalois Q.E Q.L := Q.isGalois_of_isNormalClosure hNormal
  obtain ⟨n, tower, htop, hbot, hstep, hirr⟩ := hGeneral
  cases n with
  | zero =>
      have h : (tower 0).field = (tower (Fin.last 0)).field :=
        congrArg (fun i => (tower i).field)
          (show (0 : Fin (0 + 1)) = Fin.last 0 from Fin.ext rfl)
      exact ((Q.closure_ne_bot hP hUnique hn) (htop.symm.trans (h.trans hbot))).elim
  | succ t =>
      obtain ⟨D, hD, hCompleted⟩ := Q.exists_primeCyclic_towerStep hP hUnique tower htop hbot hstep
      let S (i : Fin (t + 1)) := tower i.castSucc
      let T := S (Fin.last t)
      have hT (i : Fin (t + 1)) : T.field ≤ (S i).field :=
        tower_antitone Q.F tower hstep (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i))
      let A := MackeyChild.CompletedBase.of_tower Q D T ((hT 0).trans_eq htop) hCompleted
      refine ⟨D, hD, Q.mackeyIndex_card D hD, fun a => ?_⟩
      exact Q.exists_child_of_tower D a T A hP hUnique hD.2.2 hParent he hχ
        S hT htop rfl (fun i => hstep i.castSucc) (fun i g => hirr i.castSucc g)

end Langlands.Global.Harris
