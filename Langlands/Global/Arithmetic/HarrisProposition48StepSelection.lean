import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData
import Langlands.Global.Arithmetic.HarrisProposition48CompletionComparison

/-! # The last step of the auxiliary tower -/

noncomputable section

universe uF u

namespace Langlands.Global.Harris

open NumberField AdelicFunctoriality GeneralPosition LocalFactor.CommonClosure
open scoped NumberField FiniteExtension

section LocalTower

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

theorem tower_antitone {t : ℕ} (tower : Fin (t + 1) → Extension F)
    (hstep : ∀ i : Fin t, IsCyclicPrimeStep F (tower i.succ) (tower i.castSucc)) :
    Antitone (fun i => (tower i).field) :=
  Fin.antitone_iff_succ_le.mpr fun i => (hstep i).choose

private theorem primeStep_from_bot (A B : Extension F) (hA : A.field = ⊥)
    (h : IsCyclicPrimeStep F A B) :
    IsGalois F.Carrier B.field ∧ (Module.finrank F.Carrier B.field).Prime := by
  obtain ⟨hab, hG, _, hp⟩ := h
  let e := (IntermediateField.equivOfEq hA).trans
    (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier))
  let f : IntermediateField.extendScalars hab ≃+* B.field := RingEquiv.refl _
  have hcomm : (algebraMap F.Carrier B.field).comp e.toRingEquiv.toRingHom =
      f.toRingHom.comp (algebraMap A.field (IntermediateField.extendScalars hab)) := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    change algebraMap F.Carrier (AlgebraicClosure F.Carrier) (e x) = (x : AlgebraicClosure F.Carrier)
    obtain ⟨y, rfl⟩ := e.symm.surjective x
    rw [e.apply_symm_apply]
    exact congrArg Subtype.val (e.symm.commutes y).symm
  refine ⟨IsGalois.of_equiv_equiv (f := e.toRingEquiv) (g := f) hcomm, ?_⟩
  rw [← Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv f hcomm]
  exact hp

end LocalTower

namespace PlaceDatum

section Fields

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {F' : Extension F}
  {E E' L : Type u} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
  (P : PlaceDatum F F' E E' L) (hP : P.IsCompatible)

/-- View a stage of the original local tower as a subfield of the actual
completion of the global normal closure. -/
def towerField (T : Extension F) (hle : T.field ≤ (galoisClosure F F').field) :
    IntermediateField (P.v.adicCompletion E) (P.vTilde.adicCompletion L) :=
  MackeyCompletion.pullback P.iso P.isoTilde hP.1 (IntermediateField.restrict hle)

theorem mem_towerField (T : Extension F) (hle : T.field ≤ (galoisClosure F F').field)
    (x : P.vTilde.adicCompletion L) :
    x ∈ P.towerField hP T hle ↔ (P.isoTilde x : AlgebraicClosure F.Carrier) ∈ T.field :=
  IntermediateField.mem_restrict hle _

private def towerFieldEquiv (T : Extension F) (hle : T.field ≤ (galoisClosure F F').field) :
    P.towerField hP T hle ≃+* T.field :=
  (MackeyCompletion.pullbackEquiv P.iso P.isoTilde hP.1 (IntermediateField.restrict hle)).trans
    (IntermediateField.restrictAlgEquiv hle).symm.toRingEquiv

private theorem towerFieldEquiv_commutes (T : Extension F)
    (hle : T.field ≤ (galoisClosure F F').field) :
    (algebraMap F.Carrier T.field).comp P.iso.toRingHom =
      (P.towerFieldEquiv hP T hle).toRingHom.comp
        (algebraMap (P.v.adicCompletion E) (P.towerField hP T hle)) := by
  apply RingHom.ext
  intro x
  exact ((IntermediateField.restrictAlgEquiv hle).symm.commutes (P.iso x)).symm.trans
    (congrArg (IntermediateField.restrictAlgEquiv hle).symm
      (MackeyCompletion.pullbackEquiv_commutes P.iso P.isoTilde hP.1 _ x).symm)

theorem exists_primeCyclic_of_towerField [IsGalois E L]
    (h : HasUniquePlaceAbove L P.v)
    (T : Extension F) (hle : T.field ≤ (galoisClosure F F').field)
    (hG : IsGalois F.Carrier T.field) (hp : (Module.finrank F.Carrier T.field).Prime) :
    ∃ B : IntermediateField E L,
      MackeyCompletion.completedField P.v P.vTilde B = P.towerField hP T hle ∧
      IsGalois E B ∧ IsCyclic (B ≃ₐ[E] B) ∧ (Module.finrank E B).Prime := by
  let e := P.towerFieldEquiv hP T hle
  have hcomm := P.towerFieldEquiv_commutes hP T hle
  have hcomm' : (algebraMap (P.v.adicCompletion E) (P.towerField hP T hle)).comp P.iso.symm.toRingHom =
      e.symm.toRingHom.comp (algebraMap F.Carrier T.field) := by
    apply RingHom.ext
    intro y
    obtain ⟨x, rfl⟩ := P.iso.surjective y
    exact e.injective (by simpa using (DFunLike.congr_fun hcomm x).symm)
  have := IsGalois.of_equiv_equiv (f := P.iso.symm) (g := e.symm) hcomm'
  exact MackeyCompletion.exists_primeCyclic_completedField P.v P.vTilde h _ (by
    rw [Algebra.finrank_eq_of_equiv_equiv P.iso e hcomm]
    exact hp)

end Fields
end PlaceDatum

namespace Proposition48Problem

variable (Q : Proposition48Problem.{uF})

theorem isGalois_of_isNormalClosure (hL : IsNormalClosure Q.E Q.E' Q.L) : IsGalois Q.E Q.L := by
  have : Normal Q.E Q.L := IsNormalClosure.normal (K := Q.E')
  exact ⟨⟩

theorem closure_ne_bot (hP : Q.Ps.IsCompatible) (h : HasUniquePlaceAbove Q.L Q.Ps.v)
    (hn : 1 < Module.finrank Q.E Q.E') :
    (galoisClosure Q.F Q.F').field ≠ ⊥ := by
  intro hz
  have hdeg := (MackeyCompletion.finrank_eq Q.Ps.v Q.Ps.vTilde h).symm.trans
    (Algebra.finrank_eq_of_equiv_equiv Q.Ps.iso Q.Ps.isoTilde
      (RingHom.ext fun x => (hP.1 x).symm))
  rw [hz, IntermediateField.finrank_bot] at hdeg
  have hd := Module.finrank_dvd_finrank_right Q.E Q.E' Q.L
  exact hn.ne' (Nat.dvd_one.mp (hdeg ▸ hd))

theorem exists_primeCyclic_towerStep [IsGalois Q.E Q.L]
    (hP : Q.Ps.IsCompatible) (h : HasUniquePlaceAbove Q.L Q.Ps.v)
    {t : ℕ} (tower : Fin (t + 1 + 1) → Extension Q.F)
    (htop : (tower 0).field = (galoisClosure Q.F Q.F').field)
    (hbot : (tower (Fin.last (t + 1))).field = ⊥)
    (hstep : ∀ i : Fin (t + 1), IsCyclicPrimeStep Q.F (tower i.succ) (tower i.castSucc)) :
    ∃ D : IntermediateField Q.E Q.L, Q.IsPrimeCyclicStep D ∧
      ∀ x : Q.Ps.vTilde.adicCompletion Q.L,
        x ∈ MackeyCompletion.completedField Q.Ps.v Q.Ps.vTilde D ↔
          (Q.Ps.isoTilde x : AlgebraicClosure Q.F.Carrier) ∈
            (tower (Fin.last t).castSucc).field := by
  let i := Fin.last t
  have hle : (tower i.castSucc).field ≤ (galoisClosure Q.F Q.F').field :=
    htop ▸ tower_antitone Q.F tower hstep (Fin.zero_le _)
  have hi : (tower i.succ).field = ⊥ := by simpa only [i, Fin.succ_last] using hbot
  obtain ⟨hG, hp⟩ := primeStep_from_bot Q.F _ _ hi (hstep i)
  obtain ⟨D, hD, hdeg⟩ :=
    Q.Ps.exists_primeCyclic_of_towerField hP h _ hle hG hp
  refine ⟨D, hdeg, fun x => ?_⟩
  rw [hD]
  exact Q.Ps.mem_towerField hP _ hle x

end Proposition48Problem
end Langlands.Global.Harris
