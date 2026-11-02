import Langlands.Representation.Classification.LinkedSegmentOverlapShapes
import Langlands.Representation.Classification.ProductLeviCuspidalJacquetAssembly

/-!
# The induced side of the identity piece of two overlapping segment socles

The intersection transport of the identity piece and the normalized refined
induction from the target identity refinement, written with the triple product
`GL(deg Δ) × GL(deg init) × GL(deg term)`.
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.Classification.QuotientHom

open GeneralLinear Geometric CategoryTheory PadicField.TopologicalData
open scoped TensorProduct

universe uF uV uW

/-- Representations with the same action are equivalent. -/
def equivOfApplyEq {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ σ : Representation ℂ G V) (h : ∀ g, ρ g = σ g) : ρ.Equiv σ :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => by
    ext v
    simp [h g])

section Triple

variable {G₀ G₁ G₂ : Type*} [Monoid G₀] [Monoid G₁] [Monoid G₂]
  {V₀ V₁ V₂ : Type*} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]

/-- The external tensor product of three actions on a triple product. -/
def tripleTensor (ρ₀ : Representation ℂ G₀ V₀) (ρ₁ : Representation ℂ G₁ V₁)
    (ρ₂ : Representation ℂ G₂ V₂) :
    Representation ℂ (G₀ × G₁ × G₂) (V₀ ⊗[ℂ] (V₁ ⊗[ℂ] V₂)) :=
  Representation.tprod (ρ₀.comp (MonoidHom.fst _ _))
    (Representation.tprod (ρ₁.comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)))
      (ρ₂.comp ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _))))

end Triple

theorem reindex_finCongr_symm_self {R : Type*} [CommRing R] {a : ℕ} (h : a = a)
    (g : GeneralLinear a R) : (GeneralLinear.reindex (R := R) (finCongr h)).symm g = g := by
  apply Units.ext
  ext i j
  rfl

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData} {n : ℕ}

/-- The normalized induction from the one-block shape of `GL_m` of a single factor
is that factor. -/
def oneBlockInducedEquiv (m : ℕ) (hm : 0 < m)
    (π : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear m F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (T.normalizedParabolicInduced (CuspidalSupport.LeviAdmissibility.oneBlock m hm)
        (FiniteTensor.externalSmoothObject (fun _ => π) :
          SmoothRep.{0, uF, uW} ℂ
            ((CuspidalSupport.LeviAdmissibility.oneBlock m hm).Levi F.Carrier)).representation)
      π.representation := by
  let := T.topology
  let B := CuspidalSupport.LeviAdmissibility.oneBlock m hm
  let e : Representation.Equiv
      (T.normalizedProductInduced B (fun _ => π.representation))
      (π.representation.comp (GeneralLinear.reindex (R := F.Carrier)
        (finCongr (B.singleBlock_size rfl ⟨0, Nat.one_pos⟩))).symm.toMonoidHom) :=
    T.singleBlockNormalizedProductEquiv B rfl (fun _ => π.representation)
      (fun _ => π.isSmooth) ⟨0, Nat.one_pos⟩
  exact e.trans (equivOfApplyEq _ _ fun g =>
    congrArg π.representation (reindex_finCongr_symm_self rfl g))

/-- The normalized induction from a shape equal to the one-block shape, of a factor
equal to the external tensor of a single factor, is that factor. -/
def inducedEquivOfEq {m : ℕ} (B' : BlockShape m) (hm : 0 < m)
    (hB : B' = CuspidalSupport.LeviAdmissibility.oneBlock m hm)
    (σ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (B'.Levi F.Carrier))
    (π : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear m F.Carrier))
    (hσ : letI := T.topology
      HEq σ (FiniteTensor.externalSmoothObject (fun _ => π) :
        SmoothRep.{0, uF, uW} ℂ
          ((CuspidalSupport.LeviAdmissibility.oneBlock m hm).Levi F.Carrier))) :
    letI := T.topology
    Representation.Equiv (T.normalizedParabolicInduced B' σ.representation)
      π.representation := by
  let := T.topology
  subst hB
  obtain rfl := eq_of_heq hσ
  exact oneBlockInducedEquiv m hm π

namespace OverlapConfig

variable (O : OverlapConfig.{uF, uV} T n)

/-- The intersection transport of the identity piece: an identification of the
refined Jacquet module with a representation of `P` pulled back along `φB` becomes
the same representation pulled back along `φC`. -/
def transportedPieceEquiv
    (X : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (O.B.Levi F.Carrier))
    {V : Type*} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ O.P V)
    (eJ : letI := T.topology
      Representation.Equiv ((T.normalizedRefinedJacquetFunctor O.B O.S).obj X).representation
        (τ.comp O.φB)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    Representation.Equiv
      ((subgroupEqualityFunctor _ _ O.hR.2.1).obj
        ((intersectionTransportFunctor F.Carrier O.B O.C 1).obj
          ((subgroupEqualityFunctor _ _ O.hS.2.1.symm).obj
            ((T.normalizedRefinedJacquetFunctor O.B O.S).obj X)))).representation
      (τ.comp O.φC) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let J := (T.normalizedRefinedJacquetFunctor O.B O.S).obj X
  let J' := (subgroupEqualityFunctor _ _ O.hS.2.1.symm).obj J
  have eJ' : J'.representation.Equiv
      (τ.comp (O.φB.comp (MulEquiv.subgroupCongr O.hS.2.1.symm).symm.toMonoidHom)) :=
    SegmentEdge.subgroupEqualityCompEquiv _ _ O.hS.2.1.symm J τ O.φB eJ
  let ψB : sourceLevi F.Carrier O.B O.C 1 →* O.P :=
    O.φB.comp (MulEquiv.subgroupCongr O.hS.2.1.symm).symm.toMonoidHom
  let ψC : sourceLevi F.Carrier O.C O.B 1⁻¹ →* O.P :=
    O.φC.comp (MulEquiv.subgroupCongr O.hR.2.1).toMonoidHom
  have hψ : ∀ x y, O.B.leviEmbedding F.Carrier x.val = O.C.leviEmbedding F.Carrier y.val →
      ψB x = ψC y :=
    fun x y h => O.coords_compat _ _ h
  let Q := (intersectionTransportFunctor F.Carrier O.B O.C 1).obj J'
  have eQ : Q.representation.Equiv (τ.comp ψC) :=
    intersectionTransportEquivOne O.B O.C ψB ψC hψ J'.representation τ eJ'
  refine (SegmentEdge.subgroupEqualityCompEquiv _ _ O.hR.2.1 Q τ ψC eQ).trans
    (compEquivOfEq τ fun y => ?_)
  change O.φC ((MulEquiv.subgroupCongr O.hR.2.1) ((MulEquiv.subgroupCongr O.hR.2.1).symm y)) =
    O.φC y
  rw [MulEquiv.apply_symm_apply]

/-- The two blocks `(A₀, π₁)` of the union shape. -/
def unionBlocks
    (A₀ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.Δ.degree F.Carrier))
    (π₁ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.init.degree F.Carrier)) :
    letI := T.topology
    ∀ t, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (O.unionShape.size t) F.Carrier) :=
  letI := T.topology
  Fin.cons (α := fun t : Fin 2 =>
      SmoothRep.{0, uF, uW} ℂ (GeneralLinear (O.unionShape.size t) F.Carrier)) A₀
    (Fin.cons (α := fun t : Fin 1 =>
      SmoothRep.{0, uF, uW} ℂ (GeneralLinear (O.unionShape.size t.succ) F.Carrier)) π₁
      finZeroElim)

/-- The inducing factors of the target identity piece: `A₀ ⊗ π₁` on the refined
union block and `π₂` on the intersection block. -/
def targetFactors
    (A₀ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.Δ.degree F.Carrier))
    (π₁ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.init.degree F.Carrier))
    (π₂ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.term.degree F.Carrier)) :
    Parabolic.RefinedInductionTensor.Factors.{uF, uW} F T O.C O.R :=
  letI := T.topology
  Fin.cons (α := fun j : Fin 2 => SmoothRep.{0, uF, uW} ℂ ((O.R j).Levi F.Carrier))
    (FiniteTensor.externalSmoothObject (O.unionBlocks A₀ π₁))
    (Fin.cons (α := fun j : Fin 1 => SmoothRep.{0, uF, uW} ℂ ((O.R j.succ).Levi F.Carrier))
      (FiniteTensor.externalSmoothObject (fun _ => π₂)) finZeroElim)

set_option maxHeartbeats 1000000 in
/-- The inducing representation of the target identity piece is the triple tensor
pulled back along `φC`. -/
def inducingEquiv
    (A₀ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.Δ.degree F.Carrier))
    (π₁ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.init.degree F.Carrier))
    (π₂ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.term.degree F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (Parabolic.RefinedInductionTensor.inducingRepresentation F T O.C O.R
        (O.targetFactors A₀ π₁ π₂))
      ((tripleTensor A₀.representation π₁.representation π₂.representation).comp O.φC) := by
  let := T.topology
  let j0 : Fin O.C.length := ⟨0, Nat.zero_lt_two⟩
  let j1 : Fin O.C.length := ⟨1, Nat.one_lt_two⟩
  let M := O.targetFactors A₀ π₁ π₂
  let ψ : refinedLevi F.Carrier O.C O.R →* ∀ j, (O.R j).Levi F.Carrier :=
    (refinedLeviEquiv F.Carrier O.C O.R).symm.toMonoidHom
  let ev : ∀ j, (∀ j, (O.R j).Levi F.Carrier) →* (O.R j).Levi F.Carrier :=
    fun j => Pi.evalMonoidHom (fun j => (O.R j).Levi F.Carrier) j
  let e₁ : (FiniteTensor.external fun j => (M j).representation).Equiv
      (Representation.tprod ((M j0).representation.comp (ev j0))
        ((M j1).representation.comp (ev j1))) :=
    externalTwoEquiv (H := fun j : Fin 2 => (O.R j).Levi F.Carrier)
      fun j => (M j).representation
  let e₂ := externalTwoEquiv (H := fun t : Fin 2 => GeneralLinear ((O.R j0).size t) F.Carrier)
    fun t => (O.unionBlocks A₀ π₁ t).representation
  let e₃ := (O.R j1).singleBlockTensorEquiv rfl (fun _ => π₂.representation)
    ⟨0, Nat.one_pos⟩
  let e₄ := FiniteTensorFiltration.compCongr (e₁.trans (FiniteTensorFiltration.tprodCongr
    (FiniteTensorFiltration.compCongr e₂ (ev j0))
    (FiniteTensorFiltration.compCongr e₃ (ev j1)))) ψ
  let α := A₀.representation.comp ((MonoidHom.fst _ _).comp O.φC)
  let β := π₁.representation.comp (((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)).comp O.φC)
  let γ := π₂.representation.comp (((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)).comp O.φC)
  exact ((e₄.trans (equivOfApplyEq _ (Representation.tprod (Representation.tprod α β) γ)
    fun _ => rfl)).trans (tprodAssocEquiv α β γ)).trans (equivOfApplyEq _ _ fun _ => rfl)

/-- The induced intersection block of the target identity piece is `π₂`. -/
def inducedTermEquiv
    (A₀ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.Δ.degree F.Carrier))
    (π₁ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.init.degree F.Carrier))
    (π₂ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.term.degree F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (Parabolic.RefinedInductionTensor.blockRepresentations F T O.C O.R
        (O.targetFactors A₀ π₁ π₂) (1 : Fin 2))
      π₂.representation := by
  let := T.topology
  exact inducedEquivOfEq (T := T) (O.R (1 : Fin 2)) (O.C.positive _) rfl
    (O.targetFactors A₀ π₁ π₂ (1 : Fin 2)) π₂ HEq.rfl

/-- The induced side of the target identity piece: the union block is the product
induced from `(A₀, π₁)` and the intersection block is `π₂`. -/
theorem nonempty_inducedPieceEquiv
    (A₀ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.Δ.degree F.Carrier))
    (π₁ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.init.degree F.Carrier))
    (π₂ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.term.degree F.Carrier)) :
    letI := T.topology
    Nonempty (Representation.Equiv
      (Parabolic.RefinedInductionTensor.externalRepresentation F T O.C O.R
        (O.targetFactors A₀ π₁ π₂))
      (Representation.tprod
        ((Parabolic.RefinedInductionTensor.blockRepresentations F T O.C O.R
          (O.targetFactors A₀ π₁ π₂) (0 : Fin 2)).comp
          (Pi.evalMonoidHom (fun j : Fin 2 => GeneralLinear (O.C.size j) F.Carrier) 0))
        (π₂.representation.comp
          (Pi.evalMonoidHom (fun j : Fin 2 => GeneralLinear (O.C.size j) F.Carrier) 1)))) := by
  let := T.topology
  let H := fun j : Fin 2 => GeneralLinear (O.C.size j) F.Carrier
  let ρ := Parabolic.RefinedInductionTensor.blockRepresentations F T O.C O.R
    (O.targetFactors A₀ π₁ π₂)
  let e₀ : Representation.Equiv
      (Parabolic.RefinedInductionTensor.externalRepresentation F T O.C O.R
        (O.targetFactors A₀ π₁ π₂)) (FiniteTensor.external ρ) := Representation.Equiv.refl _
  let e₁ : Representation.Equiv (FiniteTensor.external ρ)
      (Representation.tprod ((ρ (0 : Fin 2)).comp (Pi.evalMonoidHom H 0))
        ((ρ (1 : Fin 2)).comp (Pi.evalMonoidHom H 1))) :=
    externalTwoEquiv (H := H) ρ
  let e₂ : Representation.Equiv ((ρ (1 : Fin 2)).comp (Pi.evalMonoidHom H 1))
      (π₂.representation.comp (Pi.evalMonoidHom H 1)) :=
    FiniteTensorFiltration.compCongr (O.inducedTermEquiv A₀ π₁ π₂) (Pi.evalMonoidHom H 1)
  let e₃ : Representation.Equiv (FiniteTensor.external ρ)
      (Representation.tprod ((ρ (0 : Fin 2)).comp (Pi.evalMonoidHom H 0))
        (π₂.representation.comp (Pi.evalMonoidHom H 1))) :=
    e₁.trans (FiniteTensorFiltration.tprodCongr (Representation.Equiv.refl _) e₂)
  exact ⟨e₀.trans e₃⟩

end OverlapConfig

end Langlands.Classification.QuotientHom
