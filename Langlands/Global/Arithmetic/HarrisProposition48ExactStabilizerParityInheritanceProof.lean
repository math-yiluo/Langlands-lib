import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerInheritanceStatement
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.Correspondence.BaseReciprocityCoherence
import Langlands.LocalFactor.DeligneHenniartInductionStep

/-! # Exact stabilizer under the Proposition 4.8 parity correction -/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField IsDedekindDomain AdelicFunctoriality
open LocalFactor.CommonClosure GeneralPosition Weil.Local
open scoped NumberField AdelicFunctoriality.FiniteExtension

/-- In the auxiliary tower, the two maps from the base completion to the top agree. -/
private theorem auxiliaryCompletionMap_tower (Q : Proposition48Problem.{uF})
    (x : FiniteCompletion Q.E Q.Ps.v) :
    FiniteExtension.completionMap Q.Ps.v' Q.Ps.vTilde
        (FiniteExtension.completionMap Q.Ps.v Q.Ps.v' x) =
      FiniteExtension.completionMap Q.Ps.v Q.Ps.vTilde x := by
  refine congrFun ((Q.Ps.v.denseRange_algebraMap Q.E).equalizer
    ((FiniteExtension.continuous_completionMap Q.Ps.v' Q.Ps.vTilde).comp
      (FiniteExtension.continuous_completionMap Q.Ps.v Q.Ps.v'))
    (FiniteExtension.continuous_completionMap Q.Ps.v Q.Ps.vTilde) ?_) x
  funext a
  simp only [Function.comp_apply, FiniteExtension.completionMap_coe,
    IsScalarTower.algebraMap_apply Q.E Q.E' Q.L]

/-- The range clause identifies the auxiliary completion of `E'` with `F'`. -/
private def auxiliaryCompletionEquiv (Q : Proposition48Problem.{uF})
    (hP : Q.Ps.IsCompatible) : FiniteCompletion Q.E' Q.Ps.v' ≃+* Q.F'.field := by
  let embed : FiniteCompletion Q.E' Q.Ps.v' →+* AlgebraicClosure Q.F.Carrier :=
    (galoisClosure Q.F Q.F').field.val.toRingHom.comp
      (Q.Ps.isoTilde.toRingHom.comp (FiniteExtension.completionMap Q.Ps.v' Q.Ps.vTilde))
  have hrange : Set.range embed = (Q.F'.field : Set (AlgebraicClosure Q.F.Carrier)) := hP.2
  let toField := embed.codRestrict Q.F'.field (fun x => by
    change embed x ∈ (Q.F'.field : Set (AlgebraicClosure Q.F.Carrier))
    rw [← hrange]
    exact ⟨x, rfl⟩)
  apply RingEquiv.ofBijective toField
  constructor
  · intro x y hxy
    exact embed.injective (congrArg (fun z : Q.F'.field => (z : AlgebraicClosure Q.F.Carrier)) hxy)
  · intro y
    have hy : (y : AlgebraicClosure Q.F.Carrier) ∈ Set.range embed := by
      rw [hrange]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

/-- The Weil character at the corrected auxiliary place is twisted by an ambient character. -/
private theorem correctedWeilCharacter_twist (Q : Proposition48Problem.{uF})
    (ν : HeckeCharacter Q.E) (χs : FieldCharacter Q.F Q.F')
    (he : NormalizedReciprocity Q.F Q.e) (hP : Q.Ps.IsCompatible)
    (hold : Q.Ps.HasComponent Q.ξ Q.χs)
    (hnew : Q.Ps.HasComponent (Q.correctedCharacter ν) χs) :
    ∃ ψ : localWeilGroup Q.F →* ℂˣ, ∀ w : weilSubgroup Q.F Q.F',
      weilCharacter Q.F Q.e Q.F' χs w =
        weilCharacter Q.F Q.e Q.F' Q.χs w * ψ w.val := by
  let base := Correspondence.baseExtension Q.F
  let hbase : base.field ≤ Q.F'.field := bot_le
  let : Algebra base.field Q.F'.field := (IntermediateField.inclusion hbase).toAlgebra
  let := (fieldData Q.F base).topology
  let baseIso : FiniteCompletion Q.E Q.Ps.v ≃+* base.field :=
    Q.Ps.iso.trans (IntermediateField.botEquiv Q.F.Carrier
      (AlgebraicClosure Q.F.Carrier)).symm.toRingEquiv
  let extIso := auxiliaryCompletionEquiv Q hP
  have hcomm : (algebraMap base.field Q.F'.field).comp baseIso.toRingHom =
      extIso.toRingHom.comp (FiniteExtension.completionMap Q.Ps.v Q.Ps.v') := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    change ((baseIso x : base.field) : AlgebraicClosure Q.F.Carrier) =
      (Q.Ps.isoTilde (FiniteExtension.completionMap Q.Ps.v' Q.Ps.vTilde
        (FiniteExtension.completionMap Q.Ps.v Q.Ps.v' x)) : AlgebraicClosure Q.F.Carrier)
    rw [auxiliaryCompletionMap_tower, hP.1]
    change (((IntermediateField.botEquiv Q.F.Carrier (AlgebraicClosure Q.F.Carrier)).symm
      (Q.Ps.iso x) : base.field) : AlgebraicClosure Q.F.Carrier) = _
    rw [IntermediateField.botEquiv_symm]
    rfl
  have hnorm (x : (FiniteCompletion Q.E' Q.Ps.v')ˣ) :
      FiniteExtension.localUnitNorm Q.Ps.v Q.Ps.v' x =
        Units.map baseIso.symm.toMonoidHom
          (base.unitsNorm Q.F' hbase (Units.map extIso.toMonoidHom x)) := by
    apply Units.ext
    exact Algebra.norm_eq_of_equiv_equiv baseIso extIso hcomm (x : FiniteCompletion Q.E' Q.Ps.v')
  let μ := (ν.finiteComponent Q.Ps.v).toMonoidHom.comp (Units.map baseIso.symm.toMonoidHom)
  let ψ : localWeilGroup Q.F →* ℂˣ :=
    μ.comp ((reciprocityUnits Q.F Q.e base).toMonoidHom.comp
      (Correspondence.baseWeilEquiv Q.F).toMulEquiv.toMonoidHom)
  refine ⟨ψ, fun w => ?_⟩
  let y := reciprocityUnits Q.F Q.e Q.F' w
  obtain ⟨x, hx⟩ := (Units.mapEquiv extIso.toMulEquiv).surjective y
  have hxy : (y.val : AlgebraicClosure Q.F.Carrier) =
      Q.Ps.isoTilde (FiniteExtension.completionMap Q.Ps.v' Q.Ps.vTilde x.val) := by
    rw [← hx]
    rfl
  have hχ := hnew x y hxy
  change (Q.ξ * HeckeCharacter.normComp (L := Q.E') ν).finiteComponent Q.Ps.v' x = χs y at hχ
  rw [HeckeCharacter.finiteComponent_mul] at hχ
  change Q.ξ.finiteComponent Q.Ps.v' x *
    (HeckeCharacter.normComp (L := Q.E') ν).finiteComponent Q.Ps.v' x = χs y at hχ
  have hcomp := HeckeCharacter.normComp_finiteComponent ν Q.Ps.v
    (⟨Q.Ps.v', inferInstance⟩ : FinitePlacesAbove Q.E' Q.Ps.v) x
  change (HeckeCharacter.normComp (L := Q.E') ν).finiteComponent Q.Ps.v' x =
    ν.finiteComponent Q.Ps.v (FiniteExtension.localUnitNorm Q.Ps.v Q.Ps.v' x) at hcomp
  rw [hold x y hxy, hcomp, hnorm x] at hχ
  change χs y = Q.χs y * μ (reciprocityUnits Q.F Q.e base
    (weilInclusion Q.F base Q.F' hbase w))
  rw [LocalFactor.NonabelianSystem.DeligneHenniart.reciprocityUnits_weilInclusion Q.F he]
  change χs y = Q.χs y * μ (base.unitsNorm Q.F' hbase y)
  have hmap : Units.map extIso.toMonoidHom x = y := hx
  rw [hmap] at hχ
  exact hχ.symm

/-- A twist by a character of `W_F` preserves the exact stabilizer. -/
private theorem hasExactWeilStabilizer_twist {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} {F' : Extension F}
    {χ χ' : weilSubgroup F F' →ₜ* ℂˣ} (ψ : localWeilGroup F →* ℂˣ)
    (htwist : ∀ w : weilSubgroup F F', χ' w = χ w * ψ w.val)
    (h : HasExactWeilStabilizer F F' χ) : HasExactWeilStabilizer F F' χ' := by
  intro g
  rw [← h g]
  let conj : weilSubgroup F (galoisClosure F F') →* weilSubgroup F (galoisClosure F F') :=
    (MulAut.conjNormal g⁻¹).toMonoidHom
  have hmul (x : weilSubgroup F (galoisClosure F F')) :
      closureRestriction F F' χ' x = closureRestriction F F' χ x * ψ x.val :=
    htwist (Subgroup.inclusion (galoisClosure_weilSubgroup_le F F') x)
  have hinv (x : weilSubgroup F (galoisClosure F F')) : ψ (conj x).val = ψ x.val := by
    change ψ (g⁻¹ * x.val * (g⁻¹)⁻¹) = ψ x.val
    rw [inv_inv, map_mul, map_mul, map_inv]
    exact (mul_assoc _ _ _).trans (inv_mul_cancel_comm_assoc (ψ g) (ψ x.val))
  change (closureRestriction F F' χ').comp conj = closureRestriction F F' χ' ↔
    (closureRestriction F F' χ).comp conj = closureRestriction F F' χ
  constructor
  · intro hfix
    apply MonoidHom.ext
    intro x
    have hx := DFunLike.congr_fun hfix x
    change closureRestriction F F' χ' (conj x) = closureRestriction F F' χ' x at hx
    rw [hmul, hmul, hinv] at hx
    exact mul_right_cancel hx
  · intro hfix
    apply MonoidHom.ext
    intro x
    have hx := DFunLike.congr_fun hfix x
    change closureRestriction F F' χ (conj x) = closureRestriction F F' χ x at hx
    change closureRestriction F F' χ' (conj x) = closureRestriction F F' χ' x
    rw [hmul, hmul, hinv, hx]

/-- Harris's condition (4.12) is inherited by the parity-corrected problem. -/
theorem proposition48ExactStabilizerParityInheritance :
    Proposition48ExactStabilizerParityInheritanceStatement.{uF} := by
  intro Q b ν χs hQ hparity
  obtain ⟨he, _, _, _, _, hP, _, _, hStab, _, _, _, hχ⟩ := hQ
  obtain ⟨he', hsplit, htower, hnormal, hp, hcompat, hplace, hconjPlace, _, halgebraic,
    hregular, hconj, hχ'⟩ := hparity.2.2.2
  obtain ⟨ψ, htwist⟩ := correctedWeilCharacter_twist Q ν χs he hP hχ hχ'
  exact ⟨he', hsplit, htower, hnormal, hp, hcompat, hplace, hconjPlace,
    hasExactWeilStabilizer_twist ψ htwist hStab, halgebraic, hregular, hconj, hχ'⟩

end Langlands.Global.Harris
