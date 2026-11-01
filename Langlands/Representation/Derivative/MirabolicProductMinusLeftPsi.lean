import Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction
import Langlands.Representation.Induction.BinaryPositiveCompact

/-! The natural left Psi comparison for the actual mixed and binary products. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory Topology
open scoped TensorProduct NNReal

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct

section SubgroupEquality

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

private def compactInducedSubgroupEqEquiv (H P : Subgroup G) (h : H = P)
    (σ : Representation ℂ H V) :
    (Induction.compactInduced H σ).Equiv
      (Induction.compactInduced P (σ.comp (Subgroup.inclusion h.ge))) := by
  subst P
  exact Representation.Equiv.refl _

private theorem compactInducedSubgroupEqEquiv_natural
    (H P : Subgroup G) (h : H = P)
    (σ : Representation ℂ H V) (τ : Representation ℂ H W)
    (f : σ.IntertwiningMap τ) (z : Induction.CompactFunctions H σ) :
    compactInducedSubgroupEqEquiv H P h τ (Induction.compactInducedMap H f z) =
      Induction.compactInducedMap P
        (Induction.restrictAlongMap (Subgroup.inclusion h.ge) f)
        (compactInducedSubgroupEqEquiv H P h σ z) := by
  subst P
  rfl

end SubgroupEquality

section Positive

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
variable (X : letI := T.topology
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
    SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))

/-- The normalized quotient coefficient on the equal binary parabolic. -/
def leftPsiBinaryCoefficient :
    letI := T.topology
    Representation ℂ ((BlockShape.binary k r hk hr).parabolic F.Carrier)
      (Representation.Coinvariants ((leftPsiCoefficient T X).comp
        ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier)).subtype)) :=
  letI := T.topology
  (leftPsiNormalizedCoefficient T X).comp
    (Subgroup.inclusion (leftSubgroup_comap_levi_binary hk hr).ge)

/-- The actual normalized coefficient has the binary half-modulus action. -/
theorem leftPsiBinaryCoefficient_action :
    letI := T.topology
    ∀ (q : (BlockShape.binary k r hk hr).parabolic F.Carrier) (z),
      leftPsiCoefficientEquiv T X (leftPsiBinaryCoefficient T hk hr X q z) =
        (T.parabolicHalfModulus (BlockShape.binary k r hk hr) q : ℂ) •
          TensorProduct.map
            (X.1.representation
              ((BlockShape.binary k r hk hr).leviProjection F.Carrier q (0 : Fin 2)))
            (((Mirabolic.psiMinus T r).obj X.2).representation
              ((BlockShape.binary k r hk hr).leviProjection F.Carrier q (1 : Fin 2)))
            (leftPsiCoefficientEquiv T X z) := by
  let := T.topology
  intro q z
  let g := Subgroup.inclusion (leftSubgroup_comap_levi_binary hk hr).ge q
  let h := (levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier) g
  have hp := (leftPsiSection_binary_projection hk hr g).trans
    (leftPsiSectionTwoBlock_projection g)
  have hp0 := congrArg Prod.fst hp
  have hp1 := congrArg Prod.snd hp
  have hm := leftPsiSection_halfModulus T hk hr g
  have ha := leftPsiNormalizedCoefficient_action T X g z
  change leftPsiCoefficientEquiv T X (leftPsiNormalizedCoefficient T X g z) = _
  refine ha.trans ?_
  let A (a : GeneralLinear k F.Carrier) (b : GeneralLinear r F.Carrier) :=
    TensorProduct.map (X.1.representation a)
      (((Mirabolic.psiMinus T r).obj X.2).representation b)
      (leftPsiCoefficientEquiv T X z)
  have hpA : A ((BlockShape.binary k r hk hr).leviProjection F.Carrier q (0 : Fin 2))
      ((BlockShape.binary k r hk hr).leviProjection F.Carrier q (1 : Fin 2)) =
      A (leftProjection h).1 (projection (leftProjection h).2) :=
    congrArg₂ A hp0 hp1
  exact congrArg₂ (fun (c : ℂ) (v : X.1 ⊗[ℂ] (Mirabolic.psiMinus T r).obj X.2) =>
    c • v) hm.symm hpA.symm

/-- Compact induction of this coefficient is the positive binary product. -/
def leftPsiPositiveCompactEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r)
    Representation.Equiv
      (Induction.compactInduced
        ((leftSubgroup k r F.Carrier).comap (levi (n := k + r)))
        (leftPsiNormalizedCoefficient T X))
      (((T.binaryPositiveProductFunctor hk hr).obj
        (X.1, (Mirabolic.psiMinus T r).obj X.2)).representation) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r)
  (compactInducedSubgroupEqEquiv _ _ (leftSubgroup_comap_levi_binary hk hr)
    (leftPsiNormalizedCoefficient T X)).trans
      (T.binaryPositiveCompactEquivOf hk hr
        (X.1, (Mirabolic.psiMinus T r).obj X.2)
        (leftPsiBinaryCoefficient T hk hr X)
        (leftPsiCoefficientEquiv T X) (leftPsiBinaryCoefficient_action T hk hr X))

/-- The positive-rank left Psi equivalence, before the binary functor adapter. -/
def leftPsiPositiveEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r)
    Representation.Equiv
      (((Mirabolic.psiMinus T (k + r)).obj
        ((T.leftMixedProductFunctor k r).obj X)).representation)
      (((T.binaryPositiveProductFunctor hk hr).obj
        (X.1, (Mirabolic.psiMinus T r).obj X.2)).representation) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r)
  (leftPsiInductionEquiv T X).trans (leftPsiPositiveCompactEquiv T hk hr X)

variable {Y : letI := T.topology
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
    SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)}

/-- Restrict the actual normalized coefficient map to the binary parabolic. -/
def leftPsiBinaryCoefficientMap (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    (leftPsiBinaryCoefficient T hk hr X).IntertwiningMap
      (leftPsiBinaryCoefficient T hk hr Y) :=
  letI := T.topology
  Induction.restrictAlongMap (Subgroup.inclusion (leftSubgroup_comap_levi_binary hk hr).ge)
    (leftPsiNormalizedCoefficientMap T X f)

/-- The restricted coefficient comparison is natural in the original pair. -/
theorem leftPsiBinaryCoefficient_natural (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    ∀ z, leftPsiCoefficientEquiv T Y (leftPsiBinaryCoefficientMap T hk hr X f z) =
      TensorProduct.map (SmoothRep.hom f.1).toLinearMap
        (SmoothRep.hom ((Mirabolic.psiMinus T r).map f.2)).toLinearMap
        (leftPsiCoefficientEquiv T X z) := by
  let := T.topology
  exact leftPsiCoefficientEquiv_natural T X f

/-- The compact binary comparison commutes with both input maps. -/
theorem leftPsiPositiveCompactEquiv_natural (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r)
    ∀ z, leftPsiPositiveCompactEquiv T hk hr Y
        (Induction.compactInducedMap
          ((leftSubgroup k r F.Carrier).comap (levi (n := k + r)))
          (leftPsiNormalizedCoefficientMap T X f) z) =
      SmoothRep.hom ((T.binaryPositiveProductFunctor hk hr).map
        (f.1, (Mirabolic.psiMinus T r).map f.2))
        (leftPsiPositiveCompactEquiv T hk hr X z) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r)
  intro z
  have h₁ := compactInducedSubgroupEqEquiv_natural
    ((leftSubgroup k r F.Carrier).comap (levi (n := k + r)))
    ((BlockShape.binary k r hk hr).parabolic F.Carrier)
    (leftSubgroup_comap_levi_binary hk hr)
    (leftPsiNormalizedCoefficient T X) (leftPsiNormalizedCoefficient T Y)
    (leftPsiNormalizedCoefficientMap T X f) z
  have h₂ := T.binaryPositiveCompactEquivOf_natural hk hr
    (X := (X.1, (Mirabolic.psiMinus T r).obj X.2))
    (Y := (Y.1, (Mirabolic.psiMinus T r).obj Y.2))
    (f.1, (Mirabolic.psiMinus T r).map f.2)
    (leftPsiBinaryCoefficient T hk hr X) (leftPsiCoefficientEquiv T X)
    (leftPsiBinaryCoefficient_action T hk hr X)
    (leftPsiBinaryCoefficient T hk hr Y) (leftPsiCoefficientEquiv T Y)
    (leftPsiBinaryCoefficient_action T hk hr Y)
    (leftPsiBinaryCoefficientMap T hk hr X f)
    (leftPsiBinaryCoefficient_natural T hk hr X f)
    (compactInducedSubgroupEqEquiv _ _ (leftSubgroup_comap_levi_binary hk hr)
      (leftPsiNormalizedCoefficient T X) z)
  exact (congrArg (T.binaryPositiveCompactEquivOf hk hr
    (Y.1, (Mirabolic.psiMinus T r).obj Y.2)
    (leftPsiBinaryCoefficient T hk hr Y) (leftPsiCoefficientEquiv T Y)
    (leftPsiBinaryCoefficient_action T hk hr Y)) h₁).trans h₂

/-- Naturality of the positive-rank left Psi equivalence. -/
theorem leftPsiPositiveEquiv_natural (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r)
    ∀ z : (Mirabolic.psiMinus T (k + r)).obj ((T.leftMixedProductFunctor k r).obj X),
      leftPsiPositiveEquiv T hk hr Y
        (SmoothRep.hom ((Mirabolic.psiMinus T (k + r)).map
          ((T.leftMixedProductFunctor k r).map f)) z) =
      SmoothRep.hom ((T.binaryPositiveProductFunctor hk hr).map
        (f.1, (Mirabolic.psiMinus T r).map f.2)) (leftPsiPositiveEquiv T hk hr X z) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r)
  intro z
  exact (congrArg (leftPsiPositiveCompactEquiv T hk hr Y)
    (leftPsiInductionEquiv_natural T X f z)).trans
      (leftPsiPositiveCompactEquiv_natural T hk hr X f (leftPsiInductionEquiv T X z))

end Positive

section Compatibility

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- BZ77 Proposition 4.13(b), the exact all-rank natural Psi clause. -/
theorem leftPsiCompatibility : LeftPsiCompatibility.{uF, uV} F T := by
  let := T.topology
  intro k r
  let := T.generalLinearTopologicalGroup ((k + 1) + r)
  cases r with
  | zero =>
      exact ⟨NatIso.ofComponents
        (fun X => SmoothRep.mkIso (leftPsiZeroEquiv (k := k + 1) T X))
        (fun f => MixedProductTensor.smoothRep_hom_ext fun z =>
          leftPsiZeroEquiv_natural (k := k + 1) T _ f z)⟩
  | succ r =>
      exact ⟨NatIso.ofComponents
        (fun X => SmoothRep.mkIso
          (leftPsiPositiveEquiv (k := k + 1) (r := r + 1)
            T (Nat.succ_pos k) (Nat.succ_pos r) X))
        (fun f => MixedProductTensor.smoothRep_hom_ext fun z =>
          leftPsiPositiveEquiv_natural (k := k + 1) (r := r + 1)
            T (Nat.succ_pos k) (Nat.succ_pos r) _ f z)⟩

end Compatibility

end Langlands.Derivative.MirabolicProductMinus
