import Langlands.Correspondence.AssemblyRelation
import Langlands.Representation.Classification.MultisegmentConstituentCompatibilityStatement
import Langlands.Weil.Representation.InertiaOperations
import Langlands.Correspondence.SupercuspidalOperationRealization
import Langlands.Correspondence.AssemblyLTwistedSupercuspidal
import Langlands.WeilDeligne.BlockDualProof
import Langlands.Weil.Representation.DualClasses
import Langlands.Representation.Smooth.Contragredient.Equivalence

/-!
# Dual compatibility of the assembly

The dual part of `AssemblyOperationStatement`. The dual of a block sum
`⊕_i σ_i ⊗ Sp(m_i + 1)` is the block sum of the classes `ν^(-m_i) σ_i^∨` with the
same lengths (`isBlockSum_dual`). The published contragredient compatibility of
Langlands heads replaces each segment `[c0 σ_i, ν^(m_i) c0 σ_i]` by the segment of the
same length beginning at the contragredient of its end. Under supercuspidal twist and
dual compatibility and geometric normalization, that contragredient is
`c0 (ν^(-m_i) σ_i^∨)` (`isoClass_eq_dualWeilClass`), so the contragredient of a head
class is a head class of the dual data (`isMultisegmentHeadClass_dual`).
Well-definedness of the assembly then identifies it with the assembled class
(`dualCompatibility_of_assembly`).
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

namespace AssemblyDual

open Polynomial

section LinearAlgebra

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The transpose of a power is the power of the transpose. -/
theorem dualMap_pow (f : Module.End K V) (n : ℕ) :
    ((f ^ n).dualMap : Module.End K (Module.Dual K V)) = f.dualMap ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ, ← ih]
    rfl

/-- Evaluating a polynomial at the transpose gives the transpose of the evaluation. -/
theorem aeval_dualMap (f : Module.End K V) (q : K[X]) :
    aeval (f.dualMap : Module.End K (Module.Dual K V)) q = (aeval f q).dualMap := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    rw [map_add, map_add, hq, hr]
    apply LinearMap.ext
    intro ℓ
    apply LinearMap.ext
    intro v
    simp
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, ← dualMap_pow]
    apply LinearMap.ext
    intro ℓ
    apply LinearMap.ext
    intro v
    simp [Module.algebraMap_end_apply]

/-- The transpose of a semisimple endomorphism of a finite-dimensional space is
semisimple. -/
theorem isSemisimple_dualMap [FiniteDimensional K V] {f : Module.End K V}
    (hf : f.IsSemisimple) :
    Module.End.IsSemisimple (f.dualMap : Module.End K (Module.Dual K V)) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree
  rw [aeval_dualMap, minpoly.aeval]
  apply LinearMap.ext
  intro ℓ
  apply LinearMap.ext
  intro v
  simp

end LinearAlgebra

section DirectSum

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]

/-- The dual of a finite direct sum is the direct sum of the duals: a functional `ℓ`
goes to its restrictions `ℓ ∘ lof i`. -/
def dualDirectSumLinearEquiv :
    Module.Dual K (DirectSum ι M) ≃ₗ[K] DirectSum ι fun i => Module.Dual K (M i) :=
  ((DirectSum.linearEquivFunOnFintype K ι M).symm.dualMap.trans
    (LinearMap.lsum K M K).symm).trans
    (DirectSum.linearEquivFunOnFintype K ι fun i => Module.Dual K (M i)).symm

theorem dualDirectSumLinearEquiv_apply (ℓ : Module.Dual K (DirectSum ι M)) (i : ι)
    (v : M i) : dualDirectSumLinearEquiv ℓ i v = ℓ (DirectSum.lof K ι M i v) := by
  change ℓ ((DirectSum.linearEquivFunOnFintype K ι M).symm (Pi.single i v)) = _
  rw [DirectSum.linearEquivFunOnFintype_symm_single]

variable {G : Type*} [Group G] {ν : G →* Kˣ}

/-- The dual of a finite direct sum of Weil–Deligne representations is the direct sum
of the duals. -/
def dualDirectSumEquiv (A : ι → WeilDeligneRepresentation K G ν) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.dual (WeilDeligneRepresentation.directSum A))
      (WeilDeligneRepresentation.directSum fun i => WeilDeligneRepresentation.dual (A i)) where
  representationEquiv :=
    Representation.Equiv.mk dualDirectSumLinearEquiv (fun g => by
      apply LinearMap.ext
      intro (ℓ : Module.Dual K (DirectSum ι fun i => A i))
      apply DirectSum.ext
      intro i
      apply LinearMap.ext
      intro (v : A i)
      change dualDirectSumLinearEquiv
          (ℓ ∘ₗ DirectSum.lmap fun j => (A j).representation g⁻¹) i v =
        dualDirectSumLinearEquiv ℓ i ((A i).representation g⁻¹ v)
      rw [dualDirectSumLinearEquiv_apply, dualDirectSumLinearEquiv_apply,
        LinearMap.comp_apply, DirectSum.lmap_lof])
  comm_monodromy := by
    apply LinearMap.ext
    intro (ℓ : Module.Dual K (DirectSum ι fun i => A i))
    apply DirectSum.ext
    intro i
    apply LinearMap.ext
    intro (v : A i)
    change dualDirectSumLinearEquiv
        (-(ℓ ∘ₗ DirectSum.lmap fun j => (A j).monodromy)) i v =
      -(dualDirectSumLinearEquiv ℓ i ((A i).monodromy v))
    rw [map_neg]
    change -(dualDirectSumLinearEquiv (ℓ ∘ₗ DirectSum.lmap fun j => (A j).monodromy) i v) = _
    rw [dualDirectSumLinearEquiv_apply, dualDirectSumLinearEquiv_apply, LinearMap.comp_apply,
      DirectSum.lmap_lof]

end DirectSum

section Main

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyDualFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyDualGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance assemblyDualGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- Every parameter class has a dual parameter class: the dual of a representative
has open inertia kernel, semisimple Frobenius elements and the same rank. -/
theorem exists_isDualOf {n : ℕ+} (D : WeilDeligneClass.{uF, uP} F n) :
    ∃ E : WeilDeligneClass.{uF, uP} F n,
      WeilDeligneRepresentation.ParameterRelations.IsDualOf D E := by
  obtain ⟨c, hc⟩ := D
  induction c using Quotient.inductionOn with
  | h A =>
    refine ⟨⟨Quotient.mk _ ⟨WeilDeligneRepresentation.dual A.1, ?_, ?_⟩, ?_⟩, rfl⟩
    · exact FiniteRepresentation.hasOpenInertiaKernel_dual _ A.2.1
    · intro g hg
      have hg' : Multiplicative.toAdd (Weil.Local.localDegree F g⁻¹) ≠ 0 := by
        rwa [map_inv, toAdd_inv, neg_ne_zero]
      exact isSemisimple_dualMap (A.2.2 g⁻¹ hg')
    · exact (FiniteRepresentation.rank_dual _).trans hc

/-- The inverse of `normPowerQuasiCharacter F e m`: the field quasi-character obtained by
transporting `ω^(-m)` along the reciprocity candidate `e`. Under geometric normalization
(`IsGeometricReciprocity F e`) it is `|·|^(-m)`. -/
def dualTwistCharacter (e : ReciprocityCandidate F) (m : ℕ) : QuasiCharacter F :=
  (normPowerQuasiCharacter F e m)⁻¹

/-- For every reciprocity candidate `e`, the pullback of `dualTwistCharacter F e m` to the
Weil group is `ν^(1 - (m + 1))`. -/
theorem weilCharacter_dualTwistCharacter (e : ReciprocityCandidate F) (m : ℕ) :
    (LocalFactor.RankOne.weilCharacter F e (dualTwistCharacter F e m)).toMonoidHom =
      (Weil.Local.localNormCharacter F).toMonoidHom ^ (1 - ((m + 1 : ℕ) : ℤ)) := by
  have hz : (1 - ((m + 1 : ℕ) : ℤ)) = -(m : ℤ) := by
    push_cast
    ring
  rw [hz]
  refine MonoidHom.ext fun w => ?_
  have h := DFunLike.congr_fun (weilCharacter_normPowerQuasiCharacter F e m) w
  rw [LocalFactor.RankOne.weilCharacter_apply] at h
  change (normPowerQuasiCharacter F e m (LocalFactor.RankOne.reciprocityUnits F e w))⁻¹ =
    (Weil.Local.localNormCharacter F).toMonoidHom w ^ (-(m : ℤ))
  rw [h, zpow_neg, zpow_natCast, ContinuousMonoidHom.pow_apply]
  rfl

/-- Under geometric normalization, `dualTwistCharacter F e m ∘ det` is the inverse of
`|det|^m`. -/
theorem determinantQuasiCharacter_dualTwistCharacter {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (m : ℕ) (n : ℕ+) :
    determinantQuasiCharacter F n (dualTwistCharacter F e m) =
      (F.canonicalTopologicalData.determinantPowerCharacter (n : ℕ) (m : ℝ))⁻¹ := by
  rw [← determinantQuasiCharacter_normPowerQuasiCharacter F he m n]
  rfl

/-- The irreducible Weil class `ν^(-m) σ^∨`. -/
def dualWeilClass (e : ReciprocityCandidate F) {d : ℕ}
    (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat) (m : ℕ) :
    IrreducibleWeilClass.{uF, uP} F d.succPNat :=
  FiniteRepresentation.continuousIrreducibleTwistEquiv
    (LocalFactor.RankOne.weilCharacter F e (dualTwistCharacter F e m)) _
    (FiniteRepresentation.continuousIrreducibleDualEquiv _ σ)

/-- The dual of a block sum decomposition of `D` gives one of its dual `E`, with the
classes `ν^(-m_i) σ_i^∨` and the same lengths. -/
theorem isBlockSum_dual (e : ReciprocityCandidate F) {r : ℕ} {d : Fin r → ℕ}
    (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat) (m : Fin r → ℕ)
    {n : ℕ+} {D E : WeilDeligneClass.{uF, uP} F n} (hD : IsBlockSum F σ m D)
    (hE : WeilDeligneRepresentation.ParameterRelations.IsDualOf D E) :
    IsBlockSum F (fun i => dualWeilClass F e (σ i) (m i)) m E := by
  obtain ⟨B, A, hB, hA, ⟨φ⟩⟩ := hD
  refine ⟨fun i => FiniteRepresentation.twist
      ((Weil.Local.localNormCharacter F).toMonoidHom ^ (1 - ((m i + 1 : ℕ) : ℤ)))
      (FiniteRepresentation.dual (B i)),
    WeilDeligneRepresentation.dual A, fun i => ?_, ?_, ⟨?_⟩⟩
  · have hBi := hB i
    rw [weilClassForget] at hBi
    rw [weilClassForget]
    unfold dualWeilClass
    rw [FiniteRepresentation.forget_continuousIrreducibleTwistEquiv,
      weilCharacter_dualTwistCharacter, FiniteRepresentation.forget_continuousIrreducibleDualEquiv,
      ← hBi]
    rfl
  · rw [parameterForget, hE]
    show _ = WeilDeligneRepresentation.dualClass (parameterForget F D)
    rw [← hA]
    rfl
  · exact (WeilDeligneRepresentation.directSumCongr fun i =>
      (WeilDeligneRepresentation.Blocks.blockDualEquiv _ (B i) (m i + 1)).symm).trans
      ((dualDirectSumEquiv _).symm.trans (WeilDeligneRepresentation.dualEquiv φ).symm)

/-- Under supercuspidal twist and dual compatibility and geometric normalization, the
contragredient of the end `ν^m c0 σ` of the segment `[c0 σ, ν^m c0 σ]` is
`c0 (ν^(-m) σ^∨)`. -/
theorem isoClass_eq_dualWeilClass (c0 : SupercuspidalMap.{uF, uP, uA} F)
    {e : ReciprocityCandidate F} (he : IsGeometricReciprocity F e)
    (htwist : SupercuspidalTwistCompatibility F e c0)
    (hdual : SupercuspidalDualCompatibility F c0) {d : ℕ}
    (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat) (m : ℕ)
    (B Bv : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := d + 1))
    (hB : (segmentOf F c0 σ m).last.IsRepresentedBy B)
    (hBv : Nonempty (Bv.obj.representation.Equiv (smoothContragredient B.obj.representation))) :
    Bv.isoClass = c0 d.succPNat (dualWeilClass F e σ m) := by
  have hG := GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData (d + 1)
  have hsc := F.canonicalTopologicalData.supercuspidalContragredientClosed
    GeneralLinear.supercuspidalContragredient (d + 1)
  obtain ⟨ψ⟩ := hBv
  have h1 : GeneralLinear.SupercuspidalClass.contragredient hG hsc B.isoClass = Bv.isoClass :=
    (GeneralLinear.SupercuspidalClass.contragredient_isoClass_eq_isoClass_iff hG hsc B Bv).mpr
      ⟨ψ.symm⟩
  have hB' : B.isoClass = (segmentOf F c0 σ m).last.cls := hB
  have h2 : (segmentOf F c0 σ m).last.cls = GeneralLinear.SupercuspidalClass.twist
      (F.canonicalTopologicalData.determinantPowerCharacter (d + 1) ((m + 1 - 1 : ℕ) : ℝ))
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter _ _)
      (F.canonicalTopologicalData.ker_determinant_le_ker_determinantPowerCharacter _ _)
      (c0 d.succPNat σ) := rfl
  have h3 := GeneralLinear.SupercuspidalClass.contragredient_twist hG hsc
    (F.canonicalTopologicalData.determinantPowerCharacter (d + 1) ((m + 1 - 1 : ℕ) : ℝ))
    (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter _ _)
    (F.canonicalTopologicalData.ker_determinant_le_ker_determinantPowerCharacter _ _)
    (c0 d.succPNat σ)
  have h4 : c0 d.succPNat (dualWeilClass F e σ m) = supercuspidalTwist F (dualTwistCharacter F e m)
      (supercuspidalDual F (c0 d.succPNat σ)) := by
    unfold dualWeilClass
    rw [(supercuspidalTwistCompatibility_iff F e c0).mp htwist,
      (supercuspidalDualCompatibility_iff F c0).mp hdual]
  have h : (F.canonicalTopologicalData.determinantPowerCharacter (d + 1)
      ((m + 1 - 1 : ℕ) : ℝ))⁻¹ = determinantQuasiCharacter F d.succPNat (dualTwistCharacter F e m) := by
    rw [Nat.add_sub_cancel]
    exact (determinantQuasiCharacter_dualTwistCharacter F he m d.succPNat).symm
  exact h1.symm.trans ((congrArg _ (hB'.trans h2)).trans
    (h3.trans ((GeneralLinear.SupercuspidalClass.twist_congr h _ _ _ _ _).trans h4.symm)))

/-- Under the contragredient compatibility of multisegment Langlands heads, the
smooth dual of a Langlands-head class of `σ` is a Langlands-head class of the classes
`ν^(-m_i) σ_i^∨`. -/
theorem isMultisegmentHeadClass_dual
    (hcontra : Classification.MultisegmentConstituentContragredientCompatibility.{uF, uA} F
      F.canonicalTopologicalData)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (htwist : SupercuspidalTwistCompatibility F e c0)
    (hdual : SupercuspidalDualCompatibility F c0) {r : ℕ} {d : Fin r → ℕ}
    (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat) (m : Fin r → ℕ)
    {n : ℕ+} {π : AutomorphicClass.{uF, uA} F n}
    (hπ : IsMultisegmentHeadClass F c0 σ m π) :
    ∃ π' : AutomorphicClass.{uF, uA} F n, IsSmoothDual F π π' ∧
      IsMultisegmentHeadClass F c0 (fun i => dualWeilClass F e (σ i) (m i)) m π' := by
  obtain ⟨A0, J, hA0, hJ, ⟨ψ⟩⟩ := hπ
  have hG := GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData n
  have hrep : ∀ i, ∃ B : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier)
      (n := d i + 1), (segmentOf F c0 (σ i) (m i)).last.IsRepresentedBy B :=
    fun i => ⟨Quotient.out _, Quotient.out_eq _⟩
  choose B hB using hrep
  obtain ⟨Bv, hBv, hmain⟩ := hcontra r (fun i => segmentOf F c0 (σ i) (m i)) B hB
  have hhead : Multisegment.IsLanglandsHead ((List.ofFn fun i =>
      ({ base :=
          { rank := d i + 1
            rank_pos := Nat.succ_pos (d i)
            cls := (Bv i).isoClass }
         length := m i + 1
         length_pos := Nat.succ_pos (m i) } : Segment.{uA, uF} F.canonicalTopologicalData) :
        Multiset (Segment.{uA, uF} F.canonicalTopologicalData))) J.contragredient :=
    (hmain n n.pos J).2 hJ
  have key : (fun i =>
      ({ base :=
          { rank := d i + 1
            rank_pos := Nat.succ_pos (d i)
            cls := (Bv i).isoClass }
         length := m i + 1
         length_pos := Nat.succ_pos (m i) } : Segment.{uA, uF} F.canonicalTopologicalData)) =
      fun i => segmentOf F c0 (dualWeilClass F e (σ i) (m i)) (m i) := by
    funext i
    simp only [segmentOf, cuspidalDatumOf]
    rw [isoClass_eq_dualWeilClass F c0 he htwist hdual (σ i) (m i) (B i) (Bv i) (hB i) (hBv i)]
  rw [key] at hhead
  exact ⟨automorphicClassOf F (IrreducibleAdmissibleRep.contragredient hG A0),
    ⟨A0, _, hA0, rfl, ⟨equivOfRepresentationEq rfl⟩⟩,
    IrreducibleAdmissibleRep.contragredient hG A0, J.contragredient, rfl, hhead,
    ⟨(smoothContragredientEquiv ψ).symm⟩⟩

/-- **Dual compatibility of the assembly.** Given well-definedness of the assembly and
the contragredient compatibility of multisegment Langlands heads, the assembly of a
supercuspidal map compatible with twists and duals is compatible with duals, for a
geometrically normalized reciprocity candidate. -/
theorem dualCompatibility_of_assembly
    (hwell : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    (hcontra : Classification.MultisegmentConstituentContragredientCompatibility.{uF, uA} F
      F.canonicalTopologicalData)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F) (hc : IsAssemblyOf F c0 c) (he : IsGeometricReciprocity F e)
    (htwist : SupercuspidalTwistCompatibility F e c0)
    (hdual : SupercuspidalDualCompatibility F c0) : DualCompatibility F c := by
  intro n D
  obtain ⟨E, hE⟩ := exists_isDualOf F D
  refine ⟨E, hE, ?_⟩
  obtain ⟨r, d, m, σ, hB, hH⟩ := hc n D
  obtain ⟨π', hπ', hH'⟩ := isMultisegmentHeadClass_dual F hcontra c0 he htwist hdual σ m hH
  have hE' : IsAssembledFrom F c0 E π' := ⟨r, d, m, _, isBlockSum_dual F e σ m hB hE, hH'⟩
  rwa [(hwell c0 n E).unique (hc n E) hE']

end Main

end AssemblyDual

end Langlands.Correspondence
