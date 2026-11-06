import Langlands.Correspondence.AssemblyRelation
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction

/-!
# The single-block assembly witness of a zero-monodromy parameter

Henniart 2002, §2.9: on the zero-monodromy parameter of an irreducible Weil class
`σ`, the assembly of `c0` takes the value `c0 σ`. This file proves the relation
`IsAssembledFrom F c0 D (c0 σ)` for the zero-monodromy class `D` of `σ`, with the
decomposition `D = σ ⊗ Sp(1)` and the one-element multisegment `{[c0 σ]}`.
-/

noncomputable section

namespace Langlands.WeilDeligneRepresentation

universe uK uG uV

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

open scoped TensorProduct

/-- A direct sum of a constant family indexed by `Fin 1` is its unique summand. -/
def directSumConstFinOneEquiv (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    Equiv (directSum fun _ : Fin 1 => A) A where
  representationEquiv := Representation.Equiv.mk (DirectSum.lid K A (Fin 1)) fun g => by
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    erw [DirectSum.lid_apply, DirectSum.lid_apply]
    rfl
  comm_monodromy := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    erw [DirectSum.lid_apply, DirectSum.lid_apply]
    rfl

/-- Raising monodromy on a special block of length one is zero. -/
theorem Special.raising_one : Special.raising K 1 = 0 := by
  apply LinearMap.ext
  intro w
  funext j
  rw [Special.raising_apply]
  simp

/-- The linear isomorphism `A ⊗ K^1 ≃ A`, `v ⊗ w ↦ w 0 • v`. -/
def blockOneLinearEquiv (A : FiniteRepresentation.{uK, uG, uV} K G) :
    TensorProduct K A (Fin 1 → K) ≃ₗ[K] A :=
  (TensorProduct.congr (LinearEquiv.refl K A) (LinearEquiv.funUnique (Fin 1) K K)).trans
    (TensorProduct.rid K A)

@[simp]
theorem blockOneLinearEquiv_tmul (A : FiniteRepresentation.{uK, uG, uV} K G) (v : A)
    (w : Fin 1 → K) : blockOneLinearEquiv A (v ⊗ₜ[K] w) = w 0 • v := by
  simp [blockOneLinearEquiv]

/-- The block of length one, `A ⊗ Sp(1)`, is the zero-monodromy pair of `A`. -/
def blockOneEquiv (ν : G →* Kˣ) (A : FiniteRepresentation.{uK, uG, uV} K G) :
    Equiv (block ν A 1) (zeroMonodromy ν A) where
  representationEquiv := Representation.Equiv.mk (blockOneLinearEquiv A) fun g => by
    apply TensorProduct.ext'
    intro (v : A) (w : Fin 1 → K)
    change blockOneLinearEquiv A (A.representation g v ⊗ₜ[K] Special.action ν 1 g w) =
      A.representation g (blockOneLinearEquiv A (v ⊗ₜ[K] w))
    rw [blockOneLinearEquiv_tmul, blockOneLinearEquiv_tmul, Special.action_apply,
      Fin.val_zero, pow_zero, one_mul, map_smul]
  comm_monodromy := by
    apply TensorProduct.ext'
    intro v w
    change blockOneLinearEquiv A
        ((TensorProduct.map (0 : Module.End K A) (1 : Module.End K (Fin 1 → K)) +
          TensorProduct.map (1 : Module.End K A) (Special.raising K 1) :
            Module.End K (TensorProduct K A (Fin 1 → K))) (v ⊗ₜ[K] w)) = 0
    simp [Special.raising_one]

end Langlands.WeilDeligneRepresentation

namespace Langlands.PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Undo an exact rank transport: if `X` is equivalent to the transport of `Y` along
`s = r`, then the transport of `X` along `r = s` is equivalent to `Y`. -/
def castRankEquivOfEquiv {r s : ℕ} (h : r = s) (h' : s = r)
    {X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)}
    {Y : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear s F.Carrier)}
    (e : letI := T.topology; X.representation.Equiv (T.castRank h' Y).representation) :
    letI := T.topology; (T.castRank h X).representation.Equiv Y.representation := by
  subst h
  exact e

end Langlands.PadicField.TopologicalData

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyWitnessFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyWitnessGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- The zero-monodromy class of `σ` is the block sum `σ ⊗ Sp(1)` with one block. -/
theorem isBlockSum_of_isZeroMonodromyOf {k : ℕ}
    {σ : IrreducibleWeilClass.{uF, uP} F k.succPNat}
    {D : WeilDeligneClass.{uF, uP} F k.succPNat} (h : IsZeroMonodromyOf F σ D) :
    IsBlockSum F (r := 1) (d := fun _ => k) (fun _ => σ) (fun _ => 0) D := by
  obtain ⟨A, hA, hD⟩ := h
  exact ⟨fun _ => A, WeilDeligneRepresentation.zeroMonodromy _ A, fun _ => hA, hD,
    ⟨(WeilDeligneRepresentation.directSumConstFinOneEquiv _).trans
      (WeilDeligneRepresentation.blockOneEquiv _ A)⟩⟩

section SingleSegment

variable (c0 : SupercuspidalMap.{uF, uP, uA} F) {k : ℕ}
  (σ : IrreducibleWeilClass.{uF, uP} F k.succPNat)

/-- The segment head of `[c0 σ]`: the induced representation `i(ρ)` of a
representative `ρ` of `c0 σ`, which is irreducible. -/
theorem isSegmentHead_single
    (S : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := k + 1))
    (hS : S.isoClass = c0 k.succPNat σ) :
    F.canonicalTopologicalData.IsSegmentHead (segmentOf F c0 σ 0)
      (F.canonicalTopologicalData.segmentInduced S.obj 1 (Nat.succ_pos k)) := by
  let T := F.canonicalTopologicalData
  let e1 := T.singletonSegmentInducedEquiv (Nat.succ_pos k) S.obj
  have hπ1 : Representation.IsIrreducible
      (T.segmentInduced S.obj 1 (Nat.succ_pos k)).representation :=
    (Weil.IsomorphismInvariance.irreducible_iff e1).mpr
      (T.isIrreducible_castRank (Nat.one_mul (k + 1)).symm S.obj S.property.1)
  exact ⟨S, hS, Classification.isIrreducibleHead_self _ hπ1⟩

/-- The one-segment product datum with segment `[c0 σ]` and a supplied block. -/
def singleSegmentDatum
    (π : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (1 * (k + 1)) F.Carrier)) :
    F.canonicalTopologicalData.SegmentProductDatum.{uA, uF} (k + 1) where
  length := 1
  segments := fun i => segmentOf F c0 ((fun _ : Fin 1 => σ) i) ((fun _ : Fin 1 => 0) i)
  degree_sum := by
    change ∑ _i : Fin 1, 1 * (k + 1) = k + 1
    simp
  blocks := fun _ => π

/-- The multisegment of the datum is `{[c0 σ]}`, as listed by `multisegmentOf`. -/
theorem singleSegmentDatum_multisegment
    (π : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (1 * (k + 1)) F.Carrier)) :
    (singleSegmentDatum F c0 σ π).multisegment =
      multisegmentOf F c0 (r := 1) (d := fun _ => k) (fun _ => σ) (fun _ => 0) :=
  rfl

/-- A family with one segment is precedence-ordered. -/
theorem singleSegmentDatum_isPrecedenceOrdered
    (π : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (1 * (k + 1)) F.Carrier)) :
    (singleSegmentDatum F c0 σ π).IsPrecedenceOrdered := by
  intro i j hij
  have hi : (i : ℕ) < 1 := i.isLt
  have hj : (j : ℕ) < 1 := j.isLt
  have hlt : (i : ℕ) < j := hij
  omega

/-- The induced representation of the one-segment datum is its block, after the
exact rank transport. -/
def singleSegmentDatumInducedEquiv
    (π : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (1 * (k + 1)) F.Carrier)) :
    (singleSegmentDatum F c0 σ π).induced.representation.Equiv
      (F.canonicalTopologicalData.castRank (Nat.one_mul (k + 1)) π).representation :=
  (F.canonicalTopologicalData.singleBlockNormalizedProductEquiv
      (singleSegmentDatum F c0 σ π).shape rfl
      (fun i => ((singleSegmentDatum F c0 σ π).blocks i).representation)
      (fun i => ((singleSegmentDatum F c0 σ π).blocks i).isSmooth) ⟨0, Nat.one_pos⟩).trans
    (F.canonicalTopologicalData.castRankEquiv (Nat.one_mul (k + 1)) π)

/-- The class `c0 σ` is the Langlands head of the one-segment multisegment
`{[c0 σ]}`. -/
theorem isMultisegmentHeadClass_single :
    IsMultisegmentHeadClass F c0 (r := 1) (d := fun _ => k) (fun _ => σ) (fun _ => 0)
      (supercuspidalToAutomorphic F (c0 k.succPNat σ)) := by
  let T := F.canonicalTopologicalData
  obtain ⟨S, hS⟩ := Quotient.exists_rep (c0 k.succPNat σ)
  let π1 := T.segmentInduced S.obj 1 (Nat.succ_pos k)
  let e1 := T.singletonSegmentInducedEquiv (Nat.succ_pos k) S.obj
  have hπ1 : Representation.IsIrreducible π1.representation :=
    (Weil.IsomorphismInvariance.irreducible_iff e1).mpr
      (T.isIrreducible_castRank (Nat.one_mul (k + 1)).symm S.obj S.property.1)
  let eJ := singleSegmentDatumInducedEquiv F c0 σ π1
  have hJ : Representation.IsIrreducible
      (singleSegmentDatum F c0 σ π1).induced.representation :=
    (Weil.IsomorphismInvariance.irreducible_iff eJ).mpr
      (T.isIrreducible_castRank (Nat.one_mul (k + 1)) π1 hπ1)
  refine ⟨S.toIrreducibleAdmissible, (singleSegmentDatum F c0 σ π1).induced, ?_,
    ⟨singleSegmentDatum F c0 σ π1, singleSegmentDatum_multisegment F c0 σ π1,
      singleSegmentDatum_isPrecedenceOrdered F c0 σ π1,
      fun _ => isSegmentHead_single F c0 σ S hS,
      Classification.isIrreducibleHead_self _ hJ⟩,
    ⟨eJ.trans (T.castRankEquivOfEquiv (Nat.one_mul (k + 1)) (Nat.one_mul (k + 1)).symm e1)⟩⟩
  rw [← hS]
  rfl

end SingleSegment

/-- Henniart 2002, §2.9: the zero-monodromy class `D` of an irreducible Weil class
`σ` is assembled from `c0` to `c0 σ`. -/
theorem isAssembledFrom_of_isZeroMonodromyOf (c0 : SupercuspidalMap.{uF, uP, uA} F)
    {n : ℕ+} {σ : IrreducibleWeilClass.{uF, uP} F n} {D : WeilDeligneClass.{uF, uP} F n}
    (h : IsZeroMonodromyOf F σ D) :
    IsAssembledFrom F c0 D (supercuspidalToAutomorphic F (c0 n σ)) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k.succPNat := ⟨n.natPred, (PNat.succPNat_natPred n).symm⟩
  exact ⟨1, fun _ => k, fun _ => 0, fun _ => σ, isBlockSum_of_isZeroMonodromyOf F h,
    isMultisegmentHeadClass_single F c0 σ⟩

/-- Given well-definedness, every assembly of `c0` takes the value `c0 σ` on the
zero-monodromy class of `σ`. -/
theorem assembly_apply_of_isZeroMonodromyOf
    (hwd : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {c : FullMap.{uF, uP, uA} F}
    (hc : IsAssemblyOf F c0 c) {n : ℕ+} {σ : IrreducibleWeilClass.{uF, uP} F n}
    {D : WeilDeligneClass.{uF, uP} F n} (h : IsZeroMonodromyOf F σ D) :
    c n D = supercuspidalToAutomorphic F (c0 n σ) :=
  (hwd c0 n D).unique (hc n D) (isAssembledFrom_of_isZeroMonodromyOf F c0 h)

end Langlands.Correspondence
