import Langlands.Shimura.Unitary.SufficientlySmallLevelsExistence
import Langlands.Shimura.Unitary.PointsSplit
import Langlands.Shimura.ProPLevels
import Langlands.Global.AdelesLocallyCompactProof
import Langlands.Topology.LocallyProfiniteProof
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Langlands.Shimura.Unitary.CMData

/-! # Compact open levels of finite adelic similitude groups -/

noncomputable section

open Filter Topology Langlands.Global
open scoped TensorProduct RestrictedProduct Valued NumberField

set_option autoImplicit false

universe u v w

namespace Langlands.Shimura

/-- The opposite of a compact open subgroup, as a compact open level of the opposite group. -/
def CompactOpenLevel.opOfCompact {G : Type v} [Group G] [TopologicalSpace G]
    (H : OpenSubgroup G) (hH : IsCompact (H : Set G)) : CompactOpenLevel Gᵐᵒᵖ where
  openSubgroup :=
    { toSubgroup := H.toSubgroup.op
      isOpen' := H.isOpen.preimage MulOpposite.continuous_unop }
  isCompact := MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hH

theorem CompactOpenLevel.mem_opOfCompact {G : Type v} [Group G] [TopologicalSpace G]
    (H : OpenSubgroup G) (hH : IsCompact (H : Set G)) (g : Gᵐᵒᵖ) :
    g ∈ (CompactOpenLevel.opOfCompact H hH).subgroup ↔ MulOpposite.unop g ∈ H :=
  Iff.rfl

section FiniteAdeles

variable (K : Type u) [Field K] [NumberField K]

/-- The finite adeles are Hausdorff. -/
theorem t2Space_finiteAdeles : T2Space (FiniteAdeles K) :=
  inferInstanceAs (T2Space (Πʳ v : FinitePlace K,
    [FiniteCompletion K v, v.adicCompletionIntegers K]))

/-- The prime-to-`p` finite adeles of `ℚ` are Hausdorff. -/
theorem t2Space_primeToFiniteAdeles (p : ℕ) : T2Space (PrimeToFiniteAdeles p) :=
  inferInstanceAs (T2Space (Πʳ v : PrimeToFinitePlace p,
    [FiniteCompletion ℚ v.1, v.1.adicCompletionIntegers ℚ]))

/-- The prime-to-`p` finite adeles of `ℚ` are locally compact. -/
theorem locallyCompactSpace_primeToFiniteAdeles (p : ℕ) :
    LocallyCompactSpace (PrimeToFiniteAdeles p) := by
  have : ∀ v : PrimeToFinitePlace p, CompactSpace (v.1.adicCompletionIntegers ℚ) :=
    fun v ↦ isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers ℚ v.1)
  have : Fact (∀ v : PrimeToFinitePlace p,
      IsOpen (v.1.adicCompletionIntegers ℚ : Set (FiniteCompletion ℚ v.1))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  exact inferInstanceAs (LocallyCompactSpace
    (Πʳ v : PrimeToFinitePlace p, [FiniteCompletion ℚ v.1, v.1.adicCompletionIntegers ℚ]))

/-- The prime-to-`p` finite adeles of `ℚ` are totally disconnected. -/
theorem totallyDisconnectedSpace_primeToFiniteAdeles (p : ℕ) :
    TotallyDisconnectedSpace (PrimeToFiniteAdeles p) := by
  have : ∀ v : PrimeToFinitePlace p, TotallyDisconnectedSpace (FiniteCompletion ℚ v.1) :=
    fun _ => inferInstance
  exact totallyDisconnectedSpace_of_continuous_injective
    (RestrictedProduct.continuous_coe
      (R := fun v : PrimeToFinitePlace p => FiniteCompletion ℚ v.1)
      (A := fun v => (v.1.adicCompletionIntegers ℚ : Set (FiniteCompletion ℚ v.1))))
    (fun x y h => RestrictedProduct.ext _ _ (congrFun h))

end FiniteAdeles

namespace AlgebraInvolution

section General

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]
variable (σ : AlgebraInvolution R A)
variable (S : Type w) [CommRing S] [Algebra R S] [TopologicalSpace S] [IsTopologicalRing S]

/-- The similitude subgroup is closed in `(S ⊗[R] A)ˣ × Sˣ`. -/
theorem isClosed_baseChange_similitudes [T2Space S] :
    letI : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
    IsClosed ((σ.baseChange S).similitudes : Set ((S ⊗[R] A)ˣ × Sˣ)) := by
  let : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  have : IsModuleTopology S (S ⊗[R] A) := ⟨rfl⟩
  have : IsTopologicalRing (S ⊗[R] A) := IsModuleTopology.isTopologicalRing S _
  have : ContinuousAdd (S ⊗[R] A) := IsModuleTopology.toContinuousAdd S _
  let e := (coordinateEquiv S (Module.Free.chooseBasis R A)).toHomeomorph
  have : T2Space (S ⊗[R] A) := e.isEmbedding.t2Space
  have hσ : Continuous (σ.baseChange S).linear :=
    IsModuleTopology.continuous_of_linearMap _
  have ha : Continuous (algebraMap S (S ⊗[R] A)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap S (S ⊗[R] A))
  have hset : ((σ.baseChange S).similitudes : Set ((S ⊗[R] A)ˣ × Sˣ)) =
      {x | (x.1 : S ⊗[R] A) * (σ.baseChange S).linear x.1 =
        algebraMap S (S ⊗[R] A) x.2} := by
    ext x
    exact (σ.baseChange S).mem_similitudes_iff x
  rw [hset]
  exact isClosed_eq
    ((Units.continuous_val.comp continuous_fst).mul
      (hσ.comp (Units.continuous_val.comp continuous_fst)))
    (ha.comp (Units.continuous_val.comp continuous_snd))

/-- The scalar-extended similitude group is Hausdorff over a Hausdorff ring. -/
theorem points_t2Space [T2Space S] : T2Space (σ.Points S) := by
  let : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  have : IsTopologicalRing (S ⊗[R] A) := IsModuleTopology.isTopologicalRing S _
  let e := (coordinateEquiv S (Module.Free.chooseBasis R A)).toHomeomorph
  have : T2Space (S ⊗[R] A) := e.isEmbedding.t2Space
  exact inferInstanceAs (T2Space (σ.baseChange S).similitudes)

/-- The scalar-extended similitude group is locally compact over a locally compact Hausdorff
ring. -/
theorem points_locallyCompactSpace [T2Space S] [LocallyCompactSpace S] :
    LocallyCompactSpace (σ.Points S) := by
  let : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  have : IsTopologicalRing (S ⊗[R] A) := IsModuleTopology.isTopologicalRing S _
  let e := (coordinateEquiv S (Module.Free.chooseBasis R A)).toHomeomorph
  have : T2Space (S ⊗[R] A) := e.isEmbedding.t2Space
  have : LocallyCompactSpace (S ⊗[R] A) := e.isClosedEmbedding.locallyCompactSpace
  exact (σ.isClosed_baseChange_similitudes S).locallyCompactSpace

/-- The scalar-extended similitude group is totally disconnected over a totally disconnected
ring. -/
theorem points_totallyDisconnectedSpace [TotallyDisconnectedSpace S] :
    TotallyDisconnectedSpace (σ.Points S) := by
  let : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  have : IsTopologicalRing (S ⊗[R] A) := IsModuleTopology.isTopologicalRing S _
  let e := (coordinateEquiv S (Module.Free.chooseBasis R A)).toHomeomorph
  have : TotallyDisconnectedSpace (S ⊗[R] A) :=
    totallyDisconnectedSpace_of_continuous_injective e.continuous e.injective
  have : TotallyDisconnectedSpace (S ⊗[R] A)ˣ :=
    totallyDisconnectedSpace_of_continuous_injective Units.continuous_val Units.val_injective
  have : TotallyDisconnectedSpace Sˣ :=
    totallyDisconnectedSpace_of_continuous_injective Units.continuous_val Units.val_injective
  exact inferInstanceAs (TotallyDisconnectedSpace (σ.baseChange S).similitudes)

/-- Over a locally profinite coefficient ring, the scalar-extended similitude group is locally
profinite. -/
theorem isLocallyProfinite_points [T2Space S] [LocallyCompactSpace S]
    [TotallyDisconnectedSpace S] : Langlands.Topology.IsLocallyProfinite (σ.Points S) := by
  have := σ.points_t2Space S
  have := σ.points_locallyCompactSpace S
  have := σ.points_totallyDisconnectedSpace S
  exact Langlands.Topology.isLocallyProfinite_of_mathlib

/-- Van Dantzig: every identity neighbourhood of the scalar-extended similitude group contains a
compact open subgroup. -/
theorem exists_compact_openSubgroup_subset_points [T2Space S] [LocallyCompactSpace S]
    [TotallyDisconnectedSpace S] {U : Set (σ.Points S)} (hU : U ∈ 𝓝 (1 : σ.Points S)) :
    ∃ H : OpenSubgroup (σ.Points S), IsCompact (H : Set (σ.Points S)) ∧
      (H : Set (σ.Points S)) ⊆ U :=
  ((Langlands.Topology.LocallyProfiniteProof.vanDantzig (σ.Points S)).mp
    (σ.isLocallyProfinite_points S)).2 U hU

/-- Every identity neighbourhood of the opposite group contains a compact open level. -/
theorem exists_compactOpenLevel_op_subset [T2Space S] [LocallyCompactSpace S]
    [TotallyDisconnectedSpace S] {U : Set (σ.Points S)ᵐᵒᵖ}
    (hU : U ∈ 𝓝 (1 : (σ.Points S)ᵐᵒᵖ)) :
    ∃ K : CompactOpenLevel (σ.Points S)ᵐᵒᵖ, (K.subgroup : Set (σ.Points S)ᵐᵒᵖ) ⊆ U := by
  have hU' : MulOpposite.op ⁻¹' U ∈ 𝓝 (1 : σ.Points S) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hU
  obtain ⟨H, hHc, hHU⟩ := σ.exists_compact_openSubgroup_subset_points S hU'
  exact ⟨CompactOpenLevel.opOfCompact H hHc, fun g hg => hHU hg⟩

/-- A compact open level of the opposite scalar-extended similitude group exists. -/
theorem nonempty_compactOpenLevel_op [T2Space S] [LocallyCompactSpace S]
    [TotallyDisconnectedSpace S] : Nonempty (CompactOpenLevel (σ.Points S)ᵐᵒᵖ) :=
  let ⟨K, _⟩ := σ.exists_compactOpenLevel_op_subset S univ_mem
  ⟨K⟩

end General

section Rational

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable (σ : AlgebraInvolution ℚ A)

/-- The finite adelic similitude group `σ(A_f)` is Hausdorff. -/
instance finiteAdelicPoints_t2Space : T2Space σ.FiniteAdelicPoints :=
  haveI := t2Space_finiteAdeles ℚ
  σ.points_t2Space _

/-- The finite adelic similitude group `σ(A_f)` is locally compact. -/
instance finiteAdelicPoints_locallyCompactSpace : LocallyCompactSpace σ.FiniteAdelicPoints :=
  haveI := t2Space_finiteAdeles ℚ
  haveI := finiteAdeles_locallyCompactSpace ℚ
  σ.points_locallyCompactSpace _

/-- The finite adelic similitude group `σ(A_f)` is totally disconnected. -/
instance finiteAdelicPoints_totallyDisconnectedSpace :
    TotallyDisconnectedSpace σ.FiniteAdelicPoints :=
  haveI := Langlands.Global.finiteAdeles_totallyDisconnectedSpace ℚ
  σ.points_totallyDisconnectedSpace _

/-- The finite adelic similitude group `σ(A_f)` is locally profinite. -/
theorem isLocallyProfinite_finiteAdelicPoints :
    Langlands.Topology.IsLocallyProfinite σ.FiniteAdelicPoints :=
  Langlands.Topology.isLocallyProfinite_of_mathlib

/-- Every identity neighbourhood of `σ(A_f)ᵐᵒᵖ` contains a compact open level. -/
theorem exists_finiteAdelic_compactOpenLevel_subset {U : Set σ.FiniteAdelicPointsᵐᵒᵖ}
    (hU : U ∈ 𝓝 (1 : σ.FiniteAdelicPointsᵐᵒᵖ)) :
    ∃ K : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ,
      (K.subgroup : Set σ.FiniteAdelicPointsᵐᵒᵖ) ⊆ U :=
  haveI := t2Space_finiteAdeles ℚ
  haveI := finiteAdeles_locallyCompactSpace ℚ
  haveI := Langlands.Global.finiteAdeles_totallyDisconnectedSpace ℚ
  σ.exists_compactOpenLevel_op_subset _ hU

/-- A compact open level of `σ(A_f)ᵐᵒᵖ` exists. -/
instance nonempty_finiteAdelic_compactOpenLevel :
    Nonempty (CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ) :=
  let ⟨K, _⟩ := σ.exists_finiteAdelic_compactOpenLevel_subset univ_mem
  ⟨K⟩

/-- Every identity neighbourhood of `σ(A_f)ᵐᵒᵖ` contains a sufficiently small level. -/
theorem exists_smallLevel_subset [Nontrivial A] {U : Set σ.FiniteAdelicPointsᵐᵒᵖ}
    (hU : U ∈ 𝓝 (1 : σ.FiniteAdelicPointsᵐᵒᵖ)) :
    ∃ V : σ.SmallLevelCategory, (V.obj.subgroup : Set σ.FiniteAdelicPointsᵐᵒᵖ) ⊆ U := by
  obtain ⟨K, hK⟩ := σ.exists_finiteAdelic_compactOpenLevel_subset hU
  obtain ⟨V, hV⟩ := exists_levelSufficientlySmall_le K
  exact ⟨V, fun g hg => hK (hV hg)⟩

/-- Sufficiently small levels of `σ(A_f)ᵐᵒᵖ` exist. -/
instance nonempty_smallLevelCategory_of_nontrivial [Nontrivial A] :
    Nonempty σ.SmallLevelCategory :=
  nonempty_smallLevelCategory (σ := σ)

/-- A compact open level of the opposite prime-to-`p` points `σ(A_f^p)ᵐᵒᵖ` exists. -/
instance nonempty_primeTo_compactOpenLevel (p : ℕ) :
    Nonempty (CompactOpenLevel (σ.PrimeToPoints p)ᵐᵒᵖ) :=
  haveI := t2Space_primeToFiniteAdeles p
  haveI := locallyCompactSpace_primeToFiniteAdeles p
  haveI := totallyDisconnectedSpace_primeToFiniteAdeles p
  σ.nonempty_compactOpenLevel_op _

end Rational

end AlgebraInvolution

namespace CentralSimpleUnitaryData

open NumberField Algebra

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

include D in
omit [NumberField E] [IsScalarTower E K A] [IsScalarTower ℚ E A] in
/-- The central simple algebra of Harris's unitary data is finite over `ℚ`. -/
theorem finite_rat : Module.Finite ℚ A :=
  haveI := D.finite
  Module.Finite.trans K A

/-- A compact open level of the opposite finite adelic similitude group of
Harris's unitary data exists. -/
instance nonempty_finiteAdelic_compactOpenLevel :
    Nonempty (CompactOpenLevel D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) :=
  haveI := D.finite_rat
  AlgebraInvolution.nonempty_finiteAdelic_compactOpenLevel _

/-- Sufficiently small levels of Harris's unitary data exist. -/
instance nonempty_smallLevelCategory :
    Nonempty D.rationalInvolution.SmallLevelCategory :=
  haveI := D.finite_rat
  haveI := D.simple
  AlgebraInvolution.nonempty_smallLevelCategory_of_nontrivial _

/-- A compact open level of the opposite prime-to-`p` similitude group of Harris's
unitary data exists. -/
instance nonempty_primeTo_compactOpenLevel (p : ℕ) :
    Nonempty (CompactOpenLevel (D.rationalInvolution.PrimeToPoints p)ᵐᵒᵖ) :=
  haveI := D.finite_rat
  AlgebraInvolution.nonempty_primeTo_compactOpenLevel _ p

end CentralSimpleUnitaryData

end Langlands.Shimura
