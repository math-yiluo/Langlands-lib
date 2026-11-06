import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedInducedFiniteness
import Langlands.Representation.Induction.FixedVectorModel
import Langlands.Representation.Induction.UnramifiedCompactStabilizer
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.EquationalCriterion

noncomputable section

open scoped NNReal TensorProduct

namespace Langlands.Plancherel.RationalNormalized

section TensorFixed

variable {k B H E : Type*} [Field k] [CommRing B] [Algebra k B]
  [Group H] [AddCommGroup E] [Module k E]

local instance tensorGroup (V : Type*) [AddCommGroup V] [Module k V] :
    AddCommGroup (B ⊗[k] V) := TensorProduct.addCommGroup

private theorem tensor_coordinates_baseChange {ι : Type*} [DecidableEq ι] (e : Module.Basis ι k B)
    (f : E →ₗ[k] E) (t : B ⊗[k] E) (j : ι) :
    TensorProduct.equivFinsuppOfBasisLeft e (f.baseChange B t) j =
      f (TensorProduct.equivFinsuppOfBasisLeft e t j) := by
  induction t using TensorProduct.inductionOn with
  | tmul b v => simp
  | add t s ht hs => simp only [map_add, Finsupp.add_apply, ht, hs]

/-- Extension of scalars commutes with fixed vectors when the action on the
subgroup is the scalar extension of the original action. -/
def tensorFixedEquiv (ρ : Representation k H E)
    (τ : Representation B H (B ⊗[k] E)) (Q : Subgroup H)
    (hτ : ∀ q : Q, τ q.val = (ρ q.val).baseChange B) :
    B ⊗[k] fixedVectors ρ Q ≃ₗ[B] fixedVectors τ Q := by
  classical
  let N := fixedVectors ρ Q
  let f : B ⊗[k] N →ₗ[B] fixedVectors τ Q :=
    (N.subtype.baseChange B).codRestrict _ (by
      intro t
      change ∀ q : Q, τ q.val (N.subtype.baseChange B t) = N.subtype.baseChange B t
      intro q
      rw [hτ q]
      induction t using TensorProduct.inductionOn with
      | tmul b v =>
          simp only [LinearMap.baseChange_tmul]
          exact congrArg (fun w : E => b ⊗ₜ[k] w) (v.property q)
      | add t s ht hs => simp only [map_add, ht, hs])
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    exact Module.Flat.lTensor_preserves_injective_linearMap N.subtype
      Subtype.val_injective (congrArg Subtype.val hxy)
  · intro t
    let e := Module.Free.chooseBasis k B
    let c := TensorProduct.equivFinsuppOfBasisLeft e t.val
    have hfix (j : Module.Free.ChooseBasisIndex k B) : c j ∈ N := by
      change ∀ q : Q, ρ q.val (c j) = c j
      intro q
      have ht : (ρ q.val).baseChange B t.val = t.val := by
        rw [← hτ q]
        exact t.property q
      have hc := congrArg (fun z => TensorProduct.equivFinsuppOfBasisLeft e z j) ht
      rw [tensor_coordinates_baseChange] at hc
      exact hc
    refine ⟨∑ j ∈ c.support, e j ⊗ₜ[k] (⟨c j, hfix j⟩ : N), ?_⟩
    apply Subtype.ext
    change N.subtype.baseChange B (∑ j ∈ c.support,
      e j ⊗ₜ[k] (⟨c j, hfix j⟩ : N)) = t.val
    simp only [map_sum, LinearMap.baseChange_tmul, Submodule.coe_subtype]
    simpa only [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum] using
      (TensorProduct.equivFinsuppOfBasisLeft e).symm_apply_apply t.val

end TensorFixed

section SmoothFlatness

variable {R G V : Type*} [CommRing R] [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [AddCommGroup V] [Module R V]

/-- The finite-relation criterion reduces flatness of a smooth module to
flatness of its compact-open fixed modules. -/
theorem flat_of_smooth_fixed_flat (ρ : Representation R G V) (hρ : IsSmooth ρ)
    (hfixed : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      Module.Flat R (fixedVectors ρ K.toSubgroup)) : Module.Flat R V := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro n f x hfx
  choose Q hQ using fun i => hρ (x i)
  let H : OpenSubgroup G := Finset.univ.inf Q
  have hHQ (i : Fin n) : H ≤ Q i := Finset.inf_le (Finset.mem_univ i)
  obtain ⟨K, hK, hKH⟩ := compactOpenSubgroupBasis G (H : Set G) H.mem_nhds_one
  have hx (i : Fin n) : x i ∈ fixedVectors ρ K.toSubgroup := by
    intro g
    exact hQ i ⟨g.val, hHQ i (hKH g.property)⟩
  let xK : Fin n → fixedVectors ρ K.toSubgroup := fun i => ⟨x i, hx i⟩
  have := hfixed K hK
  have hfxK : ∑ i, f i • xK i = 0 := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] using hfx
  obtain ⟨m, a, y, hxy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hfxK
  refine ⟨m, a, fun j => (y j).val, ?_, ha⟩
  intro i
  simpa only [map_sum, map_smul, Submodule.subtype_apply, xK] using
    congrArg (fixedVectors ρ K.toSubgroup).subtype (hxy i)

end SmoothFlatness

section FiniteEvaluation

variable {R G V : Type*} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [AddCommGroup V] [Module R V]

private theorem smoothInduced_fixed_finite_free (P : Subgroup G)
    [CompactSpace (Induction.LeftQuotient P)] (τ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hcoeff : ∀ x : G,
      Module.Finite R (fixedVectors τ (Induction.conjOpenSubgroup P K x).toSubgroup) ∧
      Module.Free R (fixedVectors τ (Induction.conjOpenSubgroup P K x).toSubgroup)) :
    Module.Finite R (fixedVectors (Induction.smoothInduced P τ) K.toSubgroup) ∧
    Module.Free R (fixedVectors (Induction.smoothInduced P τ) K.toSubgroup) := by
  classical
  obtain ⟨t, hcover, hdistinct⟩ := Induction.exists_finset_doubleCoset_representatives P K
  let (i : t) : Module.Finite R
      (fixedVectors τ (Induction.conjOpenSubgroup P K i).toSubgroup) := (hcoeff i).1
  let (i : t) : Module.Free R
      (fixedVectors τ (Induction.conjOpenSubgroup P K i).toSubgroup) := (hcoeff i).2
  let e := Induction.fixedEvaluationEquiv P τ K hK t hcover hdistinct
  exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩

end FiniteEvaluation

section UniversalFixed

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} {I : Type uI}
  (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (h : Aubert.General.IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (hr : Continuous h.projection)
  (π : SmoothRep.{0, uG, uV} ℂ M) (hπ : π.IsAdmissible)

local instance universalTensorGroup : AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] π) :=
  TensorProduct.addCommGroup

include hν hr hπ in
/-- The actual normalized universal inducing action has finite free fixed
modules on compact open subgroups of the parabolic. -/
theorem universalInducing_fixed_finite_free (Q : OpenSubgroup P)
    (hQ : IsCompact (Q : Set P)) :
    Module.Finite (unramifiedRegularFunctions ν)
      (fixedVectors (UnramifiedNormalized.universalInducingRepresentation ν h hU
        π.representation) Q.toSubgroup) ∧
    Module.Free (unramifiedRegularFunctions ν)
      (fixedVectors (UnramifiedNormalized.universalInducingRepresentation ν h hU
        π.representation) Q.toSubgroup) := by
  let ρ := Aubert.General.inducingRepresentation h hU π
  have := (Aubert.General.inducingRepresentation_isAdmissible h hU hr π hπ).2 Q
  have heval (q : Q) : unramifiedEvaluationRegular ν (h.projection q.val) = 1 := by
    apply Subtype.ext
    funext χ
    change (χ.val (h.projection q.val) : ℂ) = 1
    have hχ : χ.val (h.projection q.val) = 1 :=
      Induction.compactSubgroup_le_unramifiedPullback_ker ν hν h.projection hr
        χ Q.toSubgroup hQ q.property
    exact congrArg Units.val hχ
  have haction (q : Q) :
      UnramifiedNormalized.universalInducingRepresentation ν h hU π.representation q.val =
        (ρ q.val).baseChange (unramifiedRegularFunctions ν) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b v
    change (algebraMap ℂ (unramifiedRegularFunctions ν)
      (HaarModulus.closedHalfCharacter U hU P h.le_normalizer q.val : ℂ)) •
        ((unramifiedEvaluationRegular ν (h.projection q.val) * b) ⊗ₜ[ℂ]
          π.representation (h.projection q.val) v) =
      b ⊗ₜ[ℂ] ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q.val : ℂ) •
        π.representation (h.projection q.val) v)
    simp only [heval, one_mul, algebraMap_smul, TensorProduct.tmul_smul]
  let e := tensorFixedEquiv ρ
    (UnramifiedNormalized.universalInducingRepresentation ν h hU π.representation)
    Q.toSubgroup haction
  exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩

include hν hr hπ in
/-- Finite double-coset evaluation identifies the full induced fixed space with
a finite product of finite free coefficient fixed spaces. -/
theorem universalInduced_fixed_finite_free (hP : IsClosed (P : Set G))
    [CompactSpace (Induction.LeftQuotient P)]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Module.Finite (unramifiedRegularFunctions ν)
      (fixedVectors (UnramifiedNormalized.universalInducedRepresentation ν h hU
        π.representation) K.toSubgroup) ∧
    Module.Free (unramifiedRegularFunctions ν)
      (fixedVectors (UnramifiedNormalized.universalInducedRepresentation ν h hU
        π.representation) K.toSubgroup) := by
  apply smoothInduced_fixed_finite_free P
    (UnramifiedNormalized.universalInducingRepresentation ν h hU π.representation) K hK
  intro x
  exact universalInducing_fixed_finite_free ν hν h hU hr π hπ
    (Induction.conjOpenSubgroup P K x)
    (Induction.isCompact_conjOpenSubgroup P hP K hK x)

local instance universalInducedModule : Module (unramifiedRegularFunctions ν)
    (UnramifiedNormalized.UniversalInduced ν h hU π.representation) := Submodule.module _

include hν hr hπ in
/-- The full smooth normalized universal induction is flat over its coefficient
algebra because all of its compact-open fixed modules are free. -/
theorem universalInduced_flat (hP : IsClosed (P : Set G))
    [CompactSpace (Induction.LeftQuotient P)] :
    Module.Flat (unramifiedRegularFunctions ν)
      (UnramifiedNormalized.UniversalInduced ν h hU π.representation) := by
  apply flat_of_smooth_fixed_flat
    (UnramifiedNormalized.universalInducedRepresentation ν h hU π.representation)
    (UnramifiedNormalized.isSmooth_universalInducedRepresentation ν h hU π.representation)
  intro K hK
  have := (universalInduced_fixed_finite_free ν hν h hU hr π hπ hP K hK).2
  infer_instance

end UniversalFixed

open CategoryTheory _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

universe u uV

/-- Renard VI.8.1–2: flatness and compact-open fixed-space finite projectivity
for the actual full rational normalized universal induced module. -/
theorem universalInducedCoefficientFiniteness :
    UniversalInducedCoefficientFinitenessStatement.{u, uV} := by
  intro F _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro _ _ A M P U _ p l a n r _hn h hU hr _ π hπ
  have hc : IsClosedSubgroup p := r.isCompatible.parabolic.isClosedSubgroup
  have : IsClosedImmersion p.hom.hom.left := hc
  have hrep : (SubgroupFunctor.range p).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  have hP : IsClosed (ParabolicPoints p : Set (rationalPoints G)) :=
    isClosed_rationalPoint_subgroup F (SubgroupFunctor.range p) p hrep hc
  constructor
  · exact universalInduced_flat (parabolicLeviRationalNormCharacters r)
      (continuous_parabolicLeviRationalNormCharacters r) h hU hr π hπ hP
  · intro K hK
    have hf := universalInduced_fixed_finite_free (parabolicLeviRationalNormCharacters r)
      (continuous_parabolicLeviRationalNormCharacters r) h hU hr π hπ hP K hK
    have := hf.2
    exact ⟨hf.1, inferInstance⟩

end Langlands.Plancherel.RationalNormalized
