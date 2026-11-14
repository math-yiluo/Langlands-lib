import Langlands.GroupScheme.Reductive.RelativeDerivedInputs
import Langlands.GroupScheme.FppfHomDescent
import Langlands.GroupScheme.Torus.RelativeCommutativity

/-! # Reductions for the relative derived group -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {D G : GroupScheme S}

/-- Semisimple geometric fibres imply semisimplicity of each residue-field fibre. -/
theorem isSemisimple_residueFiber
    (hss : ∀ s : S, IsSemisimple (geometricFiber D s)) (s : S) :
    IsSemisimple ((baseChange (S.fromSpecResidueField s)).obj D) := by
  apply IsSemisimple.of_fieldExtension
    (k := S.residueField s) (K := AlgebraicClosure (S.residueField s))
  exact (hss s).of_iso
    (baseChangeCompIso (S.fromSpecResidueField s) (toAlgebraicClosure _) D).symm

/-- A relative semisimple group is semisimple at every field-valued point. -/
theorem IsReductive.isSemisimple_baseChange
    (hD : IsReductive D) (hss : ∀ s : S, IsSemisimple (GroupScheme.geometricFiber D s))
    {k : Type u} [Field k] (f : Spec (CommRingCat.of k) ⟶ S) :
    IsSemisimple ((GroupScheme.baseChange f).obj D) := by
  let s := f (IsLocalRing.closedPoint k)
  let φ : S.residueField s ⟶ CommRingCat.of k :=
    S.descResidueField (Scheme.stalkClosedPointTo f)
  let : Algebra (S.residueField s) k := φ.hom.toAlgebra
  have hκ := isSemisimple_residueFiber hss s
  have hfin := hκ.hasFiniteCenter.baseChange (Spec.map φ)
  have h := hfin.of_iso (baseChangeCompIso (S.fromSpecResidueField s) (Spec.map φ) D)
  have hfactor : Spec.map φ ≫ S.fromSpecResidueField s = f :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S f
  rw [hfactor] at h
  exact ⟨hD.isConnectedReductive_baseChange f, h⟩

namespace RelativeDerived

/-- Points of an admissible subgroup are locally commutators if relative
semisimple groups are fppf-perfect. -/
theorem IsAdmissible.locallyCommutator_of_mem_range
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u})
    {d : D ⟶ G} (hd : IsAdmissible d) {T : Over S} {x : T ⟶ G.X}
    (hx : x ∈ (SubgroupFunctor.range d).carrier T) : LocallyCommutator x := by
  obtain ⟨y, rfl⟩ := hx
  exact (hperf S D hd.2.2.1 hd.2.2.2.1 T y).map d

/-- An admissible subgroup with a supplied commutative quotient is the local
commutator functor, assuming relative semisimple fppf-perfectness. -/
theorem IsAdmissible.mem_range_iff_locallyCommutator
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u})
    {d : D ⟶ G} (hd : IsAdmissible d) {Q : GroupScheme S}
    (q : G ⟶ Q) [IsCommMonObj Q.X]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    (T : Over S) (x : T ⟶ G.X) :
    x ∈ (SubgroupFunctor.range d).carrier T ↔ LocallyCommutator x := by
  constructor
  · exact hd.locallyCommutator_of_mem_range hperf
  · intro hx
    rw [← hq.2.2.2]
    exact (mem_range_kernelι_iff q x).mpr (hx.comp_eq_one q)

/-- The torus quotient of an admissible subgroup is commutative, so its range
is intrinsically determined by local commutators. -/
theorem IsAdmissible.range_iff_locallyCommutator
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u})
    {d : D ⟶ G} (hd : IsAdmissible d) (T : Over S) (x : T ⟶ G.X) :
    x ∈ (SubgroupFunctor.range d).carrier T ↔ LocallyCommutator x := by
  obtain ⟨Q, q, hQ, hq⟩ := hd.2.2.2.2
  let : IsCommMonObj Q.X := hQ.isCommMonObj
  exact hd.mem_range_iff_locallyCommutator hperf q hq T x

/-- Any two admissible subgroups have the same all-test range. -/
theorem IsAdmissible.range_eq
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u})
    {d : D ⟶ G} (hd : IsAdmissible d)
    {D' : GroupScheme S} {d' : D' ⟶ G} (hd' : IsAdmissible d') :
    SubgroupFunctor.range d' = SubgroupFunctor.range d := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  exact (hd'.range_iff_locallyCommutator hperf T x).trans
    (hd.range_iff_locallyCommutator hperf T x).symm

/-- A homomorphism to a commutative group kills the kernel of every quotient by
an admissible subgroup, assuming relative semisimple fppf-perfectness. -/
theorem IsAdmissible.kernel_comp_eq_zero
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u})
    {d : D ⟶ G} (hd : IsAdmissible d) {Q : GroupScheme S} {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    {A : GroupScheme S} [IsCommMonObj A.X] (φ : G ⟶ A) :
    kernelι q ≫ φ = 0 := by
  apply Grp.hom_ext
  change (kernelι q).hom.hom ≫ φ.hom.hom = 1
  apply LocallyCommutator.comp_eq_one _ φ
  apply hd.locallyCommutator_of_mem_range hperf
  rw [← hq.2.2.2]
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩

/-- Every homomorphism to a commutative group factors uniquely through each
fppf quotient by an admissible subgroup. -/
theorem IsAdmissible.existsUnique_factor
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u})
    {d : D ⟶ G} (hd : IsAdmissible d) {Q : GroupScheme S} (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    {A : GroupScheme S} [IsCommMonObj A.X] (φ : G ⟶ A) :
    ∃! ψ : Q ⟶ A, q ≫ ψ = φ := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  exact FppfHomDescent.existsUnique_hom q φ (hd.kernel_comp_eq_zero hperf hq φ)

/-- Every admissible inclusion remains admissible after any scheme base change. -/
theorem IsAdmissible.baseChange {d : D ⟶ G} (hd : IsAdmissible d) (b : S' ⟶ S) :
    IsAdmissible ((GroupScheme.baseChange b).map d) := by
  refine ⟨hd.1.baseChange b, ?_, hd.2.2.1.baseChange b, ?_, ?_⟩
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact hd.2.1.baseChange b
  · intro s'
    have h := hd.2.2.1.isSemisimple_baseChange hd.2.2.2.1 (geometricPoint S' s' ≫ b)
    exact h.of_iso (baseChangeCompIso b (geometricPoint S' s') D).symm
  · obtain ⟨Q, q, hQ, hq⟩ := hd.2.2.2.2
    refine ⟨(GroupScheme.baseChange b).obj Q, (GroupScheme.baseChange b).map q,
      hQ.baseChange b, ?_⟩
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b

end RelativeDerived

/-- The full relative derived-group theorem follows from geometric existence
and relative semisimple fppf-perfectness. -/
def RelativeDerivedReductionStatement : Prop :=
  RelativeDerivedGroupExistenceStatement.{u} →
    RelativeSemisimpleFppfPerfectStatement.{u} → RelativeDerivedGroupStatement.{u}

/-- Conditional assembly of the unchanged relative derived-group statement. -/
theorem relativeDerivedGroup_of_inputs : RelativeDerivedReductionStatement.{u} := by
  intro hexists hperf S G hG
  obtain ⟨D, d, hd⟩ := hexists S G hG
  refine ⟨D, d, hd, ?_, ?_, ?_, ?_⟩
  · intro D' d' hd'
    exact hd.range_eq hperf hd'
  · exact hd.range_iff_locallyCommutator hperf
  · intro S' b
    exact hd.baseChange b
  · intro Q q hq A _ φ
    exact hd.existsUnique_factor hperf q hq φ

end Langlands.GroupScheme
