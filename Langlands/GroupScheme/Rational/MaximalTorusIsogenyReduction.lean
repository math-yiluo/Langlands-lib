import Langlands.GroupScheme.Rational.MaximalTorusConjugatorReductionCases
import Langlands.GroupScheme.Lie.SemisimpleIsogenyReduction
import Langlands.GroupScheme.Lie.SmoothIsogenyDimension
import Langlands.GroupScheme.CentralIsogeny.TorusNormalizerReflection
import Langlands.GroupScheme.CentralIsogeny.MaximalTorusImageSmooth
import Langlands.GroupScheme.Nilpotent.TorusNormalizer

/-! # Maximal-torus isogeny reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k : Type u} [Field k]

/-- A reachable target retaining a maximal torus and all-test normalizer reflection. -/
structure MaximalTorusReductionTarget
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    extends SemisimpleReductionTarget G where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ group
  maximal : IsMaximalTorus inclusion
  reflection : ReflectsTorusNormalizer map i inclusion
  locallyOfFinitePresentation : LocallyOfFinitePresentation map.hom.hom.left

namespace MaximalTorusReductionTarget

variable {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

instance (A : MaximalTorusReductionTarget i) : Smooth A.group.X.hom := A.smooth
instance (A : MaximalTorusReductionTarget i) : IsAffineHom A.group.X.hom := A.affine
instance (A : MaximalTorusReductionTarget i) : ConnectedSpace A.group.X.left := A.connected

/-- The algebraic-closure pullback of the retained target. -/
abbrev geometricGroup (A : MaximalTorusReductionTarget i) :=
  A.toSemisimpleReductionTarget.geometricGroup

instance (A : MaximalTorusReductionTarget i) : Smooth A.geometricGroup.X.hom :=
  inferInstanceAs (Smooth A.toSemisimpleReductionTarget.geometricGroup.X.hom)
instance (A : MaximalTorusReductionTarget i) : IsAffineHom A.geometricGroup.X.hom :=
  inferInstanceAs (IsAffineHom A.toSemisimpleReductionTarget.geometricGroup.X.hom)
instance (A : MaximalTorusReductionTarget i) : ConnectedSpace A.geometricGroup.X.left :=
  inferInstanceAs (ConnectedSpace A.toSemisimpleReductionTarget.geometricGroup.X.left)

/-- The identity retains the given maximal torus. -/
def identity [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hi : IsMaximalTorus i) : MaximalTorusReductionTarget i where
  toSemisimpleReductionTarget := SemisimpleReductionTarget.identity G
  torus := T
  inclusion := i
  maximal := hi
  reflection := reflectsTorusNormalizer_id i
  locallyOfFinitePresentation := by
    change LocallyOfFinitePresentation (𝟙 G.X.left)
    infer_instance

/-- A further central quotient carries the retained torus onto a maximal torus
and composes its normalizer reflection with the recorded reflection. -/
def centralQuotient (A : MaximalTorusReductionTarget i)
    (Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : A.group ⟶ Q) (hq : IsCentralIsogeny q) : MaximalTorusReductionTarget i := by
  classical
  let image := hq.exists_isMaximalTorus_image A.maximal
  let S := image.choose
  let j := image.choose_spec.choose
  let f := image.choose_spec.choose_spec.choose
  have hdata := image.choose_spec.choose_spec.choose_spec
  have : Flat f.hom.hom.left := hdata.2.2.2.1
  have : Surjective f.hom.hom.left := hdata.2.2.2.2.1
  have : QuasiCompact f.hom.hom.left := hdata.2.2.2.2.2
  have : IsClosedImmersion A.inclusion.hom.hom.left := A.maximal.2.1
  have : Mono A.inclusion.hom.hom := Over.mono_of_mono_left _
  have : LocallyOfFinitePresentation A.map.hom.hom.left := A.locallyOfFinitePresentation
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.locallyOfFinitePresentation
  exact {
    toSemisimpleReductionTarget := A.toSemisimpleReductionTarget.centralQuotient Q q hq
    torus := S
    inclusion := j
    maximal := hdata.1
    reflection := A.reflection.comp
      (hq.reflectsTorusNormalizer_of_fpqc_square A.maximal.1 A.inclusion f j hdata.2.1)
    locallyOfFinitePresentation := by
      change LocallyOfFinitePresentation (A.map.hom.hom.left ≫ q.hom.hom.left)
      infer_instance }

/-- Root division applies to the family retaining the original maximal torus. -/
theorem roots_eq_empty_of_geometric_semisimple_central
    (p : ℕ) [CharP k p] [ExpChar k p] (hp : 1 < p)
    (hcen : ∀ (A : MaximalTorusReductionTarget i)
      (X : lieKernel A.geometricGroup (AlgebraicClosure k)),
      Lie.IsSemisimpleElement A.geometricGroup X →
        Lie.elementCentralizerLie A.geometricGroup X = ⊤)
    {S : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
    (hS : IsSplitTorus S.toGrp) :
    ∀ (A : MaximalTorusReductionTarget i) (j : S.toGrp ⟶ A.geometricGroup),
      roots j = ∅ := by
  apply hS.roots_eq_empty_of_centralIsogeny_descent
    (fun A : MaximalTorusReductionTarget i => A.geometricGroup) p hp
  intro A j
  obtain ⟨Q, q, hs, ha, hc, hq, hker⟩ :=
    exists_connected_centralIsogeny_ker_targetMapLinear_eq_center_lie k p hp A.group
  let B := A.centralQuotient Q q hq
  let qbar : A.geometricGroup ⟶ B.geometricGroup :=
    (GroupScheme.baseChange (toAlgebraicClosure k)).map q
  refine ⟨B, qbar, hq.baseChange (toAlgebraicClosure k), ?_⟩
  intro X
  have hX : Lie.IsSemisimpleElement A.geometricGroup (Lie.targetMap j _ X) :=
    (Lie.isSemisimpleElement_of_isSplitTorus hS X).map j
  have hz := (Lie.targetMap_baseChange_eq_one_iff_elementCentralizerLie_eq_top
    q (hker (AlgebraicClosure k)) hX).2 (hcen A _ hX)
  apply Subtype.ext
  change X.val ≫ (j ≫ qbar).hom.hom = 1
  rw [Grp.comp_hom_hom, ← Category.assoc]
  exact congrArg Subtype.val hz

/-- Some retained target is nilpotent or has a noncentral geometric semisimple tangent. -/
theorem exists_alternative [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (hi : IsMaximalTorus i) :
    ∃ A : MaximalTorusReductionTarget i,
      IsNilpotentGroupScheme A.group ∨
        ∃ X : lieKernel A.geometricGroup (AlgebraicClosure k),
          Lie.IsSemisimpleElement A.geometricGroup X ∧
            Lie.elementCentralizerLie A.geometricGroup X ≠ ⊤ := by
  classical
  by_contra h
  have hnil : ∀ A : MaximalTorusReductionTarget i, ¬ IsNilpotentGroupScheme A.group := by
    intro A hn
    exact h ⟨A, Or.inl hn⟩
  have hcen : ∀ (A : MaximalTorusReductionTarget i)
      (X : lieKernel A.geometricGroup (AlgebraicClosure k)),
      Lie.IsSemisimpleElement A.geometricGroup X →
        Lie.elementCentralizerLie A.geometricGroup X = ⊤ := by
    intro A X hX
    by_contra hn
    exact h ⟨A, Or.inr ⟨X, hX, hn⟩⟩
  let A := identity hi
  rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
  · let _ : CharZero k := hzero
    exact hnil A
      (A.toSemisimpleReductionTarget.isNilpotent_of_geometric_semisimple_central (hcen A))
  · let _ : Fact p.Prime := hp
    let _ : CharP k p := hchar
    obtain ⟨S, j, hj⟩ := TorusExistence.exists_isMaximalTorus A.geometricGroup
    have hS := hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
    have hroot := roots_eq_empty_of_geometric_semisimple_central p hp.out.one_lt hcen hS A j
    exact hnil A
      (A.toSemisimpleReductionTarget.isNilpotent_of_geometric_central_maximalTorus hj
        (isCentral_of_roots_eq_empty hS j hroot))

end MaximalTorusReductionTarget

/-- The exact Case B reduction for every maximal torus over an arbitrary field. -/
theorem maximalTorusIsogenyReduction : MaximalTorusIsogenyReductionStatement.{u} := by
  intro k _ G _ _ _ T i hi
  obtain ⟨A, hA⟩ := MaximalTorusReductionTarget.exists_alternative hi
  have : IsFinite A.map.hom.hom.left := A.isogeny.1
  have : Flat A.map.hom.hom.left := A.isogeny.2.1
  have : LocallyOfFinitePresentation A.map.hom.hom.left := A.locallyOfFinitePresentation
  refine ⟨A.group, A.smooth, A.affine, A.connected, A.torus, A.inclusion, A.map,
    A.isogeny.2.1, A.isogeny.2.2, inferInstance, inferInstance,
    A.reflection, A.maximal, ?_, ?_⟩
  · exact (Lie.finrank_kernel_eq_of_isogeny A.map A.isogeny).symm.le
  · rcases hA with hnil | hnoncentral
    · exact Or.inl (fun U g => hnil.mem_torusNormalizer A.maximal.1 A.inclusion U g)
    · exact Or.inr hnoncentral

end Langlands.GroupScheme
