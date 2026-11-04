import Langlands.GroupScheme.HomogeneousQuotientFiber
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.StabilizerClosedSubgroup
import Langlands.GroupScheme.SchemeActionCurveOrbit
import Langlands.GroupScheme.Reductive.UnipotentDominantOrbitBound
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Actual orbits on smooth homogeneous quotient curves -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotient

section ArbitraryBase

variable {S : Scheme.{u}} {G B U : GroupScheme S}
    (b : B ⟶ G) {Q : Over S} (q : G.X ⟶ Q)
    (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier T)
    [QuasiCompact q.left] [Flat q.left] [Surjective q.left]

/-- The actual identity-coset stabilizer is the supplied exact-fiber subgroup,
on every test scheme. -/
theorem stabilizer_identityCoset :
    (Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).stabilizer
      (identityCoset G q) = SubgroupFunctor.range b := by
  ext T g
  rw [SchemeAction.mem_stabilizer]
  have hbase : toUnit T ≫ identityCoset G q = (1 : T ⟶ G.X) ≫ q := by
    rw [identityCoset, ← Category.assoc, MonObj.comp_one]
  rw [hbase, Dynamic.flagQuotientSchemeAction_act_lift, mul_one]
  exact (eq_comm.trans (hfib T 1 g)).trans (by simp only [inv_one, one_mul])

/-- A monic exact-fiber subgroup represents the actual identity-coset stabilizer. -/
theorem stabilizer_identityCoset_isRepresentedBy [Mono b.hom.hom] :
    ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).stabilizer
      (identityCoset G q)).IsRepresentedBy b := by
  rw [stabilizer_identityCoset b q hfib]
  exact ⟨inferInstance, rfl⟩

/-- A subgroup fixes the identity coset exactly when its all-test range lies in
the supplied exact-fiber subgroup. -/
theorem isFixed_identityCoset_iff (i : U ⟶ G) :
    ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict i).IsFixed
      (identityCoset G q) ↔ SubgroupFunctor.range i ≤ SubgroupFunctor.range b := by
  rw [SchemeAction.isFixed_restrict_iff, stabilizer_identityCoset b q hfib]

end ArbitraryBase

section Field

variable {k : Type u} [Field k]
    {G B U H : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- A smooth surjective quotient of a smooth connected affine group is smooth,
reduced and irreducible over the field. -/
theorem smooth_reduced_irreducible_quotient (q : G.X ⟶ Q)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth q.left] [Surjective q.left] :
    Smooth Q.hom ∧ IsReduced Q.left ∧ IrreducibleSpace Q.left := by
  have : Smooth (q.left ≫ Q.hom) := by
    rw [Over.w q]
    infer_instance
  have : Smooth Q.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
      q.left Q.hom
  have : GeometricallyIntegral G.X.hom :=
    smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
  have : IrreducibleSpace G.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton G.X.hom
  exact ⟨inferInstance,
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k Q.left Q.hom,
    q.left.surjective.irreducibleSpace q.left.continuous⟩

/-- A chosen actual moving rational point together with dominance and
quasi-compactness of its orbit map. -/
structure CurveOrbitData (a : SchemeAction U Q)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Q) where
  movingPoint : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U.X
  moves : a.act movingPoint x ≠ x
  dominant : IsDominant (a.orbitMap x).left
  quasiCompact : QuasiCompact (a.orbitMap x).left

variable [IsAlgClosed k] (b : B ⟶ G) (q : G.X ⟶ Q)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier T)
    [QuasiCompact q.left] [Smooth q.left] [Surjective q.left]

/-- Noncontainment in the exact-fiber subgroup produces an actual moving
rational translate and a dominant quasi-compact orbit on the quotient curve. -/
def curveOrbitData
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    [IsSeparated Q.hom]
    (hdim : topologicalKrullDim Q.left ≤ 1)
    (i : U ⟶ G) (hi : ¬ SubgroupFunctor.range i ≤ SubgroupFunctor.range b) :
    CurveOrbitData
      ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict i)
      (identityCoset G q) := by
  obtain ⟨hsm, _, hirr⟩ := smooth_reduced_irreducible_quotient q
  letI := hsm
  letI := hirr
  let a := (Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict i
  have hx : ¬ a.IsFixed (identityCoset G q) :=
    fun h => hi ((isFixed_identityCoset_iff b q hfib i).mp h)
  let h := a.nonfixedRationalTranslate (identityCoset G q) hx
  have horbit := a.dominant_quasiCompact_orbitMap_of_not_isFixed_of_dimension_le_one
    hdim (identityCoset G q) hx
  exact ⟨h.val, h.property, horbit.1, horbit.2⟩

include q hfib in
/-- The conditional unipotent orbit bound applied to the actual identity coset
of a smooth exact homogeneous quotient curve. -/
theorem unipotent_dimension_le_one_of_structural
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsPseudoReductive G)
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    [IsSeparated Q.hom]
    (hdimQ : topologicalKrullDim Q.left ≤ 1)
    (i : U ⟶ G) [Mono i.hom.hom] (j : H ⟶ U) (hj : IsClosedSubgroup j)
    (hU : IsUnipotent U) (hH : IsUnipotent H)
    (hdim : Lie.dimension U ≤ Lie.dimension H + 1)
    (hi : ¬ SubgroupFunctor.range i ≤ SubgroupFunctor.range b)
    (hji : SubgroupFunctor.range (j ≫ i) ≤ SubgroupFunctor.range b)
    (hb : IsClosedSubgroup b) (hB : IsSolvableGroupScheme B) :
    SubgroupFunctor.range j = ⊥ ∧ Lie.dimension H = 0 ∧ Lie.dimension U ≤ 1 := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsClosedImmersion b.hom.hom.left := hb
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  obtain ⟨hsm, hred, _⟩ := smooth_reduced_irreducible_quotient q
  have := hsm
  have := hred
  let a := Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib
  let D := curveOrbitData b q hfib hdimQ i hi
  have := D.dominant
  have := D.quasiCompact
  have hfix : ((a.restrict i).restrict j).IsFixed (identityCoset G q) := by
    have h := (isFixed_identityCoset_iff b q hfib (j ≫ i)).mpr hji
    intro T f g
    simpa only [SchemeAction.restrict_act, Grp.comp_hom_hom, Category.assoc]
      using h T f g
  exact a.unipotent_dimension_le_one_of_dominant_orbit_of_structural
    htorus hG i j hj hU hH hdim (identityCoset G q) hfix b hb
    (stabilizer_identityCoset_isRepresentedBy b q hfib) hB

end Field

end Langlands.GroupScheme.HomogeneousQuotient
