import Langlands.GroupScheme.Cartan.Induction
import Langlands.GroupScheme.GeneratedFamily
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.RootParabolicProper
import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Closed generation by a split torus and its actual root subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

namespace RelativeRoot

/-- Self-centralization on all tests puts the zero adjoint weight in the
actual tangent image of the torus. -/
theorem weightSpace_zero_le_tangentSubmodule_range_of_selfCentralizing
    [IsAffineHom T.toGrp.X.hom] (i : T.toGrp ⟶ G)
    (hself : torusCentralizer i = SubgroupFunctor.range i) :
    weightSpace i 0 ≤ tangentSubmodule (SubgroupFunctor.range i) := by
  intro X hX
  change X.toMul.val ∈ (SubgroupFunctor.range i).carrier _
  rw [← hself]
  exact Lie.mem_torusCentralizer_of_mem_weightSpace_zero i X.toMul hX

end RelativeRoot

section Generation

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hzero : weightSpace i 0 ≤
      RelativeRoot.tangentSubmodule (SubgroupFunctor.range i))
    {D : GroupScheme (Spec (CommRingCat.of k))} (d : D ⟶ G)
    (hd : IsClosedSubgroup d)
    (hDT : SubgroupFunctor.range i ≤ SubgroupFunctor.range d)
    (hDroot : ∀ α ∈ relativeRoots i,
      RelativeRoot.subgroup i α ≤ SubgroupFunctor.range d)

include hT hzero hd hDT hDroot in
/-- A closed subgroup containing the split torus and all its intrinsic root
functors is full when the zero adjoint weight lies in the torus tangent image.
The closed competitor need not be smooth or connected. -/
theorem range_eq_top_of_torus_and_rootSubgroups :
    SubgroupFunctor.range d = ⊤ := by
  classical
  have hrep : ∀ α : relativeRoots i,
      RelativeRoot.IsSmoothConnectedClosed (RelativeRoot.subgroup i α.val) := by
    intro α
    exact RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero hT i α.val α.property.1
  choose U j hj hjclosed hjsmooth hjconn using hrep
  let A : Option (relativeRoots i) → GroupScheme (Spec (CommRingCat.of k)) :=
    fun s => match s with
      | none => T.toGrp
      | some α => U α
  let a : ∀ s, A s ⟶ G := fun s => match s with
    | none => i
    | some α => j α
  have hA : ∀ s, Smooth (A s).X.hom ∧ IsAffineHom (A s).X.hom ∧
      ConnectedSpace (A s).X.left := by
    intro s
    cases s with
    | none => exact ⟨hT.smooth, hT.isAffineHom, hT.connectedSpace⟩
    | some α => exact ⟨hjsmooth α, (hjclosed α).isAffineHom, hjconn α⟩
  obtain ⟨H, e, hHsmooth, hHaffine, hHconn, he⟩ :=
    FiniteGeneration.exists_smooth_generated_family (A := A) (a := a) hA
  let : Smooth H.X.hom := hHsmooth
  let : IsAffineHom H.X.hom := hHaffine
  let : ConnectedSpace H.X.left := hHconn
  have heT : SubgroupFunctor.range i ≤ SubgroupFunctor.range e :=
    (factorsThrough_hom_iff_range_le i e).1 (he.2.1 none)
  have heroot : ∀ α ∈ relativeRoots i,
      RelativeRoot.subgroup i α ≤ SubgroupFunctor.range e := by
    intro α hα
    rw [← (hj ⟨α, hα⟩).2]
    exact (factorsThrough_hom_iff_range_le (j ⟨α, hα⟩) e).1 (he.2.1 (some ⟨α, hα⟩))
  have hlie : RelativeRoot.tangentSubmodule (SubgroupFunctor.range e) = ⊤ := by
    apply top_unique
    rw [← RelativeRoot.iSup_actionWeightSpace_eq_top (AutomorphicAction.conjugation i) hT]
    apply iSup_le
    intro χ
    rw [RelativeRoot.actionWeightSpace_conjugation]
    by_cases hχ : χ = 0
    · subst χ
      exact hzero.trans (RelativeRoot.tangentSubmodule_mono heT)
    · by_cases hχweight : weightSpace i χ = ⊥
      · rw [hχweight]
        exact bot_le
      · exact (RelativeRoot.weightSpace_le_tangentSubmodule_subgroup i hT hχ).trans
          (RelativeRoot.tangentSubmodule_mono (heroot χ ⟨hχ, hχweight⟩))
  have heclosed : IsClosedImmersion e.hom.hom.left := he.1
  let : Mono e.hom.hom := Over.mono_of_mono_left _
  have hsurj : Function.Surjective (Lie.targetMapLinear e k) := by
    apply LinearMap.range_eq_top.mp
    rw [← RelativeRoot.tangentSubmodule_range e, hlie]
  let : IsIso e := Lie.isIso_of_surjective_targetMapLinear e he.1 hsurj
  have htop : SubgroupFunctor.range e = ⊤ := by
    simpa using (SubgroupFunctor.range_iso_comp (asIso e) (𝟙 G)).trans
      (SubgroupFunctor.top_isRepresentedBy_id G).2
  have hfamilyD : ∀ s, FactorsThrough (a s).hom.hom d := by
    intro s
    apply (factorsThrough_hom_iff_range_le (a s) d).2
    cases s with
    | none => exact hDT
    | some α =>
      change SubgroupFunctor.range (j α) ≤ SubgroupFunctor.range d
      rw [(hj α).2]
      exact hDroot α.val α.property
  have hle := he.2.2 D d hd hfamilyD
  rw [htop] at hle
  apply SubgroupFunctor.ext
  intro V
  exact le_antisymm le_top (hle V)

/-- The actual group-scheme isomorphism supplied by closed torus-and-root
generation, retaining its explicit zero-weight hypothesis. -/
def rootTorusGenerationIso : D ≅ G := by
  let : IsClosedImmersion d.hom.hom.left := hd
  have hfull : (⊤ : SubgroupFunctor G).IsRepresentedBy d :=
    ⟨Over.mono_of_mono_left _,
      range_eq_top_of_torus_and_rootSubgroups i hT hzero d hd hDT hDroot⟩
  exact hfull.topIso

/-- The constructed isomorphism has the original closed inclusion as its
forward homomorphism. -/
theorem rootTorusGenerationIso_hom :
    (rootTorusGenerationIso i hT hzero d hd hDT hDroot).hom = d := by
  apply SubgroupFunctor.IsRepresentedBy.topIso_hom

end Generation

section SelfCentralizing

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    {D : GroupScheme (Spec (CommRingCat.of k))} (d : D ⟶ G)
    (hd : IsClosedSubgroup d)
    (hDT : SubgroupFunctor.range i ≤ SubgroupFunctor.range d)
    (hDroot : ∀ α ∈ relativeRoots i,
      RelativeRoot.subgroup i α ≤ SubgroupFunctor.range d)

include hT hself hd hDT hDroot in
/-- Self-centralization is sufficient for closed generation by a split torus
and its actual root functors. It remains an explicit premise. -/
theorem range_eq_top_of_selfCentralizing_torus_and_rootSubgroups :
    SubgroupFunctor.range d = ⊤ := by
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  exact range_eq_top_of_torus_and_rootSubgroups i hT
    (RelativeRoot.weightSpace_zero_le_tangentSubmodule_range_of_selfCentralizing i hself)
    d hd hDT hDroot

end SelfCentralizing

end Langlands.GroupScheme
