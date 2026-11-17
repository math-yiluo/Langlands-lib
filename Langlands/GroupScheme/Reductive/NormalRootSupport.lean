import Langlands.GroupScheme.Reductive.RootPairNoncommutation
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Rational.RootParabolicProper
import Langlands.GroupScheme.Dynamic.CommonTorusIntersectionDeterminants
import Langlands.GroupScheme.Derived.SplitTorusCommutators

/-! # Root support and coroots in normal subgroup functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)

/-- Root indices whose full intrinsic root subgroup is contained in a given
subgroup functor. -/
def normalRootSupport {J : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (F : SubgroupFunctor G) : Set J :=
  {r | RelativeRoot.subgroup i (P.root r) ≤ F}

/-- A root subgroup centralized by a cocharacter has zero integral pairing
with that cocharacter. This uses the nonzero actual root tangent space. -/
theorem relativeRoot_pairing_eq_zero_of_subgroup_le_dynamicCentralizer
    [Smooth G.X.hom] (hT : IsSplitTorus T.toGrp)
    {a : characterLattice T} (ha : a ∈ relativeRoots i)
    (nu : cocharacterLattice T)
    (hle : RelativeRoot.subgroup i a ≤
      Dynamic.centralizer (CommGroupScheme.groupHom nu ≫ i)) :
    latticePairing T a nu = 0 := by
  by_contra hn
  have hzero := weightSpace_inf_tangentSubmodule_centralizer hT i nu a
  simp only [hn, ↓reduceIte] at hzero
  have hweight : weightSpace i a ≤ RelativeRoot.tangentSubmodule
      (Dynamic.centralizer (CommGroupScheme.groupHom nu ≫ i)) :=
    (RelativeRoot.weightSpace_le_tangentSubmodule_subgroup i hT ha.1).trans
      (RelativeRoot.tangentSubmodule_mono hle)
  exact ha.2 (by rw [← inf_eq_left.mpr hweight, hzero])

section Normalizer

variable [Mono i.hom.hom.left] {F : SubgroupFunctor G}

omit [IsAffineHom G.X.hom] in
/-- Normality transports containment of full root functors under actual
normalizing points, on every scheme test. -/
theorem rootSubgroup_le_normal_weyl (hF : F.IsNormal)
    (n : normalizerPoints i) {a : characterLattice T}
    (ha : RelativeRoot.subgroup i a ≤ F) :
    RelativeRoot.subgroup i (weylAction i n a) ≤ F := by
  intro U x hx
  obtain ⟨y, hy⟩ := (RelativeRoot.normalizerConjEquiv i a n U).surjective ⟨x, hx⟩
  have he : G.constantPoint n U * y.val * (G.constantPoint n U)⁻¹ = x :=
    congrArg Subtype.val hy
  rw [← he]
  exact hF U (G.constantPoint n U) y.val (Subgroup.mem_top _) (ha U y.property)

/-- The root support of a normal subgroup is invariant under every reflection
of any actual realizing root datum. -/
theorem normalRootSupport_reflection {J : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (hF : F.IsNormal) (r s : J)
    (hr : r ∈ normalRootSupport i P F) :
    P.reflectionPerm s r ∈ normalRootSupport i P F := by
  obtain ⟨n, sigma, hn, hsigma⟩ := hP.2.2 s
  let m : normalizerPoints i := ⟨n, sigma, hn⟩
  have he : weylAction i m (P.root r) = P.root (P.reflectionPerm s r) := by
    rw [weylAction_eq i (n := m) (σ := sigma) hn (P.root r),
      ← characterAut_apply, hsigma, P.root_reflectionPerm]
  have h := rootSubgroup_le_normal_weyl i hF m hr
  rwa [he] at h

end Normalizer

/-- The rank-one Gauss relation expresses every coroot point as a product of
points in its two opposite root subgroups. Consequently their containment in
any subgroup functor forces containment of the entire coroot. -/
theorem IsRootDatumOf.coroot_mem_of_opposite_rootGroups
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) {J : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (r : J) (F : SubgroupFunctor G)
    (hplus : RelativeRoot.subgroup i (P.root r) ≤ F)
    (hminus : RelativeRoot.subgroup i (-P.root r) ≤ F) :
    P.coroot r ∈ cocharactersLandingIn i F := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨xp, xm, hxpm, hxmm, hxp, hxm, hrel⟩ :=
    exists_monic_rootRankOneRelations hG hT i hi P hP r
  have hroot (s : J) : P.root s ∈ roots i := hP.2.1 ▸ Set.mem_range_self s
  obtain ⟨s, hs⟩ : -P.root r ∈ Set.range P.root :=
    P.neg_mem_range_root_iff.mpr (Set.mem_range_self r)
  have hxprep := hxp.represents_root hG hT hi (hroot r)
    (RootPairNoncommutation.hasNoHigherRoots hG hT hi hP r)
  have hxmrep := hxm.represents_root hG hT hi (hs ▸ hroot s)
    (hs ▸ RootPairNoncommutation.hasNoHigherRoots hG hT hi hP s)
  intro U z
  let u : Γ(U.left, ⊤)ˣ := Gm.pointsEquiv _ U z
  let c : Γ(U.left, ⊤) := (u : Γ(U.left, ⊤)) - 1
  let w : Γ(U.left, ⊤) := ((u⁻¹ : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤))
  have hrelation := hrel U (RootCell.pt 1) (RootCell.pt c)
    (RootCell.pt (w * 1)) (RootCell.pt (w * c)) u
    (by rw [RootCell.crd_pt, RootCell.crd_pt, one_mul]; simp [c])
    (by rw [RootCell.crd_pt, RootCell.crd_pt])
    (by rw [RootCell.crd_pt, RootCell.crd_pt])
  have he := RootPairNoncommutation.solve_middle hrelation
  have hp (a : Γ(U.left, ⊤)) : RootCell.pt a ≫ xp.hom.hom ∈ F.carrier U :=
    hplus U (RootPairNoncommutation.mem_of_isRepresentedBy hxprep _)
  have hm (a : Γ(U.left, ⊤)) : RootCell.pt a ≫ xm.hom.hom ∈ F.carrier U :=
    hminus U (RootPairNoncommutation.mem_of_isRepresentedBy hxmrep _)
  change z ≫ (CommGroupScheme.groupHom (P.coroot r)).hom.hom ≫ i.hom.hom ∈ F.carrier U
  rw [← (Gm.pointsEquiv _ U).symm_apply_apply z]
  change (Gm.pointsEquiv _ U).symm u ≫
    (CommGroupScheme.groupHom (P.coroot r)).hom.hom ≫ i.hom.hom ∈ F.carrier U
  rw [he]
  exact (F.carrier U).mul_mem
    ((F.carrier U).mul_mem ((F.carrier U).inv_mem (hm _))
      ((F.carrier U).mul_mem (hp _) (hm _))) ((F.carrier U).inv_mem (hp _))

/-- A normal subgroup containing a root group contains the corresponding
actual coroot torus on all scheme tests. -/
theorem IsRootDatumOf.coroot_mem_of_normalRootSupport
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) {J : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) {F : SubgroupFunctor G} (hF : F.IsNormal)
    (r : J) (hr : r ∈ normalRootSupport i P F) :
    P.coroot r ∈ cocharactersLandingIn i F := by
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  have hminus := normalRootSupport_reflection i hP hF r r hr
  change RelativeRoot.subgroup i (P.root (P.reflectionPerm r r)) ≤ F at hminus
  rw [P.root_reflectionPerm, P.reflection_apply_self] at hminus
  exact hP.coroot_mem_of_opposite_rootGroups i hG hT hi r F hr hminus

/-- A root group centralizing a normal subgroup has zero Cartan pairing with
every root whose root group is contained in that subgroup. -/
theorem IsRootDatumOf.pairing_eq_zero_of_normalRootSupport_centralizer
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) {J : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) {F : SubgroupFunctor G} (hF : F.IsNormal)
    (r s : J) (hr : r ∈ normalRootSupport i P F)
    (hs : RelativeRoot.subgroup i (P.root s) ≤ F.centralizer) :
    P.pairing s r = 0 := by
  let : Smooth G.X.hom := hG.smooth
  have hcor := hP.coroot_mem_of_normalRootSupport i hG hT hi hF r hr
  have hle : RelativeRoot.subgroup i (P.root s) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom (P.coroot r) ≫ i) := by
    rw [← torusCentralizer_gm_eq_dynamicCentralizer]
    intro U x hx V f z
    exact hs U hx V f _ (hcor V z)
  have hz := relativeRoot_pairing_eq_zero_of_subgroup_le_dynamicCentralizer i hT
    (show P.root s ∈ relativeRoots i from by
      rw [relativeRoots_eq_roots, ← hP.2.1]
      exact Set.mem_range_self s)
    (P.coroot r) hle
  rwa [← hP.1, P.root_coroot_eq_pairing] at hz

end Langlands.GroupScheme
