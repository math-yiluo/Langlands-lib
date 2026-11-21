import Langlands.Global.AdelicIntertwiningOperator
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Descent.ClosedSubgroupIdeals
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.Unipotent.CharZeroConnectedProof

/-! # The closed stabilizer of the actual adelic intertwining integral -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P U V : GroupScheme (Spec (CommRingCat.of F))}
  (p : P ⟶ G) (iU : U ⟶ P) (j : V ⟶ G)
  (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)

/-- The scheme-theoretic intersection of `V` with the rational conjugate of `U`. -/
abbrev IntertwiningStabilizer := subgroupIntersection j (iU ≫ p ≫ (G.innerIso w).hom)

/-- The actual intersection has its natural ambient immersion. -/
def intertwiningStabilizerHom : IntertwiningStabilizer p iU j w ⟶ G :=
  subgroupIntersectionHom j (iU ≫ p ≫ (G.innerIso w).hom)

/-- The subgroup in `V(𝔸)` given by this scheme intersection. -/
def intertwiningAdelicStabilizer :
    Subgroup (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
  (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (intertwiningStabilizerHom p iU j w))).comap
    (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)).subtype

/-- Membership in the stabilizer is exactly conjugated membership in `U(𝔸)`. -/
theorem mem_intertwiningAdelicStabilizer_iff
    (v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
    v ∈ intertwiningAdelicStabilizer p iU j w ↔
      (innerAdelicPoint F G w)⁻¹ * v.val * innerAdelicPoint F G w ∈ parabolicUnipotentImage F p iU := by
  let d := iU ≫ p ≫ (G.innerIso w).hom
  let wA := innerAdelicPoint F G w
  have hv : v.val ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) := v.property
  change v.val ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (subgroupIntersectionHom j d)) ↔ _
  rw [range_subgroupIntersectionHom]
  change (v.val ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) ∧
    v.val ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range d)) ↔ _
  rw [and_iff_right hv]
  have hMap (x : AdelicGroupPoints F U) : map F U G d x = wA * map F U G (iU ≫ p) x * wA⁻¹ := by
    unfold d
    rw [← Category.assoc, map_comp_apply_of_hom, map_apply, affinePointsTarget_innerIso_hom]
  constructor
  · rintro ⟨x, hx⟩
    let a : AdelicGroupPoints F U := x
    have ha : map F U G d a = v.val := hx
    change wA⁻¹ * v.val * wA ∈ parabolicUnipotentImage F p iU
    refine ⟨a, show map F U G (iU ≫ p) a = wA⁻¹ * v.val * wA from ?_⟩
    rw [← ha, hMap]
    group
  · rintro ⟨x, hx⟩
    let a : AdelicGroupPoints F U := x
    have ha : map F U G (iU ≫ p) a = wA⁻¹ * v.val * wA := hx
    refine ⟨a, show map F U G d a = v.val from ?_⟩
    rw [hMap, ha]
    group

/-- A rational point in a closed adelic subgroup already lies in that closed
subgroup over the number field. The diagonal coefficient map is injective. -/
theorem rational_mem_adelicPoints_range_iff
    {H : GroupScheme (Spec (CommRingCat.of F))} {k : H ⟶ G} (hk : IsClosedSubgroup k)
    (x : RationalGroupPoints F G) :
    rational F G x ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range k) ↔
      x ∈ AdelicSubgroupPoints.rationalPoints F G (SubgroupFunctor.range k) := by
  let a := (algSpec (CommRingCat.of F)).map
    (CommAlgCat.ofHom (Algebra.ofId F (AdeleRing (𝓞 F) F))).op
  have ha : IsSchemeTheoreticallyDominant a.left := by
    change IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom
      (algebraMap F (AdeleRing (𝓞 F) F))))
    let : Nontrivial (AdeleRing (𝓞 F) F) := by
      change Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
      infer_instance
    have hinj : Function.Injective (algebraMap F (AdeleRing (𝓞 F) F)) :=
      (algebraMap F (AdeleRing (𝓞 F) F)).injective
    have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap F (AdeleRing (𝓞 F) F)))) := by
      constructor
      change DenseRange (PrimeSpectrum.comap (algebraMap F (AdeleRing (𝓞 F) F)))
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
        (RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le
    exact IsSchemeTheoreticallyDominant.of_isDominant _
  change a ≫ x ∈ (SubgroupFunctor.range k).carrier _ ↔ x ∈ (SubgroupFunctor.range k).carrier _
  rw [hk.mem_range_iff_ker_le, hk.mem_range_iff_ker_le, Over.comp_left, Scheme.Hom.ker_comp,
    a.left.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- The lattice of the adelic stabilizer is the actual rational subgroup used
in the defining integral, seen in the ambient radical. -/
theorem intertwiningRationalSubgroup_eq_rational_inf_stabilizer :
    intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w) =
      AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j) ⊓
        intertwiningAdelicStabilizer p iU j w := by
  ext v
  rw [mem_intertwiningRationalSubgroup_iff, Subgroup.mem_inf, mem_intertwiningAdelicStabilizer_iff]

omit [NumberField F] in
private theorem range_intertwiningStabilizer_le :
    SubgroupFunctor.range (intertwiningStabilizerHom p iU j w) ≤ SubgroupFunctor.range j := by
  unfold intertwiningStabilizerHom
  rw [range_subgroupIntersectionHom]
  exact fun _ _ hx => hx.1

/-- The stabilizer as an adelic subgroup of `G` and as a subgroup of the
adelic radical are the same topological group via the inclusion. -/
def intertwiningStabilizerEquiv :
    AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (intertwiningStabilizerHom p iU j w))
      ≃ₜ* intertwiningAdelicStabilizer p iU j w where
  toFun x := ⟨⟨x.val, range_intertwiningStabilizer_le p iU j w _ x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- In the adelic stabilizer, the rational subgroup in the defining
integral is exactly its intrinsic principal rational subgroup. -/
theorem map_rationalSubgroup_intertwiningStabilizerEquiv
    (hk : IsClosedSubgroup (intertwiningStabilizerHom p iU j w)) :
    (AdelicSubgroupPoints.rationalSubgroup F G
      (SubgroupFunctor.range (intertwiningStabilizerHom p iU j w))).map
        (intertwiningStabilizerEquiv p iU j w).toMonoidHom =
      (intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)).comap
        (intertwiningAdelicStabilizer p iU j w).subtype := by
  let k := intertwiningStabilizerHom p iU j w
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j)
  ext x
  rw [Subgroup.mem_comap, intertwiningRationalSubgroup_eq_rational_inf_stabilizer, Subgroup.mem_inf]
  change _ ↔ x.val ∈ Γ ∧ x.val ∈ intertwiningAdelicStabilizer p iU j w
  rw [and_iff_left x.property]
  constructor
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    refine ⟨⟨r.val, range_intertwiningStabilizer_le p iU j w _ r.property⟩, Subtype.ext rfl⟩
  · rintro ⟨r, hr⟩
    have hrq : rational F G r.val = x.val.val :=
      congrArg (fun a : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) => a.val) hr
    have hx : x.val.val ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range k) := x.property
    have hR : r.val ∈ AdelicSubgroupPoints.rationalPoints F G (SubgroupFunctor.range k) :=
      (rational_mem_adelicPoints_range_iff hk r.val).mp (hrq.symm ▸ hx)
    let r' : AdelicSubgroupPoints.rationalPoints F G (SubgroupFunctor.range k) := ⟨r.val, hR⟩
    refine ⟨AdelicSubgroupPoints.rational F G _ r', ⟨r', rfl⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hrq

/-- The intersection of closed unipotent subgroups is closed, smooth,
connected and unipotent over the number field. -/
theorem intertwiningStabilizer_geometry
    [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
    (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup (iU ≫ p)) (hV : IsUnipotent V) :
    IsClosedSubgroup (intertwiningStabilizerHom p iU j w) ∧
      Smooth (IntertwiningStabilizer p iU j w).X.hom ∧
      ConnectedSpace (IntertwiningStabilizer p iU j w).X.left ∧
      IsUnipotent (IntertwiningStabilizer p iU j w) := by
  let d := iU ≫ p ≫ (G.innerIso w).hom
  let H := IntertwiningStabilizer p iU j w
  have hd : IsClosedSubgroup d := by
    unfold d
    rw [← Category.assoc]
    exact hi.comp_iso (G.innerIso w)
  have hι := isClosedSubgroup_subgroupIntersectionFst j hd
  have hHc : IsClosedSubgroup (intertwiningStabilizerHom p iU j w) := hι.comp hj
  let hA : IsAffineHom H.X.hom := hι.isAffineHom
  let : IsClosedImmersion (subgroupIntersectionFst j d).hom.hom.left := hι
  have hft : LocallyOfFiniteType H.X.hom := by
    rw [← Over.w (subgroupIntersectionFst j d).hom.hom]
    infer_instance
  have hu : IsUnipotent H := unipotentClosedSubgroup F V H (subgroupIntersectionFst j d) hι hV
  exact ⟨hHc, affineCartierSmooth F H hA hft, charZeroUnipotentConnected F H hA hft hu, hu⟩

/-- In an affine ambient group, the stabilizer for the actual integral is
closed and has a compact rational quotient. -/
def IntertwiningStabilizerStatement : Prop :=
  ∀ [IsAffine G.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom],
    IsClosedSubgroup j → IsClosedSubgroup (iU ≫ p) → IsUnipotent V →
      IsClosed (intertwiningAdelicStabilizer p iU j w :
        Set (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j))) ∧
      Nonempty (CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
        (SubgroupFunctor.range (intertwiningStabilizerHom p iU j w)))) ∧
      (AdelicSubgroupPoints.rationalSubgroup F G
        (SubgroupFunctor.range (intertwiningStabilizerHom p iU j w))).map
          (intertwiningStabilizerEquiv p iU j w).toMonoidHom =
        (intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)).comap
          (intertwiningAdelicStabilizer p iU j w).subtype

theorem intertwiningStabilizer : IntertwiningStabilizerStatement p iU j w := by
  intro _ _ _ hj hi hV
  obtain ⟨hclosed, hs, hc, hu⟩ := intertwiningStabilizer_geometry p iU j w hj hi hV
  let k := intertwiningStabilizerHom p iU j w
  let : IsClosedImmersion k.hom.hom.left := hclosed
  let : IsAffine (IntertwiningStabilizer p iU j w).X.left := isAffine_of_isAffineHom k.hom.hom.left
  exact ⟨(AdelicSubgroupPoints.isClosed_adelicPoints_range F G k).preimage continuous_subtype_val,
    ⟨AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F k hs hc hu⟩,
    map_rationalSubgroup_intertwiningStabilizerEquiv p iU j w hclosed⟩

end Langlands.Global.AdelicGroupPoints
