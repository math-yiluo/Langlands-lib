import Langlands.GroupScheme.Rational.RationalReflectionAssembly
import Langlands.GroupScheme.Rational.RelativeReflectionPairing
import Langlands.GroupScheme.Rational.RootFactorPairTransport
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Rational.PositiveRootStabilizerAveraging
import Langlands.GroupScheme.Rational.DominantChamberMove
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Actual relative root systems in represented cocharacter centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

open RelativeRootSystem

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G L : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- Extract rational reflection data from the complete actual root-system
predicate; no integral coroot lift is needed. -/
theorem HasRelativeRootSystem.nonempty_rationalReflectionData
    (hroot : HasRelativeRootSystem i) :
    Nonempty (RelativeRootRationalReflectionData i) := by
  classical
  obtain ⟨J, hJ, P, hP, hcrys, _, hroots, hW, _⟩ := hroot
  let := hJ
  let := hcrys
  have hindex (α : relativeRoots i) : ∃ j, P.root j = rootVector i α := by
    have hx : toRat α.val ∈ Subtype.val '' Set.range P.root := by
      rw [hroots]
      exact Set.mem_image_of_mem _ α.property
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hx
    exact ⟨j, Subtype.ext hj⟩
  choose index hindex using hindex
  have hrep (α : relativeRoots i) :
      ∃ w : relativeWeylGroup i, relativeWeylAction i w = P.reflection (index α) := by
    have hr : P.reflection (index α) ∈ (relativeWeylAction i).range := by
      rw [← hW]
      exact Subgroup.mem_map.mpr ⟨RootPairing.Equiv.reflection P (index α),
        P.reflection_mem_weylGroup (index α),
        RootPairing.Equiv.reflection_weightEquiv P (index α)⟩
    exact hr
  choose representative hrep using hrep
  refine ⟨⟨fun α => P.coroot' (index α), representative, ?_, ?_, ?_⟩⟩
  · intro α
    rw [← hindex]
    exact P.coroot_root_two _
  · intro α β
    rw [← hindex]
    exact P.exists_value (index α) (index β)
  · intro α x
    rw [hrep, P.reflection_apply, hindex]

/-- A chosen rational-functional realization of the ambient actual reflections. -/
def rationalReflectionDataOfRootSystem (hroot : HasRelativeRootSystem i) :
    RelativeRootRationalReflectionData i :=
  Classical.choice hroot.nonempty_rationalReflectionData

/-- An actual root reflection belongs to every cocharacter centralizer whose
cocharacter pairs to zero with that root. -/
theorem IsRelativeReflection.mem_dynamicCentralizer
    {α : characterLattice T} (n : normalizerPoints i)
    (h : IsRelativeReflection i α (QuotientGroup.mk n))
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ζ : cocharacterLattice T} (hαζ : latticePairing T α ζ = 0) :
    n.val ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier
      (Over.mk (𝟙 _)) := by
  rw [normalizerPoint_mem_dynamicCentralizer_iff]
  apply hi.isSplitSubtorus.1.hom_ext_characters
  intro χ
  apply (gmEndEquiv k).injective
  change latticePairing T χ (cocharacterAut (normalizingAut i n) ζ) =
    latticePairing T χ ζ
  rw [latticePairing_cocharacterAut_normalizingAut]
  have he := h.latticePairing_schemeWeylCharacterAction hG hi hαζ
    (weylAction i n⁻¹ χ)
  change latticePairing T (weylAction i n (weylAction i n⁻¹ χ)) ζ =
    latticePairing T (weylAction i n⁻¹ χ) ζ at he
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at he
  exact he.symm

section Restriction

variable (iL : T.toGrp ⟶ L) (j : L ⟶ G)
  (hcomp : iL ≫ j = i) (ζ : cocharacterLattice T)
  (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
  [Mono iL.hom.hom.left] [IsAffineHom L.X.hom]

/-- The same-torus inclusion of actual root spans in a represented centralizer. -/
def centralizerRootSpanInclusion : relativeRootSpan iL →ₗ[ℚ] relativeRootSpan i :=
  Submodule.inclusion (Submodule.span_mono (Set.image_mono
    (relativeRoots_subset_of_factor hj iL hcomp)))

omit [Mono i.hom.hom.left] [Mono iL.hom.hom.left] in
@[simp] theorem centralizerRootSpanInclusion_rootVector (α : relativeRoots iL) :
    centralizerRootSpanInclusion iL j hcomp ζ hj (rootVector iL α) =
      rootVector i ⟨α.val, relativeRoots_subset_of_factor hj iL hcomp α.property⟩ :=
  rfl

/-- Each ambient actual reflection at an intrinsic root lifts to an actual
normalizing point of the represented centralizer, with unchanged character action. -/
theorem exists_centralizer_reflection_lift [LocallyOfFiniteType L.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootRationalReflectionData i) (α : relativeRoots iL) :
    ∃ nL : normalizerPoints iL,
      ∃ n : normalizerPoints i,
        QuotientGroup.mk n = D.representative
          ⟨α.val, relativeRoots_subset_of_factor hj iL hcomp α.property⟩ ∧
        weylAction iL nL = weylAction i n := by
  let a : relativeRoots i := ⟨α.val, relativeRoots_subset_of_factor hj iL hcomp α.property⟩
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (D.representative a)
  have href : IsRelativeReflection i α.val (QuotientGroup.mk n) := by
    refine ⟨a.property, D.coroot a, D.pair_self a, ?_⟩
    rw [hn]
    apply LinearEquiv.ext
    intro x
    exact (D.action a x).trans (Module.reflection_apply x (D.pair_self a)).symm
  have hzero : latticePairing T α.val ζ = 0 :=
    relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer hj iL hcomp ζ le_rfl α.property
  have hmem := href.mem_dynamicCentralizer n hG hi hzero
  rw [← hj.2] at hmem
  obtain ⟨p, hp⟩ := SubgroupFunctor.mem_range.mp hmem
  have : Mono j.hom.hom := hj.1
  have hpnormal : p ∈ normalizerPoints iL := by
    apply (mem_normalizerPoints_comp_iff iL j p).mp
    rw [hcomp, hp]
    exact n.property
  let nL : normalizerPoints iL := ⟨p, hpnormal⟩
  have hnmap : normalizerPointsMap iL j i hcomp nL = n := Subtype.ext hp
  refine ⟨nL, n, hn, ?_⟩
  rw [← hnmap, weylAction_normalizerPointsMap]

/-- Equal full-character actions give compatible actions on the included root spans. -/
theorem centralizerRootSpanInclusion_relativeWeylAction
    (nL : normalizerPoints iL) (n : normalizerPoints i)
    (haction : weylAction iL nL = weylAction i n) (x : relativeRootSpan iL) :
    centralizerRootSpanInclusion iL j hcomp ζ hj
        (relativeWeylAction iL (QuotientGroup.mk nL) x) =
      relativeWeylAction i (QuotientGroup.mk n)
        (centralizerRootSpanInclusion iL j hcomp ζ hj x) := by
  apply Subtype.ext
  change ratAut (weylAction iL nL) x.val = ratAut (weylAction i n) x.val
  rw [haction]

include hj hcomp in
/-- Ambient rational coroots restrict to the intrinsic root span, and the
actual lifted normalizers realize their reflections. -/
theorem nonempty_centralizerRationalReflectionData [LocallyOfFiniteType L.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootRationalReflectionData i) :
    Nonempty (RelativeRootRationalReflectionData iL) := by
  classical
  let toAmbient (α : relativeRoots iL) : relativeRoots i :=
    ⟨α.val, relativeRoots_subset_of_factor hj iL hcomp α.property⟩
  let incl := centralizerRootSpanInclusion iL j hcomp ζ hj
  choose nL n hn haction using
    exists_centralizer_reflection_lift iL j hcomp ζ hj hG hi D
  refine ⟨⟨fun α => (D.coroot (toAmbient α)).comp incl,
    fun α => QuotientGroup.mk (nL α), ?_, ?_, ?_⟩⟩
  · intro α
    exact D.pair_self (toAmbient α)
  · intro α β
    exact D.integral (toAmbient α) (toAmbient β)
  · intro α x
    have h := D.action (toAmbient α) (incl x)
    rw [← hn α] at h
    rw [← centralizerRootSpanInclusion_relativeWeylAction iL j hcomp ζ hj
      (nL α) (n α) (haction α) x] at h
    apply Subtype.ext
    exact congrArg (fun y : relativeRootSpan i => y.val) h

/-- Choose the restricted rational reflection data on an actual represented
cocharacter centralizer. -/
def centralizerRationalReflectionData [LocallyOfFiniteType L.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootRationalReflectionData i) : RelativeRootRationalReflectionData iL :=
  Classical.choice (nonempty_centralizerRationalReflectionData iL j hcomp ζ hj hG hi D)

include hj hcomp in
/-- A connected reductive represented cocharacter centralizer inherits the full
actual relative root-system predicate for the same maximal split torus. -/
theorem HasRelativeRootSystem.of_cocharacterCentralizer
    (hroot : HasRelativeRootSystem i)
    (hG : IsConnectedReductive G) (hL : IsConnectedReductive L)
    (hi : IsMaximalSplitTorus i) (hiL : IsMaximalSplitTorus iL) :
    HasRelativeRootSystem iL := by
  have := hL.smooth
  let D := centralizerRationalReflectionData iL j hcomp ζ hj hG hi
    (rationalReflectionDataOfRootSystem hroot)
  obtain ⟨ν, hν⟩ := hiL.isSplitSubtorus.1.exists_genericCocharacter iL
  exact D.hasRelativeRootSystem_of_positive_stabilizer hiL.isSplitSubtorus.1
    (hiL.isSplitSubtorus.1.finite_relativeRoots iL) hν
    (hasTrivialPositiveRootStabilizer iL hL hiL hν)

end Restriction

/-- Every closed connected reductive representative of a standard Levi
inherits the actual root system through its canonical torus factor. -/
theorem HasRelativeRootSystem.of_standardLeviTorusFactor
    (hroot : HasRelativeRootSystem i) (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)
    (hL : IsConnectedReductive L) (j : L ⟶ G)
    (hj : (standardLevi i ν J).IsRepresentedBy j) (hjc : IsClosedSubgroup j) :
    haveI := hL.isAffineHom
    haveI := (hi.isMaximalSplitTorus_standardLeviTorusFactor i ν J hj hjc).isSplitSubtorus.mono
    HasRelativeRootSystem (standardLeviTorusFactor i ν J hj) := by
  have := hL.isAffineHom
  let iL := standardLeviTorusFactor i ν J hj
  have hcomp : iL ≫ j = i := standardLeviTorusFactor_comp i ν J hj
  have hiL := hi.isMaximalSplitTorus_standardLeviTorusFactor i ν J hj hjc
  have := hiL.isSplitSubtorus.mono
  obtain ⟨⟨ζ, hζ⟩, hcomparison⟩ := hStandard k G hG T i hi ν hν J hJ
  have hrep : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j := by
    rw [← (hcomparison ζ hζ).2.1]
    exact hj
  exact HasRelativeRootSystem.of_cocharacterCentralizer iL j hcomp ζ hrep
    hroot hG hL hi hiL

end Langlands.GroupScheme
