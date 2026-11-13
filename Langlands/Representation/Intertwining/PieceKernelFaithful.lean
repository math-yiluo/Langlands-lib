import Langlands.Representation.Intertwining.PieceActionQuotientFiniteness
import Langlands.Representation.Intertwining.PQRegularityFiltration
import Langlands.Representation.Intertwining.PQRegularity
import Langlands.Representation.Induction.Faithful
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility

/-! # Faithfulness of normalized induction for central group-algebra kernels -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.PQFiniteActionRegularity

/-- An intertwiner commutes with the group-algebra actions. -/
theorem intertwiningMap_asAlgebraHom_apply
    {H B V W : Type*} [Monoid H] [Monoid B]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {τ : Representation ℂ H W}
    (f : ρ.IntertwiningMap τ) (φ : B →* H) (c : MonoidAlgebra ℂ B) (v : V) :
    f (Representation.asAlgebraHom (ρ.comp φ) c v) =
      Representation.asAlgebraHom (τ.comp φ) c (f v) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single b z =>
    simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
    exact congrArg (fun y => z • y)
      (Representation.IntertwiningMap.isIntertwining ρ τ f (φ b) v)

section Ambient

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance pieceFaithfulAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {B : CommGroupScheme (Spec (CommRingCat.of k))}

set_option maxHeartbeats 4000000 in
/-- Through a map `b` into the Levi whose image is central in `G(F)`, every group-algebra
element killing the normalized induction of `τ` also kills `τ`: evaluation at the identity is
a surjective intertwiner for the central action. -/
theorem leviInduction_groupAlgebraKernel_le (b : B.toGrp ⟶ M) (aG : B.toGrp ⟶ G)
    (hb : b ≫ l ≫ p = aG)
    (hcen : ∀ t, rationalPoints.map aG t ∈ Subgroup.center (rationalPoints G)) :
    letI := leviPointTopology l hl
    ∀ τ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      groupAlgebraKernel
          (((leviInductionFunctor p l r hp hr hl hmul).obj τ).representation.comp
            (rationalPoints.map aG)) (MonoidHom.id _) ≤
        groupAlgebraKernel (τ.representation.comp (rationalPoints.map b)) (MonoidHom.id _) := by
  let := leviPointTopology l hl
  intro τ
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  let W := SmoothRep.pullback (leviPointsEquiv p l hp hl).symm τ
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hU := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let centralMap := splitComponentPointsMap (l ≫ p) b
  let j := (Subgroup.inclusion h.levi_le).comp centralMap
  have he : ∀ t, ((j t : pointImage p) : rationalPoints G) = rationalPoints.map aG t := by
    intro t
    change rationalPoints.map (l ≫ p) (rationalPoints.map b t) = _
    rw [← pointMap_comp_apply, hb]
  have hc : ∀ t, ((j t : pointImage p) : rationalPoints G) ∈ Subgroup.center (rationalPoints G) :=
    fun t => (he t).symm ▸ hcen t
  have hj : ∀ t (g : rationalPoints G), ((j t : pointImage p) : rationalPoints G) * g = g * j t :=
    fun t g => (Subgroup.mem_center_iff.mp (hc t) g).symm
  have hact : (inducingRepresentation h hU W).comp j =
      τ.representation.comp (rationalPoints.map b) := by
    apply MonoidHom.ext
    intro t
    apply LinearMap.ext
    intro v
    change ((HaarModulus.closedHalfCharacter (pointImage (r ≫ p)) hU (pointImage p)
      h.le_normalizer (j t) : ℂˣ) : ℂ) •
      W.representation (h.projection (j t)) v = τ.representation (rationalPoints.map b t) v
    rw [closedHalfCharacter_eq_one_of_mem_center _ _ hU h.le_normalizer (j t) (hc t),
      Units.val_one, one_smul]
    have hproj : h.projection (j t) = centralMap t := h.projection_levi (centralMap t)
    rw [hproj]
    change τ.representation ((leviPointsEquiv p l hp hl).symm (centralMap t)) v = _
    have hsymm : (leviPointsEquiv p l hp hl).symm (centralMap t) = rationalPoints.map b t := by
      rw [ContinuousMulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    rw [hsymm]
  have hind : ((leviInductionFunctor p l r hp hr hl hmul).obj τ).representation.comp
      (rationalPoints.map aG) =
      (Induction.smoothInduced (pointImage p) (inducingRepresentation h hU W)).comp
        ((pointImage p).subtype.comp j) := by
    apply MonoidHom.ext
    intro t
    change Induction.smoothInduced (pointImage p) (inducingRepresentation h hU W)
      (rationalPoints.map aG t) = Induction.smoothInduced (pointImage p)
        (inducingRepresentation h hU W) ((j t : pointImage p) : rationalPoints G)
    rw [he]
  rw [hind, ← hact]
  have hproj := continuous_projection_pointImage p l r hp hl hr hmul
  have hsm : IsSmooth (inducingRepresentation h hU W) :=
    (isSmooth_twist_iff _ _
      (HaarModulus.isOpen_ker_closedHalfCharacter _ hU _ h.le_normalizer)).mpr
      (isSmooth_comp h.projection hproj W.isSmooth)
  intro c hc
  apply (mem_groupAlgebraKernel_iff _ _ c).mpr
  apply LinearMap.ext
  intro w
  obtain ⟨f, rfl⟩ := Induction.smoothEvaluation_surjective (pointImage p)
    (inducingRepresentation h hU W) hsm 1 w
  let ev := Induction.centralEvaluation (pointImage p) (inducingRepresentation h hU W) j hj 1
  have hev := intertwiningMap_asAlgebraHom_apply ev (MonoidHom.id _) c f
  have hc' := (mem_groupAlgebraKernel_iff _ _ c).mp hc
  erw [hc'] at hev
  exact hev.symm.trans (map_zero ev)

/-- The two inclusions together: through a central map, `τ` and its normalized induction have
the same group-algebra kernel. -/
theorem leviInduction_groupAlgebraKernel_eq (b : B.toGrp ⟶ M) (aG : B.toGrp ⟶ G)
    (hb : b ≫ l ≫ p = aG)
    (hcen : ∀ t, rationalPoints.map aG t ∈ Subgroup.center (rationalPoints G)) :
    letI := leviPointTopology l hl
    ∀ τ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      groupAlgebraKernel
          (((leviInductionFunctor p l r hp hr hl hmul).obj τ).representation.comp
            (rationalPoints.map aG)) (MonoidHom.id _) =
        groupAlgebraKernel (τ.representation.comp (rationalPoints.map b)) (MonoidHom.id _) := by
  let := leviPointTopology l hl
  intro τ
  exact le_antisymm (leviInduction_groupAlgebraKernel_le p l r hp hl hr hmul b aG hb hcen τ)
    (groupAlgebraKernel_le_leviInduction p l r hp hl hr hmul b aG hb hcen τ)

end Ambient

section Piece

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance pieceKernelAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

/-- The kernel in `ℂ[A(F)]` of the action through `b : A ⟶ L'` on the inner representation
`ι ∘ r^M_{P'}(σ)` of `L'(F)` of a geometric-lemma piece, before the outer induction. -/
def GeometricLemmaIntersectionDatum.innerSplitComponentKernel
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (b : A.toGrp ⟶ D.L')
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    Ideal (MonoidAlgebra ℂ (rationalPoints A.toGrp)) :=
  haveI := hl.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  haveI := leviPoints_locallyCompactSpace p l hp hl
  haveI := leviPoints_nonarchimedeanGroup p l hp hl
  letI := leviPointTopology D.l' D.hl'
  letI := leviPointTopology D.lQ' D.hlQ'
  groupAlgebraKernel ((SmoothRep.pullbackFunctor D.e).obj
    ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ)).representation
    (rationalPoints.map b)

set_option maxHeartbeats 1000000 in
/-- The piece kernel of a geometric-lemma datum is the kernel on the inner representation:
the split component acts centrally, so the outer normalized induction changes no kernel. -/
theorem GeometricLemmaIntersectionDatum.pieceSplitComponentKernel_eq_inner
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
    (b : A.toGrp ⟶ D.L') (hb : b ≫ D.lQ' ≫ D.q' = a)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    pieceSplitComponentKernel a D σ = D.innerSplitComponentKernel b σ := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  have hcen : ∀ t, rationalPoints.map a t ∈ Subgroup.center (rationalPoints M) :=
    ha.isCentralSplitTorus.isCentral.map_mem_center
  exact leviInduction_groupAlgebraKernel_eq D.q' D.lQ' D.rQ' D.hq' D.hlQ' D.hrQ' D.hmulQ' b a hb
    hcen ((SmoothRep.pullbackFunctor D.e).obj
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ))

end Piece

end Langlands.Aubert.General.RepresentedParabolic
