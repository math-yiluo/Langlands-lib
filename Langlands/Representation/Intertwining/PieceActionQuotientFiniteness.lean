import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Langlands.Representation.Exponents.CentralDecompositionProof
import Langlands.Representation.Intertwining.CentralActionQuotientFiniteness

/-! # Finite action quotients on geometric-lemma pieces -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.PQFiniteActionRegularity

section Ambient

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance pieceFinitenessAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {B : CommGroupScheme (Spec (CommRingCat.of k))}

set_option maxHeartbeats 4000000 in
/-- Through a map `b` into the Levi whose image is central in `G(F)`, every group-algebra
element killing `τ` also kills the normalized induction of `τ`. -/
theorem groupAlgebraKernel_le_leviInduction (b : B.toGrp ⟶ M) (aG : B.toGrp ⟶ G)
    (hb : b ≫ l ≫ p = aG)
    (hcen : ∀ t, rationalPoints.map aG t ∈ Subgroup.center (rationalPoints G)) :
    letI := leviPointTopology l hl
    ∀ τ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      groupAlgebraKernel (τ.representation.comp (rationalPoints.map b)) (MonoidHom.id _) ≤
        groupAlgebraKernel
          (((leviInductionFunctor p l r hp hr hl hmul).obj τ).representation.comp
            (rationalPoints.map aG)) (MonoidHom.id _) := by
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
  refine CentralActionQuotient.groupAlgebraKernel_le_of_jointlyInjective _ _
    (fun x => Induction.centralEvaluation (pointImage p) (inducingRepresentation h hU W) j hj x)
    ?_
  intro f hf
  by_contra hne
  obtain ⟨x, hx⟩ := Induction.exists_smoothInduced_eval_ne_zero (pointImage p)
    (inducingRepresentation h hU W) hne
  exact hx (hf x)

/-- A finitely generated admissible Jacquet module on which a split component of the Levi acts
centrally has a finite-dimensional action quotient for that component. -/
theorem finite_actionQuotient_leviJacquet {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ M} (ha : IsSplitComponent a) :
    letI := leviPointTopology l hl
    ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints G),
      ((leviJacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible →
      Module.Finite (MonoidAlgebra ℂ (rationalPoints M))
        ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.asModule →
      Module.Finite ℂ (actionQuotient
        (((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.comp
          (rationalPoints.map a))) := by
  let := leviPointTopology l hl
  intro π hJadm hJfg
  let J := (leviJacquetFunctor p l r hp hr hl hmul).obj π
  have hcen : ∀ t, rationalPoints.map a t ∈ Subgroup.center (rationalPoints M) :=
    ha.isCentralSplitTorus.isCentral.map_mem_center
  have hloc : ∀ v : J, ∃ W : Subrepresentation (J.representation.comp (rationalPoints.map a)),
      Module.Finite ℂ W.toSubmodule ∧ v ∈ W := by
    intro v
    obtain ⟨W, hWfin, hvW⟩ := CentralDecomposition.admissible_centerFinite J.representation hJadm v
    exact ⟨⟨W.toSubmodule, fun t _ hw => W.apply_mem_toSubmodule ⟨_, hcen t⟩ hw⟩,
      hWfin, hvW⟩
  exact CentralActionQuotient.finite_actionQuotient_of_locallyFinite J.representation
    (rationalPoints.map a) hcen hloc

/-- A finitely generated admissible Jacquet module has only finitely many normalized
exponents along a split component of the Levi. -/
theorem finite_normalizedJacquetExponents_of_leviJacquet
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) :
    letI := leviPointTopology l hl
    ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints G),
      ((leviJacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible →
      Module.Finite (MonoidAlgebra ℂ (rationalPoints M))
        ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.asModule →
      {θ | IsNormalizedJacquetExponent p l r hp hl hr hmul ha π θ}.Finite := by
  let := leviPointTopology l hl
  intro π hJadm hJfg
  have := finite_actionQuotient_leviJacquet p l r hp hl hr hmul ha π hJadm hJfg
  refine (CentralActionQuotient.finite_generalizedEigencharacters
    (((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.comp
      (rationalPoints.map a))).subset ?_
  intro θ hθ
  exact (isNormalizedJacquetExponent_iff_leviJacquet p l r hp hl hr hmul ha π θ).mp hθ

end Ambient

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance pieceFinitenessPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ L}

/-- The split component of `L` acts on the full piece `i^L_{Q'} ∘ ι ∘ r^M_{P'}(σ)` through
a finite-dimensional quotient of its group algebra, when the Jacquet module of `σ` along
`P'` is admissible and finitely generated. -/
theorem finite_actionQuotient_piece (ha : IsSplitComponent a) (b : A.toGrp ⟶ D.L')
    (hb : b ≫ D.lQ' ≫ D.q' = a) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ).IsAdmissible →
      Module.Finite (MonoidAlgebra ℂ (rationalPoints D.M'))
        ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ).representation.asModule →
      Module.Finite ℂ (actionQuotient ((D.pieceFunctor.obj σ).ρ.comp (rationalPoints.map a))) := by
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  intro σ hJadm hJfg
  let J := (leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ
  let τ := SmoothRep.pullback D.e J
  let κ : rationalPoints A.toGrp →* rationalPoints D.M' := rationalPoints.map (b ≫ D.φ.hom)
  have hcenL : ∀ t, rationalPoints.map a t ∈ Subgroup.center (rationalPoints L) :=
    ha.isCentralSplitTorus.isCentral.map_mem_center
  have hinj : Function.Injective (rationalPoints.map (D.lQ' ≫ D.q')) := by
    intro x y hxy
    exact (leviPointsEquiv D.q' D.lQ' D.hq' D.hlQ').injective (Subtype.ext hxy)
  have hba : ∀ t, rationalPoints.map (D.lQ' ≫ D.q') (rationalPoints.map b t) =
      rationalPoints.map a t := by
    intro t
    rw [← pointMap_comp_apply, hb]
  have hcenL' : ∀ t, rationalPoints.map b t ∈ Subgroup.center (rationalPoints D.L') := by
    intro t
    rw [Subgroup.mem_center_iff]
    intro g
    apply hinj
    rw [map_mul, map_mul, hba]
    exact Subgroup.mem_center_iff.mp (hcenL t) _
  have hκ : ∀ t, κ t = D.e (rationalPoints.map b t) := by
    intro t
    rw [D.e_apply, ← pointMap_comp_apply]
  have hcenM' : ∀ t, κ t ∈ Subgroup.center (rationalPoints D.M') := by
    intro t
    rw [Subgroup.mem_center_iff]
    intro g
    rw [hκ]
    obtain ⟨g', rfl⟩ := D.e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hcenL' t) g']
  have hloc : ∀ v : J, ∃ W : Subrepresentation (J.representation.comp κ),
      Module.Finite ℂ W.toSubmodule ∧ v ∈ W := by
    intro v
    obtain ⟨W, hWfin, hvW⟩ := CentralDecomposition.admissible_centerFinite J.representation hJadm v
    exact ⟨⟨W.toSubmodule, fun t _ hw => W.apply_mem_toSubmodule ⟨κ t, hcenM' t⟩ hw⟩,
      hWfin, hvW⟩
  have hfinJ : Module.Finite ℂ (actionQuotient (J.representation.comp κ)) :=
    CentralActionQuotient.finite_actionQuotient_of_locallyFinite J.representation κ hcenM' hloc
  have hker := groupAlgebraKernel_le_leviInduction D.q' D.lQ' D.rQ' D.hq' D.hlQ' D.hrQ' D.hmulQ'
    b a hb hcenL τ
  have hcomp : τ.representation.comp (rationalPoints.map b) = J.representation.comp κ := by
    apply MonoidHom.ext
    intro t
    change J.representation (D.e (rationalPoints.map b t)) = J.representation (κ t)
    rw [hκ]
  rw [hcomp] at hker
  exact @CentralActionQuotient.finite_actionQuotient_of_kernel_le _ _ _ _ _ _ _ _
    (J.representation.comp κ) _ hker hfinJ

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
