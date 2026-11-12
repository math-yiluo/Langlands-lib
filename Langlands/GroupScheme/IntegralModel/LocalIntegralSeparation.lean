import Langlands.GroupScheme.IntegralModel.IntegralPointDescent
import Langlands.GroupScheme.IntegralModel.LocalField
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.RingTheory.LocalFieldDensity.LocalSeparationProof

/-! # Openness of the integral-point image over a local field -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology GaloisPointComparison

section Coordinates

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

private instance localSeparationModelAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

/-- The original-model coordinates of a rational point of the generic group, as an
`R`-algebra map into `K`. -/
def coordinateAlgHom (g : rationalPoints G) : AffineCoordinateRing R M.group.X →ₐ[R] K :=
  (affineSchemePointEquiv R M.group.X K
    (M.genericModelPointEquiv K (rationalCoeffEquiv K G g))).toAlgHom

theorem coordinateAlgHom_apply (g : rationalPoints G) (a : AffineCoordinateRing R M.group.X) :
    M.coordinateAlgHom g a =
      G.affinePointEvaluation (CommAlgCat.of K K) (rationalCoeffEquiv K G g)
        (M.genericCoordinate a) :=
  M.genericModelPointEquiv_evaluation K _ a

/-- Integrality is tested on algebra generators of the original coordinate ring. -/
theorem mem_integralPoints_iff_of_adjoin_eq_top {s : Set (AffineCoordinateRing R M.group.X)}
    (hs : Algebra.adjoin R s = ⊤) (g : rationalPoints G) :
    g ∈ M.integralPoints ↔ ∀ a ∈ s, M.coordinateAlgHom g a ∈ Set.range (algebraMap R K) := by
  rw [mem_integralPoints_iff_genericCoordinates]
  constructor
  · intro h a _
    have h' := h a
    rw [← coordinateAlgHom_apply] at h'
    exact h'
  · intro h a
    have hle : Algebra.adjoin R s ≤ (Algebra.ofId R K).range.comap (M.coordinateAlgHom g) :=
      Algebra.adjoin_le fun b hb => by
        obtain ⟨r, hr⟩ := h b hb
        exact ⟨r, hr⟩
    rw [hs] at hle
    obtain ⟨r, hr⟩ := hle (Algebra.mem_top : a ∈ ⊤)
    exact ⟨r, hr.trans (coordinateAlgHom_apply M g a)⟩

/-- The original coordinate ring is flat over the integral base. -/
theorem flat_affineCoordinateRing : Module.Flat R (AffineCoordinateRing R M.group.X) := by
  have hfl : AlgebraicGeometry.Flat (Spec.algebraMap R (AffineCoordinateRing R M.group.X)) := by
    rw [affineCoordinateSpecMap]
    infer_instance
  exact RingHom.flat_algebraMap_iff.mp (HasRingHomProperty.Spec_iff.mp hfl)

/-- Restriction of original coordinates to the generic group is injective. -/
theorem genericCoordinate_injective : Function.Injective M.genericCoordinate := by
  have := M.flat_affineCoordinateRing
  intro a b hab
  have hinv : Function.Injective M.genericIso.inv.hom.hom.left.appTop.hom := by
    have : IsIso M.genericIso.inv.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map M.genericIso.inv.hom.hom))
    exact (asIso M.genericIso.inv.hom.hom.left.appTop).commRingCatIsoToRingEquiv.injective
  have h1 := hinv hab
  change (pullback.fst M.group.X.hom (Spec.algebraMap R K)).appTop.hom a =
    (pullback.fst M.group.X.hom (Spec.algebraMap R K)).appTop.hom b at h1
  rw [← ringBaseChangeCoordinateAlgEquiv_one_tmul, ← ringBaseChangeCoordinateAlgEquiv_one_tmul]
    at h1
  have h2 := (ringBaseChangeCoordinateAlgEquiv R K M.group.X).injective h1
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap
    (M := AffineCoordinateRing R M.group.X) (Algebra.linearMap R K)
    (IsFractionRing.injective R K)
  have h3 : (Algebra.linearMap R K).rTensor _ ((1 : R) ⊗ₜ[R] a) =
      (Algebra.linearMap R K).rTensor _ ((1 : R) ⊗ₜ[R] b) := by
    simpa using h2
  have h4 := hinj h3
  simpa using congrArg (TensorProduct.lid R _) h4

end Coordinates

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  (M : IntegralModel ↥𝒪[F] F G)

omit [IsNonarchimedeanLocalField F] in
/-- Each original-model coordinate is continuous on the rational points of the generic group. -/
theorem continuous_coordinateAlgHom_apply (a : AffineCoordinateRing ↥𝒪[F] M.group.X) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    Continuous fun g : rationalPoints G => M.coordinateAlgHom g a := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have hc : Continuous (fun g : rationalPoints G =>
      rationalPointAlgebraHom F G.X g (M.genericCoordinate a)) :=
    (AlgPoint.continuous_eval _).comp
      ((affineSchemePointHomeomorph F G.X F).continuous.comp
        (rationalPointHomeomorph F G.X).continuous)
  convert hc using 1
  funext g
  rw [coordinateAlgHom_apply, rationalCoeffEquiv_eq]
  exact (affineSchemePointEquiv_apply_eq_evaluation G _ _).symm

/-- **The original integral-point image is open** in the rational-point topology. -/
theorem isOpen_integralPoints_localField :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsOpen (M.integralPoints : Set (rationalPoints G)) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  obtain ⟨s, hs⟩ := (inferInstance :
    Algebra.FiniteType ↥𝒪[F] (AffineCoordinateRing ↥𝒪[F] M.group.X)).out
  have heq : (M.integralPoints : Set (rationalPoints G)) =
      ⋂ a ∈ s, (fun g => M.coordinateAlgHom g a) ⁻¹'
        ((ValuativeRel.valuation F).integer : Set F) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
    rw [M.mem_integralPoints_iff_of_adjoin_eq_top hs]
    refine forall₂_congr fun a _ => ?_
    constructor
    · rintro ⟨r, hr⟩
      rw [← hr]
      exact r.2
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
  rw [heq]
  exact isOpen_biInter_finset fun a _ =>
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F)).preimage
      (M.continuous_coordinateAlgHom_apply a)

/-- **Separation by integral points.** For a connected reductive generic group, a nonzero
original coordinate is nonzero at some original integral section. -/
theorem exists_integralSection_apply_ne_zero (hG : IsConnectedReductive G)
    {b : AffineCoordinateRing ↥𝒪[F] M.group.X} (hb : b ≠ 0) :
    ∃ s : M.integralSections,
      affineSchemePointEquiv ↥𝒪[F] M.group.X ↥𝒪[F] (rationalPointEquiv ↥𝒪[F] M.group.X s) b ≠
        0 := by
  have := hG.smooth
  have := hG.connectedSpace
  set A := AffineCoordinateRing F G.X
  have hsm : Smooth (Spec.algebraMap F A) := by
    rw [affineCoordinateSpecMap]
    infer_instance
  have : Algebra.Smooth F A := RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hsm)
  have : IsLocallyNoetherian G.X.left := by
    have : LocallyOfFiniteType G.X.hom := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsIntegral G.X.left := CharacterLatticeProof.isIntegral_of_smooth F G.X.hom
  have : IsDomain A := inferInstanceAs (IsDomain Γ(G.X.left, ⊤))
  have hc : M.genericCoordinate b ≠ 0 := fun h =>
    hb (M.genericCoordinate_injective (h.trans (map_zero _).symm))
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let Φ := (rationalPointHomeomorph F G.X).trans (affineSchemePointHomeomorph F G.X F)
  have hopen : IsOpen (Φ '' (M.integralPoints : Set (rationalPoints G))) :=
    Φ.isOpenMap _ M.isOpen_integralPoints_localField
  have hmem : Φ 1 ∈ Φ '' (M.integralPoints : Set (rationalPoints G)) :=
    ⟨1, M.integralPoints.one_mem, rfl⟩
  let _ := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let _ : (Valued.v (R := F)).RankOne :=
  { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
      MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let _ : NontriviallyNormedField F :=
    Valued.toNontriviallyNormedField F (ValuativeRel.ValueGroupWithZero F)
  have : CompleteSpace F := inferInstance
  obtain ⟨y, ⟨g, hg, rfl⟩, hy⟩ :=
    Langlands.RingTheory.LocalFieldDensity.localSeparation F A (Φ 1) _
      (hopen.mem_nhds hmem) _ hc
  obtain ⟨s, rfl⟩ := hg
  refine ⟨s, fun hs => hy ?_⟩
  have h1 : Φ (M.integralPointMap s) (M.genericCoordinate b) =
      M.coordinateAlgHom (M.integralPointMap s) b := by
    rw [coordinateAlgHom_apply, rationalCoeffEquiv_eq]
    exact affineSchemePointEquiv_apply_eq_evaluation G _ _
  have h2 : M.coordinateAlgHom (M.integralPointMap s) b =
      algebraMap ↥𝒪[F] F (affineSchemePointEquiv ↥𝒪[F] M.group.X ↥𝒪[F]
        (rationalPointEquiv ↥𝒪[F] M.group.X s) b) := by
    unfold coordinateAlgHom
    rw [genericModelPointEquiv_integralPointMap, affineSchemePointEquiv_changeRing]
    rfl
  rw [h1, h2, hs, map_zero]

end LocalField

end Langlands.GroupScheme.IntegralModel
