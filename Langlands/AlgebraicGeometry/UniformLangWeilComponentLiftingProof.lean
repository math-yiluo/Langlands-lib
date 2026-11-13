import Langlands.AlgebraicGeometry.UniformLangWeilComponentLiftingStatement
import Langlands.AlgebraicGeometry.UniformLangWeilFiniteFields
import Langlands.AlgebraicGeometry.SmoothTargetComponentGeometryProof

/-! # Uniform lifting across the finite actual target components -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry

/-- Choose a single finite-field lifting threshold over all target components. -/
def uniformLangWeilComponentFiniteFieldPointLifts
    (hLW : UniformLangWeilStatement.{u})
    (B Y : Scheme.{u}) (f : Y ⟶ B)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B))
    (hBqc : CompactSpace B) (hsmooth : Smooth f)
    (hsep : IsSeparated f) (hqc : QuasiCompact f)
    (hconn : GeometricallyConnected f) :
    Σ C : {C : ℝ // 0 < C},
      (K : Type u) → [Field K] → [Finite K] →
        (p : Spec (CommRingCat.of K) ⟶ B) →
        C.1 ^ 2 < (Nat.card K : ℝ) →
        {q : Spec (CommRingCat.of K) ⟶ Y // q ≫ f = p} := by
  classical
  let := hBft
  let := hBqc
  let := hsmooth
  let := hsep
  let := hqc
  let := hconn
  letI : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  letI : IsLocallyNoetherian B :=
    LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.{u}.from B)
  letI : Finite (_root_.ConnectedComponents B) := finite_componentIndex_of_compact
  letI := Fintype.ofFinite (_root_.ConnectedComponents B)
  have hcompft (c : _root_.ConnectedComponents B) :
      LocallyOfFiniteType (specULiftZIsTerminal.{u}.from (componentScheme B c)) := by
    have : LocallyOfFiniteType (componentι B c ≫ specULiftZIsTerminal.{u}.from B) :=
      inferInstance
    convert this using 1
    exact specULiftZIsTerminal.{u}.hom_ext _ _
  let lifts (c : _root_.ConnectedComponents B) :=
    uniformLangWeilLargeFiniteFieldPointLifts hLW
      (componentScheme B c) (componentPreimageScheme f c)
      (targetComponentRestriction f c) (smoothTargetComponentDimensions f c)
      (hcompft c) (QuasiCompact.compactSpace_of_compactSpace (componentι B c))
      inferInstance
      (MorphismProperty.of_isPullback (targetComponentRestriction_isPullback f c).flip hsep)
      inferInstance inferInstance
      (MorphismProperty.of_isPullback (targetComponentRestriction_isPullback f c).flip hqc)
      inferInstance
      ((SchemeFiberGeometry.nonemptyGeometricallyConnectedPureDimensionFibers_iff
        (targetComponentRestriction f c)).mp
        (smoothTargetComponentGeometry.1 Y B f c)).2
  let C : ℝ := 1 + ∑ c : _root_.ConnectedComponents B, (lifts c).1.1
  have hnonneg : 0 ≤ ∑ c : _root_.ConnectedComponents B, (lifts c).1.1 :=
    Finset.sum_nonneg fun c _ => (lifts c).1.2.le
  have hC : 0 < C := by dsimp [C]; linarith
  have hbound (c : _root_.ConnectedComponents B) : (lifts c).1.1 ≤ C := by
    have := Finset.single_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (_root_.ConnectedComponents B))) =>
        (lifts i).1.2.le) (Finset.mem_univ c)
    dsimp [C]
    linarith
  refine ⟨⟨C, hC⟩, fun K _ _ p hlarge => ?_⟩
  let c : _root_.ConnectedComponents B := _root_.ConnectedComponents.mk (p (IsLocalRing.closedPoint K))
  have hrange : Set.range p ⊆ Set.range (componentι B c) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change _root_.ConnectedComponents.mk (p x) = c
    have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hx]
  let pc := IsOpenImmersion.lift (componentι B c) p hrange
  have hlargec : (lifts c).1.1 ^ 2 < (Nat.card K : ℝ) := by
    have hc := (lifts c).1.2
    have hb := hbound c
    have hsquare := sq_le_sq₀ hc.le hC.le |>.mpr hb
    exact lt_of_le_of_lt hsquare hlarge
  let q := (lifts c).2 K pc hlargec
  refine ⟨q.1 ≫ componentPreimageι f c, ?_⟩
  rw [Category.assoc, ← targetComponentRestriction_ι, ← Category.assoc, q.2]
  exact IsOpenImmersion.lift_fac _ _ _

/-- Apply smooth Hensel lifting after choosing a point over the residue field. -/
def uniformLangWeilComponentHenselianPointLifts
    (hLW : UniformLangWeilStatement.{u})
    (B Y : Scheme.{u}) (f : Y ⟶ B)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B))
    (hBqc : CompactSpace B) (hsmooth : Smooth f)
    (hsep : IsSeparated f) (hqc : QuasiCompact f)
    (hconn : GeometricallyConnected f) :
    Σ C : {C : ℝ // 0 < C},
      (R : Type u) → [CommRing R] → [HenselianLocalRing R] →
        (K : Type u) → [Field K] → [Finite K] → [Algebra R K] →
        Function.Surjective (algebraMap R K) → C.1 ^ 2 < (Nat.card K : ℝ) →
        (p : Spec (CommRingCat.of R) ⟶ B) →
        {q : Spec (CommRingCat.of R) ⟶ Y // q ≫ f = p} := by
  classical
  let := hsmooth
  let lifts := uniformLangWeilComponentFiniteFieldPointLifts hLW B Y f
    hBft hBqc hsmooth hsep hqc hconn
  refine ⟨lifts.1, fun R _ _ K _ _ _ hK hlarge p => ?_⟩
  let q := lifts.2 K (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ p) hlarge
  let h := PointTopology.exists_smooth_lift_of_residue_point hK f p q.1 q.2
  exact ⟨h.choose, h.choose_spec.1⟩

namespace PointTopology

/-- Recover the original coefficient structure of the actual integral lift. -/
def uniformLangWeilComponentHenselianRingPointLifts
    (hLW : UniformLangWeilStatement.{u})
    (A : Type u) [CommRing A] (B Y : Over (Spec (CommRingCat.of A)))
    (f : Y ⟶ B)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left))
    (hBqc : CompactSpace B.left) (hsmooth : Smooth f.left)
    (hsep : IsSeparated f.left) (hqc : QuasiCompact f.left)
    (hconn : GeometricallyConnected f.left) :
    Σ C : {C : ℝ // 0 < C},
      (R : Type u) → [CommRing R] → [HenselianLocalRing R] → [Algebra A R] →
        (K : Type u) → [Field K] → [Finite K] → [Algebra A K] →
        (φ : R →ₐ[A] K) → Function.Surjective φ → C.1 ^ 2 < (Nat.card K : ℝ) →
        (p : RingPoint A B R) → {q : RingPoint A Y R // q ≫ f = p} := by
  classical
  let lifts := uniformLangWeilComponentHenselianPointLifts hLW B.left Y.left f.left
    hBft hBqc hsmooth hsep hqc hconn
  refine ⟨lifts.1, fun R _ _ _ K _ _ _ φ hφ hlarge p => ?_⟩
  let : Algebra R K := φ.toRingHom.toAlgebra
  let q := lifts.2 R K hφ hlarge p.left
  let qR : RingPoint A Y R := Over.homMk q.1 (by
    change q.1 ≫ Y.hom = Spec.algebraMap A R
    rw [← Over.w f, ← Category.assoc, q.2]
    exact Over.w p)
  exact ⟨qR, RingPoint.ext A q.2⟩

end PointTopology

/-- Uniform Lang-Weil controls finite-field and Henselian lifts without a
prescribed common dimension on all target components. -/
theorem uniformLangWeilComponentLifting : UniformLangWeilComponentLiftingStatement.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro hLW B Y f hBft hBqc hsmooth hsep hqc hconn
    let lifts := uniformLangWeilComponentFiniteFieldPointLifts hLW B Y f
      hBft hBqc hsmooth hsep hqc hconn
    exact ⟨lifts.1.1, lifts.1.2, fun K _ _ p hlarge =>
      ⟨(lifts.2 K p hlarge).1, (lifts.2 K p hlarge).2⟩⟩
  · intro hLW B Y f hBft hBqc hsmooth hsep hqc hconn
    let lifts := uniformLangWeilComponentHenselianPointLifts hLW B Y f
      hBft hBqc hsmooth hsep hqc hconn
    exact ⟨lifts.1.1, lifts.1.2, fun R _ _ K _ _ _ hK hlarge p =>
      ⟨(lifts.2 R K hK hlarge p).1, (lifts.2 R K hK hlarge p).2⟩⟩
  · intro hLW A _ B Y f hBft hBqc hsmooth hsep hqc hconn
    let lifts := PointTopology.uniformLangWeilComponentHenselianRingPointLifts hLW A B Y f
      hBft hBqc hsmooth hsep hqc hconn
    exact ⟨lifts.1.1, lifts.1.2, fun R _ _ _ K _ _ _ φ hφ hlarge p =>
      ⟨(lifts.2 R K φ hφ hlarge p).1, (lifts.2 R K φ hφ hlarge p).2⟩⟩

end Langlands.AlgebraicGeometry
