import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianChartIntegralPointsClosedStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsOpenProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTotallyDisconnected
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPointsSurjective
import Langlands.AlgebraicGeometry.PointTopology.HenselianValuationRingProof
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeGeneration

/-!
# Integral points of one affine étale chart have closed image

Let `K` be a nontrivially normed field whose closed unit ball is a henselian subring `O`, let
`X` be a separated algebraic space locally of finite type over `Spec O`, and let `U → X` be an
étale map from an affine scheme. The image of `U(O)` in `X_K(K)` is closed.

The `O`-points of `U` form a closed subset `B` of `U_K(K)` on which every coordinate function
is bounded: the coordinate ring of `U_K` is generated over `K` by that of `U`, whose functions
take values in `O` on `B`. Since `X_K` is separated and `K` is henselian, the image of `B`
meets every affine chart of `X_K` in a closed set (`isClosed_preimage_image_of_bounded`), and
chart maps are open, so the complement of the image is open.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianUnitBall

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

set_option backward.isDefEq.respectTransparency false in
/-- The coordinates of a point of an affine scheme are the values of its global sections. -/
theorem affineSchemePointEquiv_apply (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (p : RingPoint R X S) (a : AffineCoordinateRing R X) :
    affineSchemePointEquiv R X S p a =
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom (p.left.appTop a) := by
  dsimp only [RingPoint] at p
  have h : CommRingCat.ofHom (affineSchemePointEquiv R X S p).toAlgHom.toRingHom =
      p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := by
    apply Spec.map_injective
    rw [affineSchemePointEquiv_spec R S p, Spec.map_comp, ← Scheme.isoSpec_Spec_hom,
      ← Scheme.isoSpec_hom_naturality]
    rfl
  exact congrArg (fun f => f.hom a) h

variable {K : Type u} [NontriviallyNormedField K] (O : Subring K)

/-- The `O`-points of an affine scheme over `O` form a closed subset of its `K`-points. -/
theorem isClosed_range_changeRing (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (U : Over (Spec (CommRingCat.of O))) [IsAffine U.left] :
    IsClosed[schemePointTopology O U K]
      (Set.range (RingPoint.changeRing (Algebra.ofId O K) : RingPoint O U O → RingPoint O U K)) := by
  rw [schemePointTopology_eq_affine]
  let A := AffineCoordinateRing O U
  let T : Set (AlgPoint O A K) :=
    ⋂ a : A, (fun φ : AlgPoint O A K => φ a) ⁻¹' Metric.closedBall 0 1
  have hT : IsClosed T := isClosed_iInter fun a =>
    Metric.isClosed_closedBall.preimage (AlgPoint.continuous_eval a)
  have heq : Set.range (RingPoint.changeRing (Algebra.ofId O K) : RingPoint O U O → RingPoint O U K) =
      affineSchemePointEquiv O U K ⁻¹' T := by
    ext p
    constructor
    · rintro ⟨p₀, rfl⟩
      simp only [T, Set.mem_preimage, Set.mem_iInter, mem_closedBall_zero_iff]
      intro a
      rw [affineSchemePointEquiv_changeRing]
      exact (hO _).1 (affineSchemePointEquiv O U O p₀ a).2
    · intro hp
      let φ : A →ₐ[O] K := (affineSchemePointEquiv O U K p).toAlgHom
      have hall : ∀ a, φ a ∈ O := by
        intro a
        simp only [T, Set.mem_preimage, Set.mem_iInter, mem_closedBall_zero_iff] at hp
        exact (hO _).2 (hp a)
      let ψ : A →ₐ[O] O :=
        { toFun := fun a => ⟨φ a, hall a⟩
          map_one' := Subtype.ext (map_one φ)
          map_mul' := fun a b => Subtype.ext (map_mul φ a b)
          map_zero' := Subtype.ext (map_zero φ)
          map_add' := fun a b => Subtype.ext (map_add φ a b)
          commutes' := fun r => Subtype.ext (φ.commutes r) }
      refine ⟨(affineSchemePointEquiv O U O).symm (AlgPoint.ofAlgHom ψ), ?_⟩
      apply (affineSchemePointEquiv O U K).injective
      rw [affineSchemePointEquiv_changeRing, Equiv.apply_symm_apply]
      ext a
      rfl
  rw [heq]
  exact hT.preimage continuous_induced_dom

/-- On the base change to `K` of the `O`-points of an affine scheme over `O`, every coordinate
function of the base-changed scheme is bounded. -/
theorem bounded_baseChange_range_changeRing (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (U : Over (Spec (CommRingCat.of O))) [IsAffine U.left] [IsAffine (ringBaseChange O K U).left]
    (g : AffineCoordinateRing K (ringBaseChange O K U)) :
    ∃ C : ℝ, ∀ p ∈ ringPointBaseChangeEquiv O K K U ''
        Set.range (RingPoint.changeRing (Algebra.ofId O K) : RingPoint O U O → RingPoint O U K),
      ‖affineSchemePointEquiv K (ringBaseChange O K U) K p g‖ ≤ C := by
  let UK := ringBaseChange O K U
  let T : Set (AffineCoordinateRing K UK →ₐ[K] K) :=
    (fun p => AlgPoint.toAlgHom (affineSchemePointEquiv K UK K p)) ''
      (ringPointBaseChangeEquiv O K K U ''
        Set.range (RingPoint.changeRing (Algebra.ofId O K) : RingPoint O U O → RingPoint O U K))
  have hgen : ∀ x ∈ Set.range ((pullback.fst U.hom (Spec.algebraMap O K)).appTop.hom :
      AffineCoordinateRing O U →+* AffineCoordinateRing K UK), ∃ C, ∀ φ ∈ T, ‖φ x‖ ≤ C := by
    rintro _ ⟨a, rfl⟩
    refine ⟨1, ?_⟩
    rintro _ ⟨_, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩
    set q : RingPoint O U K := v.changeRing (Algebra.ofId O K)
    have h₁ : affineSchemePointEquiv K UK K (ringPointBaseChangeEquiv O K K U q)
        ((pullback.fst U.hom (Spec.algebraMap O K)).appTop.hom a) =
          affineSchemePointEquiv O U K q a := by
      refine (affineSchemePointEquiv_apply UK _ _).trans
        (Eq.trans ?_ (affineSchemePointEquiv_apply U q a).symm)
      congr 1
      have hq : q.left = (ringPointBaseChangeEquiv O K K U q).left ≫
          pullback.fst U.hom (Spec.algebraMap O K) :=
        (ringPointBaseChangeEquiv_left_fst O K K U q).symm
      rw [hq]
      have h3 := Scheme.Hom.comp_appTop (ringPointBaseChangeEquiv O K K U q).left
        (pullback.fst U.hom (Spec.algebraMap O K))
      rw [h3]
      rfl
    have h₂ : ‖affineSchemePointEquiv O U K (v.changeRing (Algebra.ofId O K)) a‖ ≤ 1 := by
      rw [affineSchemePointEquiv_changeRing]
      exact (hO _).1 (affineSchemePointEquiv O U O v a).2
    exact (congrArg norm h₁).trans_le h₂
  obtain ⟨C, hC⟩ := bounded_of_adjoin_eq_top T _ (adjoin_range_baseChange_fst_eq_top O K U) hgen g
  exact ⟨C, fun p hp => hC _ ⟨p, hp, rfl⟩⟩

end HenselianUnitBall

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint schemePointTopology ringBaseChange ringPointBaseChangeEquiv
    schemeBaseChangeTopology_proof)

open HenselianIntegralPointsOpen in
/-- **Closed image of the integral points of one affine étale chart.** For a nontrivially
normed field `K` whose closed unit ball is a henselian subring `O`, a separated algebraic
space `X` locally of finite type over `Spec O` and an étale map `f : U → X` from an affine
scheme, the image of `U(O)` in `X_K(K)` is closed for the étale-chart topology. -/
theorem henselianChartIntegralPointsClosed : HenselianChartIntegralPointsClosedStatement.{u} := by
  intro K _ O hO hH X hXsep hXlft U f hU hf
  have : IsUltrametricDist K := PointTopology.HenselianUnitBall.isUltrametricDist O hO
  have hK : PointTopology.IsHenselianValuedField K :=
    (PointTopology.henselianIffValuationRingHenselian K O hO).mpr hH
  have : IsAffine U.left := hU
  let XK := baseChange (Spec.algebraMap O K) X
  have hXKsep : IsSeparated XK := hXsep.baseChange
  have hXKqs : IsQuasiSeparated XK :=
    (SpaceProductPoints.isQuasiSeparated_of_isSeparated hXsep).baseChange
  have hXKlft : LocallyOfFiniteTypeOverBase XK := hXlft.baseChange
  have : LocallyOfFiniteType U.hom :=
    HenselianIntegralPointsOpen.locallyOfFiniteType_of_isEtale hXlft (hom f) hf
  -- the base-changed chart is an affine étale chart of finite type
  let UK := ringBaseChange O K U
  have : IsAffine UK.left := by
    change IsAffine (Limits.pullback U.hom (Spec.algebraMap O K))
    infer_instance
  have hUKlft : LocallyOfFiniteType UK.hom := by
    change LocallyOfFiniteType (pullback.snd U.hom (Spec.algebraMap O K))
    infer_instance
  have hUKqc : QuasiCompact UK.hom := by
    change QuasiCompact (pullback.snd U.hom (Spec.algebraMap O K))
    infer_instance
  let aK : (schemeYoneda _).obj UK ⟶ XK.presheaf := restrictAtlas (Spec.algebraMap O K) (hom f)
  have haK : IsEtale aK := by
    have : MorphismProperty.RespectsIso (@Etale.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have h := hf
    unfold IsEtale at h ⊢
    exact relative_restrictAtlas (g := Spec.algebraMap O K) (@Etale.{u}) h
  let c : EtaleFiniteTypeChart K XK :=
    { scheme := UK
      hom := AlgebraicSpace.homMk aK
      isEtale := haK
      locallyOfFiniteType := hUKlft
      quasiCompact := hUKqc }
  have : IsAffine c.scheme.left := inferInstanceAs (IsAffine UK.left)
  -- the closed bounded set of base-changed integral points
  let S₀ : Set (RingPoint O U K) :=
    Set.range (RingPoint.changeRing (Algebra.ofId O K) : RingPoint O U O → RingPoint O U K)
  let B : Set (RingPoint K UK K) := ringPointBaseChangeEquiv O K K U '' S₀
  have he := schemeBaseChangeTopology_proof O K K U
  have hBcl : IsClosed[schemePointTopology K c.scheme K] B :=
    @IsHomeomorph.isClosedMap _ _ (schemePointTopology O U K) (schemePointTopology K UK K) _ he
      S₀ (PointTopology.HenselianUnitBall.isClosed_range_changeRing O hO U)
  have hBbdd : ∀ g : PointTopology.AffineCoordinateRing K c.scheme, ∃ C : ℝ,
      ∀ p ∈ B, ‖PointTopology.affineSchemePointEquiv K c.scheme K p g‖ ≤ C :=
    PointTopology.HenselianUnitBall.bounded_baseChange_range_changeRing O hO U
  -- the image of `U(O)` is the image of `B` under the chart map
  have hcompat : ∀ v : RingPoint O U O,
      schemePointsMap (X := XK) aK
          (ringPointBaseChangeEquiv O K K U (v.changeRing (Algebra.ofId O K))) =
        (baseChangeRingPointsEquiv O K K X).symm (RingPoints.changeRing (Algebra.ofId O K)
          (RingPoints.map f ((schemeRingPointsEquiv O U O).symm v))) := by
    intro v
    apply (baseChangeRingPointsEquiv O K K X).injective
    refine (baseChangeRingPointsEquiv_schemePointsMap f _).trans ?_
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply, RingPoints.changeRing_map]
    rfl
  have hrange : (Set.range fun u : RingPoint O U O =>
      (baseChangeRingPointsEquiv O K K X).symm (RingPoints.changeRing (Algebra.ofId O K)
        (RingPoints.map f ((schemeRingPointsEquiv O U O).symm u)))) = c.pointMap '' B := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨_, ⟨_, ⟨v, rfl⟩, rfl⟩, hcompat v⟩
    · rintro ⟨_, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩
      exact ⟨v, (hcompat v).symm⟩
  rw [hrange]
  -- the complement of the image is open
  let : TopologicalSpace (RingPoints K XK K) := etaleChartTopology K XK
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨e, v, he, rfl⟩ := exists_affine_chart_pointMap_eq hXKqs hXKlft z
  have hcl := isClosed_preimage_image_of_bounded hK hXKsep c e B hBcl hBbdd
  refine ⟨e.pointMap '' (e.pointMap ⁻¹' (c.pointMap '' B))ᶜ, ?_,
    e.isOpenMap_pointMap hK _ hcl.isOpen_compl, ⟨v, hz, rfl⟩⟩
  rintro _ ⟨m, hm, rfl⟩ hmem
  exact hm hmem

end Langlands.AlgebraicGeometry.AlgebraicSpace
