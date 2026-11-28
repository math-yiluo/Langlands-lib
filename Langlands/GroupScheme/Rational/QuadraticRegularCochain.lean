import Langlands.GroupScheme.Rational.GaloisTwistedPointDensity
import Langlands.GroupScheme.Rational.StronglyRegularFieldOpen
import Langlands.GroupScheme.Rational.QuadraticCocycleSquareNeighborhood
import Langlands.AlgebraicGeometry.PointTopology.NormedOpenZariskiDensity
import Langlands.AlgebraicGeometry.PointTopology.RationalLocalDensityProof
import Langlands.GroupScheme.AffinePointTopologicalGroup
import Langlands.GroupScheme.General.AffinePointBaseChangeManifold

/-! # Regular twists inside prescribed neighborhoods of cochains -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuadraticToralReduction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 900000

/-- The full scheme centralizer of this rational point is a maximal torus. -/
def HasToralCentralizer {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (z : rationalPoints G) : Prop :=
  ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
    IsMaximalTorus j ∧ SubgroupFunctor.range j = G.pointCentralizer z

section Values

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- The Galois value of a twist is given by the usual change of cochain. -/
theorem value_twist (ξ : Cocycle G (ringTest K M)) (σ : M ≃ₐ[K] M)
    (f : G.affinePoints (CommAlgCat.of K M)) :
    GaloisCocycle.value (ξ.twist f) σ =
      f⁻¹ * GaloisCocycle.value ξ σ * GaloisPoint.conjugate K M G σ f := by
  change ((𝟙 _ ≫ f : G.affinePoints (CommAlgCat.of K M)))⁻¹ *
    GaloisCocycle.value ξ σ * GaloisPoint.conjugate K M G σ f = _
  rw [Category.id_comp]

/-- The Galois value at an automorphism of order two is inverted by it. -/
theorem conjugate_value_eq_inv (ξ : Cocycle G (ringTest K M)) (σ : M ≃ₐ[K] M)
    (hσ : σ * σ = 1) :
    GaloisPoint.conjugate K M G σ (GaloisCocycle.value ξ σ) = (GaloisCocycle.value ξ σ)⁻¹ := by
  have hone : GaloisCocycle.value ξ (1 : M ≃ₐ[K] M) = 1 := by
    rw [GaloisCocycle.value, GaloisCocycle.arrow_one, Cocycle.toFun_self]
  have h := GaloisCocycle.value_mul ξ σ σ
  rw [hσ, hone] at h
  exact eq_inv_of_mul_eq_one_right h.symm

end Values

section Regularity

variable {K M : Type u} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

private abbrev coefficientGroup := (baseChange (algebraBaseMap K M)).obj G

private instance coefficientGroup_affine : IsAffine (coefficientGroup (M := M) (G := G)).X.left :=
  ringBaseChange_isAffine K M G.X

private instance coefficientGroup_finiteType : LocallyOfFiniteType (coefficientGroup (M := M) (G := G)).X.hom :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.X.hom (algebraBaseMap K M)))

private abbrev cochainGroup := AffineWeil.groupScheme K M (coefficientGroup (M := M) (G := G))

/-- The cochains giving strongly regular values include the ground-field points
of a nonempty open in the Weil restriction. -/
theorem exists_regular_weilOpen (hG : IsConnectedReductive G) (ξ : Cocycle G (ringTest K M))
    (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1) :
    let W := cochainGroup (M := M) (G := G)
    ∃ V : Set W.X.left, IsOpen V ∧ V.Nonempty ∧
      ∀ q : RingPoint K W.X K, q.left (IsLocalRing.closedPoint K) ∈ V →
        HasToralCentralizer ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm
          (GaloisCocycle.value (ξ.twist (GaloisTwistedPointDensity.cochainEquiv K M G q)) σ)) := by
  have hH := connectedReductiveFieldExtensionStatement K M G hG
  obtain ⟨V, hV, hVne, hreg⟩ := exists_stronglyRegular_fieldOpen M _ hH
  obtain ⟨U, hU, hUne, htwist⟩ := GaloisTwistedPointDensity.exists_open_twist_preimage K M G
    σ hσ (GaloisCocycle.value ξ σ) V hV hVne
  refine ⟨U, hU, hUne, fun q hq => ?_⟩
  rw [value_twist]
  exact hreg _ (htwist q hq)

/-- At a finite Galois extension of an infinite field, a cocycle can be twisted
so that its value at a chosen nonidentity automorphism is strongly regular. -/
theorem exists_regular_cochain [Infinite K] (hG : IsConnectedReductive G)
    (ξ : Cocycle G (ringTest K M)) (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1) :
    ∃ f : RingPoint K G.X M, HasToralCentralizer
      ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm (GaloisCocycle.value (ξ.twist f) σ)) := by
  let W := cochainGroup (M := M) (G := G)
  have hW : IsConnectedReductive W := AffineWeil.isConnectedReductive_restriction K M _
    (connectedReductiveFieldExtensionStatement K M G hG)
  have hd := (ConnectedUnirationality.infinite_reductive_isUnirational torusUnirationality W hW).hasDenseRationalPoints
  obtain ⟨V, hV, hVne, hv⟩ := exists_regular_weilOpen hG ξ σ hσ
  obtain ⟨x, hx, hxd⟩ := hd.inter_open_nonempty V hV hVne
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hxd
  obtain ⟨a, ha⟩ := hq
  have hqV : (rationalPointEquiv K W.X q).left (IsLocalRing.closedPoint K) ∈ V := by
    rw [rationalPointEquiv_left, show IsLocalRing.closedPoint K = a from Subsingleton.elim _ _]
    change q.left a ∈ V
    rwa [ha]
  exact ⟨_, hv _ hqV⟩

end Regularity

section Neighborhood

variable {K M : Type u} [NontriviallyNormedField K] [NontriviallyNormedField M]
  [Algebra K M] [FiniteDimensional K M] [IsGalois K M] [IsModuleTopology K M]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

private theorem continuous_underlyingNormedPoint (X : Over (Spec (CommRingCat.of K))) [IsAffine X.left] :
    Continuous (underlyingNormedPoint X) := by
  let e := affineSchemePointHomeomorph K X K
  let s : X.left ≃ₜ PrimeSpectrum (AffineCoordinateRing K X) := Scheme.homeoOfIso X.left.isoSpec
  have h (p : RingPoint K X K) : algPointSpectrum (e p) = s (underlyingNormedPoint X p) := by
    exact congrArg (fun f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (AffineCoordinateRing K X)) =>
      f (IsLocalRing.closedPoint K)) (affineSchemePointEquiv_spec K K p)
  rw [show underlyingNormedPoint X = s.symm ∘ algPointSpectrum ∘ e from
    funext fun p => by simp only [Function.comp_apply, h, Homeomorph.symm_apply_apply]]
  exact s.symm.continuous.comp (continuous_algPointSpectrum.comp e.continuous)

/-- A nonempty analytic open of cochains contains a nonempty open on which
all twisted values at the chosen automorphism are strongly regular. -/
theorem exists_regular_cochainOpen (hG : IsConnectedReductive G) (ξ : Cocycle G (ringTest K M))
    (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1) (U : Set (RingPoint K G.X M)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (RingPoint K G.X M), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ f ∈ V, HasToralCentralizer ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm
        (GaloisCocycle.value (ξ.twist f) σ)) := by
  let W := cochainGroup (M := M) (G := G)
  have hW : IsConnectedReductive W := AffineWeil.isConnectedReductive_restriction K M _
    (connectedReductiveFieldExtensionStatement K M G hG)
  let e : RingPoint K W.X K ≃ RingPoint K G.X M := GaloisTwistedPointDensity.cochainEquiv K M G
  have he : IsHomeomorph e := GaloisTwistedPointDensity.isHomeomorph_cochainEquiv K M G
  obtain ⟨Z, hZ, hZne, hz⟩ := exists_regular_weilOpen hG ξ σ hσ
  have hu := hU.preimage he.continuous
  have hune := hUne.preimage e.surjective
  have hd := dense_underlyingNormedPoint_of_unirational W
    (ConnectedUnirationality.infinite_reductive_isUnirational torusUnirationality W hW) _ hu hune
  obtain ⟨x, hx, q, hq, hqx⟩ := hd.inter_open_nonempty Z hZ hZne
  let S := e ⁻¹' U ∩ underlyingNormedPoint W.X ⁻¹' Z
  have hSo : IsOpen S := hu.inter (hZ.preimage (continuous_underlyingNormedPoint W.X))
  have hSne : S.Nonempty := ⟨q, hq, by change underlyingNormedPoint W.X q ∈ Z; rwa [hqx]⟩
  refine ⟨e '' S, he.isOpenMap _ hSo, hSne.image e, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  · rintro _ ⟨p, hp, rfl⟩
    exact hz p hp.2

end Neighborhood

section Archimedean

variable {K M : Type u} [NontriviallyNormedField K] [RCLike M]
  [Algebra K M] [FiniteDimensional K M] [IsGalois K M] [IsModuleTopology K M]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (G.affinePoints (CommAlgCat.of K M)) :=
  G.affinePointsTopologicalSpace _

/-- A locally trivial cocycle has a nonempty open of cochains giving strongly
regular values with square roots inverted by the coefficient automorphism. -/
theorem exists_regular_squareCochainOpen (hG : IsConnectedReductive G)
    (ξ : Cocycle G (ringTest K M)) (hξ : ξ.IsTrivial)
    (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1) (hσ₂ : σ * σ = 1) :
    ∃ U : Set (G.affinePoints (CommAlgCat.of K M)), IsOpen U ∧ U.Nonempty ∧
      ∀ f ∈ U,
        let y := GaloisCocycle.value (ξ.twist f) σ
        HasToralCentralizer ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm y) ∧
          ∃ s : G.affinePoints (CommAlgCat.of K M),
            s * s = y ∧ GaloisPoint.conjugate K M G σ s = s⁻¹ := by
  let C := CommAlgCat.of K M
  let A := G.affinePoints C
  let : IsTopologicalGroup A := G.affinePointsIsTopologicalGroup C
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let d := Lie.dimension G
  have hdim : SmoothOfRelativeDimension d G.X.hom :=
    SubgroupProductOrbit.smoothOfRelativeDimension_lie_dimension G
  let := General.affineBaseChangeChartedSpace K M G hdim
  let : LieGroup 𝓘(ℝ, Fin d → M) ∞ A := General.affineBaseChangeLieGroup K M G hdim
  let φ : A ≃* A := (G.affinePointFunctor.mapIso (CommAlgCat.isoMk σ)).groupIsoToMulEquiv
  have hφ : Continuous φ := G.continuous_affinePointMap (A := C) (CommAlgCat.ofHom (Y := C) σ.toAlgHom)
    (IsModuleTopology.continuous_of_linearMap σ.toLinearMap)
  obtain ⟨V, hV, hV₁, hsq⟩ := exists_normOneSquareNeighborhood (E := Fin d → M) φ hφ
  let twist (f : A) := GaloisCocycle.value (ξ.twist f) σ
  have htwist : Continuous twist := by
    rw [show twist = fun f : A => f⁻¹ * GaloisCocycle.value ξ σ * φ f from
      funext (value_twist ξ σ)]
    exact (continuous_inv.mul continuous_const).mul hφ
  obtain ⟨f₀, hf₀⟩ := (GaloisCocycle.isTrivial_iff ξ).mp hξ
  have h₀ : twist f₀ = 1 := by
    change GaloisCocycle.value (ξ.twist f₀) σ = 1
    rw [value_twist, hf₀ σ]
    group
  let e := G.affinePointsRingPointHomeomorph C
  let B := e '' (twist ⁻¹' V)
  have hB : IsOpen B := e.isOpenMap _ (hV.preimage htwist)
  have hBn : B.Nonempty := ⟨e f₀, f₀, by change twist f₀ ∈ V; rwa [h₀], rfl⟩
  obtain ⟨U, hU, hUn, hUV, hreg⟩ := exists_regular_cochainOpen hG ξ σ hσ B hB hBn
  refine ⟨e ⁻¹' U, hU.preimage e.continuous, hUn.preimage e.surjective, fun f hf => ?_⟩
  have hregf := hreg (e f) hf
  rw [affinePointsRingPointHomeomorph_apply] at hregf
  refine ⟨hregf, hsq (twist f) ?_ (conjugate_value_eq_inv (ξ.twist f) σ hσ₂)⟩
  obtain ⟨g, hg, he⟩ := hUV hf
  exact e.injective he ▸ hg

end Archimedean

end Langlands.GroupScheme.QuadraticToralReduction
