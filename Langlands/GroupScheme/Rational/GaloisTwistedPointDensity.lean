import Langlands.GroupScheme.AffineWeilEmbeddingCoordinateMorphism
import Langlands.GroupScheme.AffineWeilRestrictionTopology
import Langlands.GroupScheme.Reductive.AffineWeilConnectedReductive
import Langlands.GroupScheme.Absolute.StronglyRegularGroupOpen
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Rational.ConnectedGroupUnirationalityReduction
import Langlands.GroupScheme.Rational.GaloisCocycleStronglyRegular
import Langlands.GroupScheme.Rational.GeometricPointHom
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Reductive.FiniteProducts
import Langlands.GroupScheme.Torus.TorusUnirationalityProof

/-! # Density of twisted Galois values -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Algebra.SeparableTensor
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

/-- Twisted values at a nonidentity coefficient automorphism are Zariski dense. -/
def GaloisTwistedPointDensityStatement : Prop :=
  ∀ (K M : Type u) [Field K] [Infinite K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] [IsAlgClosed M]
    (G : GroupScheme (Spec (CommRingCat.of K))), IsConnectedReductive G →
    ∀ (σ : M ≃ₐ[K] M), σ ≠ 1 →
    ∀ y : ringTest K M ⟶ G.X,
      Dense (⋃ f : (ringTest K M ⟶ G.X),
        Set.range ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm
          (f⁻¹ * y * (ringTestMap K σ.toAlgHom ≫ f))).left)

namespace GaloisTwistedPointDensity

variable (K M : Type u) [Field K] [Field M] [Algebra K M] [FiniteDimensional K M]
  (G : GroupScheme (Spec (CommRingCat.of K)))

private abbrev b := algebraBaseMap K M
private abbrev geometricGroup := (baseChange (b K M)).obj G

variable [IsAffine (geometricGroup K M G).X.left]
  [LocallyOfFiniteType (geometricGroup K M G).X.hom]

private abbrev restriction := AffineWeil.groupScheme K M (geometricGroup K M G)

private abbrev coefficientMap (τ : M →ₐ[K] M) :=
  Spec.map (CommRingCat.ofHom τ.toRingHom)

private abbrev coefficientIso (τ : M →ₐ[K] M) :=
  descentBaseChangeIso (b K M) (coefficientMap K M τ)
    (AffineWeil.embeddingBaseMap_over K M M τ) G

/-- A coordinate of the geometric Weil restriction in the original geometric group. -/
private def coefficientProjection (τ : M →ₐ[K] M) :
    (baseChange (b K M)).obj (restriction K M G) ⟶ geometricGroup K M G :=
  EmbeddingProduct.evaluationComponent (b K M) (b K M) (coefficientMap K M τ)
    (AffineWeil.embeddingBaseMap_over K M M τ) (restriction K M G) (geometricGroup K M G)
    (AffineWeil.evaluation K M (geometricGroup K M G)) ≫ (coefficientIso K M G τ).hom

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientProjection_on_extended
    (q : rationalPoints (restriction K M G)) (τ : M →ₐ[K] M) :
    baseChangeBasePointsEquiv (b K M) G
        (geometricRationalPointHom (K := M) (restriction K M G) q ≫
          (coefficientProjection K M G τ).hom.hom) =
      ringTestMap K τ ≫ baseChangeBasePointsEquiv (b K M) G
        (geometricRationalPointHom (K := M) (restriction K M G) q ≫
          (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom) := by
  let a := coefficientMap K M τ
  let W := restriction K M G
  let H := geometricGroup K M G
  let v := geometricRationalPointHom (K := M) W q
  let e := AffineWeil.evaluation K M H
  let h := AffineWeil.embeddingBaseMap_over K M M τ
  let p := EmbeddingProduct.intermediateProjection (b K M) (b K M) a h W
  have hv₁ : v.left ≫ pullback.fst W.X.hom (b K M) = b K M ≫ q.left :=
    baseChangeSectionHom_fst (b K M) W q
  have hv₂ : v.left ≫ pullback.snd W.X.hom (b K M) = 𝟙 (Spec (CommRingCat.of M)) := Over.w v
  have hvp : v.left ≫ p = a ≫ v.left := by
    apply pullback.hom_ext
    · rw [Category.assoc, EmbeddingProduct.intermediateProjection_fst, hv₁,
        Category.assoc, hv₁, ← Category.assoc, h]
    · calc
        _ = a := by
          rw [Category.assoc, EmbeddingProduct.intermediateProjection_snd, ← Category.assoc,
            hv₂]
          exact Category.id_comp a
        _ = _ := by
          rw [Category.assoc, hv₂]
          exact (Category.comp_id a).symm
  have hc : (coefficientProjection K M G τ).hom.hom.left ≫ pullback.fst G.X.hom (b K M) =
      p ≫ e.hom.hom.left ≫ pullback.fst G.X.hom (b K M) := by
    simp only [coefficientProjection, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      coefficientIso, descentBaseChangeIso_hom_fst]
    change _ ≫ pullback.fst H.X.hom a ≫ pullback.fst G.X.hom (b K M) = _
    rw [← Category.assoc, EmbeddingProduct.evaluationComponent_fst, Category.assoc]
  apply Over.OverMorphism.ext
  simp only [baseChangeBasePointsEquiv_left, Over.comp_left, ringTestMap_left]
  change (v.left ≫ (coefficientProjection K M G τ).hom.hom.left) ≫
      pullback.fst G.X.hom (b K M) =
    a ≫ (v.left ≫ e.hom.hom.left) ≫ pullback.fst G.X.hom (b K M)
  rw [Category.assoc, hc, ← Category.assoc v.left p, hvp]
  simp only [Category.assoc]

private def twistMap {S : Scheme.{u}} {W H : GroupScheme S}
    (p q : W ⟶ H) (z : Over.mk (𝟙 S) ⟶ H.X) : W.X ⟶ H.X :=
  p.hom.hom⁻¹ * H.constantPoint z W.X * q.hom.hom

private theorem comp_twistMap {S S' : Scheme.{u}} (b : S' ⟶ S) (G : GroupScheme S)
    {W : GroupScheme S'} (p q : W ⟶ (baseChange b).obj G)
    (v : Over.mk (𝟙 S') ⟶ W.X) (y : Over.mk b ⟶ G.X) :
    v ≫ twistMap p q ((baseChangeBasePointsEquiv b G).symm y) =
      (baseChangeBasePointsEquiv b G).symm
        ((baseChangeBasePointsEquiv b G (v ≫ p.hom.hom))⁻¹ * y *
          baseChangeBasePointsEquiv b G (v ≫ q.hom.hom)) := by
  apply (baseChangeBasePointsEquiv b G).injective
  simp only [twistMap, MonObj.comp_mul, GrpObj.comp_inv, map_mul, map_inv,
    MulEquiv.apply_symm_apply]
  rw [constantPoint_naturality]
  have hc : ((baseChange b).obj G).constantPoint ((baseChangeBasePointsEquiv b G).symm y)
      (Over.mk (𝟙 S')) = (baseChangeBasePointsEquiv b G).symm y :=
    Category.id_comp _
  rw [hc, MulEquiv.apply_symm_apply]

private theorem twistMap_surjective {S : Scheme.{u}} {W H : GroupScheme S}
    {I : Type u} [Finite I] (A : I → GroupScheme S)
    (e : W ≅ GroupScheme.pi A) (e₀ : ∀ i, A i ≅ H)
    (p : I → (W ⟶ H)) (hp : ∀ i, p i = e.hom ≫ Pi.π A i ≫ (e₀ i).hom)
    {a b : I} (hab : a ≠ b) (z : Over.mk (𝟙 S) ⟶ H.X) :
    Function.Surjective (twistMap (p a) (p b) z).left := by
  classical
  let v (i : I) : H.X ⟶ H.X :=
    if i = b then (H.constantPoint z H.X)⁻¹ * 𝟙 H.X else 1
  let r : H.X ⟶ W.X := (piPointsEquiv A H.X).symm
    (fun i => v i ≫ (e₀ i).inv.hom.hom) ≫ e.inv.hom.hom
  have hr (i : I) : r ≫ (p i).hom.hom = v i := by
    have hpi : e.inv ≫ p i = Pi.π A i ≫ (e₀ i).hom := by
      rw [hp, Iso.inv_hom_id_assoc]
    dsimp only [r]
    rw [Category.assoc, ← Grp.comp_hom_hom, hpi, Grp.comp_hom_hom,
      ← Category.assoc, piPointsEquiv_symm_π, Category.assoc,
      ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hsection : r ≫ twistMap (p a) (p b) z = 𝟙 H.X := by
    simp only [twistMap, MonObj.comp_mul, GrpObj.comp_inv, hr, constantPoint_naturality]
    simp [v, hab]
  intro x
  use r.left x
  have hx := congrArg (fun f : H.X ⟶ H.X => f.left x) hsection
  have hi : (𝟙 H.X.left) x = x := rfl
  simpa only [Over.comp_left, Scheme.Hom.comp_apply, Over.id_left, hi] using hx

omit [FiniteDimensional K M] [IsAffine (geometricGroup K M G).X.left]
  [LocallyOfFiniteType (geometricGroup K M G).X.hom] in
set_option backward.isDefEq.respectTransparency false in
private theorem dense_of_surjective_twistMap
    {W : GroupScheme (Spec (CommRingCat.of K))}
    (p : (M →ₐ[K] M) → ((baseChange (b K M)).obj W ⟶ geometricGroup K M G))
    (ev : (baseChange (b K M)).obj W ⟶ geometricGroup K M G)
    (hcoord : ∀ (q : rationalPoints W) (τ : M →ₐ[K] M),
      baseChangeBasePointsEquiv (b K M) G
          (geometricRationalPointHom (K := M) W q ≫ (p τ).hom.hom) =
        ringTestMap K τ ≫ baseChangeBasePointsEquiv (b K M) G
          (geometricRationalPointHom (K := M) W q ≫ ev.hom.hom))
    (β : M →ₐ[K] M) (y : ringTest K M ⟶ G.X)
    (hdenseW : HasDenseRationalPoints K W.X)
    (hsurj : Function.Surjective
      (twistMap (p (AlgHom.id K M)) (p β) ((baseChangeBasePointsEquiv (b K M) G).symm y)).left) :
    Dense (⋃ f : (ringTest K M ⟶ G.X),
      Set.range ((baseChangeBasePointsEquiv (b K M) G).symm
        (f⁻¹ * y * (ringTestMap K β ≫ f))).left) := by
  let α := AlgHom.id K M
  let z := (baseChangeBasePointsEquiv (b K M) G).symm y
  let m := twistMap (p α) (p β) z
  refine (hsurj.denseRange.dense_image m.left.continuous
    (dense_geometricRationalPointHom (K := M) W hdenseW)).mono ?_
  rintro x ⟨w, hw, rfl⟩
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hw
  let vq := geometricRationalPointHom (K := M) W q
  obtain ⟨a, rfl⟩ := hq
  let f : ringTest K M ⟶ G.X :=
    baseChangeBasePointsEquiv (b K M) G (vq ≫ ev.hom.hom)
  have hconstant :
      vq ≫ (geometricGroup K M G).constantPoint z ((baseChange (b K M)).obj W).X = z := by
    rw [constantPoint_naturality]
    exact Category.id_comp z
  have hcoordinate (τ : M →ₐ[K] M) :
      baseChangeBasePointsEquiv (b K M) G (vq ≫ (p τ).hom.hom) = ringTestMap K τ ≫ f :=
    hcoord q τ
  have hidentity : baseChangeBasePointsEquiv (b K M) G (vq ≫ (p α).hom.hom) = f := by
    rw [hcoordinate α, show ringTestMap K α = 𝟙 _ from ringTestMap_id K M, Category.id_comp]
  have hz : baseChangeBasePointsEquiv (b K M) G z = y := MulEquiv.apply_symm_apply _ _
  have hvalue : vq ≫ m = (baseChangeBasePointsEquiv (b K M) G).symm
      (f⁻¹ * y * (ringTestMap K β ≫ f)) := by
    apply (baseChangeBasePointsEquiv (b K M) G).injective
    simp only [m, twistMap, MonObj.comp_mul, GrpObj.comp_inv, map_mul, map_inv, hconstant,
      MulEquiv.apply_symm_apply, hidentity, hcoordinate β, hz]
  refine Set.mem_iUnion.mpr ⟨f, ⟨a, ?_⟩⟩
  rw [← hvalue, Over.comp_left, Scheme.Hom.comp_apply]

omit [FiniteDimensional K M] [IsAffine (geometricGroup K M G).X.left]
  [LocallyOfFiniteType (geometricGroup K M G).X.hom] in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_open_of_surjective_twistMap
    {W : GroupScheme (Spec (CommRingCat.of K))}
    (p : (M →ₐ[K] M) → ((baseChange (b K M)).obj W ⟶ geometricGroup K M G))
    (f : (ringTest K K ⟶ W.X) → (ringTest K M ⟶ G.X))
    (hcoord : ∀ (q : rationalPoints W) (τ : M →ₐ[K] M),
      baseChangeBasePointsEquiv (b K M) G
          (geometricRationalPointHom (K := M) W q ≫ (p τ).hom.hom) =
        ringTestMap K τ ≫ f (rationalPointEquiv K W.X q))
    (β : M →ₐ[K] M) (y : ringTest K M ⟶ G.X)
    (hsurj : Function.Surjective
      (twistMap (p (AlgHom.id K M)) (p β) ((baseChangeBasePointsEquiv (b K M) G).symm y)).left)
    (V : Set (geometricGroup K M G).X.left) (hV : IsOpen V) (hVne : V.Nonempty) :
    ∃ U : Set W.X.left, IsOpen U ∧ U.Nonempty ∧
      ∀ q : ringTest K K ⟶ W.X, q.left (IsLocalRing.closedPoint K) ∈ U →
        Set.range ((baseChangeBasePointsEquiv (b K M) G).symm
          ((f q)⁻¹ * y * (ringTestMap K β ≫ f q))).left ⊆ V := by
  let α := AlgHom.id K M
  let m := twistMap (p α) (p β) ((baseChangeBasePointsEquiv (b K M) G).symm y)
  let π := pullback.fst W.X.hom (b K M)
  let O := m.left ⁻¹' V
  refine ⟨π '' O, π.isOpenMap _ (hV.preimage m.left.continuous),
    (hVne.preimage hsurj).image π, fun q hq => ?_⟩
  let q₀ := (rationalPointEquiv K W.X).symm q
  let vq := geometricRationalPointHom (K := M) W q₀
  obtain ⟨a, ha, haq⟩ := hq
  have hav : a ∈ Set.range vq.left := by
    have hvq : vq = geometricRationalPoint (K := M) W.X q₀ := geometricRationalPointHom_apply W q₀
    erw [hvq, range_geometricRationalPoint]
    refine ⟨IsLocalRing.closedPoint K, ?_⟩
    rw [rationalPointEquiv_symm_left]
    exact haq.symm
  obtain ⟨x, hx⟩ := hav
  have hq₀ : rationalPointEquiv K W.X q₀ = q := (rationalPointEquiv K W.X).apply_symm_apply q
  have h₁ : baseChangeBasePointsEquiv (b K M) G (vq ≫ (p α).hom.hom) = f q := by
    rw [hcoord q₀ α, hq₀, show ringTestMap K α = 𝟙 _ from ringTestMap_id K M, Category.id_comp]
  have h₂ : baseChangeBasePointsEquiv (b K M) G (vq ≫ (p β).hom.hom) = ringTestMap K β ≫ f q := by
    rw [hcoord q₀ β, hq₀]
  have hvalue := comp_twistMap (b K M) G (p α) (p β) vq y
  rw [h₁, h₂] at hvalue
  rw [← hvalue]
  rintro _ ⟨t, rfl⟩
  have ht : t = x := @Subsingleton.elim (PrimeSpectrum M) inferInstance _ _
  rw [ht, Over.comp_left, Scheme.Hom.comp_apply, hx]
  exact ha

section Split

variable [IsGalois K M]

private abbrev factors := AffineWeil.embeddingFactor K M M (geometricGroup K M G)

private theorem embeddingEvaluation_bijective :
    Function.Bijective (embeddingEvaluation K M M) :=
  embeddingEvaluationStatement K M M (IsGalois.splits K)

private def restrictionProductIso :
    (baseChange (b K M)).obj (restriction K M G) ≅ GroupScheme.pi (factors K M G) :=
  AffineWeil.embeddingProductIsoOfBijective K M M (embeddingEvaluation_bijective K M)
    (geometricGroup K M G)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
private theorem coefficientProjection_eq_pi (τ : M →ₐ[K] M) :
    coefficientProjection K M G τ =
      (restrictionProductIso K M G).hom ≫ Pi.π (factors K M G) τ ≫
        (coefficientIso K M G τ).hom := by
  have hτ := AffineWeil.embeddingProductIsoOfBijective_hom_π K M M
    (embeddingEvaluation_bijective K M) (geometricGroup K M G) τ
  exact (congrArg (fun f => f ≫ (coefficientIso K M G τ).hom) hτ.symm).trans
    (Category.assoc _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_hasDenseRationalPoints [Infinite K]
    (hH : IsConnectedReductive (geometricGroup K M G)) :
    HasDenseRationalPoints K (restriction K M G).X := by
  have hW : IsConnectedReductive (restriction K M G) :=
    AffineWeil.isConnectedReductive_restriction K M (geometricGroup K M G) hH
  exact IsUnirational.hasDenseRationalPoints
    (ConnectedUnirationality.infinite_reductive_isUnirational torusUnirationality _ hW)

/-- Ground-field points of the Weil restriction are exactly the cochains
on the field cover. -/
def cochainEquiv :
    (ringTest K K ⟶ (restriction K M G).X) ≃ (ringTest K M ⟶ G.X) :=
  ((AffineWeil.basePointsEquiv K M (geometricGroup K M G)).trans
    (affinePointsBaseChangeMulEquiv K M M G).symm).toEquiv

/-- The cochain comparison preserves the evaluation topologies over a
finite extension of topological fields with the module topology. -/
theorem isHomeomorph_cochainEquiv [TopologicalSpace K] [IsTopologicalRing K]
    [TopologicalSpace M] [IsTopologicalRing M] [IsModuleTopology K M]
    [IsAffine G.X.left] : @IsHomeomorph (RingPoint K (restriction K M G).X K)
      (RingPoint K G.X M) inferInstance inferInstance (cochainEquiv K M G) := by
  let H := geometricGroup K M G
  let e := ringPointBaseChangeEquiv K M M G.X
  let e' := e.toHomeomorphOfIsInducing
    (isHomeomorph_ringPointBaseChangeEquiv K M M G.X).isInducing
  let h := (affineWeilRestrictionPointHomeomorph K M H.X).trans e'.symm
  have he (p : RingPoint K (restriction K M G).X K) :
      cochainEquiv K M G p = h p := by
    apply e.injective
    change e ((affinePointsBaseChangeMulEquiv K M M G).symm
      (AffineWeil.basePointsEquiv K M H p)) = e' (h p)
    change (ringPointBaseChangeEquiv K M M G.X) _ = _
    rw [← affinePointsBaseChangeMulEquiv_eq_ringPoint, MulEquiv.apply_symm_apply]
    have hp := e'.apply_symm_apply (affineWeilRestrictionPointHomeomorph K M H.X p)
    exact (AffineWeil.basePointsEquiv_eq K M H p).trans hp.symm
  rw [show (cochainEquiv K M G : _ → _) = h from funext he]
  exact h.isHomeomorph

section Evaluation

attribute [local instance] AffineWeil.coefficientBaseAlgebra AffineWeil.coefficientScalarTower

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional K M] [IsGalois K M] in
private theorem evalTensorMap_comp (A : CommAlgCat.{u} (CommRingCat.of M)) :
    CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := M) M (Algebra.ofId K A)) ≫
        AffineWeil.evaluationCoefficientMap K M A =
      CommAlgCat.ofHom (Algebra.TensorProduct.rid K M M).toAlgHom ≫
        CommAlgCat.ofHom (Y := A) (Algebra.ofId M A) := by
  apply CommAlgCat.hom_ext
  apply Algebra.TensorProduct.ext'
  intro m k
  change (AffineWeil.evaluationCoefficientMap K M A).hom (m ⊗ₜ[K] algebraMap K A k) =
    algebraMap M A (k • m)
  rw [AffineWeil.evaluationCoefficientMap_tmul, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply]
  exact mul_comm _ _

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
private theorem evaluation_of_extended_point (A : CommAlgCat.{u} (CommRingCat.of M))
    (p : (restriction K M G).affinePoints (CommAlgCat.of K K))
    (q : ((baseChange (b K M)).obj (restriction K M G)).affinePoints A)
    (hq : (affinePointsBaseChangeMulEquiv K M A (restriction K M G)).symm q =
      (restriction K M G).affinePointMap (CommAlgCat.ofHom (Algebra.ofId K A)) p) :
    q ≫ (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom =
      (geometricGroup K M G).affinePointMap (CommAlgCat.ofHom (Y := A) (Algebra.ofId M A))
        (AffineWeil.basePointsEquiv K M (geometricGroup K M G) p) := by
  let H := geometricGroup K M G
  let W := restriction K M G
  let α := Algebra.ofId K A
  let x := AffineWeil.pointsEquiv K M H K p
  have hpt : AffineWeil.baseChangeTensorPointsEquiv K M M H A q =
      H.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := M) M α)) x := by
    change AffineWeil.pointsEquiv K M H A ((affinePointsBaseChangeMulEquiv K M A W).symm q) = _
    exact (congrArg (AffineWeil.pointsEquiv K M H A) hq).trans
      (AffineWeil.pointsEquiv_naturality K M H α p)
  let l := CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := M) M α)
  let e := AffineWeil.evaluationCoefficientMap K M A
  let r := CommAlgCat.ofHom (Algebra.TensorProduct.rid K M M).toAlgHom
  let a := CommAlgCat.ofHom (Y := A) (Algebra.ofId M A)
  have he : H.affinePointMap e (H.affinePointMap l x) = H.affinePointMap a (H.affinePointMap r x) :=
    calc
      _ = H.affinePointMap (l ≫ e) x := DFunLike.congr_fun (H.affinePointMap_comp l e).symm x
      _ = H.affinePointMap (r ≫ a) x := congrArg (fun f => H.affinePointMap f x) (evalTensorMap_comp K M A)
      _ = _ := DFunLike.congr_fun (H.affinePointMap_comp r a) x
  exact (AffineWeil.evaluation_affinePoints K M H A q).trans
    ((congrArg (H.affinePointMap e) hpt).trans he)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
private theorem evaluation_on_rational (q : rationalPoints (restriction K M G)) :
    rationalPointEquiv M (geometricGroup K M G).X
        (geometricRationalPointHom (K := M) (restriction K M G) q ≫
          (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom) =
      AffineWeil.basePointsEquiv K M (geometricGroup K M G)
        (rationalPointEquiv K (restriction K M G).X q) := by
  let W := restriction K M G
  let H := geometricGroup K M G
  let q' := geometricRationalPointHom (K := M) W q
  let p := rationalPointEquiv K W.X q
  let A := CommAlgCat.of (CommRingCat.of M) M
  let α : K →ₐ[K] A := Algebra.ofId K A
  have hq : (affinePointsBaseChangeMulEquiv K M A W).symm
      (rationalPointEquiv M _ q') = W.affinePointMap (CommAlgCat.ofHom α) p := by
    apply Over.OverMorphism.ext
    rw [affinePointsBaseChangeMulEquiv_symm_left, rationalPointEquiv_left]
    change (baseChangeSectionHom (b K M) W q).left ≫ pullback.fst W.X.hom (b K M) =
      Spec.map (CommRingCat.ofHom α.toRingHom) ≫ p.left
    rw [baseChangeSectionHom_fst, rationalPointEquiv_left]
    rfl
  rw [rationalPointEquiv_natural]
  have he := evaluation_of_extended_point K M G A p (rationalPointEquiv M _ q') hq
  have hid : CommAlgCat.ofHom (Y := A) (Algebra.ofId M A) = 𝟙 A :=
    CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)
  rw [hid, affinePointMap_id, MonoidHom.id_apply] at he
  exact he

end Evaluation

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
private theorem cochainEquiv_eq_evaluation (q : rationalPoints (restriction K M G)) :
    cochainEquiv K M G (rationalPointEquiv K (restriction K M G).X q) =
      baseChangeBasePointsEquiv (b K M) G
        (geometricRationalPointHom (K := M) (restriction K M G) q ≫
          (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom) := by
  let p : rationalPoints (geometricGroup K M G) :=
    geometricRationalPointHom (K := M) (restriction K M G) q ≫
      (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom
  have h : (affinePointsBaseChangeMulEquiv K M M G).symm
      (rationalPointEquiv M (geometricGroup K M G).X p) =
        baseChangeBasePointsEquiv (b K M) G p := by
    apply Over.OverMorphism.ext
    rw [affinePointsBaseChangeMulEquiv_symm_left, rationalPointEquiv_left,
      baseChangeBasePointsEquiv_left]
  exact (congrArg (affinePointsBaseChangeMulEquiv K M M G).symm
    (evaluation_on_rational K M G q).symm).trans h

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientProjection_on_cochain (q : rationalPoints (restriction K M G))
    (τ : M →ₐ[K] M) :
    baseChangeBasePointsEquiv (b K M) G
        (geometricRationalPointHom (K := M) (restriction K M G) q ≫
          (coefficientProjection K M G τ).hom.hom) =
      ringTestMap K τ ≫ cochainEquiv K M G (rationalPointEquiv K (restriction K M G).X q) :=
  (coefficientProjection_on_extended K M G q τ).trans
    (congrArg (fun f : ringTest K M ⟶ G.X => ringTestMap K τ ≫ f)
      (cochainEquiv_eq_evaluation K M G q).symm)

set_option backward.isDefEq.respectTransparency false in
/-- A nonempty Zariski open in the coefficient group gives a nonempty
Zariski open of cochains whose twisted values lie in that open. -/
theorem exists_open_twist_preimage (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1)
    (y : ringTest K M ⟶ G.X) (V : Set (geometricGroup K M G).X.left)
    (hV : IsOpen V) (hVne : V.Nonempty) :
    ∃ U : Set (restriction K M G).X.left, IsOpen U ∧ U.Nonempty ∧
      ∀ q : RingPoint K (restriction K M G).X K,
        q.left (IsLocalRing.closedPoint K) ∈ U →
        let f := cochainEquiv K M G q
        Set.range ((baseChangeBasePointsEquiv (b K M) G).symm
          (f⁻¹ * y * (ringTestMap K σ.toAlgHom ≫ f))).left ⊆ V := by
  let α := AlgHom.id K M
  let β := σ.toAlgHom
  have hneq : α ≠ β := fun h => hσ (AlgEquiv.ext fun x => DFunLike.congr_fun h.symm x)
  have hsurj := twistMap_surjective (factors K M G) (restrictionProductIso K M G)
    (coefficientIso K M G) (coefficientProjection K M G)
    (coefficientProjection_eq_pi K M G) hneq ((baseChangeBasePointsEquiv (b K M) G).symm y)
  exact exists_open_of_surjective_twistMap K M G (coefficientProjection K M G) (cochainEquiv K M G)
    (coefficientProjection_on_cochain K M G) β y hsurj V hV hVne

end Split

end GaloisTwistedPointDensity

open GaloisTwistedPointDensity in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 500000 in
/-- The scalar-extended Weil restriction has two independent coordinates for a
nonidentity automorphism, so twisted values of its ground-field points are dense. -/
theorem galoisTwistedPointDensity_of_isGalois
    (K M : Type u) [Field K] [Infinite K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (G : GroupScheme (Spec (CommRingCat.of K))) (hG : IsConnectedReductive G)
    (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1) (y : ringTest K M ⟶ G.X) :
    Dense (⋃ f : (ringTest K M ⟶ G.X),
      Set.range ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm
        (f⁻¹ * y * (ringTestMap K σ.toAlgHom ≫ f))).left) := by
  let H := geometricGroup K M G
  have hH : IsConnectedReductive H := connectedReductiveFieldExtensionStatement K M G hG
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : LocallyOfFiniteType H.X.hom := by
    let : Smooth H.X.hom := hH.smooth
    infer_instance
  have hneq : AlgHom.id K M ≠ σ.toAlgHom := by
    intro h
    exact hσ (AlgEquiv.ext fun x => DFunLike.congr_fun h.symm x)
  exact dense_of_surjective_twistMap K M G (coefficientProjection K M G)
    (AffineWeil.evaluation K M H) (coefficientProjection_on_extended K M G)
    σ.toAlgHom y (restriction_hasDenseRationalPoints K M G hH)
    (twistMap_surjective (factors K M G) (restrictionProductIso K M G)
      (coefficientIso K M G) (coefficientProjection K M G)
      (coefficientProjection_eq_pi K M G) hneq _)

/-- The original density proposition over algebraically closed coefficients. -/
theorem galoisTwistedPointDensity : GaloisTwistedPointDensityStatement.{u} := by
  intro K M _ _ _ _ _ _ _ G hG σ hσ y
  exact galoisTwistedPointDensity_of_isGalois K M G hG σ hσ y

set_option backward.isDefEq.respectTransparency false in
/-- The dense twisted values meet the open whose points have maximal torus centralizers. -/
theorem galoisCocycleStronglyRegularValue : GaloisCocycleStronglyRegularValueStatement.{u} := by
  intro K M _ _ _ _ _ _ _ G hG ξ σ hσ
  let b := algebraBaseMap K M
  let H := (baseChange b).obj G
  have hH : IsConnectedReductive H := connectedReductiveFieldExtensionStatement K M G hG
  let y : ringTest K M ⟶ G.X := GaloisCocycle.value ξ σ
  obtain ⟨V, hV, hVne, hVreg⟩ := stronglyRegularGroupOpen M H hH
  have hdense := galoisTwistedPointDensity K M G hG σ hσ y
  obtain ⟨x, hx, hxd⟩ := hdense.inter_open_nonempty V hV hVne
  obtain ⟨f, a, ha⟩ := Set.mem_iUnion.mp hxd
  let z : rationalPoints H := (baseChangeBasePointsEquiv b G).symm
    (f⁻¹ * y * (ringTestMap K σ.toAlgHom ≫ f))
  have hza : z.left a = x := ha
  have hz : Set.range z.left ⊆ V := by
    rintro _ ⟨a', rfl⟩
    have : Subsingleton ↥(Over.mk (𝟙 (Spec (CommRingCat.of M)))).left :=
      inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of M)))
    rw [show a' = a from Subsingleton.elim _ _, hza]
    exact hx
  obtain ⟨T, j, hj, hc⟩ := hVreg z hz
  refine ⟨f, T, j, hj, ?_⟩
  have htwist : GaloisCocycle.value (ξ.twist f) σ =
      f⁻¹ * y * (ringTestMap K σ.toAlgHom ≫ f) := by
    change (𝟙 _ ≫ f)⁻¹ * y * (ringTestMap K σ.toAlgHom ≫ f) = _
    rw [Category.id_comp]
  rw [htwist]
  exact hc

/-- Every cohomology class on the algebraically closed quadratic cover
has a representative in a maximal torus defined over the base. -/
theorem quadraticToralRepresentatives : QuadraticToralRepresentativesStatement.{u} :=
  quadraticToralRepresentatives_of_stronglyRegularValue galoisCocycleStronglyRegularValue

end Langlands.GroupScheme
