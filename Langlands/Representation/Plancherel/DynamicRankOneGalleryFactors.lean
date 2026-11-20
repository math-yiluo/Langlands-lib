import Langlands.Representation.Plancherel.DynamicRankOneWallTwist
import Langlands.Representation.Plancherel.DynamicOppositeAmbientTwist
import Langlands.Representation.Plancherel.RationalValuationKernelCoordinates
import Langlands.Representation.Plancherel.RationalAmbientBlockScaling
import Langlands.Representation.Schur.RationalPoints

/-! # Factors on principal open loci for rank-one gallery edges -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General.RepresentedParabolic DynamicCommonLeviComposition
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open ValuationKernelCoordinates

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

set_option hygiene false in
local notation "d" => galleryVertexData (χ := χ) hG ha
set_option hygiene false in
local notation "X" => unramifiedCharacters (normCharacters χ)
set_option hygiene false in
local notation "H" => parameterScheme χ
set_option hygiene false in
local notation "hH" => parameterScheme_isConnectedReductive χ hG
set_option hygiene false in
local notation "principal" => rationalUnramifiedPrincipalOpen H hH
set_option hygiene false in
local notation "Poly" => MvPolynomial (Fin (rationalImageRank H)) ℂ
set_option hygiene false in
local notation "Lattice" => Additive (rationalDiscreteValuationImage H)

variable (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))

private def twistedCoefficient (z : X) : SmoothRep.{0, u, uV} ℂ (rationalPoints H) :=
  σ.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker (normCharacters χ) z)

set_option hygiene false in
local notation "twisted" => twistedCoefficient (χ := χ) σ
set_option hygiene false in
local notation "PQ(" x "," y "," z ")" => representedIsPQRegular hG (d x) (d y) (twisted z)
set_option hygiene false in
local notation "Scalar" => IsGalleryCompositeScalar hG ha K hK

/-- A gallery edge factor and its translation coordinates on a nonzero principal open. -/
def HasGenericRankOneGalleryFactorCoordinates (x y : GalleryVertex χ) : Prop :=
  ∃ (p : Poly) (r n : ℕ) (e : Lattice ≃ₗ[ℤ] (Fin r → ℤ) × (Fin n → ℤ)) (g : X → ℂ),
    p ≠ 0 ∧ r ≤ 1 ∧
    (∀ (c : Fin n → ℂˣ) (z : X), z ∈ principal p → complementParameter e c * z ∈ principal p →
      g (complementParameter e c * z) = g z) ∧
    ∀ z ∈ principal p, PQ(x, y, z) → PQ(y, x, z) → Scalar (twisted z) x y (g z)

private theorem twistedCoefficient_mul (t z : X) :
    (twisted z).twist t.val.toMonoidHom (unramifiedCharacter_isOpen_ker (normCharacters χ) t) =
      twisted (t * z) := by
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  exact congrArg Rep.of (Langlands.twist_twist t.val.toMonoidHom z.val.toMonoidHom σ.representation)

set_option maxHeartbeats 1500000 in
private theorem galleryScalar_complementTranslation
    {x y : GalleryVertex χ} (W : DynamicRankOneWall χ x.val y.val)
    {r n : ℕ} (e : Lattice ≃ₗ[ℤ] (Fin r → ℤ) × (Fin n → ℤ))
    (he : ∀ v : Lattice, (e v).2 = 0 ↔ rationalValuationImageMap (W.wall.l ≫ W.wall.q) v.toMul = 1)
    (c : Fin n → ℂˣ) (z : X) (s : ℂ)
    (hzF : PQ(x, y, z)) (hzR : PQ(y, x, z))
    (htF : PQ(x, y, complementParameter e c * z)) (htR : PQ(y, x, complementParameter e c * z))
    (hs : Scalar (twisted z) x y s) : Scalar (twisted (complementParameter e c * z)) x y s := by
  have : IsAffineHom W.wall.M.X.hom := W.wall.levi.isConnectedReductive.isAffineHom
  have : IsAffine W.wall.M.X.left := isAffine_of_isAffineHom W.wall.M.X.hom
  have : Smooth W.wall.M.X.hom := W.wall.levi.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints W.wall.M) := leviPointTopology W.wall.m W.wall.levi
  let t := complementParameter e c
  obtain ⟨eta, heta⟩ := complementParameter_ambient e (W.wall.l ≫ W.wall.q) he c
  let etaSmooth : Induction.SmoothCharacter ℂ (rationalPoints W.wall.M) :=
    ⟨eta.val.toMonoidHom, unramifiedCharacter_isOpen_ker _ eta⟩
  let tSmooth : Induction.SmoothCharacter ℂ (rationalPoints H) :=
    ⟨t.val.toMonoidHom, unramifiedCharacter_isOpen_ker (normCharacters χ) t⟩
  have hrestrict (m : rationalPoints H) : tSmooth.toMonoidHom m =
      etaSmooth.toMonoidHom (rationalPoints.map (W.wall.l ≫ W.wall.q) m) :=
    (congrArg (fun z : X => z.val m) heta).symm
  have h₁ := unramifiedCharacter_isLimitOfCompactSubgroups_le_ker _
    (fun i => (rationalNormContinuousCharacter W.wall.M i).continuous) eta
    (pointImage (W.innerRadical.inclusion ≫ W.wall.q))
    (isLimitOfCompactSubgroups_pointImage_radical W.wall.q W.innerRadical.inclusion
      W.wall.innerParabolic.isClosedSubgroup W.innerRadical.isRadical.1)
  have h₂ := unramifiedCharacter_isLimitOfCompactSubgroups_le_ker _
    (fun i => (rationalNormContinuousCharacter W.wall.M i).continuous) eta
    (pointImage (W.innerRadical'.inclusion ≫ W.wall.q'))
    (isLimitOfCompactSubgroups_pointImage_radical W.wall.q' W.innerRadical'.inclusion
      W.wall.innerParabolic'.isClosedSubgroup W.innerRadical'.isRadical.1)
  have hmul : (twisted z).twist tSmooth.toMonoidHom tSmooth.isOpen_ker = twisted (t * z) :=
    twistedCoefficient_mul σ t z
  have h := W.galleryScalar_of_ambientTwist hG ha K hK (twisted z) etaSmooth tSmooth
    hrestrict h₁ h₂ hzF hzR (hmul.symm ▸ htF) (hmul.symm ▸ htR) s hs
  exact hmul ▸ h

private theorem exists_translationInvariantChoice {Z C : Type*}
    (D : Set Z) (translate : C → Z → Z) (valid : Z → ℂ → Prop)
    (hUnique : ∀ z ∈ D, ∃! s, valid z s)
    (hTransfer : ∀ c z, z ∈ D → translate c z ∈ D → ∀ s, valid z s → valid (translate c z) s) :
    ∃ g : Z → ℂ, (∀ c z, z ∈ D → translate c z ∈ D → g (translate c z) = g z) ∧
      ∀ z ∈ D, valid z (g z) := by
  classical
  let g (z : Z) : ℂ := if hz : z ∈ D then (hUnique z hz).exists.choose else 0
  have hg (z : Z) (hz : z ∈ D) : valid z (g z) := by
    dsimp only [g]
    rw [dite_eq_left hz]
    exact (hUnique z hz).exists.choose_spec
  refine ⟨g, ?_, hg⟩
  intro c z hz ht
  exact (hUnique _ ht).unique (hg _ ht) (hTransfer c z hz ht _ (hg z hz))

set_option maxHeartbeats 1400000 in
private theorem existsUnique_galleryCompositeScalar
    (τ : SmoothRep.{0, u, uV} ℂ (rationalPoints H)) (x y : GalleryVertex χ)
    (hirr : (representedInduction hG (d x) τ).IsIrreducible) :
    ∃! s, Scalar τ x y s := by
  unfold IsGalleryCompositeScalar
  apply Langlands.Schur.separableSmooth_scalarEndomorphism
  · exact (representedInduction hG (d x) τ).isSmooth
  · exact hirr

set_option maxHeartbeats 4000000 in
/-- At a rank-one wall, irreducibility and the two ordered regularities on a
principal open give a scalar factor invariant under complement translations. -/
theorem hasGenericRankOneGalleryFactorCoordinates_of_wall
    {x y : GalleryVertex χ} (W : DynamicRankOneWall χ x.val y.val)
    (p : Poly) (hp : p ≠ 0)
    (hIrrOn : ∀ z ∈ principal p, (representedInduction hG (d x) (twisted z)).IsIrreducible)
    (hRegF : ∀ z ∈ principal p, PQ(x, y, z)) (hRegR : ∀ z ∈ principal p, PQ(y, x, z)) :
    HasGenericRankOneGalleryFactorCoordinates hG ha K hK σ x y := by
  obtain ⟨r, n, hr, e, he⟩ := exists_maximalLevi_product_coordinates
    W.wall.levi.isConnectedReductive W.wall.innerParabolic W.wall.innerLevi W.wall.proper W.wall.maximal ha
  have hS (z : X) (hz : z ∈ principal p) : ∃! s, Scalar (twisted z) x y s :=
    existsUnique_galleryCompositeScalar hG ha K hK (twisted z) x y (hIrrOn z hz)
  let translate (c : Fin n → ℂˣ) (z : X) := complementParameter e c * z
  have hTransfer (c : Fin n → ℂˣ) (z : X) (hz : z ∈ principal p) (ht : translate c z ∈ principal p)
      (s : ℂ) (hs : Scalar (twisted z) x y s) : Scalar (twisted (translate c z)) x y s := by
    exact galleryScalar_complementTranslation hG ha K hK σ W e he c z s
      (hRegF z hz) (hRegR z hz) (hRegF _ ht) (hRegR _ ht) hs
  obtain ⟨factor, hInv, hFactor⟩ := exists_translationInvariantChoice (principal p) translate
    (fun z s => Scalar (twisted z) x y s) hS hTransfer
  exact ⟨p, r, n, e, factor, hp, hr, hInv, fun z hz _ _ => hFactor z hz⟩



end Langlands.Plancherel.DynamicCommonLeviPresentations
