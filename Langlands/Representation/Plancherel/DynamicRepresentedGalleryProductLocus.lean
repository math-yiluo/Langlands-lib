import Langlands.Representation.Plancherel.DynamicRepresentedGalleryProduct
import Langlands.Representation.Plancherel.RationalRankOneProductDifferences

/-! # A common dense locus for the represented rank-one gallery product -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction Aubert.General.RepresentedParabolic
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition

open ValuationKernelCoordinates (RankOneTranslationChart)

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (first last : GalleryVertex χ)

set_option hygiene false in
local notation "d" => galleryVertexData (χ := χ) hG ha

set_option hygiene false in
local notation "Mχ" => parameterScheme χ
set_option hygiene false in
local notation "hMχ" => parameterScheme_isConnectedReductive χ hG
set_option hygiene false in
local notation "X" => unramifiedCharacters (normCharacters χ)
set_option hygiene false in
local notation "Poly" => MvPolynomial (Fin (rationalImageRank Mχ)) ℂ
set_option hygiene false in
local notation "principal" => rationalUnramifiedPrincipalOpen Mχ hMχ
set_option hygiene false in
local notation "PQ(" x "," y "," B ")" =>
  representedIsPQRegular hG (d x) (d y) B
set_option hygiene false in
local notation "ScalarComposite" => IsGalleryCompositeScalar (χ := χ) hG ha K hK

variable (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))

private def twistAt (z : X) : SmoothRep.{0, u, uV} ℂ (rationalPoints Mχ) :=
  σ.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker (normCharacters χ) z)

set_option hygiene false in
local notation "σz" => twistAt (χ := χ) σ

/-- A scalar factor for an edge on one nonzero principal open region.
Its value represents the product of the two fixed gallery operators at
parameters where both pairs are `PQ`-regular. -/
def HasGenericRankOneGalleryFactor (x y : GalleryVertex χ) : Prop :=
  ∃ (p : Poly) (chart : RankOneTranslationChart Mχ) (g : X → ℂ),
    p ≠ 0 ∧ chart.InvariantOn Mχ (principal p) g ∧
    ∀ (z : X), z ∈ principal p → PQ(x, y, σz z) → PQ(y, x, σz z) →
      ScalarComposite (σz z) x y (g z)

/-- The common open locus has both endpoint regularities and the pointwise
scalar formula with the fixed total Haar constant. -/
def HasDenseRepresentedGalleryProduct : Prop :=
  ∃ (charts : List (RankOneTranslationChart Mχ)) (κ : ℂˣ) (D : Set X) (factors : List (X → ℂ)),
    Dense D ∧ IsOpen D ∧ List.Forall₂ (fun chart g => chart.InvariantOn Mχ D g) charts factors ∧
    ∀ (z : X), z ∈ D → PQ(first, last, σz z) ∧ PQ(last, first, σz z) ∧
      ScalarComposite (σz z) first last
        ((κ : ℂ) * (factors.map (fun g => g z)).prod)

set_option maxHeartbeats 700000 in
/-- Intersect the finitely many edge loci with simultaneous `PQ` regularity
of all gallery pairs. Preserve the order and multiplicities of the edge list. -/
theorem hasDenseRepresentedGalleryProduct
    (data : RepresentedGalleryProductData.{u, uV} hG ha K hK first last)
    (hσ : σ.IsIrreducible) (hA : σ.IsAdmissible)
    (hEdge : ∀ e ∈ data.edges, HasGenericRankOneGalleryFactor hG ha K hK σ e.1 e.2) :
    HasDenseRepresentedGalleryProduct hG ha K hK first last σ := by
  classical
  obtain ⟨p, hp0, hregular⟩ := exists_generic_galleryRegular (χ := χ) hG ha data.vertices σ hσ hA
  let edges := data.edges.attach
  choose edgePoly chart factor hne hInv hScalar using
    fun e : {e // e ∈ data.edges} => hEdge e.val e.property
  let q := p * ∏ e ∈ edges.toFinset, edgePoly e
  have hq0 : q ≠ 0 := mul_ne_zero hp0 (Finset.prod_ne_zero_iff.mpr (fun e _ => hne e))
  have hmem (z : X) (hz : z ∈ principal q) :
      z ∈ principal p ∧ ∀ e : {e // e ∈ data.edges}, z ∈ principal (edgePoly e) := by
    have he := (mem_rationalUnramifiedPrincipalOpen Mχ hMχ q z).mp hz
    dsimp only [q] at he
    rw [map_mul, map_prod] at he
    refine ⟨(mem_rationalUnramifiedPrincipalOpen Mχ hMχ p z).mpr (left_ne_zero_of_mul he), ?_⟩
    intro e
    exact (mem_rationalUnramifiedPrincipalOpen Mχ hMχ (edgePoly e) z).mpr
      (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul he) e (List.mem_toFinset.mpr (List.mem_attach _ _)))
  have hκ0 : (data.scale : ℂ) ≠ 0 := by exact_mod_cast data.scale_pos.ne'
  refine ⟨edges.map chart, Units.mk0 _ hκ0, principal q, edges.map factor,
    dense_rationalUnramifiedPrincipalOpen Mχ hMχ q hq0,
    isOpen_rationalUnramifiedPrincipalOpen Mχ hMχ q, ?_, ?_⟩
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro e _ c z hz htz
    exact hInv e c z ((hmem z hz).2 e) ((hmem _ htz).2 e)
  · intro z hz
    have hPQ := hregular z (hmem z hz).1
    refine ⟨hPQ first data.first_mem last data.last_mem, hPQ last data.last_mem first data.first_mem, ?_⟩
    let g (e : GalleryVertex χ × GalleryVertex χ) : ℂ :=
      if he : e ∈ data.edges then factor ⟨e, he⟩ z else 1
    have hscalar := data.product (σz z) hPQ g (fun e he => by
      have h := hScalar ⟨e, he⟩ z ((hmem z hz).2 ⟨e, he⟩)
        (hPQ e.1 (data.edge_mem e he).1 e.2 (data.edge_mem e he).2)
        (hPQ e.2 (data.edge_mem e he).2 e.1 (data.edge_mem e he).1)
      simpa only [g, dite_eq_left he] using h)
    have hmap : (edges.map factor).map (fun f => f z) = data.edges.map g := by
      rw [List.map_map]
      calc
        edges.map (fun e => factor e z) = edges.map (g ∘ Subtype.val) := by
          apply List.map_congr_left
          intro e _
          simp only [Function.comp_apply, g, dite_eq_left e.property]
        _ = data.edges.map g := by rw [← List.map_map]; simp [edges]
    rw [hmap]
    exact hscalar

end Langlands.Plancherel.DynamicCommonLeviPresentations
