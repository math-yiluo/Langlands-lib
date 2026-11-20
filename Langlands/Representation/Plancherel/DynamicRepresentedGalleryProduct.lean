import Langlands.Representation.Plancherel.DynamicRepresentedGalleryOperators

/-! # Scalar product along the represented dynamic gallery -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction Aubert.General.RepresentedParabolic
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition

private theorem oppositeComposite_of_scalars {H V₀ V₁ V₂ : Type*} [Group H]
    [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    {ρ₀ : Representation ℂ H V₀} {ρ₁ : Representation ℂ H V₁} {ρ₂ : Representation ℂ H V₂}
    {J₀₁ : ρ₀.IntertwiningMap ρ₁} {J₁₀ : ρ₁.IntertwiningMap ρ₀}
    {J₁₂ : ρ₁.IntertwiningMap ρ₂} {J₂₁ : ρ₂.IntertwiningMap ρ₁}
    {J₀₂ : ρ₀.IntertwiningMap ρ₂} {J₂₀ : ρ₂.IntertwiningMap ρ₀}
    {a b s t : ℂ} (h : a * b ≠ 0)
    (hF : J₁₂.comp J₀₁ = a • J₀₂) (hR : J₁₀.comp J₂₁ = b • J₂₀)
    (hPrevious : J₁₀.comp J₀₁ = t • Representation.IntertwiningMap.id ρ₀)
    (hEdge : J₂₁.comp J₁₂ = s • Representation.IntertwiningMap.id ρ₁) :
    J₂₀.comp J₀₂ = ((a * b)⁻¹ * t * s) • Representation.IntertwiningMap.id ρ₀ := by
  have he : (a * b) • (J₂₀.comp J₀₂) = (t * s) • Representation.IntertwiningMap.id ρ₀ := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hFv : J₁₂ (J₀₁ v) = a • J₀₂ v := DFunLike.congr_fun hF v
    have hRv : J₁₀ (J₂₁ (J₀₂ v)) = b • J₂₀ (J₀₂ v) := DFunLike.congr_fun hR (J₀₂ v)
    have hPv : J₁₀ (J₀₁ v) = t • v := DFunLike.congr_fun hPrevious v
    have hEv : J₂₁ (J₁₂ (J₀₁ v)) = s • J₀₁ v := DFunLike.congr_fun hEdge (J₀₁ v)
    change (a * b) • J₂₀ (J₀₂ v) = (t * s) • v
    calc
      _ = J₁₀ (J₂₁ (J₁₂ (J₀₁ v))) := by rw [hFv, map_smul, map_smul, hRv, smul_smul]
      _ = _ := by rw [hEv, map_smul, hPv, smul_smul, mul_comm s t]
  simpa only [smul_smul, inv_mul_cancel₀ h, one_smul, mul_assoc] using
    congrArg ((a * b)⁻¹ • ·) he

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (first last : GalleryVertex χ)

local notation "d" => galleryVertexData hG ha
local notation "J" => galleryIntegralOperator hG ha K hK
local notation "I" => fun x σ => representedInduction hG (d x) σ
local notation "PQ" => fun x y σ => representedIsPQRegular hG (d x) (d y) σ

/-- The two normalized maps on an ordered pair have the specified scalar composite. -/
def IsGalleryCompositeScalar
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
    (x y : GalleryVertex χ) (scalar : ℂ) : Prop :=
  (J σ y x).comp (J σ x y) = scalar • Representation.IntertwiningMap.id (I x σ).representation

local notation "ScalarComposite" => IsGalleryCompositeScalar hG ha K hK

set_option maxHeartbeats 600000 in
private theorem galleryOppositeComposite_of_scalars
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
    (x y w : GalleryVertex χ) {aF aR s t : ℂ} (h : aF * aR ≠ 0)
    (hF : (J σ y w).comp (J σ x y) = aF • J σ x w)
    (hR : (J σ y x).comp (J σ w y) = aR • J σ w x)
    (hPrev : ScalarComposite σ x y t) (hEdge : ScalarComposite σ y w s) :
    ScalarComposite σ x w ((aF * aR)⁻¹ * t * s) :=
  let I₀ := I x σ
  let I₁ := I y σ
  let I₂ := I w σ
  @oppositeComposite_of_scalars (rationalPoints G) I₀ I₁ I₂ _
    I₀.obj.hV1 I₀.obj.hV2 I₁.obj.hV1 I₁.obj.hV2 I₂.obj.hV1 I₂.obj.hV2
    I₀.representation I₁.representation I₂.representation
    (J σ x y) (J σ y x) (J σ y w) (J σ w y) (J σ x w) (J σ w x)
    aF aR s t h hF hR hPrev hEdge

private theorem gallerySelfComposite_one
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
    (x : GalleryVertex χ) (hPQ : PQ x x σ) : ScalarComposite σ x x 1 := by
  let I₀ := I x σ
  let idMap := Representation.IntertwiningMap.id I₀.representation
  have hi : J σ x x = idMap := galleryIntegralOperator_self hG ha K hK σ x hPQ
  change (J σ x x).comp (J σ x x) = (1 : ℂ) • idMap
  have hid : idMap.comp idMap = (1 : ℂ) • idMap := by
    rw [one_smul]
    apply Representation.IntertwiningMap.ext
    exact LinearMap.ext fun _ => rfl
  exact (congrArg₂ (fun (j k : I₀.representation.IntertwiningMap I₀.representation) => j.comp k) hi hi).trans hid

/-- The actual finite vertex set and ordered edge list, together with the
positive Haar factor in the product of scalar edge composites. -/
structure RepresentedGalleryProductData where
  vertices : Finset (GalleryVertex χ)
  edges : List (GalleryVertex χ × GalleryVertex χ)
  first_mem : first ∈ vertices
  last_mem : last ∈ vertices
  edge_mem : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices
  edge_chamber_or_wall : ∀ e ∈ edges,
    SameDynamicChamber e.1.val e.2.val ∨ Nonempty (DynamicRankOneWall χ e.1.val e.2.val)
  scale : ℝ≥0
  scale_pos : 0 < scale
  product : ∀ (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ))),
    (∀ x ∈ vertices, ∀ y ∈ vertices, PQ x y σ) →
    ∀ g : GalleryVertex χ × GalleryVertex χ → ℂ,
      (∀ e ∈ edges, ScalarComposite σ e.1 e.2 (g e)) →
      ScalarComposite σ first last ((scale : ℂ) * (edges.map g).prod)

set_option maxHeartbeats 700000 in
private theorem nonempty_representedGalleryProductData_of_chain
    (anchor : GalleryVertex χ)
    (h : Relation.ReflTransGen (fun (x y : GalleryVertex χ) =>
      DynamicGalleryStep χ first.val anchor.val x.val y.val) first last) :
    Nonempty (RepresentedGalleryProductData.{u, uV} hG ha K hK first last) := by
  classical
  induction h with
  | refl =>
    refine ⟨⟨{first}, [], by simp, by simp, by simp, by simp, 1, one_pos, ?_⟩⟩
    intro σ hPQ g hEdge
    have hbase := gallerySelfComposite_one hG ha K hK σ first
      (hPQ first (Finset.mem_singleton_self _) first (Finset.mem_singleton_self _))
    have hOne : (1 : ℂ) = ((1 : ℝ≥0) : ℂ) * (([] : List (GalleryVertex χ × GalleryVertex χ)).map g).prod := by
      simp only [List.map_nil, List.prod_nil, NNReal.coe_one, Complex.ofReal_one, mul_one]
    exact hOne ▸ hbase
  | @tail x y hxy hstep ih =>
    obtain ⟨prev⟩ := ih
    have hdForward := hstep.distanceFromFirst
    have hdReverse : IsDistanceAdditive y.val x.val first.val :=
      ⟨by simpa only [inf_comm] using hdForward.1, by simpa only [inf_comm] using hdForward.2⟩
    obtain ⟨aF, haF, hF⟩ := exists_galleryIntegralOperator_comp_smul hG ha K hK first x y hdForward
    obtain ⟨aR, haR, hR⟩ := exists_galleryIntegralOperator_comp_smul hG ha K hK y x first hdReverse
    refine ⟨{
      vertices := insert y prev.vertices
      edges := prev.edges ++ [(x, y)]
      first_mem := Finset.mem_insert_of_mem prev.first_mem
      last_mem := Finset.mem_insert_self _ _
      edge_mem := ?_
      edge_chamber_or_wall := ?_
      scale := (aF * aR)⁻¹ * prev.scale
      scale_pos := mul_pos (inv_pos.mpr (mul_pos haF haR)) prev.scale_pos
      product := ?_ }⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact ⟨Finset.mem_insert_of_mem (prev.edge_mem e he).1,
          Finset.mem_insert_of_mem (prev.edge_mem e he).2⟩
      · obtain rfl := List.mem_singleton.mp he
        exact ⟨Finset.mem_insert_of_mem prev.last_mem, Finset.mem_insert_self _ _⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact prev.edge_chamber_or_wall e he
      · obtain rfl := List.mem_singleton.mp he
        exact hstep.chamber_or_wall
    · intro σ hPQ g hEdge
      have hfirst : first ∈ insert y prev.vertices := Finset.mem_insert_of_mem prev.first_mem
      have hx : x ∈ insert y prev.vertices := Finset.mem_insert_of_mem prev.last_mem
      have hy : y ∈ insert y prev.vertices := Finset.mem_insert_self _ _
      have hPrev : ScalarComposite σ first x ((prev.scale : ℂ) * (prev.edges.map g).prod) :=
        prev.product σ
        (fun s hs t ht => hPQ s (Finset.mem_insert_of_mem hs) t (Finset.mem_insert_of_mem ht))
        g (fun e he => hEdge e (List.mem_append_left _ he))
      have hEnd : ScalarComposite σ x y (g (x, y)) :=
        hEdge (x, y) (List.mem_append_right _ (List.mem_singleton_self _))
      have hx₁ := hF σ (hPQ first hfirst x hx) (hPQ x hx y hy) (hPQ first hfirst y hy)
      have hx₂ := hR σ (hPQ y hy x hx) (hPQ x hx first hfirst) (hPQ y hy first hfirst)
      have hscale : ((aF : ℂ) * (aR : ℂ)) ≠ 0 := by
        exact_mod_cast (mul_pos haF haR).ne'
      have hs := galleryOppositeComposite_of_scalars hG ha K hK σ first x y
        (aF := (aF : ℂ)) (aR := (aR : ℂ)) (s := g (x, y))
        (t := (prev.scale : ℂ) * (prev.edges.map g).prod) hscale hx₁ hx₂ hPrev hEnd
      have hCoeff : ((aF : ℂ) * (aR : ℂ))⁻¹ * ((prev.scale : ℂ) * (prev.edges.map g).prod) *
          g (x, y) = (((aF * aR)⁻¹ * prev.scale : ℝ≥0) : ℂ) *
            ((prev.edges ++ [(x, y)]).map g).prod := by
        simp only [NNReal.coe_mul, NNReal.coe_inv, Complex.ofReal_mul, Complex.ofReal_inv,
          List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc]
      exact hCoeff ▸ hs

/-- The literal distance-additive gallery supplies a finite represented
scalar product calculation with a positive uniform Haar factor. -/
theorem nonempty_representedGalleryProductData :
    Nonempty (RepresentedGalleryProductData.{u, uV} hG ha K hK first last) := by
  let rel := DynamicGalleryStep χ first.val last.val
  have lift (z : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
      (hpath : Relation.ReflTransGen rel first.val z) :
      ∀ hz : Dynamic.centralizer z = Dynamic.centralizer χ,
        Relation.ReflTransGen (fun (x y : GalleryVertex χ) => rel x.val y.val) first ⟨z, hz⟩ := by
    induction hpath with
    | refl => exact fun _ => Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      intro _
      exact (ih hstep.centralizer).tail hstep
  exact nonempty_representedGalleryProductData_of_chain hG ha K hK first last last
    (lift last.val (hasDistanceAdditiveDynamicGallery hG χ first.val last.val
      first.property last.property) last.property)

end Langlands.Plancherel.DynamicCommonLeviPresentations
