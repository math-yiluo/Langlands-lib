import Langlands.GroupScheme.HomogeneousClosedImmersion
import Langlands.GroupScheme.OrbitMapFlatProof
import Langlands.GroupScheme.Products
import Langlands.GroupScheme.CocharacterTransport
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeBaseChange
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Rational points of a group as products of points of a dense image

Over an algebraically closed field `K`, let `p : W → G` be a morphism of finite type schemes over
`Spec K` whose image contains a nonempty open subset of an irreducible group `G`. Then every
rational point of `G` is a product of two rational points of `G` that lift to rational points of
`W`. The open subset comes from generic flatness when `p` is dominant. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

/-- The image of an open set on which a morphism is flat near every point is open. -/
theorem isOpen_image_of_flatNear {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] {S : Set X} (hS : IsOpen S)
    (h : ∀ z ∈ S, OrbitMapFlat.FlatNear f z) : IsOpen (f '' S) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨U, V, hzV, e, hflat⟩ := h z hz
  have : LocallyOfFinitePresentation (f.resLE U V e) := inferInstance
  let W : Set V.toScheme := V.ι ⁻¹' S
  have hW : IsOpen W := hS.preimage V.ι.continuous
  refine ⟨U.ι '' ((f.resLE U V e) '' W), ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨V.ι w, hw, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.resLE_comp_ι f e, Scheme.Hom.comp_apply]
  · exact U.ι.isOpenEmbedding.isOpenMap _ ((f.resLE U V e).isOpenMap _ hW)
  · obtain ⟨w, hw⟩ : z ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hzV
    refine ⟨f.resLE U V e w, ⟨w, ?_, rfl⟩, ?_⟩
    · change V.ι w ∈ S
      rw [hw]
      exact hz
    · rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι f e, Scheme.Hom.comp_apply, hw]

/-- A dominant morphism of finite type onto a reduced locally noetherian scheme has a nonempty
open subset in its image (generic flatness). -/
theorem exists_open_subset_range {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsLocallyNoetherian Y] [IsReduced Y] [IsDominant f] (y : Y) :
    ∃ O : Set Y, IsOpen O ∧ O.Nonempty ∧ O ⊆ Set.range f := by
  obtain ⟨U, hU, hflat⟩ := OrbitMapFlat.exists_open_flatNear f y
  obtain ⟨x, hx⟩ := f.denseRange.exists_mem_open U.isOpen hU
  refine ⟨f '' (f ⁻¹' U), isOpen_image_of_flatNear f (U.isOpen.preimage f.continuous)
    (fun w hw => hflat w hw), ⟨f x, x, hx, rfl⟩, ?_⟩
  rintro _ ⟨w, -, rfl⟩
  exact ⟨w, rfl⟩

section AlgClosed

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- In an irreducible group of finite type over an algebraically closed field, every rational
point is a product of two rational points lying in a given nonempty open set. -/
theorem exists_mul_mem_open {G : GroupScheme (Spec (CommRingCat.of K))}
    [LocallyOfFiniteType G.X.hom] [IrreducibleSpace G.X.left] {O : Set G.X.left}
    (hO : IsOpen O) (hne : O.Nonempty) (g : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X) :
    ∃ u v : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X, g = u * v ∧
      u.left (IsLocalRing.closedPoint K) ∈ O ∧ v.left (IsLocalRing.closedPoint K) ∈ O := by
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  let σ : G.X ⟶ G.X := (𝟙 G.X)⁻¹ * (toUnit G.X ≫ g)
  let σ' : G.X ⟶ G.X := (toUnit G.X ≫ g) * (𝟙 G.X)⁻¹
  have hσσ' : σ' ≫ σ = 𝟙 G.X := by
    simp only [σ, σ', MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, comp_toUnit_assoc,
      mul_inv_rev, inv_inv]
    group
  have hsurj : Function.Surjective σ.left := by
    intro x
    refine ⟨σ'.left x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hσσ', Over.id_left]
    rfl
  have hO₂ : IsOpen (σ.left ⁻¹' O) := hO.preimage σ.left.continuous
  have hne₂ : (σ.left ⁻¹' O).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨w, rfl⟩ := hsurj x
    exact ⟨w, hx⟩
  obtain ⟨c, ⟨hcO, hcO₂⟩, hc⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter hO hO₂ hne hne₂) (hO.inter hO₂).isLocallyClosed
  let u : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom c hc) (pointOfClosedPoint_comp G.X.hom c hc)
  have hu : u.left (IsLocalRing.closedPoint K) = c := pointOfClosedPoint_apply G.X.hom c hc _
  refine ⟨u, u ≫ σ, ?_, by rw [hu]; exact hcO, ?_⟩
  · have h1 : u ≫ toUnit G.X = 𝟙 _ := toUnit_unique _ _
    simp only [σ, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ← Category.assoc, h1,
      Category.id_comp]
    group
  · change σ.left (u.left (IsLocalRing.closedPoint K)) ∈ O
    rw [hu]
    exact hcO₂

end AlgClosed

section FieldExtension

variable {k : Type u} [Field k] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]

/-- The base map `Spec K → Spec k` of a field extension. -/
abbrev extMap : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The `K`-valued points of a scheme over `k`, as a test object over `Spec k`. -/
abbrev extPoint : Over (Spec (CommRingCat.of k)) := Over.mk (extMap K)

/-- A rational point of a pullback gives a `K`-valued point of the original scheme. -/
def pullbackPoint {W : Over (Spec (CommRingCat.of k))}
    (a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ (Over.pullback (extMap K)).obj W) :
    extPoint K ⟶ W :=
  Over.homMk (a.left ≫ pullback.fst W.hom (extMap K)) (by
    have ha : a.left ≫ pullback.snd W.hom (extMap K) = 𝟙 _ := a.w
    change (a.left ≫ pullback.fst W.hom (extMap K)) ≫ W.hom = extMap K
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Category.id_comp])

omit [IsAlgClosed K] in
theorem baseChangeBasePointsEquiv_comp_map {G : GroupScheme (Spec (CommRingCat.of k))}
    {W : Over (Spec (CommRingCat.of k))} (p : W ⟶ G.X)
    (a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ (Over.pullback (extMap K)).obj W) :
    baseChangeBasePointsEquiv (extMap K) G (a ≫ (Over.pullback (extMap K)).map p) =
      pullbackPoint K a ≫ p := by
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left]
  change (a.left ≫ ((Over.pullback (extMap K)).map p).left) ≫ pullback.fst G.X.hom (extMap K) =
    (a.left ≫ pullback.fst W.hom (extMap K)) ≫ p.left
  simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]

/-- **Points of a group with a dominant morphism.** Let `G` be a smooth, affine, geometrically
irreducible group over a field `k`, and `p : W → G` a dominant morphism from an affine scheme
of finite type. For an algebraically closed extension `K` of `k`, every `K`-valued point of `G`
is a product of two `K`-valued points of `G` that factor through `p`. -/
theorem exists_mul_of_isDominant {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyIrreducible G.X.hom]
    {W : Over (Spec (CommRingCat.of k))} [IsAffineHom W.hom] [LocallyOfFiniteType W.hom]
    (p : W ⟶ G.X) [IsDominant p.left] (g : extPoint K ⟶ G.X) :
    ∃ a b : extPoint K ⟶ W, g = (a ≫ p) * (b ≫ p) := by
  let β := extMap (k := k) K
  let G' := (GroupScheme.baseChange β).obj G
  let W' := (Over.pullback β).obj W
  let p' : W' ⟶ G'.X := (Over.pullback β).map p
  have : Flat β := (fieldExtension_fpqc k K).2.1
  have : GeometricallyReduced G.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth _
  have : IsReduced G.X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian G.X.hom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine W.left := isAffine_of_isAffineHom W.hom
  have : QuasiCompact p.left := inferInstance
  have : IsSchemeTheoreticallyDominant p.left := .of_isDominant _
  have : IsSchemeTheoreticallyDominant p'.left :=
    EnvelopeBaseChange.isSchemeTheoreticallyDominant_pullback_map β p
  have : IsAffineHom G'.X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom β))
  have : IsAffineHom W'.hom := inferInstanceAs (IsAffineHom (pullback.snd W.hom β))
  have : LocallyOfFiniteType G'.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom β))
  have : LocallyOfFiniteType W'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd W.hom β))
  have : IsReduced G'.X.left := inferInstanceAs (IsReduced (pullback G.X.hom β))
  have : IrreducibleSpace G'.X.left :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback G.X.hom β)
  have : IsLocallyNoetherian G'.X.left := LocallyOfFiniteType.isLocallyNoetherian G'.X.hom
  have : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
  have : IsAffine W'.left := isAffine_of_isAffineHom W'.hom
  have : QuasiCompact p'.left := inferInstance
  have : LocallyOfFiniteType p'.left := by
    have : LocallyOfFiniteType (p'.left ≫ G'.X.hom) := by rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp p'.left G'.X.hom
  let g' := (baseChangeBasePointsEquiv β G).symm g
  obtain ⟨O, hO, hne, hOp⟩ := exists_open_subset_range p'.left
    (g'.left (IsLocalRing.closedPoint K))
  obtain ⟨u, v, huv, hu, hv⟩ := exists_mul_mem_open hO hne g'
  obtain ⟨a', ha'⟩ := HomogeneousClosedImmersion.exists_rational_lift p' u (hOp hu)
  obtain ⟨b', hb'⟩ := HomogeneousClosedImmersion.exists_rational_lift p' v (hOp hv)
  refine ⟨pullbackPoint K a', pullbackPoint K b', ?_⟩
  rw [← baseChangeBasePointsEquiv_comp_map, ← baseChangeBasePointsEquiv_comp_map, ha', hb',
    ← map_mul, ← huv]
  exact ((baseChangeBasePointsEquiv β G).apply_symm_apply g).symm

end FieldExtension

end Langlands.GroupScheme.SplitExistence
