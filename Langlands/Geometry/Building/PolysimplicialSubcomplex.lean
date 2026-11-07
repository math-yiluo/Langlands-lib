import Langlands.Geometry.Building.AbstractBuilding

/-! # Products constructed from subcomplex coordinate faces -/

noncomputable section

universe u v

namespace Langlands.Geometry.Building.AbstractBuilding.PolysimplicialComplex

variable {ι : Type v} {V : ι → Type u}

/-- The coordinate vertices that occur in some facet of `B`. -/
def coordinateSupport (B : Set (Set (∀ i, V i))) (i : ι) : Set (V i) :=
  {a | ∃ F ∈ B, a ∈ (fun x => x i) '' F}

/-- Coordinate faces from independently chosen facets may be combined. -/
def IsCoordinateMixingClosed (B : Set (Set (∀ i, V i))) : Prop :=
  ∀ F : ι → B, Set.univ.pi (fun i => (fun x => x i) '' (F i).val) ∈ B

theorem mem_coordinateSupport {B : Set (Set (∀ i, V i))}
    {F : Set (∀ i, V i)} (hF : F ∈ B) {x : ∀ i, V i} (hx : x ∈ F) (i : ι) :
    x i ∈ coordinateSupport B i :=
  ⟨F, hF, x, hx, rfl⟩

theorem image_preimage_coordinateProjection {B : Set (Set (∀ i, V i))}
    {F : Set (∀ i, V i)} (hF : F ∈ B) (i : ι) :
    Subtype.val '' ((Subtype.val : coordinateSupport B i → V i) ⁻¹'
      ((fun x => x i) '' F)) = (fun x => x i) '' F := by
  apply Set.Subset.antisymm (Set.image_preimage_subset _ _)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨⟨x i, mem_coordinateSupport hF hx i⟩, ⟨x, hx, rfl⟩, rfl⟩

variable [Finite ι] (K : PolysimplicialComplex ι V)

/-- A facet is the product of its coordinate projections. -/
theorem eq_pi_coordinateProjection {F : Set (∀ i, V i)} (hF : F ∈ K.facets) :
    F = Set.univ.pi (fun i => (fun x => x i) '' F) :=
  (congrArg Subtype.val (K.facetsOrderIso.symm_apply_apply ⟨F, hF⟩)).symm

/-- The actual simplicial factor on the coordinate vertices supported by `B`.
Its faces are the nonempty sets contained in a projected facet of `B`. -/
def subcomplexFactor (B : Set (Set (∀ i, V i))) (hB : IsSubcomplex B K.facets)
    (hne : B.Nonempty) (i : ι) : SimplicialComplex (coordinateSupport B i) where
  faces := {s | s.Nonempty ∧ ∃ F ∈ B,
    Subtype.val '' s ⊆ (fun x => x i) '' F}
  nonempty_vertices := by
    obtain ⟨F, hF⟩ := hne
    obtain ⟨x, hx⟩ := K.nonempty_of_mem_facets (hB.1 hF)
    exact ⟨⟨x i, mem_coordinateSupport hF hx i⟩⟩
  finite_of_mem s hs := by
    obtain ⟨_, F, hF, hsF⟩ := hs
    exact Set.Finite.of_finite_image
      (((K.finite_of_mem_facets (hB.1 hF)).image (fun x => x i)).subset hsF)
      Subtype.val_injective.injOn
  nonempty_of_mem _ hs := hs.1
  singleton_mem a := by
    obtain ⟨F, hF, ha⟩ := a.property
    exact ⟨Set.singleton_nonempty a, F, hF, by
      simpa only [Set.image_singleton, Set.singleton_subset_iff] using ha⟩
  mem_of_subset s hs t ht hts := by
    obtain ⟨_, F, hF, hsF⟩ := hs
    exact ⟨ht, F, hF, (Set.image_mono hts).trans hsF⟩

/-- The finite product of the supported coordinate simplicial factors. -/
def subcomplexProduct (B : Set (Set (∀ i, V i))) (hB : IsSubcomplex B K.facets)
    (hne : B.Nonempty) :
    PolysimplicialComplex ι (fun i => coordinateSupport B i) :=
  ⟨K.subcomplexFactor B hB hne⟩

theorem image_mem_factor_of_subcomplexFactor
    {B : Set (Set (∀ i, V i))} (hB : IsSubcomplex B K.facets) (hne : B.Nonempty)
    {i : ι} {s : Set (coordinateSupport B i)}
    (hs : s ∈ (K.subcomplexFactor B hB hne i).faces) :
    Subtype.val '' s ∈ (K.factor i).faces := by
  obtain ⟨hsne, F, hF, hsF⟩ := hs
  exact (K.factor i).mem_of_subset _
    (K.facetsOrderIso ⟨F, hB.1 hF⟩ i).property _
    (hsne.image Subtype.val) hsF

theorem pi_image_mem_of_coordinateMixingClosed
    {B : Set (Set (∀ i, V i))} (hB : IsSubcomplex B K.facets) (hne : B.Nonempty)
    (hmix : IsCoordinateMixingClosed B)
    (s : ∀ i, (K.subcomplexFactor B hB hne i).faces) :
    Set.univ.pi (fun i => Subtype.val '' (s i).val) ∈ B := by
  classical
  choose F hFB hsF using fun i => (s i).property.2
  have hbig := hmix (fun i => ⟨F i, hFB i⟩)
  refine hB.2 _ hbig _ (K.pi_mem_facets fun i =>
    K.image_mem_factor_of_subcomplexFactor hB hne (s i).property) ?_
  intro x hx i hi
  exact hsF i (hx i hi)

/-- The coordinate face of an original facet, on its supported vertex type. -/
def subcomplexFactorCoordinates
    {B : Set (Set (∀ i, V i))} (hB : IsSubcomplex B K.facets) (hne : B.Nonempty)
    (F : B) (i : ι) : (K.subcomplexFactor B hB hne i).faces :=
  ⟨Subtype.val ⁻¹' ((fun x => x i) '' F.val), by
    obtain ⟨x, hx⟩ := K.nonempty_of_mem_facets (hB.1 F.property)
    exact ⟨⟨⟨x i, mem_coordinateSupport F.property hx i⟩, x, hx, rfl⟩,
      F.val, F.property, Set.image_preimage_subset _ _⟩⟩

/-- The facets of the subcomplex are exactly the independent tuples of
supported factor faces, with their product inclusion order. -/
def subcomplexCoordinatesOrderIso
    {B : Set (Set (∀ i, V i))} (hB : IsSubcomplex B K.facets) (hne : B.Nonempty)
    (hmix : IsCoordinateMixingClosed B) :
    B ≃o ∀ i, (K.subcomplexFactor B hB hne i).faces where
  toFun := K.subcomplexFactorCoordinates hB hne
  invFun s := ⟨Set.univ.pi (fun i => Subtype.val '' (s i).val),
    K.pi_image_mem_of_coordinateMixingClosed hB hne hmix s⟩
  left_inv F := by
    apply Subtype.ext
    change Set.univ.pi (fun i => Subtype.val ''
      ((Subtype.val : coordinateSupport B i → V i) ⁻¹'
        ((fun x => x i) '' F.val))) = F.val
    simp only [image_preimage_coordinateProjection F.property]
    exact (K.eq_pi_coordinateProjection (hB.1 F.property)).symm
  right_inv s := by
    funext i
    apply Subtype.ext
    change (Subtype.val : coordinateSupport B i → V i) ⁻¹'
      ((fun x => x i) '' Set.univ.pi (fun j => Subtype.val '' (s j).val)) = (s i).val
    have hn : (Set.univ.pi (fun j => Subtype.val '' (s j).val)).Nonempty :=
      Set.univ_pi_nonempty_iff.mpr fun j => (s j).property.1.image Subtype.val
    rw [Set.eval_image_univ_pi hn, Set.preimage_image_eq _ Subtype.val_injective]
  map_rel_iff' {F G} := by
    change (∀ i, (Subtype.val : coordinateSupport B i → V i) ⁻¹'
      ((fun x => x i) '' F.val) ⊆
      (Subtype.val : coordinateSupport B i → V i) ⁻¹'
        ((fun x => x i) '' G.val)) ↔ F.val ⊆ G.val
    constructor
    · intro h
      rw [K.eq_pi_coordinateProjection (hB.1 G.property)]
      intro x hx i _
      exact h i (show (⟨x i, mem_coordinateSupport F.property hx i⟩ :
        coordinateSupport B i) ∈ Subtype.val ⁻¹' ((fun x => x i) '' F.val) from
          ⟨x, hx, rfl⟩)
    · intro h i
      exact Set.preimage_mono (Set.image_mono h)

/-- The constructed finite product realizes the original subcomplex's
ordered facets. -/
def subcomplexProductOrderIso
    {B : Set (Set (∀ i, V i))} (hB : IsSubcomplex B K.facets) (hne : B.Nonempty)
    (hmix : IsCoordinateMixingClosed B) :
    B ≃o (K.subcomplexProduct B hB hne).facets :=
  (K.subcomplexCoordinatesOrderIso hB hne hmix).trans
    (K.subcomplexProduct B hB hne).facetsOrderIso.symm

/-- Nonempty subcomplexes closed under coordinate mixing have a genuine
finite-product polysimplicial structure. -/
theorem isPolysimplicial_of_coordinateMixingClosed
    {B : Set (Set (∀ i, V i))} (hB : IsSubcomplex B K.facets) (hne : B.Nonempty)
    (hmix : IsCoordinateMixingClosed B) :
    IsPolysimplicial B :=
  ((K.subcomplexProduct B hB hne).isPolysimplicial_facets).of_orderIso
    (K.subcomplexProductOrderIso hB hne hmix).symm

end Langlands.Geometry.Building.AbstractBuilding.PolysimplicialComplex
