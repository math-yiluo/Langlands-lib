import Langlands.Representation.RestrictedTensor.Basic
import Mathlib.Order.Filter.Cofinite

/-! # Maps and changes of finite exceptional set for restricted tensor products -/

noncomputable section
open scoped Classical TensorProduct

universe uK uI uV uW uX

namespace Langlands.RestrictedTensor

variable {K : Type uK} [Field K] {ι : Type uI}
variable {V : ι → Type uV} {W : ι → Type uW} {X : ι → Type uX}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
variable [∀ i, AddCommGroup (X i)] [∀ i, Module K (X i)]

/-- A finite-stage map, enlarged enough to contain the target exceptional set and all
failures of reference-vector preservation. -/
def mapStage (E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (F : Finset ι) (hF : E' ⊆ F) (S : Finset ι) :
    Stage K V S →ₗ[K] Space K W E' e' :=
  of K W E' e' ⟨S ∪ F, hF.trans Finset.subset_union_right⟩ ∘ₗ
    (PiTensorProduct.map (fun i : ↥(S ∪ F) => f i)) ∘ₗ
    transition e Finset.subset_union_left

@[simp]
theorem mapStage_tprod (E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (F : Finset ι) (hF : E' ⊆ F)
    (S : Finset ι) (v : ∀ i : S, V i) :
    mapStage E' e e' f F hF S (PiTensorProduct.tprod K v) =
      pure E' e' ⟨S ∪ F, hF.trans Finset.subset_union_right⟩
        (fun i => f i (extend e v i)) := by
  simp [mapStage, pure]

theorem mapStage_transition (E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (F : Finset ι) (hF : E' ⊆ F)
    (hf : ∀ i ∉ F, f i (e i) = e' i) {S T : Finset ι} (h : S ⊆ T) :
    (mapStage E' e e' f F hF T).comp (transition e h) =
      mapStage E' e e' f F hF S := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change mapStage E' e e' f F hF T (transition e h (PiTensorProduct.tprod K v)) =
    mapStage E' e e' f F hF S (PiTensorProduct.tprod K v)
  rw [transition_tprod, mapStage_tprod, mapStage_tprod]
  have hST : S ∪ F ⊆ T ∪ F := Finset.union_subset_union_left h
  rw [← pure_extend E' e' (S := ⟨S ∪ F, hF.trans Finset.subset_union_right⟩)
    (T := ⟨T ∪ F, hF.trans Finset.subset_union_right⟩) hST]
  congr 1
  funext i
  by_cases hi : i.1 ∈ S ∪ F
  · simp only [extend, dite_eq_left hi]
    by_cases hiS : i.1 ∈ S
    · simp [hiS, h hiS]
    · simp [hiS]
  · have hiS : i.1 ∉ S := fun hs => hi (Finset.mem_union_left F hs)
    have hiF : i.1 ∉ F := fun hf' => hi (Finset.mem_union_right S hf')
    simp [extend, hi, hiS, hf _ hiF]

/-- Construct the induced linear map using any finite exceptional bound. -/
def mapWithBound (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (F : Finset ι) (hF : E' ⊆ F)
    (hf : ∀ i ∉ F, f i (e i) = e' i) :
    Space K V E e →ₗ[K] Space K W E' e' :=
  lift E e (fun S => mapStage E' e e' f F hF S.1)
    (fun _S _T h x => LinearMap.congr_fun (mapStage_transition E' e e' f F hF hf h) x)

@[simp]
theorem mapWithBound_pure (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (F : Finset ι) (hF : E' ⊆ F)
    (hf : ∀ i ∉ F, f i (e i) = e' i) (S : Index E) (v : ∀ i : S.1, V i) :
    mapWithBound E E' e e' f F hF hf (pure E e S v) =
      pure E' e' ⟨S.1 ∪ F, hF.trans Finset.subset_union_right⟩
        (fun i => f i (extend e v i)) := by
  simp [mapWithBound, pure]

/-- On a stage containing the finite bound, the induced map acts factor by factor. -/
theorem mapWithBound_pure_of_subset (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (F : Finset ι) (hF : E' ⊆ F)
    (hf : ∀ i ∉ F, f i (e i) = e' i) (S : Index E) (hFS : F ⊆ S.1)
    (v : ∀ i : S.1, V i) :
    mapWithBound E E' e e' f F hF hf (pure E e S v) =
      pure E' e' ⟨S.1, hF.trans hFS⟩ (fun i => f i (v i)) := by
  rw [mapWithBound_pure]
  rw [← pure_extend E' e' (S := ⟨S.1, hF.trans hFS⟩)
    (T := ⟨S.1 ∪ F, hF.trans Finset.subset_union_right⟩) Finset.subset_union_left]
  congr 1
  funext i
  have hi : i.1 ∈ S.1 := (Finset.union_subset (Finset.Subset.refl _) hFS) i.2
  simp [extend, hi]

/-- A cofinal collection of elementary tensors determines a linear map from the limit. -/
theorem hom_ext_cofinal {Y : Type*} [AddCommGroup Y] [Module K Y]
    {E : Finset ι} {e : ∀ i, V i} (F : Finset ι)
    {f g : Space K V E e →ₗ[K] Y}
    (h : ∀ (S : Index E), F ⊆ S.1 → ∀ v, f (pure E e S v) = g (pure E e S v)) :
    f = g := by
  apply hom_ext
  intro S x
  have hs : f.comp (of K V E e S) = g.comp (of K V E e S) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change f (pure E e S v) = g (pure E e S v)
    rw [← pure_extend E e (S := S)
      (T := ⟨S.1 ∪ F, S.2.trans Finset.subset_union_left⟩) Finset.subset_union_left]
    exact h _ Finset.subset_union_right _
  exact LinearMap.congr_fun hs x

/-- Enlarging or changing the finite bound does not change the induced map. -/
theorem mapWithBound_eq (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (F G : Finset ι) (hF : E' ⊆ F) (hG : E' ⊆ G)
    (hf : ∀ i ∉ F, f i (e i) = e' i) (hg : ∀ i ∉ G, f i (e i) = e' i) :
    mapWithBound E E' e e' f F hF hf = mapWithBound E E' e e' f G hG hg := by
  apply hom_ext_cofinal (F ∪ G)
  intro S hS v
  rw [mapWithBound_pure_of_subset _ _ _ _ _ _ _ _ _ (Finset.subset_union_left.trans hS)]
  rw [mapWithBound_pure_of_subset _ _ _ _ _ _ _ _ _ (Finset.subset_union_right.trans hS)]

/-- A finite bound containing the target exceptional set and every failure of preservation. -/
def mapBound (E' : Finset ι) {e : ∀ i, V i} {e' : ∀ i, W i}
    {f : ∀ i, V i →ₗ[K] W i} (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i) :
    Finset ι :=
  E' ∪ (Filter.eventually_cofinite.mp hf).toFinset

theorem subset_mapBound (E' : Finset ι) {e : ∀ i, V i} {e' : ∀ i, W i}
    {f : ∀ i, V i →ₗ[K] W i} (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i) :
    E' ⊆ mapBound E' hf := Finset.subset_union_left

theorem mapBound_preserves (E' : Finset ι) {e : ∀ i, V i} {e' : ∀ i, W i}
    {f : ∀ i, V i →ₗ[K] W i} (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i)
    (i : ι) (hi : i ∉ mapBound E' hf) : f i (e i) = e' i := by
  by_contra h
  apply hi
  exact Finset.mem_union_right _ ((Filter.eventually_cofinite.mp hf).mem_toFinset.mpr h)

/-- The induced map for component maps preserving reference vectors at all but finitely
many indices. The source and target exceptional sets may differ. -/
def map (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i) :
    Space K V E e →ₗ[K] Space K W E' e' :=
  mapWithBound E E' e e' f (mapBound E' hf) (subset_mapBound E' hf) (mapBound_preserves E' hf)

/-- Any adequate finite bound gives the same induced map. -/
theorem map_eq_mapWithBound (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i)
    (F : Finset ι) (hF : E' ⊆ F) (h : ∀ i ∉ F, f i (e i) = e' i) :
    map E E' e e' f hf = mapWithBound E E' e e' f F hF h :=
  mapWithBound_eq E E' e e' f _ F _ hF _ h

theorem map_pure (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i)
    (S : Index E) (v : ∀ i : S.1, V i) :
    map E E' e e' f hf (pure E e S v) =
      pure E' e' ⟨S.1 ∪ mapBound E' hf, (subset_mapBound E' hf).trans Finset.subset_union_right⟩
        (fun i => f i (extend e v i)) := mapWithBound_pure E E' e e' f _ _ _ S v

theorem map_pure_of_subset (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i)
    (S : Index E) (hS : mapBound E' hf ⊆ S.1) (v : ∀ i : S.1, V i) :
    map E E' e e' f hf (pure E e S v) =
      pure E' e' ⟨S.1, (subset_mapBound E' hf).trans hS⟩ (fun i => f i (v i)) :=
  mapWithBound_pure_of_subset E E' e e' f _ _ _ S hS v

/-- A stage containing all exceptional coordinates admits the componentwise formula;
the finite bound selected in the definition of `map` need not lie in this stage. -/
theorem map_pure_of_preserves (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i)
    (S : Index E) (hS : E' ⊆ S.1) (h : ∀ i ∉ S.1, f i (e i) = e' i)
    (v : ∀ i : S.1, V i) :
    map E E' e e' f hf (pure E e S v) =
      pure E' e' ⟨S.1, hS⟩ (fun i => f i (v i)) := by
  rw [map_eq_mapWithBound E E' e e' f hf S.1 hS h]
  exact mapWithBound_pure_of_subset E E' e e' f S.1 hS h S (Finset.Subset.refl _) v

/-- Cofinite preservation is closed under composition of component linear maps. -/
theorem preserves_comp {e : ∀ i, V i} {e' : ∀ i, W i} {e'' : ∀ i, X i}
    {f : ∀ i, V i →ₗ[K] W i} {g : ∀ i, W i →ₗ[K] X i}
    (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i)
    (hg : ∀ᶠ i in Filter.cofinite, g i (e' i) = e'' i) :
    ∀ᶠ i in Filter.cofinite, ((g i).comp (f i)) (e i) = e'' i :=
  (hf.and hg).mono fun _ hi => by simpa only [LinearMap.comp_apply, hi.1] using hi.2

/-- Induced maps respect composition, even with different exceptional sets. -/
theorem map_comp (E E' E'' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i) (e'' : ∀ i, X i)
    (f : ∀ i, V i →ₗ[K] W i) (g : ∀ i, W i →ₗ[K] X i)
    (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i)
    (hg : ∀ᶠ i in Filter.cofinite, g i (e' i) = e'' i) :
    (map E' E'' e' e'' g hg).comp (map E E' e e' f hf) =
      map E E'' e e'' (fun i => (g i).comp (f i)) (preserves_comp hf hg) := by
  apply hom_ext_cofinal ((mapBound E' hf ∪ mapBound E'' hg) ∪
    mapBound E'' (preserves_comp hf hg))
  intro S hS v
  have h₁ := Finset.subset_union_left.trans (Finset.subset_union_left.trans hS)
  have h₂ := Finset.subset_union_right.trans (Finset.subset_union_left.trans hS)
  have h₃ := Finset.subset_union_right.trans hS
  rw [LinearMap.comp_apply, map_pure_of_subset _ _ _ _ _ _ _ h₁]
  rw [map_pure_of_subset E' E'' e' e'' g hg
    ⟨S.1, (subset_mapBound E' hf).trans h₁⟩ h₂]
  rw [map_pure_of_subset E E'' e e'' _ (preserves_comp hf hg) S h₃]
  rfl

@[simp]
theorem map_id (E : Finset ι) (e : ∀ i, V i) :
    map (K := K) E E e e (fun _ => LinearMap.id) (Filter.Eventually.of_forall fun _ => rfl) =
      LinearMap.id := by
  apply hom_ext_cofinal (mapBound E (Filter.Eventually.of_forall
    (fun i => (show (LinearMap.id : V i →ₗ[K] V i) (e i) = e i from rfl))))
  intro S hS v
  rw [map_pure_of_subset _ _ _ _ _ _ _ hS]
  rfl

/-- Component equivalences preserving references almost everywhere also preserve them
almost everywhere in the reverse direction. -/
theorem preserves_symm {e : ∀ i, V i} {e' : ∀ i, W i}
    (f : ∀ i, V i ≃ₗ[K] W i)
    (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i) :
    ∀ᶠ i in Filter.cofinite, (f i).symm (e' i) = e i :=
  hf.mono fun i hi => by rw [← hi, LinearEquiv.symm_apply_apply]

/-- Component linear equivalences induce an actual equivalence of restricted tensor
products, allowing different finite exceptional sets. -/
def congr (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i ≃ₗ[K] W i)
    (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i) :
    Space K V E e ≃ₗ[K] Space K W E' e' :=
  LinearEquiv.ofLinearMap (map E E' e e' (fun i => (f i).toLinearMap) hf)
    (map E' E e' e (fun i => (f i).symm.toLinearMap) (preserves_symm f hf))
    (by
      rw [map_comp]
      have h : (fun i => (f i).toLinearMap.comp (f i).symm.toLinearMap) =
          (fun i => (LinearMap.id : W i →ₗ[K] W i)) := by
        funext i
        ext x
        exact (f i).apply_symm_apply x
      simpa only [h] using map_id E' e')
    (by
      rw [map_comp]
      have h : (fun i => (f i).symm.toLinearMap.comp (f i).toLinearMap) =
          (fun i => (LinearMap.id : V i →ₗ[K] V i)) := by
        funext i
        ext x
        exact (f i).symm_apply_apply x
      simpa only [h] using map_id E e)

/-- Canonically change exceptional sets and any finitely many reference coordinates. -/
def change (E E' : Finset ι) (e e' : ∀ i, V i)
    (h : ∀ᶠ i in Filter.cofinite, e i = e' i) :
    Space K V E e ≃ₗ[K] Space K V E' e' :=
  congr E E' e e' (fun i => LinearEquiv.refl K (V i)) h

@[simp]
theorem change_refl (E : Finset ι) (e : ∀ i, V i) :
    change (K := K) E E e e (Filter.Eventually.of_forall fun _ => rfl) =
      LinearEquiv.refl K _ := by
  apply LinearEquiv.toLinearMap_injective
  exact map_id E e

/-- Changing the finite exceptions and references is coherent under successive changes. -/
theorem change_trans (E E' E'' : Finset ι) (e e' e'' : ∀ i, V i)
    (h : ∀ᶠ i in Filter.cofinite, e i = e' i)
    (h' : ∀ᶠ i in Filter.cofinite, e' i = e'' i) :
    (change (K := K) E E' e e' h).trans (change E' E'' e' e'' h') =
      change E E'' e e'' ((h.and h').mono fun _ hi => hi.1.trans hi.2) := by
  apply LinearEquiv.toLinearMap_injective
  change (map E' E'' e' e'' (fun _ => LinearMap.id) h').comp
      (map E E' e e' (fun _ => LinearMap.id) h) =
    map E E'' e e'' (fun _ => LinearMap.id) ((h.and h').mono fun _ hi => hi.1.trans hi.2)
  rw [map_comp]
  rfl

/-- Enlarging the exceptional set for prescribed reference vectors changes no tensor space. -/
def ReferenceVectors.restrict {E E' : Finset ι} (r : ReferenceVectors V E) (h : E ⊆ E') :
    ReferenceVectors V E' where
  vector i hi := r.vector i (fun hiE => hi (h hiE))
  nonzero i hi := r.nonzero i (fun hiE => hi (h hiE))

theorem ReferenceVectors.family_eventually_restrict {E E' : Finset ι}
    (r : ReferenceVectors V E) (h : E ⊆ E') :
    ∀ᶠ i in Filter.cofinite, r.family i = (r.restrict h).family i :=
  E'.eventually_cofinite_notMem.mono fun i hi => by
    simp only [ReferenceVectors.family_of_not_mem _ hi,
      ReferenceVectors.family_of_not_mem _ (fun hiE => hi (h hiE)),
      ReferenceVectors.restrict]

/-- The canonical exceptional-set enlargement for Flath's nonzero-reference input. -/
def changeExceptional {E E' : Finset ι} (r : ReferenceVectors V E) (h : E ⊆ E') :
    Product K V E r ≃ₗ[K] Product K V E' (r.restrict h) :=
  change E E' r.family (r.restrict h).family (r.family_eventually_restrict h)

/-- Canonical changes commute with any family of induced component maps. -/
theorem change_natural (E E₁ F F₁ : Finset ι)
    (e e₁ : ∀ i, V i) (d d₁ : ∀ i, W i)
    (he : ∀ᶠ i in Filter.cofinite, e i = e₁ i)
    (hd : ∀ᶠ i in Filter.cofinite, d i = d₁ i)
    (f : ∀ i, V i →ₗ[K] W i)
    (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = d i)
    (hf₁ : ∀ᶠ i in Filter.cofinite, f i (e₁ i) = d₁ i) :
    (change F F₁ d d₁ hd).toLinearMap.comp (map E F e d f hf) =
      (map E₁ F₁ e₁ d₁ f hf₁).comp (change E E₁ e e₁ he).toLinearMap := by
  change (map F F₁ d d₁ (fun _ => LinearMap.id) hd).comp (map E F e d f hf) =
    (map E₁ F₁ e₁ d₁ f hf₁).comp (map E E₁ e e₁ (fun _ => LinearMap.id) he)
  rw [map_comp, map_comp]
  rfl

end Langlands.RestrictedTensor
