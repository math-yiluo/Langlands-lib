import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingStatement
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof
import Langlands.AlgebraicGeometry.Modules.TensorUnitorLaws
import Langlands.AlgebraicGeometry.Modules.SectionResidueComparison
import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison
import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof
import Langlands.AlgebraicGeometry.Modules.TensorSectionGenerationLocusProof
import Mathlib.RingTheory.DualNumber

/-! # Field-point vanishing and frame cancellation for actual line-bundle sections -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

open Langlands.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Tensoring with a global frame on the right preserves and reflects zero. -/
private lemma tensorSection_eq_zero_iff_of_isIso_right (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) [IsIso (sectionHom N t)] :
    tensorSection M N s t = 0 ↔ s = 0 := by
  have hsplit : tensorMap (sectionHom M s) (sectionHom N t) =
      tensorMap (sectionHom M s) (𝟙 (structureSheaf X)) ≫
        tensorMap (𝟙 M) (sectionHom N t) := by
    rw [tensorMap_comp, Category.comp_id, Category.id_comp]
  have : IsIso (tensorMap (𝟙 M) (sectionHom N t)) :=
    inferInstanceAs (IsIso ((tensorFunctor X).mapIso
      ((Iso.refl M).prod (asIso (sectionHom N t)))).hom)
  rw [← sectionHom_eq_zero_iff, sectionHom_tensorSection,
    comp_eq_zero_iff_of_epi, hsplit, comp_eq_zero_iff_of_mono,
    ← comp_eq_zero_iff_of_mono (tensorRightUnitor M).hom,
    tensorRightUnitor_naturality, comp_eq_zero_iff_of_epi, sectionHom_eq_zero_iff]

/-- Tensoring with a global frame on the left preserves and reflects zero. -/
private lemma tensorSection_eq_zero_iff_of_isIso_left (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) [IsIso (sectionHom M s)] :
    tensorSection M N s t = 0 ↔ t = 0 := by
  have hsplit : tensorMap (sectionHom M s) (sectionHom N t) =
      tensorMap (𝟙 (structureSheaf X)) (sectionHom N t) ≫
        tensorMap (sectionHom M s) (𝟙 N) := by
    rw [tensorMap_comp, Category.id_comp, Category.comp_id]
  have : IsIso (tensorMap (sectionHom M s) (𝟙 N)) :=
    inferInstanceAs (IsIso ((tensorFunctor X).mapIso
      ((asIso (sectionHom M s)).prod (Iso.refl N))).hom)
  rw [← sectionHom_eq_zero_iff, sectionHom_tensorSection,
    comp_eq_zero_iff_of_epi, hsplit, comp_eq_zero_iff_of_mono,
    ← comp_eq_zero_iff_of_mono (tensorLeftUnitor N).hom,
    tensorLeftUnitor_naturality, comp_eq_zero_iff_of_epi, sectionHom_eq_zero_iff]

/-- Pullback of a tensor section and the tensor of pulled-back sections have the same zero test. -/
private lemma pullback_tensorSection_eq_zero_iff (f : Y ⟶ X) (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) :
    pullbackSection f (tensorObj M N) (tensorSection M N s t) = 0 ↔
      tensorSection ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
        (pullbackSection f M s) (pullbackSection f N t) = 0 := by
  let P := Scheme.Modules.pullback f
  let c := pullbackTensorComparison f
  have : IsIso c := pullbackTensorComparisonIsIso f
  let ι := pullbackUnitIso f
  let fs := sectionHom M s
  let ft := sectionHom N t
  have hnat : P.map (tensorMap fs ft) ≫ c.app (M, N) =
      c.app (structureSheaf X, structureSheaf X) ≫ tensorMap (P.map fs) (P.map ft) :=
    c.naturality (X := (structureSheaf X, structureSheaf X)) (Y := (M, N)) (fs, ft)
  have hcomp : P.map (tensorMap fs ft) = 0 ↔ tensorMap (P.map fs) (P.map ft) = 0 := by
    rw [← comp_eq_zero_iff_of_mono (c.app (M, N)), hnat, comp_eq_zero_iff_of_epi]
  have hunit : tensorMap (ι.inv ≫ P.map fs) (ι.inv ≫ P.map ft) =
      tensorMap ι.inv ι.inv ≫ tensorMap (P.map fs) (P.map ft) :=
    (tensorMap_comp _ _ _ _).symm
  have : IsIso (tensorMap ι.inv ι.inv) :=
    inferInstanceAs (IsIso ((tensorFunctor Y).mapIso (ι.symm.prod ι.symm)).hom)
  rw [pullbackSection_eq_zero_iff, sectionHom_tensorSection, Functor.map_comp,
    comp_eq_zero_iff_of_epi, hcomp, ← sectionHom_eq_zero_iff,
    sectionHom_tensorSection, comp_eq_zero_iff_of_epi,
    sectionHom_pullbackSection, sectionHom_pullbackSection]
  change tensorMap (P.map fs) (P.map ft) = 0 ↔
    tensorMap (ι.inv ≫ P.map fs) (ι.inv ≫ P.map ft) = 0
  rw [hunit, comp_eq_zero_iff_of_epi]

/-- A right-hand section that becomes a frame after pullback can be cancelled in a zero test. -/
private lemma pullback_tensorSection_eq_zero_iff_of_isIso_right (f : Y ⟶ X) (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) [IsIso (pullbackSectionHom f N t)] :
    pullbackSection f (tensorObj M N) (tensorSection M N s t) = 0 ↔
      pullbackSection f M s = 0 := by
  have : IsIso (sectionHom ((Scheme.Modules.pullback f).obj N) (pullbackSection f N t)) := by
    rw [sectionHom_pullbackSection]
    infer_instance
  rw [pullback_tensorSection_eq_zero_iff, tensorSection_eq_zero_iff_of_isIso_right]

/-- The corresponding zero test with a frame in the left-hand factor after pullback. -/
private lemma pullback_tensorSection_eq_zero_iff_of_isIso_left (f : Y ⟶ X) (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) [IsIso (pullbackSectionHom f M s)] :
    pullbackSection f (tensorObj M N) (tensorSection M N s t) = 0 ↔
      pullbackSection f N t = 0 := by
  have : IsIso (sectionHom ((Scheme.Modules.pullback f).obj M) (pullbackSection f M s)) := by
    rw [sectionHom_pullbackSection]
    infer_instance
  rw [pullback_tensorSection_eq_zero_iff, tensorSection_eq_zero_iff_of_isIso_left]

/-- The pullback of the zero section is zero. -/
lemma pullbackSection_zero (f : Y ⟶ X) (M : X.Modules) :
    pullbackSection f M 0 = 0 := by
  rw [pullbackSection_eq_zero_iff, (sectionHom_eq_zero_iff M 0).mpr rfl, Functor.map_zero]

end Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Every morphism out of the structure module is the section morphism of its value at one. -/
lemma sectionHom_app_top_one {M : X.Modules} (φ : structureModule X ⟶ M) :
    sectionHom M (φ.app ⊤ (1 : Γ(X, ⊤))) = φ :=
  (sectionHomEquiv M).apply_symm_apply φ

/-- A section with invertible section morphism trivializes on the whole scheme. -/
lemma trivializationOpen_eq_top_of_isIso (M : X.Modules) (s : GlobalSections M)
    (h : IsIso (sectionHom M s)) : trivializationOpen M s = ⊤ := by
  apply top_le_iff.mp
  apply le_sSup
  change IsIso ((Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).map (sectionHom M s))
  infer_instance

/-- A section trivializing on the whole scheme has an invertible section morphism. -/
lemma isIso_sectionHom_of_trivializationOpen_eq_top (M : X.Modules) (s : GlobalSections M)
    (h : trivializationOpen M s = ⊤) : IsIso (sectionHom M s) := by
  rw [isIso_iff_stalk_isIso]
  intro x
  exact isStalkFrame_of_mem_trivializationOpen M s (by rw [h]; trivial)

/-- The unit section of the trivial line bundle trivializes on the whole scheme. -/
lemma trivializationOpen_one (X : Scheme.{u}) :
    trivializationOpen (LineBundle.trivial X).obj (1 : Γ(X, ⊤)) = ⊤ := by
  apply trivializationOpen_eq_top_of_isIso
  have h : sectionHom (LineBundle.trivial X).obj (1 : Γ(X, ⊤)) =
      𝟙 (structureModule X) :=
    sectionHom_app_top_one (𝟙 (structureModule X))
  rw [h]
  infer_instance

/-- The zero section of a line bundle has empty trivialization open. -/
lemma trivializationOpen_zero (L : LineBundle X) : trivializationOpen L.obj 0 = ⊥ := by
  apply SetLike.coe_injective
  rw [← lineBundleResidueOpenComparison X L 0]
  ext x
  simp only [nonvanishingLocus, NonvanishingAt, residueSection, pullbackSection_zero,
    Set.mem_ofPred_eq, ne_eq, not_true_eq_false, Opens.coe_bot, Set.mem_empty_iff_false]

/-- If a section vanishes along a morphism, no point maps into its trivialization open. -/
lemma not_mem_of_vanishesAlong {L : LineBundle X} {f : Y ⟶ X} {s : GlobalSections L.obj}
    (h : VanishesAlong L f s) (y : Y) : f y ∉ trivializationOpen L.obj s := by
  intro hy
  have hopen := lineBundlePullbackSectionOpen X Y f L s
  have hmem : y ∈ trivializationOpen ((LineBundle.pullback f).obj L).obj
      (pullbackSection f L.obj s) := by
    change y ∈ trivializationOpen ((Scheme.Modules.pullback f).obj L.obj)
      (pullbackSection f L.obj s)
    rw [hopen]
    exact hy
  have h0 : pullbackSection f L.obj s = 0 := h
  rw [h0, trivializationOpen_zero] at hmem
  exact hmem

/-- Along a morphism from the spectrum of a field, a line-bundle section vanishes exactly
when the image of the point lies outside its trivialization open. -/
theorem vanishesAlong_field_iff {K : Type u} [Field K] (L : LineBundle X)
    (x : Spec (CommRingCat.of K) ⟶ X) (s : GlobalSections L.obj)
    (y : Spec (CommRingCat.of K)) :
    VanishesAlong L x s ↔ x y ∉ trivializationOpen L.obj s := by
  refine ⟨fun h ↦ not_mem_of_vanishesAlong h y, fun h ↦ ?_⟩
  obtain rfl : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hres : residueSection L.obj s (x (IsLocalRing.closedPoint K)) = 0 := by
    by_contra hne
    apply h
    have hmem : x (IsLocalRing.closedPoint K) ∈ nonvanishingLocus L.obj s := hne
    rw [lineBundleResidueOpenComparison X L s] at hmem
    exact hmem
  have hx := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X x
  unfold VanishesAlong
  rw [← hx, ← pullbackSection_comp_eq_zero_iff]
  change pullbackSection _ _ (residueSection L.obj s (x (IsLocalRing.closedPoint K))) = 0
  rw [hres, pullbackSection_zero]

/-- Membership of a field-valued point in the preimage of a trivialization open is
nonvanishing along the composite. -/
lemma mem_preimage_trivializationOpen_iff {K : Type u} [Field K] (g : X ⟶ Y)
    (L : LineBundle Y) (s : GlobalSections L.obj) (x : Spec (CommRingCat.of K) ⟶ X)
    (y : Spec (CommRingCat.of K)) :
    x y ∈ g ⁻¹ᵁ trivializationOpen L.obj s ↔ ¬ VanishesAlong L (x ≫ g) s := by
  rw [vanishesAlong_field_iff L (x ≫ g) s y, not_not]
  rfl

/-- A section whose pullback trivializes everywhere gives an invertible pulled-back
section morphism. -/
lemma isIso_pullback_map_sectionHom (M : LineBundle X) (u : GlobalSections M.obj)
    (f : Y ⟶ X) (hu : ∀ y, f y ∈ trivializationOpen M.obj u) :
    IsIso (sectionHom ((Scheme.Modules.pullback f).obj M.obj) (pullbackSection f M.obj u)) := by
  apply isIso_sectionHom_of_trivializationOpen_eq_top
  have hopen := lineBundlePullbackSectionOpen X Y f M u
  change trivializationOpen ((Scheme.Modules.pullback f).obj M.obj)
    (pullbackSection f M.obj u) = f ⁻¹ᵁ trivializationOpen M.obj u at hopen
  rw [hopen]
  exact top_le_iff.mp fun y _ ↦ hu y

/-- A right factor generating at every image point preserves and reflects vanishing. -/
theorem vanishesAlong_tensor_right_iff (L M : LineBundle X) (s : GlobalSections L.obj)
    (t : GlobalSections M.obj) (f : Y ⟶ X)
    (ht : ∀ y, f y ∈ trivializationOpen M.obj t) :
    VanishesAlong (LineBundle.tensor pullbackTensorComparisonIsIso L M) f
      (tensorSection L.obj M.obj s t) ↔ VanishesAlong L f s := by
  have : IsIso (pullbackSectionHom f M.obj t) := by
    rw [← sectionHom_pullbackSection]
    exact isIso_pullback_map_sectionHom M t f ht
  exact pullback_tensorSection_eq_zero_iff_of_isIso_right f L.obj M.obj s t

/-- A left factor generating at every image point preserves and reflects vanishing. -/
theorem vanishesAlong_tensor_left_iff (L M : LineBundle X) (s : GlobalSections L.obj)
    (t : GlobalSections M.obj) (f : Y ⟶ X)
    (hs : ∀ y, f y ∈ trivializationOpen L.obj s) :
    VanishesAlong (LineBundle.tensor pullbackTensorComparisonIsIso L M) f
      (tensorSection L.obj M.obj s t) ↔ VanishesAlong M f t := by
  have : IsIso (pullbackSectionHom f L.obj s) := by
    rw [← sectionHom_pullbackSection]
    exact isIso_pullback_map_sectionHom L s f hs
  exact pullback_tensorSection_eq_zero_iff_of_isIso_left f L.obj M.obj s t

/-- At a field-valued point, a product section vanishes exactly when one factor does. -/
theorem vanishesAlong_tensor_field_iff {K : Type u} [Field K] (L M : LineBundle X)
    (s : GlobalSections L.obj) (u : GlobalSections M.obj)
    (x : Spec (CommRingCat.of K) ⟶ X) :
    VanishesAlong (LineBundle.tensor pullbackTensorComparisonIsIso L M) x (tensorSection L.obj M.obj s u) ↔
      VanishesAlong L x s ∨ VanishesAlong M x u := by
  rw [vanishesAlong_field_iff _ x _ (IsLocalRing.closedPoint K),
    vanishesAlong_field_iff L x s (IsLocalRing.closedPoint K),
    vanishesAlong_field_iff M x u (IsLocalRing.closedPoint K)]
  change x _ ∉ trivializationOpen (tensorObj L.obj M.obj) (tensorSection L.obj M.obj s u) ↔ _
  rw [tensorSectionGenerationLocus X L M s u, Opens.mem_inf, not_and_or]

/-- The ring of dual numbers over a field has a single prime ideal. -/
lemma subsingleton_primeSpectrum_dualNumber (K : Type u) [Field K] :
    Subsingleton (PrimeSpectrum (DualNumber K)) := by
  have key : ∀ P Q : PrimeSpectrum (DualNumber K), P.asIdeal ≤ Q.asIdeal := by
    intro P Q a ha
    rcases TrivSqZeroExt.isUnit_or_isNilpotent a with hu | ⟨n, hn⟩
    · exact absurd (P.asIdeal.eq_top_of_isUnit_mem ha hu) P.isPrime.ne_top
    · exact Q.isPrime.mem_of_pow_mem n (hn ▸ Q.asIdeal.zero_mem)
  exact ⟨fun P Q ↦ PrimeSpectrum.ext (le_antisymm (key P Q) (key Q P))⟩

/-- A tangent vector at a point where a section does not vanish lands entirely in the
trivialization open of that section, because the spectrum of the dual numbers has a
single point. -/
theorem mem_trivializationOpen_of_isTangentVectorAt {K : Type u} [Field K]
    {p : X ⟶ Spec (CommRingCat.of K)} {x : Spec (CommRingCat.of K) ⟶ X}
    {t : Spec (CommRingCat.of (DualNumber K)) ⟶ X} (ht : IsTangentVectorAt p x t)
    {M : LineBundle X} {u : GlobalSections M.obj} (hu : ¬ VanishesAlong M x u)
    (y : Spec (CommRingCat.of (DualNumber K))) : t y ∈ trivializationOpen M.obj u := by
  have hx : x (IsLocalRing.closedPoint K) ∈ trivializationOpen M.obj u := by
    by_contra h
    exact hu ((vanishesAlong_field_iff M x u _).mpr h)
  have : Subsingleton (PrimeSpectrum (DualNumber K)) :=
    subsingleton_primeSpectrum_dualNumber K
  have hy : y = dualNumberAugmentation K (IsLocalRing.closedPoint K) :=
    Subsingleton.elim (α := PrimeSpectrum (DualNumber K)) _ _
  rw [hy, ← Scheme.Hom.comp_apply, ht.2]
  exact hx

/-- A right factor nonvanishing at the base point can be cancelled along a tangent. -/
theorem vanishesAlong_tensor_tangent_right_iff {K : Type u} [Field K]
    {p : X ⟶ Spec (CommRingCat.of K)} {x : Spec (CommRingCat.of K) ⟶ X}
    {v : Spec (CommRingCat.of (DualNumber K)) ⟶ X} (hv : IsTangentVectorAt p x v)
    (L M : LineBundle X) (s : GlobalSections L.obj) (t : GlobalSections M.obj)
    (ht : ¬ VanishesAlong M x t) :
    VanishesAlong (LineBundle.tensor pullbackTensorComparisonIsIso L M) v
      (tensorSection L.obj M.obj s t) ↔ VanishesAlong L v s :=
  vanishesAlong_tensor_right_iff L M s t v
    (mem_trivializationOpen_of_isTangentVectorAt hv ht)

/-- A left factor nonvanishing at the base point can be cancelled along a tangent. -/
theorem vanishesAlong_tensor_tangent_left_iff {K : Type u} [Field K]
    {p : X ⟶ Spec (CommRingCat.of K)} {x : Spec (CommRingCat.of K) ⟶ X}
    {v : Spec (CommRingCat.of (DualNumber K)) ⟶ X} (hv : IsTangentVectorAt p x v)
    (L M : LineBundle X) (s : GlobalSections L.obj) (t : GlobalSections M.obj)
    (hs : ¬ VanishesAlong L x s) :
    VanishesAlong (LineBundle.tensor pullbackTensorComparisonIsIso L M) v
      (tensorSection L.obj M.obj s t) ↔ VanishesAlong M v t :=
  vanishesAlong_tensor_left_iff L M s t v
    (mem_trivializationOpen_of_isTangentVectorAt hv hs)

/-- The seven field, morphism and tangent vanishing assertions in every universe. -/
theorem lineBundleSectionVanishing : LineBundleSectionVanishingStatement.{u} :=
  ⟨fun _ _ _ L x s y ↦ vanishesAlong_field_iff L x s y,
    fun _ _ _ L M x s t ↦ vanishesAlong_tensor_field_iff L M s t x,
    fun _ _ L M s t f ht ↦ vanishesAlong_tensor_right_iff L M s t f ht,
    fun _ _ L M s t f hs ↦ vanishesAlong_tensor_left_iff L M s t f hs,
    fun _ _ _ _ _ _ M t hv ht ↦
      mem_trivializationOpen_of_isTangentVectorAt (M := M) (u := t) hv ht,
    fun _ _ _ _ _ _ L M s t hv ht ↦ vanishesAlong_tensor_tangent_right_iff hv L M s t ht,
    fun _ _ _ _ _ _ L M s t hv hs ↦ vanishesAlong_tensor_tangent_left_iff hv L M s t hs⟩

end Langlands.AlgebraicGeometry.Picard
