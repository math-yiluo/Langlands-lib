/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.GluedStagesCharts

/-!
# The finite-type schemes glued from the stages of a finite affine gluing presentation

Let `G` be a finite affine gluing presentation of a scheme `S`
(`AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation`) and `l` a valid stage
(`AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.Stage`) with coefficient subrings
`Aₐ ⊆ Γ(S, Uₐ)`. We glue the charts `Spec Aₐ` along the opens `⋃_r D(f a b r) ⊆ Spec Aₐ` to a
scheme `S_l` of finite type over `ℤ`
(`AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.Stage.scheme`).

The overlap map `⋃_r D(f a b r) ⟶ Spec A_b` is characterised by being compatible with the chart
maps `Uₐ ⊓ U_b ⟶ Spec Aₐ` and `Uₐ ⊓ U_b ⟶ Spec A_b` induced by the inclusions `Aₐ ⊆ Γ(S, Uₐ)`
and `A_b ⊆ Γ(S, U_b)`. It exists because `Aₐ[1/f a b r] = A_b[1/g a b r]` inside
`Γ(S, D(f a b r))`, and it is unique because `Aₐ[1/f] ⟶ Γ(S, D(f))` is injective (localization
is exact).

For `l ≤ l'` the inclusions of the coefficient subrings induce affine transition morphisms
`S_{l'} ⟶ S_l`, giving a diagram indexed by the opposite of the directed set of stages
(`AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.stageDiagram`).

## Implementation details

The gluing conditions follow from the unit conditions of the stage and from the uniqueness of
the overlap maps.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation

variable {S : Scheme.{u}} {G : S.FiniteAffineGluingPresentation}

namespace Stage

variable (l : G.Stage)

/-- The coefficient ring of the chart `a` of a stage. -/
abbrev ring (a : G.ι) : CommRingCat.{u} := CommRingCat.of (l.A a)

/-- The basic-open element `f a b r` as an element of the coefficient subring of the chart `a`. -/
def fElem (a b : G.ι) (r : G.κ a b) : l.A a := ⟨G.f a b r, l.f_mem a b r⟩

@[simp]
lemma coe_fElem (a b : G.ι) (r : G.κ a b) : (l.fElem a b r : Γ(S, G.U a)) = G.f a b r :=
  rfl

/-- The overlap `⋃_r D(f a b r) ⊆ Spec Aₐ` of the chart `a` with the chart `b`. -/
noncomputable def overlap (a b : G.ι) : (Spec (l.ring a)).Opens :=
  ⨆ r, chartBasicOpen (l.A a) (l.fElem a b r)

lemma inf_eq_iSup_basicOpen (a b : G.ι) :
    (G.U a : S.Opens) ⊓ G.U b = ⨆ r, S.basicOpen ((l.fElem a b r : l.A a) : Γ(S, G.U a)) :=
  (G.iSup_basicOpen_f a b).symm

lemma range_subringChart_subset_overlap (a b : G.ι) {W : S.Opens} (h : W ≤ G.U a)
    (hW : W ≤ (G.U a : S.Opens) ⊓ G.U b) :
    Set.range (subringChart (l.A a) h) ⊆ l.overlap a b :=
  range_subringChart_subset _ _ _ (hW.trans (l.inf_eq_iSup_basicOpen a b).le)

/-- The chart map `Uₐ ⊓ U_b ⟶ Spec Aₐ`, lifted to the overlap `⋃_r D(f a b r)`. -/
noncomputable def chartLiftOverlap (a b : G.ι) :
    ((G.U a : S.Opens) ⊓ G.U b).toScheme ⟶ (l.overlap a b).toScheme :=
  chartLift (l.A a) inf_le_left (l.overlap a b)
    (l.range_subringChart_subset_overlap a b inf_le_left le_rfl)

@[reassoc (attr := simp)]
lemma chartLiftOverlap_ι (a b : G.ι) :
    l.chartLiftOverlap a b ≫ (l.overlap a b).ι = subringChart (l.A a) inf_le_left :=
  chartLift_ι _ _ _ _

/-- Morphisms out of the overlap into an affine scheme are determined by their restriction along
the chart lift. -/
lemma overlap_hom_ext (a b : G.ι) {R : CommRingCat.{u}} (f g : (l.overlap a b).toScheme ⟶ Spec R)
    (h : l.chartLiftOverlap a b ≫ f = l.chartLiftOverlap a b ≫ g) : f = g :=
  chartLift_cancel (l.fElem a b) (G.U a).2 rfl (l.inf_eq_iSup_basicOpen a b) inf_le_left _ f g h

/-- The overlap of a chart with itself is everything. -/
lemma overlap_self (a : G.ι) : l.overlap a a = ⊤ := by
  obtain ⟨c, hc, hsum⟩ := l.unit_self a
  refine iSup_specBasicOpen_eq_top_iff.mpr ?_
  rw [Ideal.eq_top_iff_one]
  have : (1 : l.A a) = ∑ r, ⟨c r, hc r⟩ * l.fElem a a r :=
    Subtype.ext (by simpa [fElem] using hsum.symm)
  rw [this]
  exact Ideal.sum_mem _ fun r _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨r, rfl⟩)

lemma resLE_subringRes_mem (a b : G.ι) (r : G.κ a b) (y : l.A b)
    (hi : S.basicOpen ((l.fElem a b r : l.A a) : Γ(S, G.U a)) ≤ (G.U a : S.Opens) ⊓ G.U b) :
    S.resLE hi (subringRes (l.A b) inf_le_right y) ∈ localizationSubring (l.A a) (G.f a b r)
      (S.basicOpen (G.f a b r)) le_rfl := by
  rw [l.localization_eq a b r, subringRes_apply, resLE_resLE_apply]
  exact resLE_mem_localizationSubring (G.g a b r) _ (G.basicOpen_f a b r).le y.2

lemma exists_chartLiftOverlap_comp_eq (a b : G.ι) :
    ∃ f : (l.overlap a b).toScheme ⟶ Spec (l.ring b),
      l.chartLiftOverlap a b ≫ f = subringChart (l.A b) inf_le_right :=
  exists_chartLift_comp_eq (l.fElem a b) (G.U a).2 rfl (l.inf_eq_iSup_basicOpen a b) inf_le_left
    _ (subringRes (l.A b) inf_le_right) fun r y hi ↦ l.resLE_subringRes_mem a b r y hi

/-- The overlap map `⋃_r D(f a b r) ⟶ Spec A_b`, compatible with the chart maps. -/
noncomputable def toChart (a b : G.ι) : (l.overlap a b).toScheme ⟶ Spec (l.ring b) :=
  (l.exists_chartLiftOverlap_comp_eq a b).choose

@[reassoc (attr := simp)]
lemma chartLiftOverlap_toChart (a b : G.ι) :
    l.chartLiftOverlap a b ≫ l.toChart a b = subringChart (l.A b) inf_le_right :=
  (l.exists_chartLiftOverlap_comp_eq a b).choose_spec

/-- The unit condition `unit_symm`, transported to `D(f a b r)` and the subring `Aₐ`. -/
lemma exists_unit_symm (a b : G.ι) (r : G.κ a b) (hi : S.basicOpen (G.f a b r) ≤ G.U b) :
    ∃ e : G.κ b a → Γ(S, S.basicOpen (G.f a b r)),
      (∀ q, e q ∈ localizationSubring (l.A a) (G.f a b r) (S.basicOpen (G.f a b r)) le_rfl) ∧
      ∑ q, e q * S.resLE hi (G.f b a q) = 1 := by
  obtain ⟨c, hc, hsum⟩ := l.unit_symm a b r
  refine ⟨fun q ↦ S.resLE (G.basicOpen_f a b r).le (c q), fun q ↦ ?_, ?_⟩
  · have := resLE_mem_localizationSubring_of_mem le_rfl (G.basicOpen_f a b r).le (hc q)
    rw [l.localization_eq a b r]
    exact this
  · have := congrArg (S.resLE (G.basicOpen_f a b r).le) hsum
    rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [map_mul, resLE_resLE_apply]

lemma range_toChart_subset (a b : G.ι) : Set.range (l.toChart a b) ⊆ l.overlap b a :=
  range_subset_iSup_basicOpen (l.fElem a b) (G.U a).2 rfl (l.inf_eq_iSup_basicOpen a b)
    inf_le_left _ inf_le_right _ (l.chartLiftOverlap_toChart a b) (l.fElem b a)
    fun r hi ↦ l.exists_unit_symm a b r hi

/-- The transition map `⋃_r D(f a b r) ⟶ ⋃_q D(f b a q)` of the gluing datum. -/
noncomputable def trans (a b : G.ι) : (l.overlap a b).toScheme ⟶ (l.overlap b a).toScheme :=
  IsOpenImmersion.lift (l.overlap b a).ι (l.toChart a b) (by
    rw [Scheme.Opens.range_ι]
    exact l.range_toChart_subset a b)

@[reassoc (attr := simp)]
lemma trans_ι (a b : G.ι) : l.trans a b ≫ (l.overlap b a).ι = l.toChart a b :=
  IsOpenImmersion.lift_fac _ _ _

lemma trans_self (a : G.ι) : l.trans a a = 𝟙 _ := by
  rw [← cancel_mono (l.overlap a a).ι]
  refine l.overlap_hom_ext a a _ _ ?_
  rw [trans_ι, chartLiftOverlap_toChart, Category.id_comp, chartLiftOverlap_ι]

/-! ### Triple overlaps -/

/-- The products `f a b r * f a c s` of basic-open elements, whose basic opens cover the triple
overlap. -/
def fElemMul (a b c : G.ι) (p : G.κ a b × G.κ a c) : l.A a :=
  l.fElem a b p.1 * l.fElem a c p.2

lemma overlap_inf_overlap (a b c : G.ι) :
    l.overlap a b ⊓ l.overlap a c = ⨆ p, chartBasicOpen (l.A a) (l.fElemMul a b c p) := by
  rw [overlap, overlap, iSup_inf_iSup]
  exact iSup_congr fun p ↦ (specBasicOpen_mul _ _).symm

lemma inf_inf_eq_iSup_basicOpen (a b c : G.ι) :
    ((G.U a : S.Opens) ⊓ G.U b) ⊓ ((G.U a : S.Opens) ⊓ G.U c) =
      ⨆ p, S.basicOpen ((l.fElemMul a b c p : l.A a) : Γ(S, G.U a)) := by
  rw [l.inf_eq_iSup_basicOpen a b, l.inf_eq_iSup_basicOpen a c, iSup_inf_iSup]
  simp_rw [fElemMul, Subring.coe_mul, Scheme.basicOpen_mul]

lemma range_subringChart_subset_inf (a b c : G.ι) :
    Set.range (subringChart (l.A a) (inf_le_left.trans inf_le_left :
      ((G.U a : S.Opens) ⊓ G.U b) ⊓ ((G.U a : S.Opens) ⊓ G.U c) ≤ G.U a)) ⊆
      ((l.overlap a b ⊓ l.overlap a c : (Spec (l.ring a)).Opens) : Set (Spec (l.ring a))) := by
  rw [l.overlap_inf_overlap]
  exact range_subringChart_subset _ _ _ (l.inf_inf_eq_iSup_basicOpen a b c).le

/-- The chart lift of the triple overlap. -/
noncomputable def chartLiftInf (a b c : G.ι) :
    (((G.U a : S.Opens) ⊓ G.U b) ⊓ ((G.U a : S.Opens) ⊓ G.U c)).toScheme ⟶
      (l.overlap a b ⊓ l.overlap a c).toScheme :=
  chartLift (l.A a) (inf_le_left.trans inf_le_left) _ (l.range_subringChart_subset_inf a b c)

@[reassoc]
lemma chartLiftInf_homOfLE_left (a b c : G.ι) :
    l.chartLiftInf a b c ≫ (Spec (l.ring a)).homOfLE inf_le_left =
      S.homOfLE inf_le_left ≫ l.chartLiftOverlap a b :=
  (homOfLE_chartLift _ _ _ _ _ _).symm

@[reassoc]
lemma chartLiftInf_homOfLE_right (a b c : G.ι) :
    l.chartLiftInf a b c ≫ (Spec (l.ring a)).homOfLE inf_le_right =
      S.homOfLE inf_le_right ≫ l.chartLiftOverlap a c :=
  (homOfLE_chartLift _ _ _ _ _ _).symm

/-- Morphisms out of the triple overlap into an affine scheme are determined by their
restriction along the chart lift. -/
lemma overlap_inf_hom_ext (a b c : G.ι) {R : CommRingCat.{u}}
    (f g : (l.overlap a b ⊓ l.overlap a c).toScheme ⟶ Spec R)
    (h : l.chartLiftInf a b c ≫ f = l.chartLiftInf a b c ≫ g) : f = g :=
  chartLift_cancel (l.fElemMul a b c) (G.U a).2 (l.overlap_inf_overlap a b c)
    (l.inf_inf_eq_iSup_basicOpen a b c) _ _ f g h

lemma chartLiftInf_toChart (a b c : G.ι) :
    l.chartLiftInf a b c ≫ (Spec (l.ring a)).homOfLE inf_le_left ≫ l.toChart a b =
      subringChart (l.A b) ((inf_le_left.trans inf_le_right :
        ((G.U a : S.Opens) ⊓ G.U b) ⊓ ((G.U a : S.Opens) ⊓ G.U c) ≤ G.U b)) := by
  rw [chartLiftInf_homOfLE_left_assoc, chartLiftOverlap_toChart, homOfLE_subringChart]

/-- The unit condition `unit_triple`, in the form needed for the image criterion. -/
lemma exists_unit_triple (a b c : G.ι) (p : G.κ a b × G.κ a c)
    (hi : S.basicOpen ((l.fElemMul a b c p : l.A a) : Γ(S, G.U a)) ≤ G.U b) :
    ∃ e : G.κ b c → Γ(S, S.basicOpen ((l.fElemMul a b c p : l.A a) : Γ(S, G.U a))),
      (∀ q, e q ∈ localizationSubring (l.A a) ((l.fElemMul a b c p : l.A a) : Γ(S, G.U a))
        (S.basicOpen ((l.fElemMul a b c p : l.A a) : Γ(S, G.U a))) le_rfl) ∧
      ∑ q, e q * S.resLE hi ((l.fElem b c q : l.A b) : Γ(S, G.U b)) = 1 :=
  l.unit_triple a b c p.1 p.2

lemma trans_mem (a b c : G.ι) (x : l.overlap a b) (hx : x.1 ∈ l.overlap a c) :
    (l.trans a b x).1 ∈ l.overlap b c := by
  have hrange := range_subset_iSup_basicOpen (l.fElemMul a b c) (G.U a).2
    (l.overlap_inf_overlap a b c) (l.inf_inf_eq_iSup_basicOpen a b c) _
    (l.range_subringChart_subset_inf a b c) _ _ (l.chartLiftInf_toChart a b c) (l.fElem b c)
    fun p hi ↦ l.exists_unit_triple a b c p hi
  have h1 : (l.trans a b x).1 = l.toChart a b x := by
    rw [← trans_ι, Scheme.Hom.comp_apply]
    rfl
  set x' : (l.overlap a b ⊓ l.overlap a c).toScheme := ⟨x.1, x.2, hx⟩
  have h2 : (Spec (l.ring a)).homOfLE inf_le_left x' = x := Scheme.homOfLE_apply' _ _ _
  rw [h1, ← h2, ← Scheme.Hom.comp_apply]
  exact hrange ⟨x', rfl⟩

lemma cocycle (a b c : G.ι) (H) :
    IsOpenImmersion.lift (l.overlap b c).ι
        ((Spec (l.ring a)).homOfLE (inf_le_left : l.overlap a b ⊓ l.overlap a c ≤ l.overlap a b) ≫
          l.trans a b ≫ (l.overlap b a).ι) H ≫ l.trans b c ≫ (l.overlap c b).ι =
      (Spec (l.ring a)).homOfLE (inf_le_right : l.overlap a b ⊓ l.overlap a c ≤ l.overlap a c) ≫
        l.trans a c ≫ (l.overlap c a).ι := by
  have hlift : l.chartLiftInf a b c ≫ IsOpenImmersion.lift (l.overlap b c).ι
      ((Spec (l.ring a)).homOfLE inf_le_left ≫ l.trans a b ≫ (l.overlap b a).ι) H =
      S.homOfLE (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) ≫
        l.chartLiftOverlap b c := by
    rw [← cancel_mono (l.overlap b c).ι, Category.assoc, IsOpenImmersion.lift_fac, trans_ι,
      chartLiftInf_toChart, Category.assoc, chartLiftOverlap_ι, homOfLE_subringChart]
  refine l.overlap_inf_hom_ext a b c _ _ ?_
  rw [reassoc_of% hlift, trans_ι, chartLiftOverlap_toChart, homOfLE_subringChart,
    trans_ι, chartLiftInf_homOfLE_right_assoc, chartLiftOverlap_toChart, homOfLE_subringChart]

/-- The gluing datum of a stage: the charts `Spec Aₐ`, glued along the overlaps
`⋃_r D(f a b r)`. -/
noncomputable def glueData : Scheme.OpensGlueData.{u} where
  J := G.ι
  U a := Spec (l.ring a)
  V := l.overlap
  V_self := l.overlap_self
  t := l.trans
  t_self := l.trans_self
  t_mem := l.trans_mem
  cocycle a b c := l.cocycle a b c _

/-- The finite-type scheme `S_l` of a valid stage `l` (with coefficient subrings
`Aₐ ⊆ Γ(S, Uₐ)`), obtained by gluing the charts `Spec Aₐ` along the overlaps
`⋃_r D(f a b r) ⊆ Spec Aₐ`, the overlap maps being induced by the equalities
`Aₐ[1/f a b r] = A_b[1/g a b r]` inside `Γ(S, D(f a b r))`. -/
noncomputable def scheme : Scheme.{u} := l.glueData.glued

/-- The open immersion of the chart `Spec Aₐ` into the glued scheme. -/
noncomputable def ι (a : G.ι) : Spec (l.ring a) ⟶ l.scheme := l.glueData.ι a

instance (a : G.ι) : IsOpenImmersion (l.ι a) :=
  inferInstanceAs (IsOpenImmersion (l.glueData.ι a))

@[reassoc]
lemma glue_condition (a b : G.ι) :
    l.trans a b ≫ (l.overlap b a).ι ≫ l.ι b = (l.overlap a b).ι ≫ l.ι a :=
  l.glueData.glue_condition a b

lemma iSup_opensRange_ι : ⨆ a, (l.ι a).opensRange = ⊤ :=
  l.glueData.iSup_opensRange_ι

lemma preimage_opensRange_ι (a b : G.ι) : l.ι a ⁻¹ᵁ (l.ι b).opensRange = l.overlap a b :=
  l.glueData.preimage_opensRange_ι a b

lemma hom_ext {Y : Scheme.{u}} {f₁ f₂ : l.scheme ⟶ Y} (h : ∀ a, l.ι a ≫ f₁ = l.ι a ≫ f₂) :
    f₁ = f₂ :=
  l.glueData.hom_ext h

/-- Opens of the glued scheme are determined by their preimages in the charts. -/
lemma opens_ext {O₁ O₂ : l.scheme.Opens} (h : ∀ a, l.ι a ⁻¹ᵁ O₁ = l.ι a ⁻¹ᵁ O₂) : O₁ = O₂ := by
  ext x
  obtain ⟨a, y, rfl⟩ := l.glueData.ι_jointly_surjective x
  exact SetLike.ext_iff.mp (h a) y

instance compactSpace_scheme : CompactSpace l.scheme := by
  have : Finite l.glueData.J := inferInstanceAs (Finite G.ι)
  have (a : l.glueData.J) : CompactSpace (l.glueData.U a) :=
    inferInstanceAs (CompactSpace (Spec (l.ring a)))
  exact inferInstanceAs (CompactSpace l.glueData.glued)

instance locallyOfFiniteType_scheme :
    LocallyOfFiniteType (specULiftZIsTerminal.from l.scheme) := by
  refine (l.glueData.iff_forall_ι_comp @LocallyOfFiniteType _).mpr fun a ↦ ?_
  rw [specULiftZIsTerminal.hom_ext (l.glueData.ι a ≫ _) (specULiftZIsTerminal.from _)]
  exact locallyOfFiniteType_specULiftZIsTerminal_from (l.A a)

/-! ### Transition morphisms -/

variable {l} {l' : G.Stage} (hll : l ≤ l')

/-- The inclusion of coefficient rings `Aₐ ⊆ A'ₐ` for stages `l ≤ l'`. -/
abbrev incl (a : G.ι) : l.ring a ⟶ l'.ring a :=
  CommRingCat.ofHom (Subring.inclusion (hll a))

lemma incl_refl (a : G.ι) : incl (le_refl l) a = 𝟙 _ :=
  rfl

lemma SpecMap_incl_preimage_overlap (a b : G.ι) :
    Spec.map (incl hll a) ⁻¹ᵁ l.overlap a b = l'.overlap a b := by
  rw [overlap, Scheme.Hom.preimage_iSup]
  rfl

/-- The map of overlaps induced by `l ≤ l'`. -/
noncomputable def overlapMap (a b : G.ι) : (l'.overlap a b).toScheme ⟶ (l.overlap a b).toScheme :=
  IsOpenImmersion.lift (l.overlap a b).ι ((l'.overlap a b).ι ≫ Spec.map (incl hll a)) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : x.1 ∈ Spec.map (incl hll a) ⁻¹ᵁ l.overlap a b := by
      rw [SpecMap_incl_preimage_overlap]
      exact x.2
    exact hx)

@[reassoc (attr := simp)]
lemma overlapMap_ι (a b : G.ι) :
    overlapMap hll a b ≫ (l.overlap a b).ι = (l'.overlap a b).ι ≫ Spec.map (incl hll a) :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
lemma chartLiftOverlap_overlapMap (a b : G.ι) :
    l'.chartLiftOverlap a b ≫ overlapMap hll a b = l.chartLiftOverlap a b := by
  rw [← cancel_mono (l.overlap a b).ι, Category.assoc, overlapMap_ι, chartLiftOverlap_ι_assoc,
    chartLiftOverlap_ι, subringChart_comp_SpecMap_inclusion]

@[reassoc]
lemma trans_comp_SpecMap_incl (a b : G.ι) :
    l'.trans a b ≫ (l'.overlap b a).ι ≫ Spec.map (incl hll b) =
      overlapMap hll a b ≫ l.trans a b ≫ (l.overlap b a).ι := by
  refine l'.overlap_hom_ext a b _ _ ?_
  rw [trans_ι_assoc, chartLiftOverlap_toChart_assoc, subringChart_comp_SpecMap_inclusion,
    chartLiftOverlap_overlapMap_assoc, trans_ι, chartLiftOverlap_toChart]

@[reassoc]
lemma comp_SpecMap_incl_ι (a b : G.ι) :
    l'.trans a b ≫ (l'.overlap b a).ι ≫ Spec.map (incl hll b) ≫ l.ι b =
      (l'.overlap a b).ι ≫ Spec.map (incl hll a) ≫ l.ι a := by
  rw [trans_comp_SpecMap_incl_assoc, glue_condition, overlapMap_ι_assoc]

/-- The transition morphism `S_{l'} ⟶ S_l` for stages `l ≤ l'`, induced by the inclusions of the
coefficient subrings. -/
noncomputable def transition : l'.scheme ⟶ l.scheme :=
  l'.glueData.glueMorphisms (fun a ↦ Spec.map (incl hll a) ≫ l.ι a) (comp_SpecMap_incl_ι hll)

@[reassoc (attr := simp)]
lemma ι_transition (a : G.ι) : l'.ι a ≫ transition hll = Spec.map (incl hll a) ≫ l.ι a :=
  l'.glueData.ι_glueMorphisms _ _ a

lemma transition_preimage_opensRange_ι (a : G.ι) :
    transition hll ⁻¹ᵁ (l.ι a).opensRange = (l'.ι a).opensRange := by
  refine l'.opens_ext fun b ↦ ?_
  rw [← Scheme.Hom.comp_preimage, ι_transition, Scheme.Hom.comp_preimage, preimage_opensRange_ι,
    SpecMap_incl_preimage_overlap, preimage_opensRange_ι]

/-- The transition morphisms are affine. -/
instance isAffineHom_transition : IsAffineHom (transition hll) := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x ↦ ?_
  have hx : x ∈ (⊤ : l.scheme.Opens) := trivial
  rw [← l.iSup_opensRange_ι] at hx
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨(l.ι a).opensRange, ha, isAffineOpen_opensRange _, ?_⟩
  rw [transition_preimage_opensRange_ι]
  exact isAffineOpen_opensRange _

/-- The transition morphisms satisfy the identity law. -/
lemma transition_refl : transition (le_refl l) = 𝟙 _ :=
  l.hom_ext fun a ↦ by
    rw [ι_transition, Category.comp_id, incl_refl, Spec.map_id, Category.id_comp]

/-- The transition morphisms satisfy the composition law. -/
lemma transition_trans {l'' : G.Stage} (hll' : l' ≤ l'') :
    transition (hll.trans hll') = transition hll' ≫ transition hll :=
  l''.hom_ext fun a ↦ by
    rw [ι_transition, ι_transition_assoc, ι_transition, ← Spec.map_comp_assoc]
    rfl

end Stage

/-- The diagram of the finite-type stages `S_l`, indexed by the opposite of the directed set of
valid stages, with the transition morphisms `S_{l'} ⟶ S_l` for `l ≤ l'`. -/
noncomputable def stageDiagram (G : S.FiniteAffineGluingPresentation) :
    (G.Stage)ᵒᵖ ⥤ Scheme.{u} where
  obj l := l.unop.scheme
  map f := Stage.transition (leOfHom f.unop)
  map_id _ := Stage.transition_refl
  map_comp f g := Stage.transition_trans (leOfHom g.unop) (leOfHom f.unop)

@[simp]
lemma stageDiagram_obj (l : (G.Stage)ᵒᵖ) : G.stageDiagram.obj l = l.unop.scheme := rfl

@[simp]
lemma stageDiagram_map {l l' : (G.Stage)ᵒᵖ} (f : l ⟶ l') :
    G.stageDiagram.map f = Stage.transition (leOfHom f.unop) := rfl

/-- Every glued stage `S_l` is quasi-compact and locally of finite type over `ℤ`, and every
transition morphism `S_{l'} ⟶ S_l` is affine. -/
theorem stage_finiteType_isAffineHom (l : G.Stage) :
    LocallyOfFiniteType (specULiftZIsTerminal.from l.scheme) ∧ CompactSpace l.scheme ∧
      ∀ (l' : G.Stage) (h : l ≤ l'), IsAffineHom (Stage.transition h) :=
  ⟨inferInstance, inferInstance, fun _ _ ↦ inferInstance⟩

end AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation
