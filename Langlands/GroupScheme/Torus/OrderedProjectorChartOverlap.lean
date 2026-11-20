import Langlands.GroupScheme.Torus.OrderedProjectorOverlapLocal
import Langlands.AlgebraicGeometry.Morphisms.FiniteCoproduct

/-! # The finite étale overlap of two ordered projector charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.GroupScheme.OrderedProjectorScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : CommRingCat.{u}} {J K n : Type} [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]

/-- The morphism of projector schemes given by relabelling the projectors. -/
def relabelMap (e : J ≃ K) : scheme K n R ⟶ scheme J n R :=
  (pointsEquiv J n R (scheme K n R)).symm ((pointsEquiv K n R _ (𝟙 _)).relabel e)

/-- The relabelling morphism relabels the family at every point. -/
theorem pointsEquiv_comp_relabelMap (e : J ≃ K) {T : Over (Spec R)}
    (x : T ⟶ scheme K n R) :
    pointsEquiv J n R T (x ≫ relabelMap e) = (pointsEquiv K n R T x).relabel e := by
  rw [pointsEquiv_naturality, relabelMap, Equiv.apply_symm_apply]
  have hx := pointsEquiv_naturality K n R x (𝟙 (scheme K n R))
  rw [Category.comp_id] at hx
  rw [hx]
  exact Family.ext rfl

section Overlap

variable {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']
  {w : J → Λ} {v : K → Λ'} {M : Over (Spec R)} {L : GroupScheme M.left}
  {j : L ⟶ (baseChange M.hom).obj (GeneralLinear.groupScheme n R)}
  (hj : IsClosedSubgroup j) (hL : RelativeTorus.IsTorus L) (hu : TorusSubgroupModuli.IsUniversal j)
  (hw : AddSubgroup.closure (Set.range w) = ⊤)
  (hv : AddSubgroup.closure (Set.range v) = ⊤)
  (hs : IsSplitTorus (Diagonalizable.groupScheme R Λ).toGrp)
  (ht : IsSplitTorus (Diagonalizable.groupScheme R Λ').toGrp)

local notation "firstChartMap" => chartMap w j hu hw hs
local notation "secondChartMap" => chartMap v j hu hv ht

include hj hL in
/-- Matching systems of weights give the same moduli map after relabelling. -/
theorem relabelMap_comp_chartMap (e : WeightEquivalence w v) :
    relabelMap e.labels ≫ firstChartMap = secondChartMap := by
  have h := evaluate_comp_chartMap w j hu hw hs (relabelMap e.labels)
  have hh := pointsEquiv_comp_relabelMap (n := n) (R := R) e.labels (𝟙 (scheme K n R))
  rw [Category.id_comp] at hh
  rw [hh, range_subgroupHom_eq_of_relabel] at h
  have he : TorusSubgroupModuli.evaluate j (relabelMap e.labels ≫ firstChartMap) =
      TorusSubgroupModuli.evaluate j secondChartMap := (evaluate_chartMap v j hu hv ht).symm ▸ h
  obtain ⟨x, hx, huniq⟩ := hu _ _ (TorusSubgroupModuli.isAdmissible_evaluate j hj hL secondChartMap)
  exact (huniq _ he).trans (huniq _ rfl).symm

/-- The overlap of two ordered projector charts, with its original base structure. -/
def chartOverlap : Over (Spec R) :=
  Over.mk (pullback.fst (firstChartMap).left (secondChartMap).left ≫ (scheme J n R).hom)

private def firstProjection : chartOverlap hu hw hv hs ht ⟶ scheme J n R :=
  Over.homMk (pullback.fst (firstChartMap).left (secondChartMap).left) rfl

private def secondProjection : chartOverlap hu hw hv hs ht ⟶ scheme K n R :=
  Over.homMk (pullback.snd (firstChartMap).left (secondChartMap).left) (by
    change pullback.snd (firstChartMap).left (secondChartMap).left ≫ (scheme K n R).hom =
      pullback.fst (firstChartMap).left (secondChartMap).left ≫ (scheme J n R).hom
    rw [← Over.w secondChartMap, ← Over.w firstChartMap, pullback.condition_assoc])

private theorem projections_comp :
    firstProjection hu hw hv hs ht ≫ firstChartMap =
      secondProjection hu hw hv hs ht ≫ secondChartMap := by
  apply Over.OverMorphism.ext
  exact pullback.condition

local notation "O" => chartOverlap hu hw hv hs ht
local notation "p₁" => firstProjection hu hw hv hs ht
local notation "p₂" => secondProjection hu hw hv hs ht

/-- The section of the second overlap projection for one matching of the weights. -/
def overlapInclusion (e : WeightEquivalence w v) : (scheme K n R).left ⟶ (O).left :=
  pullback.lift (relabelMap e.labels).left (𝟙 _) (by
    rw [Category.id_comp]
    exact congrArg (fun x => x.left) (relabelMap_comp_chartMap hj hL hu hw hv hs ht e))

local notation "iₑ" => overlapInclusion hj hL hu hw hv hs ht

@[reassoc (attr := simp)]
private theorem overlapInclusion_fst (e : WeightEquivalence w v) :
    iₑ e ≫ (p₁).left = (relabelMap e.labels).left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem overlapInclusion_snd (e : WeightEquivalence w v) :
    iₑ e ≫ (p₂).left = 𝟙 _ :=
  pullback.lift_snd _ _ _

private theorem mono_overlapInclusion (e : WeightEquivalence w v) : Mono (iₑ e) := by
  constructor
  intro Z a b h
  simpa only [Category.assoc, overlapInclusion_snd, Category.comp_id] using
    congrArg (fun k => k ≫ (p₂).left) h

private theorem matching_eq_of_comp_eq (hvinj : Function.Injective v)
    (e e' : WeightEquivalence w v) {X : Scheme.{u}} [Nonempty X]
    (a b : X ⟶ (scheme K n R).left) (h : a ≫ iₑ e = b ≫ iₑ e') : e = e' := by
  have hab : a = b := by
    simpa only [Category.assoc, overlapInclusion_snd, Category.comp_id] using
      congrArg (fun k => k ≫ (p₂).left) h
  subst b
  let T : Over (Spec R) := Over.mk (a ≫ (scheme K n R).hom)
  let y : T ⟶ scheme K n R := Over.homMk a rfl
  let : Nonempty T.left := ‹Nonempty X›
  have hxy : y ≫ relabelMap e.labels = y ≫ relabelMap e'.labels := by
    apply Over.OverMorphism.ext
    change a ≫ (relabelMap e.labels).left = a ≫ (relabelMap e'.labels).left
    simpa only [Category.assoc, overlapInclusion_fst] using
      congrArg (fun k => k ≫ (p₁).left) h
  apply eq_of_relabel_eq (pointsEquiv K n R T y) hvinj hv e e'
  rw [← pointsEquiv_comp_relabelMap, ← pointsEquiv_comp_relabelMap, hxy]

variable [AddMonoid.FG Λ'] (hwinj : Function.Injective w) (hvinj : Function.Injective v)

include hwinj hvinj in
private theorem locally_factors (x : (O).left) :
    ∃ (X : Scheme.{u}) (q : X ⟶ (O).left) (e : WeightEquivalence w v),
      IsOpenImmersion q ∧ x ∈ Set.range q ∧ q ≫ (p₂).left ≫ iₑ e = q := by
  let P := pointsEquiv J n R O p₁
  let Q := pointsEquiv K n R O p₂
  have h : SubgroupFunctor.range (subgroupHom w O P) =
      SubgroupFunctor.range (subgroupHom v O Q) := by
    rw [← evaluate_comp_chartMap w j hu hw hs p₁, ← evaluate_comp_chartMap v j hu hv ht p₂,
      projections_comp]
  obtain ⟨d⟩ := nonempty_localWeightMatching P Q hwinj hvinj hw hv h x
  refine ⟨d.scheme.left, d.map.left, d.matching, d.openImmersion, d.contains, ?_⟩
  have hproj : d.map ≫ p₁ = (d.map ≫ p₂) ≫ relabelMap d.matching.labels := by
    apply (pointsEquiv J n R d.scheme).injective
    rw [pointsEquiv_comp_relabelMap, pointsEquiv_naturality, pointsEquiv_naturality]
    exact d.projectors_eq
  apply pullback.hom_ext
  · change _ ≫ (p₁).left = d.map.left ≫ (p₁).left
    simpa only [Category.assoc, overlapInclusion_fst, Over.comp_left] using
      (congrArg (fun a => a.left) hproj).symm
  · change _ ≫ (p₂).left = d.map.left ≫ (p₂).left
    simp only [Category.assoc, overlapInclusion_snd, Category.comp_id]

include hwinj hvinj in
private theorem overlapInclusion_isOpenImmersion (e : WeightEquivalence w v) :
    IsOpenImmersion (iₑ e) := by
  let : Mono (iₑ e) := mono_overlapInclusion hj hL hu hw hv hs ht e
  have loc (y : (scheme K n R).left) :
      ∃ (X : Scheme.{u}) (r : X ⟶ (scheme K n R).left),
        IsOpenImmersion r ∧ y ∈ Set.range r ∧ IsOpenImmersion (r ≫ iₑ e) := by
    obtain ⟨X, q, e', hq, ⟨z, hz⟩, he'⟩ := locally_factors hj hL hu hw hv hs ht hwinj hvinj (iₑ e y)
    let r := q ≫ (p₂).left
    have he'' : r ≫ iₑ e' = q := (Category.assoc _ _ _).trans he'
    obtain ⟨t, _, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := iₑ e) (g := q) y z hz.symm
    let : Nonempty ↥(pullback (C := Scheme.{u}) (iₑ e) q) := ⟨t⟩
    have he : e = e' := matching_eq_of_comp_eq hj hL hu hw hv hs ht hvinj e e'
      (pullback.fst (iₑ e) q) (pullback.snd (iₑ e) q ≫ r) (by
        rw [Category.assoc, he'', pullback.condition])
    subst e'
    have hq' : r ≫ iₑ e = q := he''
    have hpb : IsPullback (𝟙 X) r q (iₑ e) :=
      IsPullback.of_horiz_isIso_mono ⟨(Category.id_comp q).trans hq'.symm⟩
    refine ⟨X, r, MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb hq,
      ⟨z, ?_⟩, hq'.symm ▸ hq⟩
    have h := congrArg (fun x => (p₂).left x) hz
    change r z = (𝟙 (scheme K n R).left) y
    simpa only [r, ← Scheme.Hom.comp_apply, overlapInclusion_snd] using h
  apply IsOpenImmersion.of_forall_source_exists (iₑ e)
  · intro x y h
    change (𝟙 (scheme K n R).left) x = (𝟙 (scheme K n R).left) y
    simpa only [← Scheme.Hom.comp_apply, overlapInclusion_snd] using
      congrArg (fun t => (p₂).left t) h
  · intro y
    obtain ⟨X, r, hr, hy, hopen⟩ := loc y
    exact ⟨X, r, hr, hy, hopen⟩

omit [AddMonoid.FG Λ'] in
include hvinj in
private theorem disjoint_overlapInclusion :
    Pairwise (fun e e' : WeightEquivalence w v => Disjoint (Set.range (iₑ e)) (Set.range (iₑ e'))) := by
  intro e e' hne
  rw [Set.disjoint_left]
  rintro _ ⟨y, rfl⟩ ⟨z, hz⟩
  obtain ⟨t, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := iₑ e) (g := iₑ e') y z hz.symm
  let : Nonempty ↥(pullback (C := Scheme.{u}) (iₑ e) (iₑ e')) := ⟨t⟩
  exact hne (matching_eq_of_comp_eq hj hL hu hw hv hs ht hvinj e e'
    (pullback.fst _ _) (pullback.snd _ _) pullback.condition)

include hwinj hvinj in
/-- The overlap is the disjoint union of copies of the second chart indexed by weight matchings. -/
def overlapIso : (∐ fun _ : WeightEquivalence w v => (scheme K n R).left) ≅ (O).left := by
  let : ∀ e, IsOpenImmersion (iₑ e) := overlapInclusion_isOpenImmersion hj hL hu hw hv hs ht hwinj hvinj
  have hcov : (⨆ e, (iₑ e).opensRange) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨X, q, e, _, ⟨z, hz⟩, he⟩ := locally_factors hj hL hu hw hv hs ht hwinj hvinj x
    refine Opens.mem_iSup.mpr ⟨e, ?_⟩
    exact ⟨(q ≫ (p₂).left) z, (congrArg (fun a : X ⟶ (O).left => a z)
      ((Category.assoc _ _ _).trans he)).trans hz⟩
  have hd : Pairwise (fun e e' => Disjoint (iₑ e).opensRange (iₑ e').opensRange) := by
    intro e e' hne
    exact Opens.coe_disjoint.mp (disjoint_overlapInclusion hj hL hu hw hv hs ht hvinj hne)
  let : IsIso (Sigma.desc iₑ) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk (O).left iₑ)).mp
      (nonempty_isColimit_cofanMk_of iₑ hcov hd)
  exact asIso (Sigma.desc iₑ)

include hj hL hwinj hvinj in
/-- The pullback of the first chart map along the second chart map is finite étale. -/
theorem finiteEtale_secondProjection :
    IsFinite (pullback.snd (firstChartMap).left (secondChartMap).left) ∧
      Etale (pullback.snd (firstChartMap).left (secondChartMap).left) := by
  change IsFinite (p₂).left ∧ Etale (p₂).left
  let X : WeightEquivalence w v → Scheme.{u} := fun _ => (scheme K n R).left
  let h := overlapIso hj hL hu hw hv hs ht hwinj hvinj
  let q : (∐ X) ⟶ (scheme K n R).left := Sigma.desc fun _ => 𝟙 _
  have he : h.hom ≫ (p₂).left = q := by
    apply Sigma.hom_ext
    intro e
    change Sigma.ι X e ≫ Sigma.desc iₑ ≫ (p₂).left = Sigma.ι X e ≫ q
    simp only [Sigma.ι_comp_desc_assoc, overlapInclusion_snd, q, Sigma.ι_comp_desc]
    rfl
  let : Finite (WeightEquivalence w v) := WeightEquivalence.finite w v hv
  have hprop : IsProper q := Langlands.AlgebraicGeometry.FiniteCoproduct.isProper_sigmaDesc X _
    (fun _ => inferInstance)
  let : LocallyQuasiFinite q := IsZariskiLocalAtSource.sigmaDesc (P := @LocallyQuasiFinite)
    (fun _ => inferInstanceAs (LocallyQuasiFinite (𝟙 (scheme K n R).left)))
  have hfin : IsFinite q := IsFinite.of_isProper_of_locallyQuasiFinite _
  have het : Etale q := IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
    (fun _ => inferInstanceAs (Etale (𝟙 (scheme K n R).left)))
  have hEq : (p₂).left = h.inv ≫ q := by rw [← he, Iso.inv_hom_id_assoc]
  rw [hEq]
  exact ⟨MorphismProperty.IsStableUnderComposition.comp_mem _ _ (inferInstanceAs (IsFinite h.inv)) hfin,
    MorphismProperty.IsStableUnderComposition.comp_mem _ _ (inferInstanceAs (Etale h.inv)) het⟩

end Overlap

end Langlands.GroupScheme.OrderedProjectorScheme
