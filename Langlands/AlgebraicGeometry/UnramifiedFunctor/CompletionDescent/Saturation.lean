import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.ChartDatum
import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.Puncture
import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.Completion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Saturated opens of the base change to the completion

Let `R` be a noetherian local ring, `π : Spec R̂ ⟶ Spec R` the completion map and
`U ⊆ Spec R` the punctured spectrum. Let `q' : X' ⟶ Spec R̂` represent `F ×_S Spec R̂` and
`q_U : X_U ⟶ U` represent `F ×_S U`, and let `σ : X' ×_S Spec R̂ ⟶ X'` be as in
`exists_sigma`. For a point `z` of `X' ×_S Spec R̂` lying over the closed point of `Spec R`,
`σ z` is the first projection of `z`; for a point over `U`, `σ z` and the first projection of
`z` lie in the part `P'` of `X'` over `π⁻¹(U)` and have the same image under
`puncMap : P' ⟶ X_U`. Consequently every open of the form `O' ∪ ι(puncMap⁻¹ M)`, with
`puncMap(ι⁻¹ O') ⊆ M`, is saturated for `σ`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent

variable {R : CommRingCat.{u}} [IsLocalRing R] [IsNoetherianRing R]
  {F : (Over (Spec R))ᵒᵖ ⥤ Type v} {X' : Scheme.{u}}
  {q' : X' ⟶ Spec (CommRingCat.of (AdicCompletion (maximalIdeal R) R))}
  (e : (baseChange (completionMap R) F).RepresentableBy (Over.mk q'))
  {XU : Scheme.{u}} {qU : XU ⟶ puncturedSpectrum R}
  (eU : (baseChange (puncturedSpectrum R).ι F).RepresentableBy (Over.mk qU))
  {σ : pullback (q' ≫ completionMap R) (completionMap R) ⟶ X'}
  (hσ : σ ≫ q' = pullback.snd _ _)
  (hσpt : pt e (prodOver q' (completionMap R)) σ (sigma_comp_eq hσ) =
    pt e (prodOver q' (completionMap R)) (pullback.fst _ _) (fst_comp_eq q' (completionMap R)))

/-- The residue field point `Spec κ(z) ⟶ X' ×_S Spec R̂` at `z`, as an object over `Spec R`. -/
abbrev resOver (z : ↥(pullback (C := Scheme.{u}) (q' ≫ completionMap R) (completionMap R))) : Over (Spec R) :=
  Over.mk (Scheme.fromSpecResidueField _ z ≫ pullback.snd _ _ ≫ completionMap R)

omit [IsNoetherianRing R] in
include hσ hσpt in
lemma pt_res (z : ↥(pullback (C := Scheme.{u}) (q' ≫ completionMap R) (completionMap R))) :
    pt e (resOver z) (Scheme.fromSpecResidueField _ z ≫ σ)
      (by rw [Category.assoc, sigma_comp_eq hσ]; rfl) =
      pt e (resOver z) (Scheme.fromSpecResidueField _ z ≫ pullback.fst _ _)
        (by rw [Category.assoc, fst_comp_eq]; rfl) :=
  pt_sigma e hσ hσpt (resOver z) (Scheme.fromSpecResidueField _ z) rfl

omit [IsNoetherianRing R] in
include hσ in
lemma sigma_apply_comp (z : ↥(pullback (C := Scheme.{u}) (q' ≫ completionMap R) (completionMap R))) :
    completionMap R (q' (σ z)) =
      completionMap R (q' (pullback.fst (q' ≫ completionMap R) (completionMap R) z)) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply, sigma_comp_eq hσ, fst_comp_eq q' (completionMap R)]

include hσ hσpt in
/-- Over the closed point of `Spec R`, `σ` is the first projection. -/
lemma sigma_apply_eq_of_closed (z : ↥(pullback (C := Scheme.{u}) (q' ≫ completionMap R) (completionMap R)))
    (hz : completionMap R (q' (pullback.fst (q' ≫ completionMap R) (completionMap R) z)) = closedPoint R) :
    σ z = pullback.fst (q' ≫ completionMap R) (completionMap R) z := by
  let ρ := Scheme.fromSpecResidueField _ z
  let x : Spec ((pullback (q' ≫ completionMap R) (completionMap R)).residueField z) :=
    closedPoint _
  have hx₀ : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  have hsq : (ρ ≫ pullback.fst _ _ ≫ q') ≫ completionMap R =
      (ρ ≫ σ ≫ q') ≫ completionMap R := by
    simp only [Category.assoc]
    rw [sigma_comp_eq hσ, fst_comp_eq]
  have hab := eq_of_comp_completionMap_eq R hsq x hx₀ (by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact hz)
  have h := pt_inj e (T := resOver z) (a := ρ ≫ σ) (b := ρ ≫ pullback.fst _ _)
    (by rw [Category.assoc, sigma_comp_eq hσ]; rfl) (by rw [Category.assoc, fst_comp_eq]; rfl)
    (by simp only [Category.assoc]; exact hab.symm) (pt_res e hσ hσpt z)
  have h₂ : (ρ ≫ σ) x = (ρ ≫ pullback.fst _ _) x := by rw [h]
  rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at h₂

omit [IsNoetherianRing R] in
lemma mem_range_puncι (y : X') (hy : completionMap R (q' y) ≠ closedPoint R) :
    y ∈ Set.range (puncι (completionMap R) (puncturedSpectrum R) q') := by
  rw [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Opens.range_ι]
  exact hy

omit [IsNoetherianRing R] in
include hσ hσpt in
/-- Over the punctured spectrum, `σ z` and the first projection of `z` come from points of
`P'` with the same image under `puncMap`. -/
lemma exists_puncMap_eq (z : ↥(pullback (C := Scheme.{u}) (q' ≫ completionMap R) (completionMap R)))
    (hz : completionMap R (q' (pullback.fst (q' ≫ completionMap R) (completionMap R) z)) ≠ closedPoint R) :
    ∃ a b : puncSource (completionMap R) (puncturedSpectrum R) q',
      puncι (completionMap R) (puncturedSpectrum R) q' a =
          pullback.fst (q' ≫ completionMap R) (completionMap R) z ∧
        puncι (completionMap R) (puncturedSpectrum R) q' b = σ z ∧
        puncMap (completionMap R) (puncturedSpectrum R) e eU a =
          puncMap (completionMap R) (puncturedSpectrum R) e eU b := by
  let ρ := Scheme.fromSpecResidueField _ z
  have h₁ : Set.range (ρ ≫ pullback.fst _ _) ⊆
      Set.range (puncι (completionMap R) (puncturedSpectrum R) q') := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact mem_range_puncι _ hz
  have h₂ : Set.range (ρ ≫ σ) ⊆
      Set.range (puncι (completionMap R) (puncturedSpectrum R) q') := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    apply mem_range_puncι
    rw [sigma_apply_comp hσ]
    exact hz
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Spec (Scheme.residueField _ z) ⟶
      puncSource (completionMap R) (puncturedSpectrum R) q',
      a₀ ≫ puncι (completionMap R) (puncturedSpectrum R) q' = ρ ≫ pullback.fst _ _ :=
    ⟨IsOpenImmersion.lift _ _ h₁, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Spec (Scheme.residueField _ z) ⟶
      puncSource (completionMap R) (puncturedSpectrum R) q',
      b₀ ≫ puncι (completionMap R) (puncturedSpectrum R) q' = ρ ≫ σ :=
    ⟨IsOpenImmersion.lift _ _ h₂, IsOpenImmersion.lift_fac _ _ _⟩
  have ha : a₀ ≫ puncι (completionMap R) (puncturedSpectrum R) q' ≫ q' ≫ completionMap R =
      (resOver z).hom := by
    rw [reassoc_of% ha₀, fst_comp_eq]; rfl
  have hb : b₀ ≫ puncι (completionMap R) (puncturedSpectrum R) q' ≫ q' ≫ completionMap R =
      (resOver z).hom := by
    rw [reassoc_of% hb₀, sigma_comp_eq hσ]; rfl
  have key := puncMap_eq_of_pt_eq (completionMap R) (puncturedSpectrum R) e eU ha hb
    ((pt_congr e ha₀ _ _).trans ((pt_res e hσ hσpt z).symm.trans (pt_congr e hb₀.symm _ _)))
  let x : Spec ((pullback (q' ≫ completionMap R) (completionMap R)).residueField z) :=
    closedPoint _
  refine ⟨a₀ x, b₀ x, ?_, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ha₀, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  · rw [← Scheme.Hom.comp_apply, hb₀, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  · rw [← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply]

/-- The open `O' ∪ ι(puncMap⁻¹ M)` of `X'`. -/
def satOpen (O' : X'.Opens) (M : XU.Opens) : X'.Opens :=
  O' ⊔ puncι (completionMap R) (puncturedSpectrum R) q' ''ᵁ
    (puncMap (completionMap R) (puncturedSpectrum R) e eU ⁻¹ᵁ M)

include hσ hσpt in
/-- `O' ∪ ι(puncMap⁻¹ M)` is saturated for `σ` when `puncMap(ι⁻¹ O') ⊆ M`. -/
lemma mem_satOpen (O' : X'.Opens) (M : XU.Opens)
    (hOM : ∀ a, puncι (completionMap R) (puncturedSpectrum R) q' a ∈ O' →
      puncMap (completionMap R) (puncturedSpectrum R) e eU a ∈ M)
    (z : ↥(pullback (C := Scheme.{u}) (q' ≫ completionMap R) (completionMap R)))
    (hz : pullback.fst (q' ≫ completionMap R) (completionMap R) z ∈ satOpen e eU O' M) : σ z ∈ satOpen e eU O' M := by
  by_cases hc : completionMap R (q' (pullback.fst (q' ≫ completionMap R) (completionMap R) z)) = closedPoint R
  · rw [sigma_apply_eq_of_closed e hσ hσpt z hc]
    exact hz
  · obtain ⟨a, b, ha, hb, hab⟩ := exists_puncMap_eq e eU hσ hσpt z hc
    have hbM : puncMap (completionMap R) (puncturedSpectrum R) e eU b ∈ M := by
      rcases hz with hz | ⟨a', ha'M, ha'⟩
      · rw [← hab]
        exact hOM a (ha ▸ hz)
      · have : a' = a :=
          (puncι (completionMap R) (puncturedSpectrum R) q').isOpenEmbedding.injective
            (ha'.trans ha.symm)
        rw [← hab, ← this]
        exact ha'M
    exact Or.inr ⟨b, hbM, hb⟩

include hσ hσpt in
lemma sat_satOpen (O' : X'.Opens) (M : XU.Opens)
    (hOM : ∀ a, puncι (completionMap R) (puncturedSpectrum R) q' a ∈ O' →
      puncMap (completionMap R) (puncturedSpectrum R) e eU a ∈ M) :
    ∀ z, pullback.fst (q' ≫ completionMap R) (completionMap R) z ∈
      Set.range (satOpen e eU O' M).ι → σ z ∈ Set.range (satOpen e eU O' M).ι := by
  intro z hz
  rw [Scheme.Opens.range_ι] at hz ⊢
  exact mem_satOpen e eU hσ hσpt O' M hOM z hz

omit [IsNoetherianRing R] in
lemma isCompact_satOpen {O' : X'.Opens} {M : XU.Opens} (hO : IsCompact (O' : Set X'))
    (hM : IsCompact (M : Set XU)) : IsCompact (satOpen e eU O' M : Set X') := by
  have := isAffineHom_puncMap (completionMap R) (puncturedSpectrum R) e eU
  refine hO.union ?_
  exact (QuasiCompact.isCompact_preimage
    (f := puncMap (completionMap R) (puncturedSpectrum R) e eU) _ M.isOpen hM).image
    (puncι (completionMap R) (puncturedSpectrum R) q').continuous

omit [IsNoetherianRing R] in
/-- Every compact subset of `X'` lies in a saturated open `O' ∪ ι(puncMap⁻¹ M)` with `O'` and
`M` compact and `puncMap(ι⁻¹ O') ⊆ M`. -/
lemma exists_satOpen [IsNoetherianRing (AdicCompletion (maximalIdeal R) R)]
    [LocallyOfFiniteType q'] {K : Set X'} (hK : IsCompact K) :
    ∃ (O' : X'.Opens) (M : XU.Opens), IsCompact (O' : Set X') ∧ IsCompact (M : Set XU) ∧
      (∀ a, puncι (completionMap R) (puncturedSpectrum R) q' a ∈ O' →
        puncMap (completionMap R) (puncturedSpectrum R) e eU a ∈ M) ∧ K ⊆ O' := by
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian q'
  obtain ⟨O, hOc, hOo, hKO, -⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hK isOpen_univ (Set.subset_univ _)
  have hc : IsCompact (puncMap (completionMap R) (puncturedSpectrum R) e eU ''
      (puncι (completionMap R) (puncturedSpectrum R) q' ⁻¹' O)) :=
    (QuasiCompact.isCompact_preimage
      (f := puncι (completionMap R) (puncturedSpectrum R) q') _ hOo hOc).image
      (puncMap (completionMap R) (puncturedSpectrum R) e eU).continuous
  obtain ⟨M, hMc, hMo, hcM, -⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hc isOpen_univ (Set.subset_univ _)
  exact ⟨⟨O, hOo⟩, ⟨M, hMo⟩, hOc, hMc, fun a ha ↦ hcM ⟨a, ha, rfl⟩, hKO⟩

end Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent
