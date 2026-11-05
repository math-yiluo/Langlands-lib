import Langlands.Geometry.Analytic.SaturatedSourceRefinementFractions

/-! # Complete strong restriction and equality on a common source subatlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Nested selections give actual full strong maps with every original
bounded restriction, on the literal original ambient space. -/
def refiningSubatlasMap (A : SaturatedAtlasPresentation.{u, v, w} K)
    {P Q : A.presentation.atlas.RefiningSelection} (h : P ≤ Q) :
    A.refiningSubpresentation P ⟶ A.refiningSubpresentation Q where
  baseMap := ContinuousMap.id A.presentation.space
  target_exists i := ⟨⟨i.val, h i.property⟩, by
    rintro _ ⟨x, hx, rfl⟩
    exact hx⟩
  pullback i j hij := A.presentation.atlas.restriction i.val j.val
    (fun x hx => hij ⟨x, hx, rfl⟩)
  chart_comm i j hij x := A.presentation.atlas.restriction_chart i.val j.val _ x
  restriction_comm i i' j j' hi hj h h' := by
    have hij : Set.range (A.presentation.atlas.chart i.val) ⊆
        Set.range (A.presentation.atlas.chart j.val) := fun x hx => h ⟨x, hx, rfl⟩
    have hi'j' : Set.range (A.presentation.atlas.chart i'.val) ⊆
        Set.range (A.presentation.atlas.chart j'.val) := fun x hx => h' ⟨x, hx, rfl⟩
    exact (A.presentation.atlas.restriction_comp i.val i'.val j'.val hi hi'j'
      (hi.trans hi'j')).symm.trans
        (A.presentation.atlas.restriction_comp i.val j.val j'.val hij hj (hi.trans hi'j'))

@[simp]
theorem refiningSubatlasMap_baseMap {P Q : A.presentation.atlas.RefiningSelection}
    (h : P ≤ Q) :
    (A.refiningSubatlasMap h).baseMap = ContinuousMap.id A.presentation.space := rfl

@[simp]
theorem refiningSubatlasMap_pullback {P Q : A.presentation.atlas.RefiningSelection}
    (h : P ≤ Q) (i : (A.refiningSubpresentation P).presentation.atlas.Index)
    (j : (A.refiningSubpresentation Q).presentation.atlas.Index)
    (hij : (A.refiningSubatlasMap h).baseMap ''
      Set.range ((A.refiningSubpresentation P).presentation.atlas.chart i) ⊆
        Set.range ((A.refiningSubpresentation Q).presentation.atlas.chart j)) :
    (A.refiningSubatlasMap h).pullback i j hij =
      A.presentation.atlas.restriction i.val j.val
        (fun x hx => hij ⟨x, hx, rfl⟩) := rfl

theorem isQuasiIso_refiningSubatlasMap {P Q : A.presentation.atlas.RefiningSelection}
    (h : P ≤ Q) : (A.refiningSubatlasMap h).IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro i j hij
  change PresentedAffinoidAlgebra.Represents K
    (A.presentation.atlas.restriction i.val j.val (fun x hx => hij ⟨x, hx, rfl⟩))
      (A.presentation.atlas.chart j.val ⁻¹'
        (id '' Set.range (A.presentation.atlas.chart i.val)))
  simpa only [Set.image_id] using A.presentation.atlas.restriction_represents i.val j.val
    (fun x hx => hij ⟨x, hx, rfl⟩)

/-- The inclusion diamond holds for all bounded pullbacks. -/
@[simp]
theorem refiningSubatlasMap_inclusion {P Q : A.presentation.atlas.RefiningSelection}
    (h : P ≤ Q) :
    A.refiningSubatlasMap h ≫ A.refiningSubatlasInclusion Q =
      A.refiningSubatlasInclusion P := by
  refine AffinoidAtlasPresentation.StrongHom.ext_of_saturated
    (f := A.refiningSubatlasMap h ≫ A.refiningSubatlasInclusion Q)
    (g := A.refiningSubatlasInclusion P)
    (A.refiningSubpresentation P).hasAllLocalDomains rfl ?_
  intro i
  let j : (A.refiningSubpresentation Q).presentation.atlas.Index :=
    ⟨i.val, h i.property⟩
  have h₁ : (A.refiningSubatlasMap h).baseMap ''
      Set.range ((A.refiningSubpresentation P).presentation.atlas.chart i) ⊆
        Set.range ((A.refiningSubpresentation Q).presentation.atlas.chart j) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have h₂ : (A.refiningSubatlasInclusion Q).baseMap ''
      Set.range ((A.refiningSubpresentation Q).presentation.atlas.chart j) ⊆
        Set.range (A.presentation.atlas.chart i.val) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have h₃ : (A.refiningSubatlasMap h ≫ A.refiningSubatlasInclusion Q).baseMap ''
      Set.range ((A.refiningSubpresentation P).presentation.atlas.chart i) ⊆
        Set.range (A.presentation.atlas.chart i.val) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨i.val, h₃, ?_⟩
  refine (AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback
    (A.refiningSubatlasMap h) (A.refiningSubatlasInclusion Q)
    (A.refiningSubpresentation P).hasAllLocalDomains
    (A.refiningSubpresentation Q).hasAllLocalDomains i j i.val h₁ h₂ h₃).trans ?_
  change (A.presentation.atlas.restriction i.val i.val _).comp
    (A.presentation.atlas.restriction i.val i.val _) =
      A.presentation.atlas.restriction i.val i.val _
  exact (A.presentation.atlas.restriction_comp i.val i.val i.val _ _ _).symm

@[simp]
theorem refiningSubatlasMap_id (P : A.presentation.atlas.RefiningSelection) :
    A.refiningSubatlasMap (le_refl P) = 𝟙 (A.refiningSubpresentation P) := by
  apply (postcompQuasiIsoEmbedding (A.refiningSubatlasInclusion P)
    (isQuasiIso_refiningSubatlasInclusion P)).injective
  change A.refiningSubatlasMap (le_refl P) ≫ A.refiningSubatlasInclusion P =
    𝟙 (A.refiningSubpresentation P) ≫ A.refiningSubatlasInclusion P
  rw [refiningSubatlasMap_inclusion, Category.id_comp]

theorem refiningSubatlasMap_comp {P Q R : A.presentation.atlas.RefiningSelection}
    (hPQ : P ≤ Q) (hQR : Q ≤ R) :
    A.refiningSubatlasMap hPQ ≫ A.refiningSubatlasMap hQR =
      A.refiningSubatlasMap (hPQ.trans hQR) := by
  apply (postcompQuasiIsoEmbedding (A.refiningSubatlasInclusion R)
    (isQuasiIso_refiningSubatlasInclusion R)).injective
  change (A.refiningSubatlasMap hPQ ≫ A.refiningSubatlasMap hQR) ≫
      A.refiningSubatlasInclusion R =
    A.refiningSubatlasMap (hPQ.trans hQR) ≫ A.refiningSubatlasInclusion R
  rw [Category.assoc, refiningSubatlasMap_inclusion, refiningSubatlasMap_inclusion,
    refiningSubatlasMap_inclusion]

/-- Realize the order of source selections in the full saturated strong category. -/
def refiningSubatlasFunctor (A : SaturatedAtlasPresentation.{u, v, w} K) :
    A.presentation.atlas.RefiningSelection ⥤ SaturatedAtlasPresentation.{u, v, w} K where
  obj := A.refiningSubpresentation
  map h := A.refiningSubatlasMap (leOfHom h)
  map_id P := refiningSubatlasMap_id P
  map_comp f g := (refiningSubatlasMap_comp (leOfHom f) (leOfHom g)).symm

/-- Restriction retains the actual complete strong map by precomposition. -/
def refiningHomRestriction {P Q : A.presentation.atlas.RefiningSelection}
    (h : P ≤ Q) (f : A.refiningSubpresentation Q ⟶ B) :
    A.refiningSubpresentation P ⟶ B :=
  A.refiningSubatlasMap h ≫ f

@[simp]
theorem refiningHomRestriction_id (P : A.presentation.atlas.RefiningSelection)
    (f : A.refiningSubpresentation P ⟶ B) :
    refiningHomRestriction (le_refl P) f = f := by
  unfold refiningHomRestriction
  rw [refiningSubatlasMap_id, Category.id_comp]

theorem refiningHomRestriction_comp {P Q R : A.presentation.atlas.RefiningSelection}
    (hPQ : P ≤ Q) (hQR : Q ≤ R) (f : A.refiningSubpresentation R ⟶ B) :
    refiningHomRestriction hPQ (refiningHomRestriction hQR f) =
      refiningHomRestriction (hPQ.trans hQR) f := by
  unfold refiningHomRestriction
  rw [← Category.assoc, refiningSubatlasMap_comp]

/-- Two actual numerators agree on a further original-chart source subatlas. -/
def HasCommonSourceRefinement {P Q : A.presentation.atlas.RefiningSelection}
    (f : A.refiningSubpresentation P ⟶ B) (g : A.refiningSubpresentation Q ⟶ B) : Prop :=
  ∃ (R : A.presentation.atlas.RefiningSelection) (hRP : R ≤ P) (hRQ : R ≤ Q),
    refiningHomRestriction hRP f = refiningHomRestriction hRQ g

/-- Equality of normal forms is exactly complete equality on an actual common
source subatlas. No injectivity of the restriction functions is assumed. -/
theorem localizedSourceRefinement_eq_iff {P Q : A.presentation.atlas.RefiningSelection}
    (f : A.refiningSubpresentation P ⟶ B) (g : A.refiningSubpresentation Q ⟶ B) :
    localizedRightFraction (sourceRefinementFraction P f) =
        localizedRightFraction (sourceRefinementFraction Q g) ↔
      HasCommonSourceRefinement f g := by
  constructor
  · intro heq
    have hcommon := (localizedRightFraction_eq_iff _ _).1 heq
    change ∃ (S : SaturatedAtlasPresentation.{u, v, w} K)
        (a : S ⟶ A.refiningSubpresentation P) (b : S ⟶ A.refiningSubpresentation Q),
      ∃ (_ : a ≫ A.refiningSubatlasInclusion P = b ≫ A.refiningSubatlasInclusion Q)
        (_ : a ≫ f = b ≫ g), (a ≫ A.refiningSubatlasInclusion P).IsQuasiIso at hcommon
    obtain ⟨S, a, b, hd, hn, ht⟩ := hcommon
    let τ : (quasiIsomorphisms (K := K)).RightFraction A S :=
      ⟨a ≫ A.refiningSubatlasInclusion P, ht, 𝟙 S⟩
    let T := fractionSourceSelection τ
    let R := (T ⊓ P) ⊓ Q
    have hRT : R ≤ T := inf_le_left.trans inf_le_left
    have hRP : R ≤ P := inf_le_left.trans inf_le_right
    have hRQ : R ≤ Q := inf_le_right
    let c : A.refiningSubpresentation R ⟶ S :=
      A.refiningSubatlasMap hRT ≫ fractionSourceReverse τ
    have hc : c ≫ (a ≫ A.refiningSubatlasInclusion P) =
        A.refiningSubatlasInclusion R := by
      change (A.refiningSubatlasMap hRT ≫ fractionSourceReverse τ) ≫ τ.s = _
      rw [Category.assoc, fractionSourceReverse_comp, refiningSubatlasMap_inclusion]
    have hca : c ≫ a = A.refiningSubatlasMap hRP := by
      apply (postcompQuasiIsoEmbedding (A.refiningSubatlasInclusion P)
        (isQuasiIso_refiningSubatlasInclusion P)).injective
      change (c ≫ a) ≫ A.refiningSubatlasInclusion P =
        A.refiningSubatlasMap hRP ≫ A.refiningSubatlasInclusion P
      exact (Category.assoc c a _).trans
        (hc.trans (refiningSubatlasMap_inclusion hRP).symm)
    have hcb : c ≫ b = A.refiningSubatlasMap hRQ := by
      apply (postcompQuasiIsoEmbedding (A.refiningSubatlasInclusion Q)
        (isQuasiIso_refiningSubatlasInclusion Q)).injective
      change (c ≫ b) ≫ A.refiningSubatlasInclusion Q =
        A.refiningSubatlasMap hRQ ≫ A.refiningSubatlasInclusion Q
      exact (Category.assoc c b _).trans
        ((congrArg (fun k => c ≫ k) hd.symm).trans
          (hc.trans (refiningSubatlasMap_inclusion hRQ).symm))
    refine ⟨R, hRP, hRQ, ?_⟩
    change A.refiningSubatlasMap hRP ≫ f = A.refiningSubatlasMap hRQ ≫ g
    calc
      A.refiningSubatlasMap hRP ≫ f = (c ≫ a) ≫ f :=
        congrArg (fun k => k ≫ f) hca.symm
      _ = c ≫ (a ≫ f) := Category.assoc c a f
      _ = c ≫ (b ≫ g) := congrArg (fun k => c ≫ k) hn
      _ = (c ≫ b) ≫ g := (Category.assoc c b g).symm
      _ = A.refiningSubatlasMap hRQ ≫ g := congrArg (fun k => k ≫ g) hcb
  · rintro ⟨R, hRP, hRQ, hfg⟩
    apply (localizedRightFraction_eq_iff _ _).2
    refine ⟨A.refiningSubpresentation R, A.refiningSubatlasMap hRP,
      A.refiningSubatlasMap hRQ, ?_, hfg, ?_⟩
    · exact (refiningSubatlasMap_inclusion hRP).trans
        (refiningSubatlasMap_inclusion hRQ).symm
    · change (A.refiningSubatlasMap hRP ≫ A.refiningSubatlasInclusion P).IsQuasiIso
      rw [refiningSubatlasMap_inclusion]
      exact isQuasiIso_refiningSubatlasInclusion R

end Langlands.Analytic.SaturatedAtlasPresentation
