import Langlands.AlgebraicGeometry.Picard.LinearSystemAssembly
import Langlands.AlgebraicGeometry.Picard.LinearSystemCechExact
import Langlands.CommutativeAlgebra.CokernelDualProjective
import Langlands.RingTheory.Grassmannian.LineChartFlat
import Langlands.AlgebraicGeometry.Modules.ProperFibreCohomologyDimBaseChangeProof

/-! # Flatness of the linear system when the fibres have no `H¹`

Over an affine open `V = Spec R` of the base, the fibres of `g` at points of `V` and the fibres of
the base change `Y_V → Spec R` at the residue fields of `Spec R` have the same cohomology
dimensions. If all fibres have vanishing `H¹`, the Čech model is exact at `κ ⊗ K₁` for every
residue field, so `Q` is projective and the Grassmannian of rank-one quotients of `Q` is flat and
locally of finite presentation; if moreover all fibres have nonzero `H⁰`, every residue field
carries a nonzero map `Q → κ`, i.e. a point of the Grassmannian, so it is surjective. Any
universal family over `V` is isomorphic to this model. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open Scheme.TwoAffineOpenCover SectionZeroIdeal
open Langlands.RingTheory.Grassmannian.LineQuotientCoordinates
open Module.Grassmannian.ProjectiveEmbedding (Rep InChart)
open Modules (fibreCohomology fibreCohomologyDim)
open Modules.DerivedSections
open PicardHilbertPiecesReduction (icl)
open ProperFlatIntegralSheafClassTwist (lineBundleOfIsInvertible)

section ResidueField

variable {R : Type u} [CommRing R]

/-- The residue field at a point of `Spec R`, as an `R`-algebra. -/
abbrev resAlg (p : Spec (.of R)) : Algebra R ((Spec (.of R)).residueField p) :=
  (Spec.preimage ((Spec (.of R)).fromSpecResidueField p)).hom.toAlgebra

lemma specMap_resAlg (p : Spec (.of R)) :
    letI := resAlg p
    specMap R ((Spec (.of R)).residueField p) = (Spec (.of R)).fromSpecResidueField p := by
  letI := resAlg p
  exact Spec.map_preimage _

lemma ker_resAlg (p : Spec (.of R)) :
    letI := resAlg p
    RingHom.ker (algebraMap R ((Spec (.of R)).residueField p)) = p.asIdeal := by
  letI := resAlg p
  let ψ := Spec.preimage ((Spec (.of R)).fromSpecResidueField p)
  let pt : Spec ((Spec (.of R)).residueField p) :=
    IsLocalRing.closedPoint ((Spec (.of R)).residueField p)
  have h1 : (Spec.map ψ) pt = p := by
    rw [Spec.map_preimage]
    exact Scheme.fromSpecResidueField_apply _ _
  have h2 : ((Spec.map ψ) pt).asIdeal = RingHom.ker ψ.hom := by
    ext x
    change x ∈ Ideal.comap ψ.hom (IsLocalRing.maximalIdeal _) ↔ x ∈ RingHom.ker ψ.hom
    rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
  rw [h1] at h2
  exact h2.symm

end ResidueField

lemma isPullback_of_eq {X Y Z : Scheme.{u}} (f : X ⟶ Z) {b b' : Y ⟶ Z} (e : b = b') :
    IsPullback (pullback.fst f b) (pullback.snd f b) f b' := by
  subst e
  exact IsPullback.of_hasPullback _ _

/-- A module over a field is zero iff its dimension is zero, if it is finite dimensional. -/
lemma isZero_iff_finrank_eq_zero {K : Type u} [Field K] (N : ModuleCat.{u} K) [Module.Finite K N] :
    IsZero N ↔ Module.finrank K N = 0 := by
  rw [ModuleCat.isZero_iff_subsingleton, Module.finrank_zero_iff]

section Fibres

variable {T Y : Scheme.{u}} [IsLocallyNoetherian T] (g : Y ⟶ T) [IsProper g] [Flat g]
  (M : Y.Modules) (hM : Scheme.Modules.IsInvertibleFLT M) (V : T.affineOpens)

include hM in
/-- **Fibres of `g` over `V` and of its base change to `Spec Γ(T, V)` have the same cohomology.** -/
theorem isZero_fibre_iff (p : Spec Γ(T, V.1)) (n : ℕ) :
    letI := resAlg p
    IsZero (fibreCohomology g (affPt V p) M n) ↔
      IsZero ((relativeCohomology (pullback.snd (pullback.snd g (affPt V))
        (specMap Γ(T, V.1) ((Spec Γ(T, V.1)).residueField p))) n).obj
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd g (affPt V))
            (specMap Γ(T, V.1) ((Spec Γ(T, V.1)).residueField p)))).obj
              ((Scheme.Modules.pullback (pullback.fst g (affPt V))).obj M))) := by
  letI := resAlg p
  have : IsNoetherianRing Γ(T, V.1) := IsLocallyNoetherian.component_noetherian V
  let π := pullback.snd g (affPt V)
  let MX := (Scheme.Modules.pullback (pullback.fst g (affPt V))).obj M
  have hMX : Scheme.Modules.IsInvertibleFLT MX :=
    PicardHilbertPiecesReduction.isInvertible_pullback _ hM
  have hdim := Modules.properFibreCohomologyDimBaseChange T (Spec Γ(T, V.1)) Y
    (pullback g (affPt V)) g (affPt V) π (pullback.fst g (affPt V))
    (IsPullback.of_hasPullback g (affPt V)) inferInstance M hM p n
  have hfin₁ := (Modules.properFlatFibreCohomologySemicontinuity T Y g inferInstance inferInstance
    M hM).1 (affPt V p) n
  have hfin₂ := (Modules.properFlatFibreCohomologySemicontinuity (Spec Γ(T, V.1))
    (pullback g (affPt V)) π inferInstance inferInstance MX hMX).1 p n
  obtain ⟨e⟩ := nonempty_relativeCohomology_iso_chosenPullback
    (isPullback_of_eq π (specMap_resAlg p)) MX n
  have h1 : IsZero (fibreCohomology g (affPt V p) M n) ↔
      fibreCohomologyDim g (affPt V p) M n = 0 := isZero_iff_finrank_eq_zero _
  have h2 : IsZero (fibreCohomology π p MX n) ↔ fibreCohomologyDim π p MX n = 0 :=
    isZero_iff_finrank_eq_zero _
  have h3 : fibreCohomologyDim g (affPt V p) M n = 0 ↔ fibreCohomologyDim π p MX n = 0 := by
    rw [hdim]
  exact h1.trans (h3.trans (h2.symm.trans ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩))

end Fibres

section Surjective

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} {L : LineBundle X}
  {𝒰 : X.OrderedAffineCover} (C : CechRep π L.obj 𝒰) (D : Rep R C.Q 1)

/-- **Nonzero sections on all fibres make the Grassmannian model surjective.** -/
theorem surjective_of_sections
    (h : ∀ p : Spec (.of R), letI := resAlg p
      ¬ IsZero ((relativeCohomology (pullback.snd π
        (specMap R ((Spec (.of R)).residueField p))) 0).obj
          ((Scheme.Modules.pullback (pullback.fst π
            (specMap R ((Spec (.of R)).residueField p)))).obj L.obj))) :
    Surjective D.p := by
  constructor
  intro p
  letI := resAlg p
  let κ := (Spec (.of R)).residueField p
  obtain ⟨σ, hσ⟩ : ∃ σ : Γ((Scheme.Modules.pullback (pullback.fst π (specMap R κ))).obj L.obj, ⊤),
      σ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h p
    refine IsZero.of_iso ?_ ((relativeCohomologyZeroIso _).app _)
    rw [ModuleCat.isZero_iff_subsingleton]
    exact ⟨fun a b => (hcon a).trans (hcon b).symm⟩
  let v := (C.homEquivSections κ).symm σ
  have hv0 : v ≠ 0 := by
    intro hv
    apply hσ
    have : C.homEquivSections κ v = σ := Equiv.apply_symm_apply _ _
    rw [← this, hv, homEquivSections_zero]
  obtain ⟨q, hq⟩ : ∃ q, v q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (LinearMap.ext hcon)
  have hv : Ideal.span (Set.range v) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨q, rfl⟩) (IsUnit.mk0 _ hq)
  let k := (D.pt κ (linePt v hv)).1
  have hk : k ≫ D.p = (Spec (.of R)).fromSpecResidueField p :=
    (D.pt κ (linePt v hv)).2.trans (specMap_resAlg p)
  refine ⟨k (IsLocalRing.closedPoint κ), ?_⟩
  rw [← Scheme.Hom.comp_apply, hk]
  exact Scheme.fromSpecResidueField_apply _ _

end Surjective

/-- **Local flatness of the linear system.** -/
theorem localFibreFlatness : LinearSystemGluing.LocalFibreFlatness.{u} := by
  intro T Y _ g _ _ _ M hM V P _ l W hU hH1
  have : IsNoetherianRing Γ(T, V.1) := IsLocallyNoetherian.component_noetherian V
  let a := affPt V
  let L : LineBundle (pullback g a) := pbLB (pullback.fst g a) (lineBundleOfIsInvertible M hM)
  obtain ⟨𝒰, C, D, WD, hD⟩ := exists_model (R := Γ(T, V.1)) (pullback.snd g a) L
  have hL : L.classOf = Group.pullback (pullback.fst g a) (icl M hM) := classOf_pbLB _ _
  rw [hL] at hD
  have hV : a.opensRange = V.1 := TopologicalSpace.Opens.ext (by
    rw [Scheme.Hom.coe_opensRange]
    exact range_affPt V)
  have hT := hD.transport (a := a)
  rw [hV] at hT
  have : IsProper D.p := D.isProper_p
  have : IsLocallyNoetherian D.Gr := LocallyOfFiniteType.isLocallyNoetherian D.p
  obtain ⟨ℓ, hℓ, hℓW⟩ := hT.exists_point P l hU.range_le W hU.ls
  have hiso : IsIso ℓ := LinearSystemGluing.isIso_of_isUniversalOn hU hT ℓ hℓ hℓW
  have hmem : ∀ p : Spec Γ(T, V.1), a p ∈ V.1 := fun p => (range_affPt V).subset ⟨p, rfl⟩
  have hproj : Module.Projective Γ(T, V.1) C.Q := by
    refine Langlands.CommutativeAlgebra.CokernelDualHom.projective_Q_of_exact C.δ C.δ₁
      C.δ₁_comp_δ (fun P' _ => ?_)
    let p : Spec (.of Γ(T, V.1)) := ⟨P', inferInstance⟩
    letI := resAlg p
    refine ⟨(Spec (.of Γ(T, V.1))).residueField p, inferInstance, resAlg p, ker_resAlg p,
      fun x hx => exact_of_isZero_H1 C _ ?_ x hx⟩
    exact (isZero_fibre_iff g M hM V p 1).1 (hH1 _ (hmem p))
  have hflat : Flat D.p := D.flat_p
  have hlfp : LocallyOfFinitePresentation D.p := D.locallyOfFinitePresentation_p
  subst hℓ
  have key : ∀ (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange] [Q.RespectsIso],
      Q D.p → Q (pullback.snd (ℓ ≫ D.p ≫ a) V.1.ι) := by
    intro Q _ _ hQ
    have h := LinearSystemGluing.prop_pullback_snd_comp Q (ℓ ≫ D.p) a V.1 (range_affPt V)
      ((Q.cancel_left_of_respectsIso ℓ D.p).mpr hQ)
    rwa [Category.assoc] at h
  refine ⟨key _ hflat, key _ hlfp, fun hH0 => key _ (surjective_of_sections C D fun p => ?_)⟩
  letI := resAlg p
  intro hz
  exact hH0 _ (hmem p) ((isZero_fibre_iff g M hM V p 0).2 hz)

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
