import Langlands.AlgebraicGeometry.AffineCechDeRhamInfinitesimalMorphism
import Langlands.AlgebraicGeometry.AffineCechDeRhamPullbackComposition

/-! # Functoriality of the corrected pullback of reduced scheme morphisms -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X Y Z : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
  {h : Z ⟶ Spec (CommRingCat.of R)}
  {U : Scheme.AffineOpenCover.{u} X} {V : Scheme.AffineOpenCover.{u} Y}
  {W : Scheme.AffineOpenCover.{u} Z}
  (I : Ideal R) (hI : I * I = ⊥)

private abbrev redBase (f : X ⟶ Spec (CommRingCat.of R)) := pullback.snd f (quotientBaseMap I)
private abbrev redMap (f : X ⟶ Spec (CommRingCat.of R)) := quotientReductionMap f I

private lemma reduced_over_thick
    (m : quotientReduction f I ⟶ quotientReduction g I)
    (hm : m ≫ redBase I g = redBase I f) : (m ≫ redMap I g) ≫ g = redMap I f ≫ f := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, hm, ← pullback.condition]

private lemma appLE_eq_of_hom_eq {A B : Scheme.{u}} {a b : A ⟶ B} (hab : a = b)
    (U : B.Opens) (V : A.Opens) (ha : V ≤ a ⁻¹ᵁ U) (hb : V ≤ b ⁻¹ᵁ U) :
    a.appLE U V ha = b.appLE U V hb := by
  subst b
  rfl

variable [Smooth f] [IsSeparated f] [Finite U.I₀]
  [Smooth g] [IsSeparated g] [Finite V.I₀]

/-- Corrected degree-one pullback by a morphism over the quotient spectrum,
with compatible affine covers of the thicker schemes. -/
abbrev reducedSchemePullbackH1
    (m : quotientReduction f I ⟶ quotientReduction g I)
    (hm : m ≫ redBase I g = redBase I f) (β : U.I₀ → V.I₀)
    (hβ : ∀ i, redMap I f ⁻¹ᵁ coverOpens U i ≤ (m ≫ redMap I g) ⁻¹ᵁ coverOpens V (β i)) :
    H1 g V →ₗ[R] H1 f U :=
  reductionPullbackH1 f I hI (m ≫ redMap I g) (reduced_over_thick I m hm) β hβ

section Composition

variable [Smooth h] [IsSeparated h] [Finite W.I₀]
  (m : quotientReduction f I ⟶ quotientReduction g I)
  (n : quotientReduction g I ⟶ quotientReduction h I)
  (hm : m ≫ redBase I g = redBase I f) (hn : n ≫ redBase I h = redBase I g)
  (β : U.I₀ → V.I₀) (δ : V.I₀ → W.I₀)
  (hβ : ∀ i, redMap I f ⁻¹ᵁ coverOpens U i ≤ (m ≫ redMap I g) ⁻¹ᵁ coverOpens V (β i))
  (hδ : ∀ i, redMap I g ⁻¹ᵁ coverOpens V i ≤ (n ≫ redMap I h) ⁻¹ᵁ coverOpens W (δ i))

omit [Smooth f] [IsSeparated f] [Finite U.I₀] [Smooth g] [IsSeparated g] [Finite V.I₀]
  [Smooth h] [IsSeparated h] [Finite W.I₀] in
include hβ hδ in
private lemma comp_cover_le (i : U.I₀) :
    redMap I f ⁻¹ᵁ coverOpens U i ≤ ((m ≫ n) ≫ redMap I h) ⁻¹ᵁ coverOpens W ((δ ∘ β) i) :=
  fun _ hx => hδ (β i) (hβ i hx)

/-- Corrected pullback along a composition of actual reduced morphisms
is the composition of corrected pullbacks on compatible covers. -/
theorem reducedSchemePullbackH1_comp :
    reducedSchemePullbackH1 I hI (m ≫ n) (by rw [Category.assoc, hn, hm])
      (δ ∘ β) (comp_cover_le I m n β δ hβ hδ) =
    (reducedSchemePullbackH1 I hI m hm β hβ).comp (reducedSchemePullbackH1 I hI n hn δ hδ) := by
  let c := (m ≫ n) ≫ redMap I h
  let hc : c ≫ h = redMap I f ≫ f :=
    reduced_over_thick I (m ≫ n) (by rw [Category.assoc, hn, hm])
  let L := localPullbacksOfReduction f I hI (m ≫ redMap I g) (reduced_over_thick I m hm) β hβ
  let M := localPullbacksOfReduction g I hI (n ≫ redMap I h) (reduced_over_thick I n hn) δ hδ
  let N := localPullbacksOfReduction f I hI c hc (δ ∘ β) (comp_cover_le I m n β δ hβ hδ)
  change N.pullbackH1 hI = (L.pullbackH1 hI).comp (M.pullbackH1 hI)
  rw [← L.pullbackH1_comp M hI]
  apply N.pullbackH1_eq_of_congruent hI
  intro p τ i j a
  let T := inter (coverOpens U) τ
  let T' := inter (coverOpens V) (β ∘ τ)
  let T'' := inter (coverOpens W) ((δ ∘ β) ∘ τ)
  let T₀ := redMap I f ⁻¹ᵁ T
  let T₀' := redMap I g ⁻¹ᵁ T'
  have e₁ : T₀ ≤ m ⁻¹ᵁ T₀' := by
    intro x hx
    change redMap I g (m x) ∈ T'
    exact (Langlands.Cohomology.Cech.mem_inter (β ∘ τ) _).2
      fun k => hβ (τ k) ((Langlands.Cohomology.Cech.mem_inter τ _).1 hx k)
  have e₂ : T₀' ≤ (n ≫ redMap I h) ⁻¹ᵁ T'' := by
    intro x hx
    exact (Langlands.Cohomology.Cech.mem_inter ((δ ∘ β) ∘ τ) _).2
      fun k => hδ (β (τ k)) ((Langlands.Cohomology.Cech.mem_inter (β ∘ τ) _).1 hx k)
  have e₃ : T₀ ≤ c ⁻¹ᵁ T'' := fun x hx => e₂ (e₁ hx)
  have e₁' : T₀ ≤ (m ≫ redMap I g) ⁻¹ᵁ T' := e₁
  rw [← (quotientReductionMap_appLE f I T (isAffineOpen_inter f U τ)).2,
    RingHom.mem_ker, map_sub, sub_eq_zero, LocalPullbacks.comp_sections, AlgHom.comp_apply]
  change ((redMap I f).appLE T T₀ le_rfl).hom (N.sections τ i a) =
    ((redMap I f).appLE T T₀ le_rfl).hom (L.sections τ j (M.sections (β ∘ τ) j a))
  rw [localPullbacksOfReduction_reduce_sections _ _ _ _ _ _ _ _ _ _ e₃,
    localPullbacksOfReduction_reduce_sections _ _ _ _ _ _ _ _ _ _ e₁']
  rw [← Scheme.Hom.appLE_comp_appLE m (redMap I g) T' T₀' T₀ le_rfl e₁']
  change (c.appLE T'' T₀ e₃).hom a =
    (m.appLE T₀' T₀ e₁).hom (((redMap I g).appLE T' T₀' le_rfl).hom (M.sections (β ∘ τ) j a))
  rw [localPullbacksOfReduction_reduce_sections _ _ _ _ _ _ _ _ _ _ e₂]
  change (c.appLE T'' T₀ e₃).hom a =
    ((n ≫ redMap I h).appLE T'' T₀' e₂ ≫ m.appLE T₀' T₀ e₁).hom a
  rw [Scheme.Hom.appLE_comp_appLE]
  rw [appLE_eq_of_hom_eq (Category.assoc m n (redMap I h)) T'' T₀ e₃ _]

end Composition

omit [Smooth g] [IsSeparated g] [Finite V.I₀] in
/-- The corrected pullback of the identity reduction with the same charts
is the identity in degree one. -/
theorem reducedSchemePullbackH1_id (β : U.I₀ → U.I₀) (hβ : β = id)
    (e : ∀ i, redMap I f ⁻¹ᵁ coverOpens U i ≤
      (𝟙 (quotientReduction f I) ≫ redMap I f) ⁻¹ᵁ coverOpens U (β i)) :
    reducedSchemePullbackH1 (f := f) (g := f) (U := U) (V := U)
      I hI (𝟙 (quotientReduction f I)) (Category.id_comp _) β e =
      LinearMap.id := by
  subst β
  let L := localPullbacksOfReduction (g := f) (U := U) (V := U) f I hI
    (𝟙 (quotientReduction f I) ≫ redMap I f)
    (reduced_over_thick I _ (Category.id_comp _)) id e
  let N : LocalPullbacks (f := f) (g := f) I (id : U.I₀ → U.I₀) :=
    { sections := fun _ _ => AlgHom.id R _
      restrict_sections := fun _ _ _ => rfl
      congruent := fun _ _ _ a => by simp }
  have hl : L.pullbackH1 hI = N.pullbackH1 hI := by
    apply L.pullbackH1_eq_of_congruent hI
    intro p τ i j a
    let T := inter (coverOpens U) τ
    let T₀ := redMap I f ⁻¹ᵁ T
    have et : T₀ ≤ (𝟙 (quotientReduction f I) ≫ redMap I f) ⁻¹ᵁ T := by
      rw [Category.id_comp]
    rw [← (quotientReductionMap_appLE f I T (isAffineOpen_inter f U τ)).2,
      RingHom.mem_ker, map_sub, sub_eq_zero]
    change ((redMap I f).appLE T T₀ le_rfl).hom (L.sections τ i a) =
      ((redMap I f).appLE T T₀ le_rfl).hom a
    rw [localPullbacksOfReduction_reduce_sections (g := f) (U := U) (V := U)
      f I hI (𝟙 (quotientReduction f I) ≫ redMap I f)
      (reduced_over_thick I _ (Category.id_comp _)) id e τ i a et]
    change ((𝟙 (quotientReduction f I) ≫ redMap I f).appLE T T₀ et).hom a =
      ((redMap I f).appLE T T₀ le_rfl).hom a
    rw [appLE_eq_of_hom_eq (Category.id_comp (redMap I f)) T T₀ et le_rfl]
  change L.pullbackH1 hI = LinearMap.id
  rw [hl]
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (boundaries f U).mkQ_surjective x
  rw [LocalPullbacks.pullbackH1_mk, LinearMap.id_apply]
  apply congrArg ((boundaries f U).mkQ)
  apply Subtype.ext
  refine Prod.ext (funext fun τ => ?_) (funext fun τ => ?_)
  · change (N.cochainOne hI z.val).1 τ = z.val.1 τ
    rw [LocalPullbacks.cochainOne_fst]
    let a : tupleSections f U τ := z.val.1 τ
    let s := AlgHom.id R (tupleSections f U τ)
    change a + RelativeForms.contractDifferenceOne s s hI _ _ = a
    rw [RelativeForms.contractDifferenceOne_self, add_zero]
  · exact RelativeForms.mapOne_id _

omit [Smooth g] [IsSeparated g] [Finite V.I₀] in
private lemma reducedSchemePullbackH1_eq_id (m : quotientReduction f I ⟶ quotientReduction f I)
    (hm : m ≫ redBase I f = redBase I f) (h : m = 𝟙 _) (β : U.I₀ → U.I₀) (hβ : β = id)
    (e : ∀ i, redMap I f ⁻¹ᵁ coverOpens U i ≤ (m ≫ redMap I f) ⁻¹ᵁ coverOpens U (β i)) :
    reducedSchemePullbackH1 (f := f) (g := f) (U := U) (V := U) I hI m hm β e =
      LinearMap.id := by
  subst m
  exact reducedSchemePullbackH1_id I hI β hβ e

/-- A marking isomorphism over the quotient, with a bijection matching the
reduced charts, induces a bijection on the thicker degree-one modules. -/
theorem reducedSchemePullbackH1_bijective
    (e : quotientReduction f I ≅ quotientReduction g I)
    (he : e.hom ≫ redBase I g = redBase I f) (β : U.I₀ ≃ V.I₀)
    (hβ : ∀ i, redMap I f ⁻¹ᵁ coverOpens U i = (e.hom ≫ redMap I g) ⁻¹ᵁ coverOpens V (β i)) :
    Function.Bijective (reducedSchemePullbackH1 I hI e.hom he β (fun i => (hβ i).le)) := by
  have he' : e.inv ≫ redBase I f = redBase I g := by rw [← he, e.inv_hom_id_assoc]
  have hβ' (j : V.I₀) :
      redMap I g ⁻¹ᵁ coverOpens V j ≤ (e.inv ≫ redMap I f) ⁻¹ᵁ coverOpens U (β.symm j) := by
    intro x hx
    change e.inv x ∈ redMap I f ⁻¹ᵁ coverOpens U (β.symm j)
    rw [hβ, β.apply_symm_apply]
    change redMap I g ((e.inv ≫ e.hom) x) ∈ coverOpens V j
    rw [e.inv_hom_id]
    exact hx
  let P := reducedSchemePullbackH1 I hI e.hom he β (fun i => (hβ i).le)
  let Q := reducedSchemePullbackH1 I hI e.inv he' β.symm hβ'
  have hP : P.comp Q = LinearMap.id := by
    rw [show P.comp Q = _ from
      (reducedSchemePullbackH1_comp I hI e.hom e.inv he he' β β.symm
        (fun i => (hβ i).le) hβ').symm]
    exact reducedSchemePullbackH1_eq_id I hI _ _ e.hom_inv_id _ (funext β.symm_apply_apply) _
  have hQ : Q.comp P = LinearMap.id := by
    rw [show Q.comp P = _ from
      (reducedSchemePullbackH1_comp I hI e.inv e.hom he' he β.symm β
        hβ' (fun i => (hβ i).le)).symm]
    exact reducedSchemePullbackH1_eq_id I hI _ _ e.inv_hom_id _ (funext β.apply_symm_apply) _
  exact ⟨(show Function.LeftInverse Q P from fun x => LinearMap.congr_fun hQ x).injective,
    (show Function.RightInverse Q P from fun x => LinearMap.congr_fun hP x).surjective⟩

end Langlands.AlgebraicGeometry.AffineCechDeRham
