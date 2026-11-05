import Langlands.Geometry.Building.FullValidity.Realization
import Langlands.Geometry.Building.ValuationBuildingApartmentCharts
import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Rational.SplitCentralDirectionsConstruction
import Langlands.GroupScheme.Rational.SplitCentralEmbedding
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof

/-!
# Axiom 4.1.4: the affine structure on the apartments

For building data `B : ValuationBuildingData G` over a nonarchimedean local field `F`, the
apartment `A(S)` is an affine space under `TranslationSpace B.i = V(S)/V(S)^Φ`, and `N(F)` acts
on it by affine automorphisms whose derivative is the action on `V(S)` (KP Axiom 4.1.4 (A 1),
`ValuationBuildingData.normalizerAction_linear`). KP Axiom 4.1.4 instead takes the translations
to be `V(S')`, for `S'` the maximal subtorus of `S` contained in the derived subgroup `G_der`,
through the canonical decomposition `V(S) = V(S') ⊕ V(A_G)`. This module compares the two.

* `B.ApartmentSplitting`: supplied data of the derived subgroup `d : D → G`, of a torus
  `j : S' → D` with `e : S' → S`, and of a torus `a : A_G → S`.
* `B.SatisfiesAffineApartmentAxiom T`: the clauses of KP Axiom 4.1.4 for these data. `D` is the
  derived subgroup, `S'` is a maximal split torus of `D` inside `S`, `A_G` is the split component
  of `G`, and `V(S) = V(S') ⊕ V(A_G)` (A 0). `N(F)` preserves `S'`, and the centre of `G(F)` acts
  trivially (A 1). The conjugation maps between apartments are affine with the natural
  derivative (A 2).
* `derivedTranslationEquiv`: the resulting isomorphism `V(S') ≃ TranslationSpace B.i`, which makes
  `A(S)` an affine space under `V(S')` (A 0), with the formulas of (A 1) for the derivative
  (`linear_normalizerAction_derivedTranslationEquiv`) and the translations
  (`normalizerAction_centralizer_eq_constVAdd_derivedTranslation`).
* `B.HasAffineConjugations`: KP Axiom 4.1.4 (A 2) for actual maximal split tori. It holds for
  every `B` (`hasAffineConjugations`), because the other apartments of the reduced building are the
  translates `g · A(S)` with the transported affine structure.

Nothing here asserts that the clauses hold for given data, or that data exist.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

namespace ValuationBuildingData

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-! ### Axiom 4.1.4 (A 2) -/

/-- KP Axiom 4.1.4 (A 2) for the apartments of `B(G)`: for every `g ∈ G(F)`, the map
`g : A(T₂) → A(T₃)` between the apartments of maximal split tori `T₂` and `T₃ = g T₂ g⁻¹` is
affine with derivative the natural isomorphism `V(T₂) → V(T₃)`.

The tori are actual tori `i₂ : T₂ → G`, `i₃ : T₃ → G` with an isomorphism `σ : T₂ ≅ T₃` such
that `i₂ ≫ Int(g) = σ ≫ i₃`. The apartment of `T₂` is read in a chart `x ↦ h₂ · x` from `A(S)`,
for a chart `(h₂, σ₂)` of `T₂` (`IsTorusChart`: `σ₂ : S ≅ T₂` with `i ≫ Int(h₂) = σ₂ ≫ i₂`, so
`T₂ = h₂ S h₂⁻¹`), and likewise for `T₃`. Every maximal split torus has a chart under the
torus–apartment clause of Axiom 4.1.1 (`HasTorusApartmentCorrespondence.exists_torusChart`), and
its apartment is then `h₂ · A(S)` (`HasTorusApartmentCorrespondence.torusApartment_range`). In
these charts `g` is an affine automorphism `f` of `A(S)`, and the natural isomorphism
`V(T₂) → V(T₃)` becomes `V(σ₂ ≫ σ ≫ σ₃⁻¹)` on `V(S)`, acting on the translations
`TranslationSpace B.i`. All charts are allowed, so the clause includes independence of the chart
(`exists_chartTransition`); `SatisfiesAffineApartmentAxiom.exists_derivedConjugation` reads the
derivative on `V(S')`. -/
def HasAffineConjugations : Prop :=
  ∀ (T₂ T₃ : CommGroupScheme (Spec (CommRingCat.of F))) (i₂ : T₂.toGrp ⟶ G)
    (i₃ : T₃.toGrp ⟶ G) (g : rationalPoints G) (σ : T₂ ≅ T₃),
    i₂ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom σ.hom ≫ i₃ →
    ∀ (h₂ h₃ : rationalPoints G) (σ₂ : B.S ≅ T₂) (σ₃ : B.S ≅ T₃),
      B.IsTorusChart i₂ h₂ σ₂ → B.IsTorusChart i₃ h₃ σ₃ →
      ∃ f : B.Apartment ≃ᵃ[ℝ] B.Apartment,
        (∀ x, g • B.translatedApartmentMap h₂ x = B.translatedApartmentMap h₃ (f x)) ∧
          ∀ v : V B.S, f.linear (Submodule.Quotient.mk v) =
            Submodule.Quotient.mk (cocharacterRealAut (σ₂ ≪≫ σ ≪≫ σ₃.symm) v)

/-- In the charts of `HasAffineConjugations`, `h₃⁻¹ g h₂` normalizes `S`, through the
automorphism `σ₂ ≫ σ ≫ σ₃⁻¹` of `S`. -/
theorem isNormalizingPoint_conjugation {T₂ T₃ : CommGroupScheme (Spec (CommRingCat.of F))}
    {i₂ : T₂.toGrp ⟶ G} {i₃ : T₃.toGrp ⟶ G} {g : rationalPoints G} {σ : T₂ ≅ T₃}
    (hg : i₂ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom σ.hom ≫ i₃)
    {h₂ h₃ : rationalPoints G} {σ₂ : B.S ≅ T₂} {σ₃ : B.S ≅ T₃}
    (h₂' : B.IsTorusChart i₂ h₂ σ₂) (h₃' : B.IsTorusChart i₃ h₃ σ₃) :
    IsNormalizingPoint B.i (h₃⁻¹ * g * h₂) (σ₂ ≪≫ σ ≪≫ σ₃.symm) := by
  unfold IsTorusChart at h₂' h₃'
  have h₃inv : i₃ ≫ (G.innerIso h₃⁻¹).hom = CommGroupScheme.groupHom σ₃.inv ≫ B.i := by
    rw [innerIso_inv_hom, Iso.comp_inv_eq, Category.assoc, h₃', ← Category.assoc]
    change i₃ = CommGroupScheme.groupHom (σ₃.inv ≫ σ₃.hom) ≫ i₃
    rw [Iso.inv_hom_id]
    exact (Category.id_comp i₃).symm
  change B.i ≫ (G.innerIso (h₃⁻¹ * g * h₂)).hom = _
  rw [innerIso_mul_hom, innerIso_mul_hom, ← Category.assoc, h₂', Category.assoc,
    ← Category.assoc i₂, hg, Category.assoc, h₃inv]
  rfl

/-- KP Axiom 4.1.4 (A 2) holds for the reduced building of every `B`: in the charts, `g` acts as
the normalizer element `h₃⁻¹ g h₂`, whose action on `A(S)` is affine with derivative the action
of `σ₂ ≫ σ ≫ σ₃⁻¹` on `V(S)` (KP Axiom 4.1.4 (A 1) for `B`). -/
theorem hasAffineConjugations : B.HasAffineConjugations := by
  intro T₂ T₃ i₂ i₃ g σ hg h₂ h₃ σ₂ σ₃ h₂' h₃'
  have hn := B.isNormalizingPoint_conjugation hg h₂' h₃'
  let n : normalizerPoints B.i := ⟨h₃⁻¹ * g * h₂, _, hn⟩
  refine ⟨B.normalizerAction n, fun x => ?_, fun v => ?_⟩
  · simp only [translatedApartmentMap, normalizerAction_apply]
    rw [← B.normalizer_smul_apartmentMap n x, ← mul_smul, ← mul_smul]
    change (g * h₂) • B.apartmentMap x = (h₃ * (h₃⁻¹ * g * h₂)) • B.apartmentMap x
    rw [mul_assoc h₃⁻¹, mul_inv_cancel_left]
  · rw [normalizerAction_linear]
    change Submodule.Quotient.mk (cocharacterRealAut (normalizingAut B.i n) v) = _
    rw [(isNormalizingPoint_normalizingAut B.i n).unique B.i hn]

/-- Two charts `(h, σ)` and `(h', σ')` of the same torus `T₂` differ by an affine automorphism of
`A(S)` with derivative `V(σ ≫ σ'⁻¹)`, so the affine structure on `h · A(S)` read through a chart
does not depend on the chart (the case `g = 1` of `hasAffineConjugations`). -/
theorem exists_chartTransition {T₂ : CommGroupScheme (Spec (CommRingCat.of F))}
    {i₂ : T₂.toGrp ⟶ G} {h h' : rationalPoints G} {σ σ' : B.S ≅ T₂}
    (hc : B.IsTorusChart i₂ h σ) (hc' : B.IsTorusChart i₂ h' σ') :
    ∃ f : B.Apartment ≃ᵃ[ℝ] B.Apartment,
      (∀ x, B.translatedApartmentMap h x = B.translatedApartmentMap h' (f x)) ∧
        ∀ v : V B.S, f.linear (Submodule.Quotient.mk v) =
          Submodule.Quotient.mk (cocharacterRealAut (σ ≪≫ σ'.symm) v) := by
  have h1 : i₂ ≫ (G.innerIso 1).hom = CommGroupScheme.groupHom (Iso.refl T₂).hom ≫ i₂ := by
    rw [innerIso_one_hom, Category.comp_id]
    exact (Category.id_comp i₂).symm
  obtain ⟨f, hf, hlin⟩ := B.hasAffineConjugations T₂ T₂ i₂ i₂ 1 (Iso.refl T₂) h1 h h' σ σ' hc hc'
  refine ⟨f, fun x => ?_, fun v => ?_⟩
  · rw [← hf x, one_smul]
  · rw [hlin v, Iso.refl_trans]

/-! ### The supplied derived torus and split component -/

/-- Supplied data for KP Axiom 4.1.4: a homomorphism `d : D → G` (meant: the derived subgroup
`G_der`), a torus `j : S' → D` with a homomorphism `e : S' → S` (meant: the maximal subtorus `S'`
of `S` contained in `G_der`), and a homomorphism `a : A_G → S` (meant: the maximal split torus
`A_G` of the centre of `G`). The clauses are in `SatisfiesAffineApartmentAxiom`. -/
structure ApartmentSplitting : Type (u + 1) where
  /-- The derived subgroup `G_der`. -/
  D : GroupScheme (Spec (CommRingCat.of F))
  /-- The inclusion `G_der → G`. -/
  d : D ⟶ G
  /-- The torus `S'`. -/
  derivedTorus : CommGroupScheme (Spec (CommRingCat.of F))
  /-- The inclusion `S' → G_der`. -/
  j : derivedTorus.toGrp ⟶ D
  /-- The inclusion `S' → S`. -/
  e : derivedTorus ⟶ B.S
  /-- The torus `A_G`. -/
  centralTorus : CommGroupScheme (Spec (CommRingCat.of F))
  /-- The inclusion `A_G → S`. -/
  a : centralTorus ⟶ B.S

/-- The clauses of KP Axiom 4.1.4 on the supplied data `T`, beyond those built into `B`:

* (A 0) `d` exhibits the derived subgroup of `G`. `j` is a maximal split torus of `G_der` and
  `e` is a closed immersion with `j ≫ d = e ≫ i`, so `S'` is the maximal subtorus of `S`
  contained in `G_der`. `a ≫ i` is the split component `A_G` of `G`, and
  `V(S) = V(S') ⊕ V(A_G)` (the canonical decomposition, from the isogeny `S' × A_G → S`). With
  `V(A_G) = V(S)^Φ` (`range_cocharacterMapReal_a`) this makes `A(S)` an affine space under
  `V(S')` (`derivedTranslationEquiv`).
* (A 1) `N(F)` preserves `S'`, so it acts on `X_*(S')`, and this action is the derivative of the
  action on `A(S)` (`linear_normalizerAction_derivedTranslationEquiv`). The centre of `G(F)` acts
  trivially on `A(S)`. That `N(F)` acts by affine maps, that `Z(F)` acts by the translations
  `ν(z)` (`normalizerAction_centralizer_eq_constVAdd_derivedTranslation`) and that `Z(F)^1` acts
  trivially are built into `B`.
* (A 2) `B.HasAffineConjugations`, which always holds (`hasAffineConjugations`). -/
structure SatisfiesAffineApartmentAxiom (T : B.ApartmentSplitting) : Prop where
  /-- `d` is the derived subgroup of `G`. -/
  isDerivedSubgroup : IsDerivedSubgroup T.d
  /-- `S'` is a maximal split torus of `G_der`. -/
  isMaximalSplitTorus_j : IsMaximalSplitTorus T.j
  /-- `S' → S` is a closed immersion. -/
  isClosedSubgroup_e : IsClosedSubgroup (CommGroupScheme.groupHom T.e)
  /-- `S' → G_der → G` equals `S' → S → G`. -/
  j_comp_d : T.j ≫ T.d = CommGroupScheme.groupHom T.e ≫ B.i
  /-- `A_G → S → G` is the split component of `G`. -/
  isSplitComponent : IsSplitComponent (CommGroupScheme.groupHom T.a ≫ B.i)
  /-- (A 0) `V(S) = V(S') ⊕ V(A_G)`. -/
  isCompl : IsCompl (LinearMap.range (cocharacterMapReal T.e))
    (LinearMap.range (cocharacterMapReal T.a))
  /-- (A 1) `N(F)` preserves `S'`. -/
  normalizer_derivedTorus : ∀ n : normalizerPoints B.i,
    ∃ τ : T.derivedTorus ≅ T.derivedTorus, τ.hom ≫ T.e = T.e ≫ (normalizingAut B.i n).hom
  /-- (A 1) The centre of `G(F)` acts trivially on `A(S)`. -/
  center_acts_trivially : ∀ n : normalizerPoints B.i,
    (n : rationalPoints G) ∈ (center G).carrier (Over.mk (𝟙 _)) → B.normalizerAction n = 1
  /-- (A 2) The conjugation maps between apartments are affine with the natural derivative. -/
  affineConjugations : B.HasAffineConjugations

variable {B} {T : B.ApartmentSplitting}

namespace SatisfiesAffineApartmentAxiom

variable (h : B.SatisfiesAffineApartmentAxiom T)
include h

/-- `S' → S` is a monomorphism. -/
theorem mono_e : Mono (CommGroupScheme.groupHom T.e).hom.hom.left :=
  haveI : IsClosedImmersion (CommGroupScheme.groupHom T.e).hom.hom.left := h.isClosedSubgroup_e
  inferInstance

/-- `V(S') → V(S)` is injective. -/
theorem injective_cocharacterMapReal_e : Function.Injective (cocharacterMapReal T.e) :=
  haveI := h.mono_e
  cocharacterMapReal_injective T.e

/-- `V(A_G) = V(S)^Φ`, the common kernel of the roots (by `rootAnnihilatorCentrality`). -/
theorem range_cocharacterMapReal_a :
    LinearMap.range (cocharacterMapReal T.a) = rootAnnihilator B.i :=
  haveI := B.isConnectedReductive.smooth
  haveI := B.isConnectedReductive.connectedSpace
  h.isSplitComponent.range_cocharacterMapReal_eq_relativeCentralDirections
    rootAnnihilatorCentrality B.isMaximalSplitTorus.isSplitSubtorus.1 T.a rfl

/-- `V(S)^Φ` is a complement of `V(S')`. -/
theorem isCompl_rootAnnihilator :
    IsCompl (rootAnnihilator B.i) (LinearMap.range (cocharacterMapReal T.e)) := by
  rw [← h.range_cocharacterMapReal_a]
  exact h.isCompl.symm

/-- (A 0) The isomorphism `V(S') ≃ V(S)/V(S)^Φ = TranslationSpace B.i`, `v ↦ [e(v)]`, under
which `A(S)` is an affine space under `V(S')`. -/
def derivedTranslationEquiv : V T.derivedTorus ≃ₗ[ℝ] TranslationSpace B.i :=
  ((Submodule.quotientEquivOfIsCompl _ _ h.isCompl_rootAnnihilator).trans
    (LinearEquiv.ofInjective _ h.injective_cocharacterMapReal_e).symm).symm

@[simp] theorem derivedTranslationEquiv_apply (v : V T.derivedTorus) :
    h.derivedTranslationEquiv v = Submodule.Quotient.mk (cocharacterMapReal T.e v) := by
  simp [derivedTranslationEquiv]

/-- The projection `V(S) → V(S')` along `V(A_G)` of the decomposition `V(S) = V(S') ⊕ V(A_G)`. -/
def derivedProjection : V B.S →ₗ[ℝ] V T.derivedTorus :=
  LinearMap.linearProjOfIsCompl _ _ h.injective_cocharacterMapReal_e h.isCompl

/-- The class of `v ∈ V(S)` in `TranslationSpace B.i` corresponds to its projection to `V(S')`. -/
theorem derivedTranslationEquiv_derivedProjection (v : V B.S) :
    h.derivedTranslationEquiv (h.derivedProjection v) = Submodule.Quotient.mk v := by
  rw [derivedTranslationEquiv_apply, Submodule.Quotient.eq]
  obtain ⟨x, y, rfl, -⟩ := Submodule.existsUnique_add_of_isCompl h.isCompl v
  obtain ⟨w, hw⟩ := x.2
  have hy : (y : V B.S) ∈ rootAnnihilator B.i := h.range_cocharacterMapReal_a ▸ y.2
  have hproj : h.derivedProjection ((x : V B.S) + y) = w := by
    rw [map_add, ← hw, derivedProjection, LinearMap.linearProjOfIsCompl_apply_left,
      LinearMap.linearProjOfIsCompl_apply_right, add_zero]
  rw [hproj, hw, sub_add_cancel_left]
  exact (rootAnnihilator B.i).neg_mem hy

/-- (A 1) The translation `ν(z) ∈ V(S')` of `z ∈ Z(F)`: the projection to `V(S')` of
`-ω_Z(z) ∈ V(S)`. -/
def derivedTranslation (z : rationalPoints B.centralizer.Z) : V T.derivedTorus :=
  h.derivedProjection (B.translation z).toAdd

/-- (A 1) `z ∈ Z(F)` acts on `A(S)` as the translation by `ν(z) ∈ V(S')`. -/
theorem normalizerAction_centralizer_eq_constVAdd_derivedTranslation
    (z : rationalPoints B.centralizer.Z) :
    B.normalizerAction (B.centralizer.toNormalizer z) =
      AffineEquiv.constVAdd ℝ B.Apartment (h.derivedTranslationEquiv (h.derivedTranslation z)) := by
  rw [derivedTranslation, derivedTranslationEquiv_derivedProjection]
  exact B.normalizerAction_centralizer z

/-- `derivedProjection` is the identity on `V(S')`. -/
theorem derivedProjection_e (v : V T.derivedTorus) :
    h.derivedProjection (cocharacterMapReal T.e v) = v :=
  LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ v

/-- `derivedProjection` vanishes on `V(A_G)`. -/
theorem derivedProjection_a (w : V T.centralTorus) :
    h.derivedProjection (cocharacterMapReal T.a w) = 0 :=
  LinearMap.linearProjOfIsCompl_apply_right _ _ _ _ ⟨_, LinearMap.mem_range_self _ w⟩

/-- An automorphism `τ` of `S` restricting to `τ'` on `S'` acts on `V(S)/V(S)^Φ` through `V(τ')`
on `V(S')`. -/
theorem quotientMk_cocharacterRealAut_e (τ : B.S ≅ B.S)
    (τ' : T.derivedTorus ≅ T.derivedTorus) (hτ : τ'.hom ≫ T.e = T.e ≫ τ.hom)
    (v : V T.derivedTorus) :
    (Submodule.Quotient.mk (cocharacterRealAut τ (cocharacterMapReal T.e v)) :
        TranslationSpace B.i) = h.derivedTranslationEquiv (cocharacterRealAut τ' v) := by
  rw [derivedTranslationEquiv_apply]
  congr 1
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    simp only [cocharacterMapReal_tmul, cocharacterRealAut_tmul, Category.assoc, hτ]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An affine automorphism of `A(S)` whose derivative is `V(τ)` on `V(S)/V(S)^Φ` has derivative
`V(τ')` on `V(S')`, for `τ'` the restriction of `τ` to `S'`. -/
theorem linear_derivedTranslationEquiv (f : B.Apartment ≃ᵃ[ℝ] B.Apartment) (τ : B.S ≅ B.S)
    (hf : ∀ v : V B.S, f.linear (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (cocharacterRealAut τ v))
    (τ' : T.derivedTorus ≅ T.derivedTorus) (hτ : τ'.hom ≫ T.e = T.e ≫ τ.hom)
    (v : V T.derivedTorus) :
    f.linear (h.derivedTranslationEquiv v) = h.derivedTranslationEquiv (cocharacterRealAut τ' v) := by
  rw [derivedTranslationEquiv_apply, hf, h.quotientMk_cocharacterRealAut_e τ τ' hτ]

/-- (A 1) The derivative of the action of `n ∈ N(F)` on `A(S)`, read on `V(S')`, is the action of
`n` on `V(S') = ℝ ⊗ X_*(S')` through the automorphism `τ` of `S'` induced by `n`. -/
theorem linear_normalizerAction_derivedTranslationEquiv (n : normalizerPoints B.i)
    (τ : T.derivedTorus ≅ T.derivedTorus) (hτ : τ.hom ≫ T.e = T.e ≫ (normalizingAut B.i n).hom)
    (v : V T.derivedTorus) :
    (B.normalizerAction n).linear (h.derivedTranslationEquiv v) =
      h.derivedTranslationEquiv (cocharacterRealAut τ v) :=
  h.linear_derivedTranslationEquiv _ (normalizingAut B.i n)
    (fun v => by rw [normalizerAction_linear]; rfl) τ hτ v

/-- (A 2) on `V(S')`: in the charts of `HasAffineConjugations`, `g` is an affine automorphism `f`
of `A(S)` whose derivative, read on `V(S')` through `derivedTranslationEquiv`, is `V(τ')` for the
restriction `τ'` to `S'` of `σ₂ ≫ σ ≫ σ₃⁻¹`. This is the natural isomorphism
`V(T₂') → V(T₃')` between the derived subtori `T₂' = σ₂(S')` and `T₃' = σ₃(S')`. -/
theorem exists_derivedConjugation {T₂ T₃ : CommGroupScheme (Spec (CommRingCat.of F))}
    {i₂ : T₂.toGrp ⟶ G} {i₃ : T₃.toGrp ⟶ G} {g : rationalPoints G} {σ : T₂ ≅ T₃}
    (hg : i₂ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom σ.hom ≫ i₃)
    {h₂ h₃ : rationalPoints G} {σ₂ : B.S ≅ T₂} {σ₃ : B.S ≅ T₃}
    (h₂' : B.IsTorusChart i₂ h₂ σ₂) (h₃' : B.IsTorusChart i₃ h₃ σ₃) :
    ∃ τ' : T.derivedTorus ≅ T.derivedTorus,
      τ'.hom ≫ T.e = T.e ≫ (σ₂ ≪≫ σ ≪≫ σ₃.symm).hom ∧
      ∃ f : B.Apartment ≃ᵃ[ℝ] B.Apartment,
        (∀ x, g • B.translatedApartmentMap h₂ x = B.translatedApartmentMap h₃ (f x)) ∧
          ∀ v : V T.derivedTorus,
            f.linear (h.derivedTranslationEquiv v) =
              h.derivedTranslationEquiv (cocharacterRealAut τ' v) := by
  have hn := B.isNormalizingPoint_conjugation hg h₂' h₃'
  obtain ⟨τ', hτ'⟩ := h.normalizer_derivedTorus ⟨h₃⁻¹ * g * h₂, _, hn⟩
  rw [(isNormalizingPoint_normalizingAut B.i ⟨h₃⁻¹ * g * h₂, _, hn⟩).unique B.i hn] at hτ'
  obtain ⟨f, hf, hlin⟩ := h.affineConjugations T₂ T₃ i₂ i₃ g σ hg h₂ h₃ σ₂ σ₃ h₂' h₃'
  exact ⟨τ', hτ', f, hf, h.linear_derivedTranslationEquiv f _ hlin τ' hτ'⟩

end SatisfiesAffineApartmentAxiom

end ValuationBuildingData

end Langlands.Geometry.Building
