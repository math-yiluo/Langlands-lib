import Langlands.Shimura.DefiniteFormsSmoothCoefficients
import Langlands.Cohomology.DivisibleSystem.ReductionLimit
import Langlands.Galois.CompatibleFamily
import Langlands.Global.CompletionResidue

/-!
# Inverse systems of coefficients for forms and their Ext

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, 1999, writes
`𝒪_m = 𝒪/ℓ^m 𝒪` (p.309) and, before Proposition 4.10 (p.311): "Now we want to let `m` vary. Let
the `K_ℓ`-modules `(ρ, W)` and `𝓛 = 𝓛_W` be as in §3; let `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. Then
`𝓛_m` forms an inverse system of `𝒪`-modules". The proof of Proposition 4.10 checks "a
Mittag-Leffler condition as `m` varies" for the complexes giving the spectral sequences (4.9) with
coefficients `𝓛_m`. This file makes the forms with coefficients, their smooth parts, `Ext^i(W, -)`
of the smooth parts and the intended hyperext abutments with their filtrations functorial in the
coefficients, and applies them to the published reduction tower `m ↦ 𝓛 / l ^ m 𝓛`, for `l` the
residue characteristic of `ℓ` (Harris's prime `ℓ`). This gives presheaves on levels of inverse
systems over `m`, and comparison maps from the terms for `𝓛` to the inverse limits of the terms
for `𝓛_m`. When `𝓛` is `l`-adically complete, it proves that the forms and the smooth forms with
coefficients `𝓛` are the inverse limits of those with coefficients `𝓛_m`. It does not prove
that the comparison maps for `Ext`, the abutments, filtrations or graded pieces are isomorphisms,
and does not construct the spectral sequence of Proposition 4.10 or the sheaf `W~`.

## Main definitions

For groups `Γ`, `G` with `ι : Γ →* G`, an isomorphism of topological groups `e : G ≃ₜ* H × H'`
and a subgroup `D` of `G`, in the namespace `EquivariantForms`:

* `coefficientRepFunctor R e ι K'`: Mathlib's restriction from `D` to `e⁻¹ (1 × K')` followed by
  the published `formsRepFunctor`, a functor from `Rep R D` to `Rep R H` sending `X` to the forms
  of level `e⁻¹ (1 × K')` with coefficients `X` (`coefficientRepFunctor_obj`); on morphisms it is
  postcomposition (`coefficientRepFunctor_map_apply_coe`).
* `coefficientFormsBifunctor R e ι`, `coefficientSmoothBifunctor R e ι`: the presheaves
  `coefficientFormsPresheaf R e ι X.ρ` and `coefficientSmoothPresheaf R e ι X.ρ` on the compact
  open levels of `coefficientDomain e D`, as functors of `X : Rep R D`; their maps commute with
  `coefficientTransport` (`coefficientTransport_comp_map`).
* `coefficientFormsSystem R e ι L`, `coefficientSmoothSystem R e ι L`: for an inverse system
  `L : ℕᵒᵖ ⥤ Rep R D`, the presheaves of inverse systems `m ↦ ` forms (smooth forms) with
  coefficients `L m`.
* Instances `formsRepFunctor_preservesLimits`, `coefficientRepFunctor_preservesLimits`,
  `coefficientFormsBifunctor_preservesLimits`, `coefficientSmoothBifunctor_preservesLimits`;
  `isLimitCoefficientFormsReductionCone`, `isLimitCoefficientSmoothReductionCone`: for `L`
  complete for the `ℓ`-adic topology, the forms (smooth forms) with coefficients `L` are the
  inverse limit of those with coefficients `L / ℓ ^ m L`, via the projections.
* `coefficientExtBifunctor R e ι W i`, `coefficientAbutmentBifunctor R e ι X n`,
  `coefficientFiltrationBifunctor R e ι X n p`, `coefficientGradedBifunctor R e ι X n p`: the
  presheaves `coefficientExtPresheaf`, `coefficientAbutmentPresheaf`,
  `coefficientFiltrationPresheaf` and `coefficientGradedPresheaf` as functors of the coefficients,
  with the inclusions `coefficientFiltrationBifunctorι`, `coefficientFiltrationBifunctorMapOfLE`
  and projections `coefficientGradedBifunctorπ` natural in the coefficients.
* `coefficientExtSystem`, `coefficientAbutmentSystem`, `coefficientFiltrationSystem`,
  `coefficientGradedSystem` with `coefficientFiltrationSystemι`,
  `coefficientFiltrationSystemMapOfLE`, `coefficientGradedSystemπ`: the same applied to an inverse
  system of coefficients.
* `coefficientExtReductionComparison`, `coefficientAbutmentReductionComparison`,
  `coefficientFiltrationReductionComparison`, `coefficientGradedReductionComparison`: the maps
  from the term for `L` to the inverse limit of the terms for `L / ℓ ^ m L` induced by the
  projections (`_π` lemmas), compatible with the inclusions and projections of the filtration
  (`coefficientFiltrationReductionComparison_ι`,
  `coefficientFiltrationReductionComparison_gradedπ`).

In the namespace `DefiniteForms`, for a finite place `ℓ` of `ℚ`, `σ : AlgebraInvolution ℚ A`, a
subgroup `Kℓ` of `GJ(ℚ_ℓ)`, `p ≠ 0`, the published splitting `σ.finiteAdelicPointsSplit p hp` and
`l = GaloisRepresentation.residueCharacteristic ℓ`:

* `residueCharacteristic_prime`, `residueCharacteristic_neZero`,
  `natCast_residueCharacteristic_mem`: `l` is prime and lies in the prime ideal of `ℓ`.
* `localCoefficientFunctor σ ℓ Kℓ R`: Mathlib's restriction along the `ℓ`-component map.
* `dividingCoefficientFormsBifunctor`, `dividingCoefficientSmoothBifunctor`,
  `dividingCoefficientExtBifunctor`, `dividingCoefficientAbutmentBifunctor`,
  `dividingCoefficientFiltrationBifunctor`, `dividingCoefficientGradedBifunctor`, with
  `dividingCoefficientFiltrationBifunctorι`, `dividingCoefficientFiltrationBifunctorMapOfLE`,
  `dividingCoefficientGradedBifunctorπ`: the dividing presheaves as functors of `𝓛 : Rep R Kℓ`.
* `dividingReductionFormsSystem`, `dividingReductionSmoothSystem`, `dividingReductionExtSystem`,
  `dividingReductionAbutmentSystem`, `dividingReductionFiltrationSystem`,
  `dividingReductionGradedSystem`, with `dividingReductionFiltrationSystemι`,
  `dividingReductionFiltrationSystemMapOfLE`, `dividingReductionGradedSystemπ`: Harris's inverse
  system `m ↦ 𝓛_m = 𝓛 / l ^ m 𝓛` taken through these functors.
* `dividingReductionExtComparison`, `dividingReductionAbutmentComparison`,
  `dividingReductionFiltrationComparison`, `dividingReductionGradedComparison`: the comparison
  maps to the inverse limits over `m`, with their `_π`, `_ι` and `_gradedπ` lemmas.
* `isLimitDividingCoefficientFormsReductionCone`, `isLimitDividingCoefficientSmoothReductionCone`:
  for `𝓛` complete for the `l`-adic topology, the forms (smooth forms) with coefficients `𝓛` are
  the inverse limit of those with coefficients `𝓛_m`.
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategory
open Langlands.Cohomology Langlands.Shimura.CompactOpenLevel

universe t uR uΓ uG uH uH' u w

section Functoriality

variable (R : Type uR) [CommRing R] {Γ : Type uΓ} {G : Type uG} {H : Type uH} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H'] (e : G ≃ₜ* H × H') (ι : Γ →* G) {D : Subgroup G}

/-- The forms of level `e⁻¹ (1 × K')` with right translation by `H`, as a functor of the
coefficients: Mathlib's restriction from `D` to `e⁻¹ (1 × K')` followed by the published
`formsRepFunctor`. -/
def coefficientRepFunctor (K' : Subgroup (coefficientDomain e D)) :
    Rep.{t} R D ⥤ Rep.{max uG t} R H :=
  Rep.resFunctor (Subgroup.inclusion (awayLevel_domainLevel_le e K')) ⋙
    formsRepFunctor R ι (awayLevel e (domainLevel e K')) (factorHom e)
      (factorHom_mul_awayLevel e (domainLevel e K'))

lemma coefficientRepFunctor_obj (K' : Subgroup (coefficientDomain e D)) (X : Rep.{t} R D) :
    (coefficientRepFunctor R e ι K').obj X = Rep.of (coefficientTranslation R e ι X.ρ K') :=
  rfl

@[simp]
lemma coefficientRepFunctor_map_apply_coe (K' : Subgroup (coefficientDomain e D))
    {X Y : Rep.{t} R D} (φ : X ⟶ Y) (f : coefficientForms R e ι X.ρ K') (g : G) :
    (((coefficientRepFunctor R e ι K').map φ).hom f).1 g = φ.hom (f.1 g) :=
  rfl

/-- Postcomposition with a morphism of coefficients commutes with `coefficientTransport`. -/
lemma coefficientTransport_comp_map {X Y : Rep.{t} R D} (φ : X ⟶ Y)
    {K₁ K₂ : Subgroup (coefficientDomain e D)} (c : coefficientDomain e D)
    (hc : ∀ k ∈ K₁, c⁻¹ * k * c ∈ K₂) (f : coefficientForms R e ι X.ρ K₂) :
    coefficientTransport R e ι Y.ρ c hc (((coefficientRepFunctor R e ι K₂).map φ).hom f) =
      ((coefficientRepFunctor R e ι K₁).map φ).hom (coefficientTransport R e ι X.ρ c hc f) := by
  ext x
  change Y.ρ _ (φ.hom (f.1 (x * awayHom e c))) = φ.hom (X.ρ _ (f.1 (x * awayHom e c)))
  exact (φ.hom.isIntertwining _ _ _ _).symm

/-- The presheaves `coefficientFormsPresheaf` of forms with coefficients `X`, as a
functor of `X`: on morphisms of coefficients it acts by postcomposition. -/
def coefficientFormsBifunctor :
    Rep.{t} R D ⥤ (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ Rep.{max uG t} R H where
  obj X := coefficientFormsPresheaf R e ι X.ρ
  map {X Y} φ :=
    { app K' := (coefficientRepFunctor R e ι K'.unop.subgroup).map φ
      naturality {K₁ K₂} a := by
        ext f
        exact (coefficientTransport_comp_map R e ι φ a.unop.element a.unop.respects f).symm }
  map_id _ := rfl
  map_comp _ _ := rfl

lemma coefficientFormsBifunctor_obj (X : Rep.{t} R D) :
    (coefficientFormsBifunctor R e ι).obj X = coefficientFormsPresheaf R e ι X.ρ :=
  rfl

lemma coefficientFormsBifunctor_map_app {X Y : Rep.{t} R D} (φ : X ⟶ Y)
    (K' : (CompactOpenLevel (coefficientDomain e D))ᵒᵖ) :
    ((coefficientFormsBifunctor R e ι).map φ).app K' =
      (coefficientRepFunctor R e ι K'.unop.subgroup).map φ :=
  rfl

variable [IsTopologicalGroup H]

/-- The presheaves `coefficientSmoothPresheaf` of smooth forms with coefficients `X`,
as a functor of `X`. -/
def coefficientSmoothBifunctor :
    Rep.{t} R D ⥤
      (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ SmoothRep.{uR, uH, max uG t} R H :=
  coefficientFormsBifunctor R e ι ⋙
    (Functor.whiskeringRight _ _ _).obj (SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H)

lemma coefficientSmoothBifunctor_obj (X : Rep.{t} R D) :
    (coefficientSmoothBifunctor R e ι).obj X = coefficientSmoothPresheaf R e ι X.ρ :=
  rfl

/-- Forms with coefficients `L m` for an inverse system `L` of coefficients, as a presheaf on the
compact open levels of the coefficient domain of inverse systems of representations of `H`. -/
def coefficientFormsSystem (L : ℕᵒᵖ ⥤ Rep.{t} R D) :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ ℕᵒᵖ ⥤ Rep.{max uG t} R H :=
  (L ⋙ coefficientFormsBifunctor R e ι).flip

/-- Smooth forms with coefficients `L m` for an inverse system `L` of coefficients, as a presheaf
of inverse systems of smooth representations of `H`. -/
def coefficientSmoothSystem (L : ℕᵒᵖ ⥤ Rep.{t} R D) :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ ℕᵒᵖ ⥤ SmoothRep.{uR, uH, max uG t} R H :=
  (L ⋙ coefficientSmoothBifunctor R e ι).flip

end Functoriality

section Limits

variable (R : Type uR) [CommRing R] {Γ : Type uΓ} {G : Type uG} {H : Type uH} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H'] (e : G ≃ₜ* H × H') (ι : Γ →* G) {D : Subgroup G}

/-- Forms with right translation followed by the forgetful functor to `R`-modules is the
published `formsFunctor`. -/
def formsRepFunctorCompForget₂Iso (K : Subgroup G) (ψ : H →* G)
    (hψ : ∀ (h : H) (k : K), ψ h * k = k * ψ h) :
    formsRepFunctor.{t} R ι K ψ hψ ⋙ forget₂ (Rep.{max uG t} R H) (ModuleCat.{max uG t} R) ≅
      formsFunctor.{t} R ι K :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

/-- Forms with right translation preserve limits: after the forgetful functor, which reflects
limits, they are the published `formsFunctor`, which preserves limits. -/
instance formsRepFunctor_preservesLimits (K : Subgroup G) (ψ : H →* G)
    (hψ : ∀ (h : H) (k : K), ψ h * k = k * ψ h) :
    PreservesLimits (formsRepFunctor R ι K ψ hψ : Rep.{max uG t} R K ⥤ Rep.{max uG t} R H) :=
  have : PreservesLimits (formsRepFunctor R ι K ψ hψ ⋙
      forget₂ (Rep.{max uG t} R H) (ModuleCat.{max uG t} R)) :=
    preservesLimits_of_natIso (formsRepFunctorCompForget₂Iso.{max uG t} R ι K ψ hψ).symm
  preservesLimits_of_reflects_of_preserves _ (forget₂ (Rep.{max uG t} R H) (ModuleCat R))

/-- `coefficientRepFunctor` preserves limits, as a composite of Mathlib's restriction and
`formsRepFunctor`. -/
instance coefficientRepFunctor_preservesLimits (K' : Subgroup (coefficientDomain e D)) :
    PreservesLimits
      (coefficientRepFunctor R e ι K' : Rep.{max uG t} R D ⥤ Rep.{max uG t} R H) := by
  unfold coefficientRepFunctor
  infer_instance

/-- The functor `coefficientFormsBifunctor` preserves limits: limits of presheaves are computed
levelwise, and at each level it is `coefficientRepFunctor`. -/
instance coefficientFormsBifunctor_preservesLimits [IsTopologicalGroup H'] :
    PreservesLimitsOfSize.{max uG t, max uG t} (coefficientFormsBifunctor R e ι :
      Rep.{max uG t} R D ⥤ (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ Rep.{max uG t} R H) :=
  preservesLimits_of_evaluation _ fun K' =>
    preservesLimits_of_natIso (F := (coefficientRepFunctor R e ι K'.unop.subgroup :
      Rep.{max uG t} R D ⥤ Rep.{max uG t} R H)) (NatIso.ofComponents (fun _ => Iso.refl _))

/-- The functor `coefficientSmoothBifunctor` preserves limits: at each level it is
`coefficientRepFunctor` followed by the smooth part, a right adjoint. -/
instance coefficientSmoothBifunctor_preservesLimits [IsTopologicalGroup H] [IsTopologicalGroup H'] :
    PreservesLimitsOfSize.{max uG t, max uG t} (coefficientSmoothBifunctor R e ι :
      Rep.{max uG t} R D ⥤
        (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ SmoothRep.{uR, uH, max uG t} R H) :=
  have : PreservesLimits (SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H) :=
    (SmoothRep.toRepSmoothPartAdjunction R H).rightAdjoint_preservesLimits
  preservesLimits_of_evaluation _ fun K' =>
    preservesLimits_of_natIso (F := (coefficientRepFunctor R e ι K'.unop.subgroup :
      Rep.{max uG t} R D ⥤ Rep.{max uG t} R H) ⋙
        SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H)
      (NatIso.ofComponents (fun _ => Iso.refl _))

variable [IsTopologicalGroup H'] (ℓ : ℕ) {L : Rep.{max uG t} R D}
  (hL : IsAdicComplete (Ideal.span {(ℓ : R)}) L)

/-- For coefficients `L` that are `ℓ`-adically complete, the presheaf of forms with
coefficients `L` is the inverse limit of the presheaves of forms with coefficients
`L / ℓ ^ m L`, via the projections. -/
def isLimitCoefficientFormsReductionCone :
    IsLimit ((coefficientFormsBifunctor R e ι).mapCone (DivisibleSystem.reductionCone ℓ L)) :=
  have := preservesSmallestLimits_of_preservesLimits (coefficientFormsBifunctor R e ι :
    Rep.{max uG t} R D ⥤ (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ Rep.{max uG t} R H)
  isLimitOfPreserves _ (DivisibleSystem.isLimitReductionCone ℓ hL)

/-- For coefficients `L` that are `ℓ`-adically complete, the presheaf of smooth forms with
coefficients `L` is the inverse limit of the presheaves of smooth forms with coefficients
`L / ℓ ^ m L`, via the projections. -/
def isLimitCoefficientSmoothReductionCone [IsTopologicalGroup H] :
    IsLimit ((coefficientSmoothBifunctor R e ι).mapCone (DivisibleSystem.reductionCone ℓ L)) :=
  have := preservesSmallestLimits_of_preservesLimits (coefficientSmoothBifunctor R e ι :
    Rep.{max uG t} R D ⥤
      (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ SmoothRep.{uR, uH, max uG t} R H)
  isLimitOfPreserves _ (DivisibleSystem.isLimitReductionCone ℓ hL)

end Limits

section CoefficientExt

variable (R : Type u) [CommRing R] {Γ : Type uΓ} {G : Type u} {H : Type u} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group H'] [TopologicalSpace H'] (e : G ≃ₜ* H × H') (ι : Γ →* G) {D : Subgroup G}

/-- The presheaves `coefficientExtPresheaf` of `Ext^i(W, -)` of the smooth forms with
coefficients `X`, as a functor of `X`. -/
def coefficientExtBifunctor (W : SmoothRep.{u, u, u} R H) (i : ℕ) :
    Rep.{u} R D ⥤ (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ ModuleCat.{u} R :=
  coefficientSmoothBifunctor R e ι ⋙
    (Functor.whiskeringRight _ _ _).obj (SmoothExt.ext R H W i)

lemma coefficientExtBifunctor_obj (W : SmoothRep.{u, u, u} R H) (i : ℕ) (X : Rep.{u} R D) :
    (coefficientExtBifunctor R e ι W i).obj X = coefficientExtPresheaf R e ι X.ρ W i :=
  rfl

/-- `Ext^i(W, -)` of the smooth forms with coefficients `L m`, for an inverse system `L` of
coefficients, as a presheaf of inverse systems of `R`-modules. -/
def coefficientExtSystem (W : SmoothRep.{u, u, u} R H) (i : ℕ) (L : ℕᵒᵖ ⥤ Rep.{u} R D) :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  (L ⋙ coefficientExtBifunctor R e ι W i).flip

/-- The comparison map from `Ext^i(W, -)` of the smooth forms with coefficients `L` to the inverse
limit over `m` of `Ext^i(W, -)` of the smooth forms with coefficients `L / ℓ ^ m L`, induced by
the projections `L ⟶ L / ℓ ^ m L`. -/
def coefficientExtReductionComparison (W : SmoothRep.{u, u, u} R H) (i : ℕ) (ℓ : ℕ)
    (L : Rep.{u} R D) :
    (coefficientExtBifunctor R e ι W i).obj L ⟶
      limit (DivisibleSystem.reductionTower ℓ L ⋙ coefficientExtBifunctor R e ι W i) :=
  limit.lift _ ((coefficientExtBifunctor R e ι W i).mapCone (DivisibleSystem.reductionCone ℓ L))

@[reassoc (attr := simp)]
lemma coefficientExtReductionComparison_π (W : SmoothRep.{u, u, u} R H) (i : ℕ) (ℓ : ℕ)
    (L : Rep.{u} R D) (m : ℕ) :
    coefficientExtReductionComparison R e ι W i ℓ L ≫ limit.π _ (op m) =
      (coefficientExtBifunctor R e ι W i).map (DivisibleSystem.reductionπ ℓ L m) :=
  limit.lift_π _ _

variable [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R H)]

/-- The presheaves `coefficientAbutmentPresheaf` of the abutments `Hom(X, A(K')[n])`,
for the smooth forms `A(K')` with coefficients `Y`, as a functor of `Y`. -/
def coefficientAbutmentBifunctor (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ) :
    Rep.{u} R D ⥤ (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  coefficientSmoothBifunctor R e ι ⋙ (Functor.whiskeringRight _ _ _).obj
    (singleFunctor _ 0 ⋙ shiftFunctor _ n ⋙ preadditiveCoyoneda.obj (op X))

lemma coefficientAbutmentBifunctor_obj (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ)
    (Y : Rep.{u} R D) :
    (coefficientAbutmentBifunctor R e ι X n).obj Y = coefficientAbutmentPresheaf R e ι Y.ρ X n :=
  rfl

/-- The presheaves `coefficientFiltrationPresheaf` of the filtration steps `F^p` of
the abutments, for the smooth forms with coefficients `Y`, as a functor of `Y`. -/
def coefficientFiltrationBifunctor (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) :
    Rep.{u} R D ⥤ (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  coefficientSmoothBifunctor R e ι ⋙ (Functor.whiskeringRight _ _ _).obj
    (singleFunctor _ 0 ⋙ HyperextAbutment.filtrationFunctor TStructure.t X n p)

lemma coefficientFiltrationBifunctor_obj (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (Y : Rep.{u} R D) :
    (coefficientFiltrationBifunctor R e ι X n p).obj Y =
      coefficientFiltrationPresheaf R e ι Y.ρ X n p :=
  rfl

/-- The presheaves `coefficientGradedPresheaf` of the graded pieces `gr^p` of the
abutment filtrations, for the smooth forms with coefficients `Y`, as a functor of `Y`. -/
def coefficientGradedBifunctor (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) :
    Rep.{u} R D ⥤ (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  coefficientSmoothBifunctor R e ι ⋙ (Functor.whiskeringRight _ _ _).obj
    (singleFunctor _ 0 ⋙ HyperextAbutment.gradedFunctor TStructure.t X n p)

lemma coefficientGradedBifunctor_obj (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (Y : Rep.{u} R D) :
    (coefficientGradedBifunctor R e ι X n p).obj Y =
      coefficientGradedPresheaf R e ι Y.ρ X n p :=
  rfl

/-- The inclusions `F^p ⟶ Hom(X, A(K')[n])` of `coefficientFiltrationι`, natural in the
coefficients. -/
def coefficientFiltrationBifunctorι (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) :
    coefficientFiltrationBifunctor (D := D) R e ι X n p ⟶ coefficientAbutmentBifunctor R e ι X n :=
  Functor.whiskerLeft (coefficientSmoothBifunctor R e ι) ((Functor.whiskeringRight _ _ _).map
    (Functor.whiskerLeft (singleFunctor _ 0) (HyperextAbutment.filtrationι TStructure.t X n p)))

lemma coefficientFiltrationBifunctorι_app (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (Y : Rep.{u} R D) :
    (coefficientFiltrationBifunctorι R e ι X n p).app Y = coefficientFiltrationι R e ι Y.ρ X n p :=
  rfl

/-- The inclusions `F^q ⟶ F^p` of `coefficientFiltrationMapOfLE` for `p ≤ q`, natural in the
coefficients. -/
def coefficientFiltrationBifunctorMapOfLE (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n : ℤ) {p q : ℤ} (hpq : p ≤ q) :
    coefficientFiltrationBifunctor (D := D) R e ι X n q ⟶
      coefficientFiltrationBifunctor R e ι X n p :=
  Functor.whiskerLeft (coefficientSmoothBifunctor R e ι) ((Functor.whiskeringRight _ _ _).map
    (Functor.whiskerLeft (singleFunctor _ 0)
      (HyperextAbutment.filtrationMapOfLE TStructure.t X n hpq)))

lemma coefficientFiltrationBifunctorMapOfLE_app (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n : ℤ) {p q : ℤ} (hpq : p ≤ q) (Y : Rep.{u} R D) :
    (coefficientFiltrationBifunctorMapOfLE R e ι X n hpq).app Y =
      coefficientFiltrationMapOfLE R e ι Y.ρ X n hpq :=
  rfl

/-- The projections `F^p ⟶ gr^p` of `coefficientGradedπ`, natural in the coefficients. -/
def coefficientGradedBifunctorπ (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) :
    coefficientFiltrationBifunctor (D := D) R e ι X n p ⟶ coefficientGradedBifunctor R e ι X n p :=
  Functor.whiskerLeft (coefficientSmoothBifunctor R e ι) ((Functor.whiskeringRight _ _ _).map
    (Functor.whiskerLeft (singleFunctor _ 0) (HyperextAbutment.gradedπ TStructure.t X n p)))

lemma coefficientGradedBifunctorπ_app (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (Y : Rep.{u} R D) :
    (coefficientGradedBifunctorπ R e ι X n p).app Y = coefficientGradedπ R e ι Y.ρ X n p :=
  rfl

/-- The abutments `Hom(X, A(K')[n])` for the smooth forms with coefficients `L m`, for an
inverse system `L` of coefficients, as a presheaf of inverse systems of abelian groups. -/
def coefficientAbutmentSystem (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ)
    (L : ℕᵒᵖ ⥤ Rep.{u} R D) :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ ℕᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (L ⋙ coefficientAbutmentBifunctor R e ι X n).flip

/-- The filtration steps `F^p` of the abutments for the smooth forms with coefficients `L m`, as
a presheaf of inverse systems of abelian groups. -/
def coefficientFiltrationSystem (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (L : ℕᵒᵖ ⥤ Rep.{u} R D) :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ ℕᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (L ⋙ coefficientFiltrationBifunctor R e ι X n p).flip

/-- The graded pieces `gr^p` of the abutment filtrations for the smooth forms with coefficients
`L m`, as a presheaf of inverse systems of abelian groups. -/
def coefficientGradedSystem (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (L : ℕᵒᵖ ⥤ Rep.{u} R D) :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ ℕᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (L ⋙ coefficientGradedBifunctor R e ι X n p).flip

/-- The inclusions `F^p ⟶ Hom(X, A(K')[n])` for the coefficients `L m`, as a morphism of
presheaves of inverse systems. -/
def coefficientFiltrationSystemι (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (L : ℕᵒᵖ ⥤ Rep.{u} R D) :
    coefficientFiltrationSystem R e ι X n p L ⟶ coefficientAbutmentSystem R e ι X n L :=
  (flipFunctor _ _ _).map (Functor.whiskerLeft L (coefficientFiltrationBifunctorι R e ι X n p))

/-- The inclusions `F^q ⟶ F^p` for `p ≤ q` and the coefficients `L m`, as a morphism of
presheaves of inverse systems. -/
def coefficientFiltrationSystemMapOfLE (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ)
    {p q : ℤ} (hpq : p ≤ q) (L : ℕᵒᵖ ⥤ Rep.{u} R D) :
    coefficientFiltrationSystem R e ι X n q L ⟶ coefficientFiltrationSystem R e ι X n p L :=
  (flipFunctor _ _ _).map
    (Functor.whiskerLeft L (coefficientFiltrationBifunctorMapOfLE R e ι X n hpq))

/-- The projections `F^p ⟶ gr^p` for the coefficients `L m`, as a morphism of presheaves of
inverse systems. -/
def coefficientGradedSystemπ (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (L : ℕᵒᵖ ⥤ Rep.{u} R D) :
    coefficientFiltrationSystem R e ι X n p L ⟶ coefficientGradedSystem R e ι X n p L :=
  (flipFunctor _ _ _).map (Functor.whiskerLeft L (coefficientGradedBifunctorπ R e ι X n p))

/-- The comparison map from the abutments `Hom(X, A(K')[n])` for the coefficients `L` to the
inverse limit over `m` of those for the coefficients `L / ℓ ^ m L`, induced by the projections
`L ⟶ L / ℓ ^ m L`. -/
def coefficientAbutmentReductionComparison (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n : ℤ) (ℓ : ℕ) (L : Rep.{u} R D) :
    (coefficientAbutmentBifunctor R e ι X n).obj L ⟶
      limit (DivisibleSystem.reductionTower ℓ L ⋙ coefficientAbutmentBifunctor R e ι X n) :=
  limit.lift _
    ((coefficientAbutmentBifunctor R e ι X n).mapCone (DivisibleSystem.reductionCone ℓ L))

/-- The comparison map from the filtration steps `F^p` for the coefficients `L` to the inverse
limit over `m` of those for the coefficients `L / ℓ ^ m L`. -/
def coefficientFiltrationReductionComparison (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (ℓ : ℕ) (L : Rep.{u} R D) :
    (coefficientFiltrationBifunctor R e ι X n p).obj L ⟶
      limit (DivisibleSystem.reductionTower ℓ L ⋙ coefficientFiltrationBifunctor R e ι X n p) :=
  limit.lift _
    ((coefficientFiltrationBifunctor R e ι X n p).mapCone (DivisibleSystem.reductionCone ℓ L))

/-- The comparison map from the graded pieces `gr^p` for the coefficients `L` to the inverse
limit over `m` of those for the coefficients `L / ℓ ^ m L`. -/
def coefficientGradedReductionComparison (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (ℓ : ℕ) (L : Rep.{u} R D) :
    (coefficientGradedBifunctor R e ι X n p).obj L ⟶
      limit (DivisibleSystem.reductionTower ℓ L ⋙ coefficientGradedBifunctor R e ι X n p) :=
  limit.lift _
    ((coefficientGradedBifunctor R e ι X n p).mapCone (DivisibleSystem.reductionCone ℓ L))

@[reassoc (attr := simp)]
lemma coefficientAbutmentReductionComparison_π (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n : ℤ) (ℓ : ℕ) (L : Rep.{u} R D) (m : ℕ) :
    coefficientAbutmentReductionComparison R e ι X n ℓ L ≫ limit.π _ (op m) =
      (coefficientAbutmentBifunctor R e ι X n).map (DivisibleSystem.reductionπ ℓ L m) :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma coefficientFiltrationReductionComparison_π
    (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) (ℓ : ℕ) (L : Rep.{u} R D) (m : ℕ) :
    coefficientFiltrationReductionComparison R e ι X n p ℓ L ≫ limit.π _ (op m) =
      (coefficientFiltrationBifunctor R e ι X n p).map (DivisibleSystem.reductionπ ℓ L m) :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma coefficientGradedReductionComparison_π (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (ℓ : ℕ) (L : Rep.{u} R D) (m : ℕ) :
    coefficientGradedReductionComparison R e ι X n p ℓ L ≫ limit.π _ (op m) =
      (coefficientGradedBifunctor R e ι X n p).map (DivisibleSystem.reductionπ ℓ L m) :=
  limit.lift_π _ _

/-- The comparison maps commute with the inclusions `F^p ⟶ Hom(X, A(K')[n])`. -/
lemma coefficientFiltrationReductionComparison_ι
    (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) (ℓ : ℕ) (L : Rep.{u} R D) :
    coefficientFiltrationReductionComparison R e ι X n p ℓ L ≫
        limMap (Functor.whiskerLeft (DivisibleSystem.reductionTower ℓ L)
          (coefficientFiltrationBifunctorι R e ι X n p)) =
      (coefficientFiltrationBifunctorι R e ι X n p).app L ≫
        coefficientAbutmentReductionComparison R e ι X n ℓ L :=
  limit.hom_ext fun m => by
    simp only [Category.assoc, limMap_π, Functor.whiskerLeft_app]
    erw [coefficientAbutmentReductionComparison_π R e ι X n ℓ L m.unop,
      coefficientFiltrationReductionComparison_π_assoc R e ι X n p ℓ L m.unop]
    exact ((coefficientFiltrationBifunctorι R e ι X n p).naturality _).symm

/-- The comparison maps commute with the projections `F^p ⟶ gr^p`. -/
lemma coefficientFiltrationReductionComparison_gradedπ
    (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) (ℓ : ℕ) (L : Rep.{u} R D) :
    coefficientFiltrationReductionComparison R e ι X n p ℓ L ≫
        limMap (Functor.whiskerLeft (DivisibleSystem.reductionTower ℓ L)
          (coefficientGradedBifunctorπ R e ι X n p)) =
      (coefficientGradedBifunctorπ R e ι X n p).app L ≫
        coefficientGradedReductionComparison R e ι X n p ℓ L :=
  limit.hom_ext fun m => by
    simp only [Category.assoc, limMap_π, Functor.whiskerLeft_app]
    erw [coefficientGradedReductionComparison_π R e ι X n p ℓ L m.unop,
      coefficientFiltrationReductionComparison_π_assoc R e ι X n p ℓ L m.unop]
    exact ((coefficientGradedBifunctorπ R e ι X n p).naturality _).symm

end CoefficientExt

end Langlands.Shimura.EquivariantForms

namespace Langlands.Shimura.DefiniteForms

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategory
open Langlands.Global Langlands.Cohomology Langlands.Shimura.EquivariantForms
open Langlands.Shimura.CompactOpenLevel
open scoped NumberField

universe u w

section ResidueCharacteristic

variable (ℓ : FinitePlace ℚ)

/-- The published residue characteristic of a finite place `ℓ` of `ℚ` is prime. -/
lemma residueCharacteristic_prime : (GaloisRepresentation.residueCharacteristic ℓ).Prime := by
  unfold GaloisRepresentation.residueCharacteristic
  rw [← CompletionResidue.ringChar_residueField]
  exact CompletionResidue.prime_ringChar_residueField ℚ ℓ

instance residueCharacteristic_neZero : NeZero (GaloisRepresentation.residueCharacteristic ℓ) :=
  ⟨(residueCharacteristic_prime ℓ).ne_zero⟩

/-- The residue characteristic of `ℓ` lies in the prime ideal of `ℓ`. -/
lemma natCast_residueCharacteristic_mem :
    ((GaloisRepresentation.residueCharacteristic ℓ : ℕ) : 𝓞 ℚ) ∈ ℓ.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

end ResidueCharacteristic

section DividingSystem

variable {A : Type u} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (ℓ : FinitePlace ℚ) (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ ℓ))) (R : Type u) [CommRing R]

/-- Mathlib's restriction along the `ℓ`-component map `g ↦ g_ℓ`, sending a representation `𝓛`
of `Kℓ` to `localCoefficientRep σ ℓ Kℓ 𝓛`. -/
abbrev localCoefficientFunctor : Rep.{u} R Kℓ ⥤ Rep.{u} R (localCoefficientDomain σ ℓ Kℓ) :=
  Rep.resFunctor (localCoefficientMap σ ℓ Kℓ)

lemma localCoefficientFunctor_obj_ρ (𝓛 : Rep.{u} R Kℓ) :
    ((localCoefficientFunctor σ ℓ Kℓ R).obj 𝓛).ρ = localCoefficientRep σ ℓ Kℓ 𝓛.ρ :=
  rfl

variable (p : ℕ) (hp : p ≠ 0)

/-- The forms of level `e⁻¹ (1 × K')` with coefficients `𝓛` composed with the `ℓ`-component map,
with right translation by `GJ(∏_{v ∣ p} ℚ_v)`, as a functor of the representation `𝓛` of `Kℓ`
to presheaves on the compact open levels of `dividingCoefficientDomain σ ℓ Kℓ p hp`. -/
def dividingCoefficientFormsBifunctor :
    Rep.{u} R Kℓ ⥤
      (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤
        Rep.{u} R (σ.DividingPoints p) :=
  localCoefficientFunctor σ ℓ Kℓ R ⋙
    coefficientFormsBifunctor R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal

lemma dividingCoefficientFormsBifunctor_obj (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientFormsBifunctor σ ℓ Kℓ R p hp).obj 𝓛 =
      coefficientFormsPresheaf R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
        (localCoefficientRep σ ℓ Kℓ 𝓛.ρ) :=
  rfl

/-- `dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛 p hp`, as a functor of the
representation `𝓛` of `Kℓ`. -/
def dividingCoefficientSmoothBifunctor :
    Rep.{u} R Kℓ ⥤
      (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤
        SmoothRep.{u, u, u} R (σ.DividingPoints p) :=
  localCoefficientFunctor σ ℓ Kℓ R ⋙
    coefficientSmoothBifunctor R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal

lemma dividingCoefficientSmoothBifunctor_obj (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientSmoothBifunctor σ ℓ Kℓ R p hp).obj 𝓛 =
      dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛.ρ p hp :=
  rfl

/-- `dividingCoefficientExtPresheaf σ ℓ Kℓ 𝓛 p hp W i`, as a functor of the
representation `𝓛` of `Kℓ`. -/
def dividingCoefficientExtBifunctor (W : SmoothRep.{u, u, u} R (σ.DividingPoints p)) (i : ℕ) :
    Rep.{u} R Kℓ ⥤ (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ ModuleCat.{u} R :=
  localCoefficientFunctor σ ℓ Kℓ R ⋙
    coefficientExtBifunctor R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal W i

lemma dividingCoefficientExtBifunctor_obj (W : SmoothRep.{u, u, u} R (σ.DividingPoints p))
    (i : ℕ) (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientExtBifunctor σ ℓ Kℓ R p hp W i).obj 𝓛 =
      dividingCoefficientExtPresheaf σ ℓ Kℓ 𝓛.ρ p hp W i :=
  rfl

/-- Harris's inverse system `m ↦ 𝓛_m = 𝓛 / l ^ m 𝓛` (1999, §4, p.311), for the residue
characteristic `l` of `ℓ`, taken through the forms: the forms of level `e⁻¹ (1 × K')` with
coefficients `𝓛_m` composed with the `ℓ`-component map, as a presheaf of inverse systems of
representations of `GJ(∏_{v ∣ p} ℚ_v)`. -/
def dividingReductionFormsSystem (𝓛 : Rep.{u} R Kℓ) :
    (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤
      ℕᵒᵖ ⥤ Rep.{u} R (σ.DividingPoints p) :=
  (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 ⋙
    dividingCoefficientFormsBifunctor σ ℓ Kℓ R p hp).flip

/-- `dividingReductionFormsSystem` is the general `coefficientFormsSystem` for the inverse
system `m ↦ 𝓛_m` composed with the `ℓ`-component map. -/
lemma dividingReductionFormsSystem_eq (𝓛 : Rep.{u} R Kℓ) :
    dividingReductionFormsSystem σ ℓ Kℓ R p hp 𝓛 =
      coefficientFormsSystem R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
        (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 ⋙
          localCoefficientFunctor σ ℓ Kℓ R) :=
  rfl

/-- Harris's inverse system `m ↦ 𝓛_m` taken through the smooth forms: the presheaf of inverse
systems `m ↦ dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛_m p hp`. -/
def dividingReductionSmoothSystem (𝓛 : Rep.{u} R Kℓ) :
    (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤
      ℕᵒᵖ ⥤ SmoothRep.{u, u, u} R (σ.DividingPoints p) :=
  (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 ⋙
    dividingCoefficientSmoothBifunctor σ ℓ Kℓ R p hp).flip

/-- Harris's inverse system `m ↦ 𝓛_m` taken through `Ext^i(W, -)` of the smooth forms: the
presheaf of inverse systems `m ↦ dividingCoefficientExtPresheaf σ ℓ Kℓ 𝓛_m p hp W i`. -/
def dividingReductionExtSystem (W : SmoothRep.{u, u, u} R (σ.DividingPoints p)) (i : ℕ)
    (𝓛 : Rep.{u} R Kℓ) :
    (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 ⋙
    dividingCoefficientExtBifunctor σ ℓ Kℓ R p hp W i).flip

/-- The comparison map from `Ext^i(W, -)` of the smooth forms with coefficients `𝓛` to the
inverse limit over `m` of `Ext^i(W, -)` of the smooth forms with coefficients `𝓛_m`, induced by
the projections `𝓛 ⟶ 𝓛_m`. -/
def dividingReductionExtComparison (W : SmoothRep.{u, u, u} R (σ.DividingPoints p)) (i : ℕ)
    (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientExtBifunctor σ ℓ Kℓ R p hp W i).obj 𝓛 ⟶
      limit (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 ⋙
        dividingCoefficientExtBifunctor σ ℓ Kℓ R p hp W i) :=
  limit.lift _ ((dividingCoefficientExtBifunctor σ ℓ Kℓ R p hp W i).mapCone
    (DivisibleSystem.reductionCone _ 𝓛))

@[reassoc (attr := simp)]
lemma dividingReductionExtComparison_π (W : SmoothRep.{u, u, u} R (σ.DividingPoints p)) (i : ℕ)
    (𝓛 : Rep.{u} R Kℓ) (m : ℕ) :
    dividingReductionExtComparison σ ℓ Kℓ R p hp W i 𝓛 ≫ limit.π _ (op m) =
      (dividingCoefficientExtBifunctor σ ℓ Kℓ R p hp W i).map
        (DivisibleSystem.reductionπ (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 m) :=
  limit.lift_π _ _

section DividingAbutment

variable [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R (σ.DividingPoints p))]

/-- `dividingCoefficientAbutmentPresheaf σ ℓ Kℓ 𝓛 p hp X n`, as a functor of the representation
`𝓛` of `Kℓ`. -/
def dividingCoefficientAbutmentBifunctor
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ) :
    Rep.{u} R Kℓ ⥤
      (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  localCoefficientFunctor σ ℓ Kℓ R ⋙
    coefficientAbutmentBifunctor R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal X n

lemma dividingCoefficientAbutmentBifunctor_obj
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientAbutmentBifunctor σ ℓ Kℓ R p hp X n).obj 𝓛 =
      dividingCoefficientAbutmentPresheaf σ ℓ Kℓ 𝓛.ρ p hp X n :=
  rfl

/-- `dividingCoefficientFiltrationPresheaf σ ℓ Kℓ 𝓛 p hp X n i`, as a functor of the
representation `𝓛` of `Kℓ`. -/
def dividingCoefficientFiltrationBifunctor
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ) :
    Rep.{u} R Kℓ ⥤
      (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  localCoefficientFunctor σ ℓ Kℓ R ⋙
    coefficientFiltrationBifunctor R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
      X n i

lemma dividingCoefficientFiltrationBifunctor_obj
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientFiltrationBifunctor σ ℓ Kℓ R p hp X n i).obj 𝓛 =
      dividingCoefficientFiltrationPresheaf σ ℓ Kℓ 𝓛.ρ p hp X n i :=
  rfl

/-- `dividingCoefficientGradedPresheaf σ ℓ Kℓ 𝓛 p hp X n i`, as a functor of the
representation `𝓛` of `Kℓ`. -/
def dividingCoefficientGradedBifunctor
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ) :
    Rep.{u} R Kℓ ⥤
      (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  localCoefficientFunctor σ ℓ Kℓ R ⋙
    coefficientGradedBifunctor R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal X n i

lemma dividingCoefficientGradedBifunctor_obj
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientGradedBifunctor σ ℓ Kℓ R p hp X n i).obj 𝓛 =
      dividingCoefficientGradedPresheaf σ ℓ Kℓ 𝓛.ρ p hp X n i :=
  rfl

/-- The inclusions `dividingCoefficientFiltrationι` of `F^i` into `Hom(X, A(K')[n])`, natural
in the representation `𝓛` of `Kℓ`. -/
def dividingCoefficientFiltrationBifunctorι
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ) :
    dividingCoefficientFiltrationBifunctor σ ℓ Kℓ R p hp X n i ⟶
      dividingCoefficientAbutmentBifunctor σ ℓ Kℓ R p hp X n :=
  Functor.whiskerLeft (localCoefficientFunctor σ ℓ Kℓ R)
    (coefficientFiltrationBifunctorι R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
      X n i)

lemma dividingCoefficientFiltrationBifunctorι_app
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientFiltrationBifunctorι σ ℓ Kℓ R p hp X n i).app 𝓛 =
      dividingCoefficientFiltrationι σ ℓ Kℓ 𝓛.ρ p hp X n i :=
  rfl

/-- The inclusions `dividingCoefficientFiltrationMapOfLE` of `F^j` into `F^i` for `i ≤ j`,
natural in the representation `𝓛` of `Kℓ`. -/
def dividingCoefficientFiltrationBifunctorMapOfLE
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ) {i j : ℤ}
    (hij : i ≤ j) :
    dividingCoefficientFiltrationBifunctor σ ℓ Kℓ R p hp X n j ⟶
      dividingCoefficientFiltrationBifunctor σ ℓ Kℓ R p hp X n i :=
  Functor.whiskerLeft (localCoefficientFunctor σ ℓ Kℓ R)
    (coefficientFiltrationBifunctorMapOfLE R (σ.finiteAdelicPointsSplit p hp)
      σ.finiteAdelicDiagonal X n hij)

lemma dividingCoefficientFiltrationBifunctorMapOfLE_app
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ) {i j : ℤ}
    (hij : i ≤ j) (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientFiltrationBifunctorMapOfLE σ ℓ Kℓ R p hp X n hij).app 𝓛 =
      dividingCoefficientFiltrationMapOfLE σ ℓ Kℓ 𝓛.ρ p hp X n hij :=
  rfl

/-- The projections `dividingCoefficientGradedπ` of `F^i` onto `gr^i`, natural in the
representation `𝓛` of `Kℓ`. -/
def dividingCoefficientGradedBifunctorπ
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ) :
    dividingCoefficientFiltrationBifunctor σ ℓ Kℓ R p hp X n i ⟶
      dividingCoefficientGradedBifunctor σ ℓ Kℓ R p hp X n i :=
  Functor.whiskerLeft (localCoefficientFunctor σ ℓ Kℓ R)
    (coefficientGradedBifunctorπ R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
      X n i)

lemma dividingCoefficientGradedBifunctorπ_app
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientGradedBifunctorπ σ ℓ Kℓ R p hp X n i).app 𝓛 =
      dividingCoefficientGradedπ σ ℓ Kℓ 𝓛.ρ p hp X n i :=
  rfl

/-- Harris's inverse system `m ↦ 𝓛_m` taken through the abutments: the presheaf of inverse
systems `m ↦ dividingCoefficientAbutmentPresheaf σ ℓ Kℓ 𝓛_m p hp X n`. -/
def dividingReductionAbutmentSystem
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ ℕᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 ⋙
    dividingCoefficientAbutmentBifunctor σ ℓ Kℓ R p hp X n).flip

/-- Harris's inverse system `m ↦ 𝓛_m` taken through the filtration steps `F^i`: the presheaf of
inverse systems `m ↦ dividingCoefficientFiltrationPresheaf σ ℓ Kℓ 𝓛_m p hp X n i`. -/
def dividingReductionFiltrationSystem
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ ℕᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 ⋙
    dividingCoefficientFiltrationBifunctor σ ℓ Kℓ R p hp X n i).flip

/-- Harris's inverse system `m ↦ 𝓛_m` taken through the graded pieces `gr^i`: the presheaf of
inverse systems `m ↦ dividingCoefficientGradedPresheaf σ ℓ Kℓ 𝓛_m p hp X n i`. -/
def dividingReductionGradedSystem
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ ℕᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 ⋙
    dividingCoefficientGradedBifunctor σ ℓ Kℓ R p hp X n i).flip

/-- The inclusions `F^i ⟶ Hom(X, A(K')[n])` for the coefficients `𝓛_m`, as a morphism of
presheaves of inverse systems. -/
def dividingReductionFiltrationSystemι
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    dividingReductionFiltrationSystem σ ℓ Kℓ R p hp X n i 𝓛 ⟶
      dividingReductionAbutmentSystem σ ℓ Kℓ R p hp X n 𝓛 :=
  (flipFunctor _ _ _).map (Functor.whiskerLeft
    (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛)
    (dividingCoefficientFiltrationBifunctorι σ ℓ Kℓ R p hp X n i))

/-- The inclusions `F^j ⟶ F^i` for `i ≤ j` and the coefficients `𝓛_m`, as a morphism of
presheaves of inverse systems. -/
def dividingReductionFiltrationSystemMapOfLE
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ) {i j : ℤ}
    (hij : i ≤ j) (𝓛 : Rep.{u} R Kℓ) :
    dividingReductionFiltrationSystem σ ℓ Kℓ R p hp X n j 𝓛 ⟶
      dividingReductionFiltrationSystem σ ℓ Kℓ R p hp X n i 𝓛 :=
  (flipFunctor _ _ _).map (Functor.whiskerLeft
    (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛)
    (dividingCoefficientFiltrationBifunctorMapOfLE σ ℓ Kℓ R p hp X n hij))

/-- The projections `F^i ⟶ gr^i` for the coefficients `𝓛_m`, as a morphism of presheaves of
inverse systems. -/
def dividingReductionGradedSystemπ
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    dividingReductionFiltrationSystem σ ℓ Kℓ R p hp X n i 𝓛 ⟶
      dividingReductionGradedSystem σ ℓ Kℓ R p hp X n i 𝓛 :=
  (flipFunctor _ _ _).map (Functor.whiskerLeft
    (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛)
    (dividingCoefficientGradedBifunctorπ σ ℓ Kℓ R p hp X n i))

/-- The comparison map from the abutment `Hom(X, A(K')[n])` for the coefficients `𝓛` to the
inverse limit over `m` of those for the coefficients `𝓛_m`, induced by the projections
`𝓛 ⟶ 𝓛_m`. -/
def dividingReductionAbutmentComparison
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientAbutmentBifunctor σ ℓ Kℓ R p hp X n).obj 𝓛 ⟶
      limit (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 ⋙
        dividingCoefficientAbutmentBifunctor σ ℓ Kℓ R p hp X n) :=
  limit.lift _ ((dividingCoefficientAbutmentBifunctor σ ℓ Kℓ R p hp X n).mapCone
    (DivisibleSystem.reductionCone _ 𝓛))

/-- The comparison map from the filtration step `F^i` for the coefficients `𝓛` to the inverse
limit over `m` of those for the coefficients `𝓛_m`. -/
def dividingReductionFiltrationComparison
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientFiltrationBifunctor σ ℓ Kℓ R p hp X n i).obj 𝓛 ⟶
      limit (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 ⋙
        dividingCoefficientFiltrationBifunctor σ ℓ Kℓ R p hp X n i) :=
  limit.lift _ ((dividingCoefficientFiltrationBifunctor σ ℓ Kℓ R p hp X n i).mapCone
    (DivisibleSystem.reductionCone _ 𝓛))

/-- The comparison map from the graded piece `gr^i` for the coefficients `𝓛` to the inverse
limit over `m` of those for the coefficients `𝓛_m`. -/
def dividingReductionGradedComparison
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    (dividingCoefficientGradedBifunctor σ ℓ Kℓ R p hp X n i).obj 𝓛 ⟶
      limit (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 ⋙
        dividingCoefficientGradedBifunctor σ ℓ Kℓ R p hp X n i) :=
  limit.lift _ ((dividingCoefficientGradedBifunctor σ ℓ Kℓ R p hp X n i).mapCone
    (DivisibleSystem.reductionCone _ 𝓛))

@[reassoc (attr := simp)]
lemma dividingReductionAbutmentComparison_π
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ)
    (𝓛 : Rep.{u} R Kℓ) (m : ℕ) :
    dividingReductionAbutmentComparison σ ℓ Kℓ R p hp X n 𝓛 ≫ limit.π _ (op m) =
      (dividingCoefficientAbutmentBifunctor σ ℓ Kℓ R p hp X n).map
        (DivisibleSystem.reductionπ (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 m) :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma dividingReductionFiltrationComparison_π
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) (m : ℕ) :
    dividingReductionFiltrationComparison σ ℓ Kℓ R p hp X n i 𝓛 ≫ limit.π _ (op m) =
      (dividingCoefficientFiltrationBifunctor σ ℓ Kℓ R p hp X n i).map
        (DivisibleSystem.reductionπ (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 m) :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma dividingReductionGradedComparison_π
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) (m : ℕ) :
    dividingReductionGradedComparison σ ℓ Kℓ R p hp X n i 𝓛 ≫ limit.π _ (op m) =
      (dividingCoefficientGradedBifunctor σ ℓ Kℓ R p hp X n i).map
        (DivisibleSystem.reductionπ (GaloisRepresentation.residueCharacteristic ℓ) 𝓛 m) :=
  limit.lift_π _ _

/-- The comparison maps commute with the inclusions `F^i ⟶ Hom(X, A(K')[n])`. -/
lemma dividingReductionFiltrationComparison_ι
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    dividingReductionFiltrationComparison σ ℓ Kℓ R p hp X n i 𝓛 ≫
        limMap (Functor.whiskerLeft
          (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛)
          (dividingCoefficientFiltrationBifunctorι σ ℓ Kℓ R p hp X n i)) =
      (dividingCoefficientFiltrationBifunctorι σ ℓ Kℓ R p hp X n i).app 𝓛 ≫
        dividingReductionAbutmentComparison σ ℓ Kℓ R p hp X n 𝓛 :=
  limit.hom_ext fun m => by
    simp only [Category.assoc, limMap_π, Functor.whiskerLeft_app]
    erw [dividingReductionAbutmentComparison_π σ ℓ Kℓ R p hp X n 𝓛 m.unop,
      dividingReductionFiltrationComparison_π_assoc σ ℓ Kℓ R p hp X n i 𝓛 m.unop]
    exact ((dividingCoefficientFiltrationBifunctorι σ ℓ Kℓ R p hp X n i).naturality _).symm

/-- The comparison maps commute with the projections `F^i ⟶ gr^i`. -/
lemma dividingReductionFiltrationComparison_gradedπ
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (𝓛 : Rep.{u} R Kℓ) :
    dividingReductionFiltrationComparison σ ℓ Kℓ R p hp X n i 𝓛 ≫
        limMap (Functor.whiskerLeft
          (DivisibleSystem.reductionTower (GaloisRepresentation.residueCharacteristic ℓ) 𝓛)
          (dividingCoefficientGradedBifunctorπ σ ℓ Kℓ R p hp X n i)) =
      (dividingCoefficientGradedBifunctorπ σ ℓ Kℓ R p hp X n i).app 𝓛 ≫
        dividingReductionGradedComparison σ ℓ Kℓ R p hp X n i 𝓛 :=
  limit.hom_ext fun m => by
    simp only [Category.assoc, limMap_π, Functor.whiskerLeft_app]
    erw [dividingReductionGradedComparison_π σ ℓ Kℓ R p hp X n i 𝓛 m.unop,
      dividingReductionFiltrationComparison_π_assoc σ ℓ Kℓ R p hp X n i 𝓛 m.unop]
    exact ((dividingCoefficientGradedBifunctorπ σ ℓ Kℓ R p hp X n i).naturality _).symm

end DividingAbutment

/-- The functor `dividingCoefficientFormsBifunctor` preserves limits. -/
instance dividingCoefficientFormsBifunctor_preservesLimits :
    PreservesLimitsOfSize.{u, u} (dividingCoefficientFormsBifunctor σ ℓ Kℓ R p hp) := by
  unfold dividingCoefficientFormsBifunctor
  infer_instance

/-- The functor `dividingCoefficientSmoothBifunctor` preserves limits. -/
instance dividingCoefficientSmoothBifunctor_preservesLimits :
    PreservesLimitsOfSize.{u, u} (dividingCoefficientSmoothBifunctor σ ℓ Kℓ R p hp) := by
  unfold dividingCoefficientSmoothBifunctor
  infer_instance

variable {R} {𝓛 : Rep.{u} R Kℓ}
  (h𝓛 : IsAdicComplete (Ideal.span {(GaloisRepresentation.residueCharacteristic ℓ : R)}) 𝓛)

/-- For Harris's inverse system (1999, §4, p.311) and the forms: for `𝓛` complete for the
`l`-adic topology, `l` the residue characteristic of `ℓ`, the presheaf of forms with
coefficients `𝓛` is the inverse limit of the presheaves of forms with coefficients
`𝓛_m = 𝓛 / l ^ m 𝓛`, via the projections. -/
def isLimitDividingCoefficientFormsReductionCone :
    IsLimit ((dividingCoefficientFormsBifunctor σ ℓ Kℓ R p hp).mapCone
      (DivisibleSystem.reductionCone (GaloisRepresentation.residueCharacteristic ℓ) 𝓛)) :=
  have := preservesSmallestLimits_of_preservesLimits
    (dividingCoefficientFormsBifunctor σ ℓ Kℓ R p hp)
  isLimitOfPreserves _ (DivisibleSystem.isLimitReductionCone _ h𝓛)

/-- For Harris's inverse system (1999, §4, p.311) and the smooth forms: for `𝓛` complete for the
`l`-adic topology, the presheaf `dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛 p hp` is the inverse
limit of the presheaves `dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛_m p hp`, via the
projections. -/
def isLimitDividingCoefficientSmoothReductionCone :
    IsLimit ((dividingCoefficientSmoothBifunctor σ ℓ Kℓ R p hp).mapCone
      (DivisibleSystem.reductionCone (GaloisRepresentation.residueCharacteristic ℓ) 𝓛)) :=
  have := preservesSmallestLimits_of_preservesLimits
    (dividingCoefficientSmoothBifunctor σ ℓ Kℓ R p hp)
  isLimitOfPreserves _ (DivisibleSystem.isLimitReductionCone _ h𝓛)

end DividingSystem

end Langlands.Shimura.DefiniteForms
