import Langlands.Cohomology.DivisibleSystem.EtaleAdicCohomology

/-!
# Rational `ℓ`-adic étale cohomology by extension of scalars

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, §4, p.311: "the inverse
system `{𝓛̃_m}` defines a lisse `ℓ`-adic sheaf `W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ` on `S̄_{K(N)}`", and the
spectral sequence of Proposition 4.10 has abutment `H^{i+j}(S̄_{K(N)}, W̃)`. Deligne, SGA 4½,
*Rapport*, 2.10, p.84, defines the compactly supported cohomology of a `ℚ_ℓ`-sheaf `F ~ F' ⊗ ℚ_ℓ`
as `(lim H^q_c(X, F' ⊗ ℤ/ℓ^n)) ⊗_{ℤ_ℓ} ℚ_ℓ`; we use the same recipe for ordinary cohomology, with
the inverse limits `adicCohomology` of `EtaleAdicCohomology`.

For a scheme `X`, commutative rings `R` and `S` with an `R`-algebra structure on `S`, extension
of scalars is Mathlib's `ModuleCat.extendScalars (algebraMap R S)`, sending `M` to `S ⊗_R M`.

* `rationalAdicCohomology X R S q`: the functor `F ↦ S ⊗_R lim_m H^q(X, F_m)` on inverse systems
  of étale sheaves of `R`-modules; `rationalAdicSections` is `S ⊗_R lim_m Γ(X, F_m)`, and
  `rationalAdicCohomologyZeroIso` identifies the two in degree zero.
* `rationalLimitComparison X R S q`: the comparison `S ⊗_R H^q(X, lim_m F_m) ⟶ S ⊗_R
  lim_m H^q(X, F_m)` induced by `limitComparison`; it is an isomorphism in degree zero
  (instance). Nothing is claimed in higher degrees.
* `rationalAdicCohomologyUnit X R S q`: the natural map `x ↦ 1 ⊗ x` from `lim_m H^q(X, F_m)` to
  its extension of scalars, the unit of the adjunction `ModuleCat.extendRestrictScalarsAdj`
  (`rationalAdicCohomologyUnit_app_apply`).
* `rationalIdealAdicCohomology S I q`, for an ideal `I` of `R`: `S ⊗_R lim_n H^q(X, F / I ^ n F)`,
  with the degree-zero identification `rationalIdealAdicCohomologyZeroIso`.
* `equivariantRationalAdicCohomology R S ρ q`, `equivariantRationalAdicSections R S ρ` and
  `equivariantRationalIdealAdicCohomology S ρ I q`: the same modules for sheaves equivariant for
  an action `ρ` of a group `G` on `X`, as representations of `G` acting on the second tensor
  factor (`Functor.mapAction` of extension of scalars); their underlying modules are the
  non-equivariant ones (`equivariantRationalAdicCohomologyForgetIso`,
  `equivariantRationalIdealAdicCohomologyForgetIso`), with the degree-zero identification
  `equivariantRationalAdicCohomologyZeroIso` and the `G`-equivariant unit
  `equivariantRationalAdicCohomologyUnit`.
* `harrisEtaleRationalCohomology ℓ ρ p U X Y hY q`: Harris's `H^q(X, W̃)`, the extension of
  scalars of the published `harrisEtaleAdicCohomology` (`lim_m H^q(X, 𝓛̃_m)`) along the published
  `harrisCoefficientIntegersMap` from `𝒪 = HarrisCoefficientIntegers L p` to
  `L_p = L ⊗_ℚ ℚ_p`; with its unit `harrisEtaleRationalCohomologyUnit` and the degree-zero
  identifications `harrisEtaleRationalCohomologyZeroIso`,
  `harrisEtaleRationalCohomologyZeroLimitIso` and, under an explicit surjectivity hypothesis,
  `harrisEtaleRationalCohomologyZeroDivisibleIso`.

The lisse sheaf `W̃` itself, finiteness, independence of the lattice and comparisons in positive
degrees are not formalized.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.Geometry
open scoped ChangeOfRings TensorProduct

universe u w

namespace EtaleAdicCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]

section Rational

/-- `S ⊗_R lim_m H^q(X, F_m)`, the extension of scalars of `adicCohomology X R q`. -/
def rationalAdicCohomology (q : ℕ) :
    (ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) ⥤ ModuleCat.{u} S :=
  adicCohomology X R q ⋙ ModuleCat.extendScalars (algebraMap R S)

/-- `rationalAdicCohomology X R S q` of `F` is `S ⊗_R lim_m H^q(X, F_m)`. -/
lemma rationalAdicCohomology_obj (q : ℕ) (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    (rationalAdicCohomology X R S q).obj F =
      (ModuleCat.extendScalars (algebraMap R S)).obj
        (limit (F ⋙ EtaleDerivedSections.cohomology X R q)) :=
  rfl

/-- `S ⊗_R lim_m Γ(X, F_m)`, the extension of scalars of `adicSections X R`. -/
def rationalAdicSections : (ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) ⥤ ModuleCat.{u} S :=
  adicSections X R ⋙ ModuleCat.extendScalars (algebraMap R S)

/-- In degree zero, `S ⊗_R lim_m H^0(X, F_m) ≅ S ⊗_R lim_m Γ(X, F_m)`. -/
def rationalAdicCohomologyZeroIso : rationalAdicCohomology X R S 0 ≅ rationalAdicSections X R S :=
  Functor.isoWhiskerRight (adicCohomologyZeroIso X R) _

/-- The comparison `S ⊗_R H^q(X, lim_m F_m) ⟶ S ⊗_R lim_m H^q(X, F_m)` induced by
`limitComparison`. -/
def rationalLimitComparison (q : ℕ) :
    (lim ⋙ EtaleDerivedSections.cohomology X R q) ⋙ ModuleCat.extendScalars (algebraMap R S) ⟶
      rationalAdicCohomology X R S q :=
  Functor.whiskerRight (limitComparison X R q) _

/-- In degree zero, the comparison is an isomorphism. -/
instance : IsIso (rationalLimitComparison X R S 0) :=
  Functor.isIso_whiskerRight (limitComparison X R 0) _

/-- The map `lim_m H^q(X, F_m) ⟶ S ⊗_R lim_m H^q(X, F_m)`, `x ↦ 1 ⊗ x`: the unit of the
adjunction between extension and restriction of scalars. -/
def rationalAdicCohomologyUnit (q : ℕ) :
    adicCohomology X R q ⟶
      rationalAdicCohomology X R S q ⋙ ModuleCat.restrictScalars (algebraMap R S) :=
  Functor.whiskerLeft (adicCohomology X R q)
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit

/-- The unit map sends `x` to `1 ⊗ x`. -/
lemma rationalAdicCohomologyUnit_app_apply (q : ℕ)
    (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) (x : (adicCohomology X R q).obj F) :
    (rationalAdicCohomologyUnit X R S q).app F x = (1 : S) ⊗ₜ[R, algebraMap R S] x :=
  rfl

end Rational

section Ideal

variable {X R} (I : Ideal R)

/-- `S ⊗_R lim_n H^q(X, F / I ^ n F)`. -/
def rationalIdealAdicCohomology (q : ℕ) : EtaleDerivedSections.ModuleSheaf X R ⥤ ModuleCat.{u} S :=
  idealAdicCohomology I q ⋙ ModuleCat.extendScalars (algebraMap R S)

/-- `rationalIdealAdicCohomology S I q` is `rationalAdicCohomology` of the reductions
`F / I ^ n F`. -/
lemma rationalIdealAdicCohomology_eq (q : ℕ) :
    rationalIdealAdicCohomology S I q =
      EtaleAdicSystem.functor X I ⋙ rationalAdicCohomology X R S q :=
  rfl

/-- In degree zero, `S ⊗_R lim_n H^0(X, F / I ^ n F) ≅ S ⊗_R Γ(X, lim_n F / I ^ n F)`. -/
def rationalIdealAdicCohomologyZeroIso :
    rationalIdealAdicCohomology S I 0 ≅
      EtaleAdicSystem.functor X I ⋙ lim ⋙ EtaleDerivedSections.sections X R ⋙
        ModuleCat.extendScalars (algebraMap R S) :=
  Functor.isoWhiskerRight (idealAdicCohomologyZeroIso I) _

end Ideal

section Equivariant

variable {X} {G : Type w} [Group G] (ρ : G →* (Aut X)ᵐᵒᵖ)

/-- `S ⊗_R lim_m H^q(X, F_m)` for an inverse system of `ρ`-equivariant sheaves, with `G`
acting through `equivariantAdicCohomology` on the second factor. -/
def equivariantRationalAdicCohomology (q : ℕ) :
    (ℕᵒᵖ ⥤ EtaleCohomologyAction.EquivariantSheaf R ρ) ⥤ Action (ModuleCat.{u} S) G :=
  equivariantAdicCohomology R ρ q ⋙ (ModuleCat.extendScalars (algebraMap R S)).mapAction G

/-- The underlying module of `equivariantRationalAdicCohomology` is `rationalAdicCohomology` of
the underlying inverse system of sheaves. -/
def equivariantRationalAdicCohomologyForgetIso (q : ℕ) :
    equivariantRationalAdicCohomology R S ρ q ⋙ Action.forget (ModuleCat.{u} S) G ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj TranslationAction.Equivariant.forget ⋙
        rationalAdicCohomology X R S q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (equivariantAdicCohomology R ρ q)
      (Iso.refl (Action.forget (ModuleCat.{u} R) G ⋙ ModuleCat.extendScalars (algebraMap R S))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (equivariantAdicCohomologyForgetIso R ρ q) _ ≪≫
    Functor.associator _ _ _

/-- `S ⊗_R lim_m Γ(X, F_m)` with the action of `G` from `equivariantAdicSections`. -/
def equivariantRationalAdicSections :
    (ℕᵒᵖ ⥤ EtaleCohomologyAction.EquivariantSheaf R ρ) ⥤ Action (ModuleCat.{u} S) G :=
  equivariantAdicSections R ρ ⋙ (ModuleCat.extendScalars (algebraMap R S)).mapAction G

/-- In degree zero, `S ⊗_R lim_m H^0(X, F_m) ≅ S ⊗_R lim_m Γ(X, F_m)` as representations
of `G`. -/
def equivariantRationalAdicCohomologyZeroIso :
    equivariantRationalAdicCohomology R S ρ 0 ≅ equivariantRationalAdicSections R S ρ :=
  Functor.isoWhiskerRight (equivariantAdicCohomologyZeroIso R ρ) _

/-- The `G`-equivariant map `x ↦ 1 ⊗ x` from `lim_m H^q(X, F_m)` to its extension of
scalars. -/
def equivariantRationalAdicCohomologyUnit (q : ℕ) :
    equivariantAdicCohomology R ρ q ⟶
      equivariantRationalAdicCohomology R S ρ q ⋙
        (ModuleCat.restrictScalars (algebraMap R S)).mapAction G where
  app _ :=
    { hom := (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app _
      comm := fun _ => (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.naturality _ }
  naturality _ _ φ :=
    Action.Hom.ext ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.naturality
      ((equivariantAdicCohomology R ρ q).map φ).hom)

/-- The underlying map of `equivariantRationalAdicCohomologyUnit` sends `x` to `1 ⊗ x`. -/
lemma equivariantRationalAdicCohomologyUnit_app_hom_apply (q : ℕ)
    (F : ℕᵒᵖ ⥤ EtaleCohomologyAction.EquivariantSheaf R ρ)
    (x : ((equivariantAdicCohomology R ρ q).obj F).V) :
    ((equivariantRationalAdicCohomologyUnit R S ρ q).app F).hom x =
      (1 : S) ⊗ₜ[R, algebraMap R S] x :=
  rfl

variable {R} (I : Ideal R)

/-- `S ⊗_R lim_n H^q(X, F / I ^ n F)` for a `ρ`-equivariant sheaf `F`, as a representation
of `G`. -/
def equivariantRationalIdealAdicCohomology (q : ℕ) :
    EtaleCohomologyAction.EquivariantSheaf R ρ ⥤ Action (ModuleCat.{u} S) G :=
  EtaleAdicSystem.equivariantFunctor I ρ ⋙ equivariantRationalAdicCohomology R S ρ q

/-- The underlying module of `equivariantRationalIdealAdicCohomology` is
`rationalIdealAdicCohomology` of the underlying sheaf. -/
def equivariantRationalIdealAdicCohomologyForgetIso (q : ℕ) :
    equivariantRationalIdealAdicCohomology S ρ I q ⋙ Action.forget (ModuleCat.{u} S) G ≅
      TranslationAction.Equivariant.forget ⋙ rationalIdealAdicCohomology S I q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (EtaleAdicSystem.equivariantFunctor I ρ)
      (equivariantRationalAdicCohomologyForgetIso R S ρ q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (EtaleAdicSystem.equivariantFunctorForgetIso I ρ)
      (rationalAdicCohomology X R S q) ≪≫
    Functor.associator _ _ _

end Equivariant

end EtaleAdicCohomology

namespace EtaleAdicCohomology

section Harris

open Langlands.Global Langlands.Shimura Langlands.Shimura.Coefficients

variable (ℓ : ℕ)
variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints)
variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U ℓ) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))

/-- Harris's `H^q(X, W̃)` with `W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ`: the extension of scalars
`(L ⊗_ℚ ℚ_p) ⊗_𝒪 lim_m H^q(X, 𝓛̃_m)` of `harrisEtaleAdicCohomology`, where
`𝒪 = HarrisCoefficientIntegers L p`. -/
def harrisEtaleRationalCohomology (q : ℕ) : ModuleCat.{u} (L ⊗[ℚ] FiniteCompletion ℚ p) :=
  (rationalAdicCohomology X (HarrisCoefficientIntegers L p) (L ⊗[ℚ] FiniteCompletion ℚ p) q).obj
    (harrisEtaleCoefficientSystem ρ p U ℓ X Y hY)

/-- `harrisEtaleRationalCohomology` is the extension of scalars of `harrisEtaleAdicCohomology`
along `harrisCoefficientIntegersMap`. -/
lemma harrisEtaleRationalCohomology_eq (q : ℕ) :
    harrisEtaleRationalCohomology ℓ ρ p U X Y hY q =
      (ModuleCat.extendScalars (harrisCoefficientIntegersMap L p)).obj
        (harrisEtaleAdicCohomology ℓ ρ p U X Y hY q) :=
  rfl

/-- The map `x ↦ 1 ⊗ x` from `lim_m H^q(X, 𝓛̃_m)` to Harris's `H^q(X, W̃)`. -/
def harrisEtaleRationalCohomologyUnit (q : ℕ) :
    harrisEtaleAdicCohomology ℓ ρ p U X Y hY q ⟶
      (ModuleCat.restrictScalars (harrisCoefficientIntegersMap L p)).obj
        (harrisEtaleRationalCohomology ℓ ρ p U X Y hY q) :=
  (rationalAdicCohomologyUnit X (HarrisCoefficientIntegers L p)
    (L ⊗[ℚ] FiniteCompletion ℚ p) q).app (harrisEtaleCoefficientSystem ρ p U ℓ X Y hY)

/-- In degree zero, `H^0(X, W̃) ≅ (L ⊗_ℚ ℚ_p) ⊗_𝒪 lim_m Γ(X, 𝓛̃_m)`. -/
def harrisEtaleRationalCohomologyZeroIso :
    harrisEtaleRationalCohomology ℓ ρ p U X Y hY 0 ≅
      (ModuleCat.extendScalars (harrisCoefficientIntegersMap L p)).obj
        (limit (harrisEtaleSectionsSystem ρ p U ℓ X Y hY)) :=
  (ModuleCat.extendScalars (harrisCoefficientIntegersMap L p)).mapIso
    (harrisEtaleAdicCohomologyZeroIso ℓ ρ p U X Y hY)

/-- In degree zero, `H^0(X, W̃) ≅ (L ⊗_ℚ ℚ_p) ⊗_𝒪 Γ(X, lim_m 𝓛̃_m)`. -/
def harrisEtaleRationalCohomologyZeroLimitIso :
    harrisEtaleRationalCohomology ℓ ρ p U X Y hY 0 ≅
      (ModuleCat.extendScalars (harrisCoefficientIntegersMap L p)).obj
        ((EtaleDerivedSections.sections X (HarrisCoefficientIntegers L p)).obj
          (limit (harrisEtaleCoefficientSystem ρ p U ℓ X Y hY))) :=
  (ModuleCat.extendScalars (harrisCoefficientIntegersMap L p)).mapIso
    (harrisEtaleAdicCohomologyZeroLimitIso ℓ ρ p U X Y hY)

/-- When the section maps of the projections are surjective, `H^0(X, W̃)` is the extension of
scalars of the inverse limit of `harrisEtaleSectionsDivisibleSystem`. -/
def harrisEtaleRationalCohomologyZeroDivisibleIso [NeZero ℓ]
    (hΓ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((EtaleDerivedSections.sections X (HarrisCoefficientIntegers L p)).map
          ((DivisibleSystem.harrisEtaleDivisibleSystem ℓ ρ p U X Y hY).projection h))) :
    harrisEtaleRationalCohomology ℓ ρ p U X Y hY 0 ≅
      (ModuleCat.extendScalars (harrisCoefficientIntegersMap L p)).obj
        (DivisibleSystem.harrisEtaleSectionsDivisibleSystem ℓ ρ p U X Y hY hΓ).inverseLimit :=
  (ModuleCat.extendScalars (harrisCoefficientIntegersMap L p)).mapIso
    (harrisEtaleAdicCohomologyZeroDivisibleIso ℓ ρ p U X Y hY hΓ)

end Harris

end EtaleAdicCohomology

end Langlands.Cohomology
