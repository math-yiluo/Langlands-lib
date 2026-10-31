import Langlands.Cohomology.DivisibleSystem.HarrisEtale
import Langlands.Cohomology.DivisibleSystem.InverseLimit
import Langlands.Geometry.EtaleActionFunctor
import Langlands.Geometry.EtaleEquivariantAdicSystem

/-!
# `ℓ`-adic étale cohomology as an inverse limit of cohomology modules

Milne, *Étale Cohomology* (1980), Ch. V, §1, p.164: "The cohomology groups of an `l`-adic sheaf
`F` are defined to be `H^r(X, F) = lim H^r(X, F_n)`. Note that `H^r(X, F) ≠ H^r(X, lim F_n)` in
general". Harris, *Galois properties of cohomological automorphic forms on GL(n)*, §4, p.312,
(4.10.4), uses the cohomology `H^{i+j}(S̄_{K(N)}, 𝓛̃)` of the inverse system `{𝓛̃_m}`.

For a scheme `X` and a commutative ring `R`, the cohomology `H^q(X, -)` below is the published
`EtaleDerivedSections.cohomology X R q`, the right derived functors of global sections of sheaves
of `R`-modules on the small étale site of `X`.

* `adicCohomology X R q` sends an inverse system `F : ℕᵒᵖ ⥤ Sheaf` to `lim_m H^q(X, F_m)`, with
  projections `adicCohomologyπ`; `adicSections` is `lim_m Γ(X, F_m)`, and
  `adicCohomologyZeroIso` identifies the two in degree zero. Any inverse system is allowed;
  Milne's `l`-adic sheaves are a special case.
* `limitSectionsIso`: `Γ(X, lim_m F_m) ≅ lim_m Γ(X, F_m)`, since global sections are a right
  adjoint. `limitComparison X R q : H^q(X, lim_m F_m) ⟶ lim_m H^q(X, F_m)` is the canonical
  comparison; `limitComparison_zero` identifies it in degree zero with `limitSectionsIso`, and it
  is an isomorphism in degree zero. Nothing is claimed in higher degrees.
* `idealAdicCohomology I q`, for an ideal `I` of `R`: `lim_n H^q(X, F / I ^ n F)` for the
  published reductions `EtaleAdicSystem.functor X I`; in degree zero it is the sections of the
  published inverse-limit sheaf (`idealAdicCohomologyZeroInverseLimitIso`), and
  `idealLimitComparison` is the comparison map.
* `equivariantAdicCohomology R ρ q` and `equivariantIdealAdicCohomology ρ I q`: the same limits
  for sheaves equivariant for an action `ρ` of a group `G` on `X`, as representations of `G`
  through the published `EtaleCohomologyAction.pullbackCohomologyFunctor`; their underlying
  modules are the non-equivariant limits (`equivariantAdicCohomologyForgetIso`,
  `equivariantIdealAdicCohomologyForgetIso`), and `equivariantAdicCohomologyZeroIso` is the
  degree-zero identification.
* `harrisEtaleAdicCohomology ℓ ρ p U X Y hY q`: `lim_m H^q(X, 𝓛 / ℓ ^ m)` for the published
  Harris étale coefficient sheaves `harrisEtaleCoefficientSystem`, with its degree-zero
  identifications `harrisEtaleAdicCohomologyZeroIso`, `harrisEtaleAdicCohomologyZeroLimitIso` and,
  under an explicit surjectivity hypothesis, `harrisEtaleAdicCohomologyZeroDivisibleIso`.

Mathlib's `AlgebraicGeometry.Scheme.EllAdicCohomology` is the pro-étale cohomology of `X` with
coefficients in the sheaf of continuous `ℤ_[ℓ]`-valued functions; it is a different construction,
and no comparison with it is made here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.Geometry

universe u w

namespace EtaleAdicCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

section Adic

/-- Global sections on the small étale site are a right adjoint (of the constant sheaf functor). -/
instance : (EtaleDerivedSections.sections X R).IsRightAdjoint :=
  inferInstanceAs (CategoryTheory.Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u} R)).IsRightAdjoint

/-- Milne, *Étale Cohomology*, V.1, p.164: the cohomology of an inverse system of étale
sheaves `(F_m)` is `lim_m H^q(X, F_m)`. -/
def adicCohomology (q : ℕ) :
    (ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) ⥤ ModuleCat.{u} R :=
  EtaleDerivedSections.diagramFunctor X R ℕᵒᵖ q ⋙ lim

/-- `adicCohomology X R q` of `F` is the limit of the cohomology modules `H^q(X, F_m)`. -/
lemma adicCohomology_obj (q : ℕ) (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    (adicCohomology X R q).obj F = limit (F ⋙ EtaleDerivedSections.cohomology X R q) :=
  rfl

variable {X R}

/-- The projection `lim_m H^q(X, F_m) ⟶ H^q(X, F_n)`. -/
def adicCohomologyπ (q : ℕ) (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) (n : ℕ) :
    (adicCohomology X R q).obj F ⟶ (EtaleDerivedSections.cohomology X R q).obj (F.obj (op n)) :=
  limit.π (F ⋙ EtaleDerivedSections.cohomology X R q) (op n)

/-- The projections are compatible with the maps `H^q(X, F_n) ⟶ H^q(X, F_m)` for `m ≤ n`. -/
@[reassoc]
lemma adicCohomologyπ_map (q : ℕ) (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R)
    {m n : ℕ} (h : m ≤ n) :
    adicCohomologyπ q F n ≫ (EtaleDerivedSections.cohomology X R q).map (F.map (homOfLE h).op) =
      adicCohomologyπ q F m :=
  limit.w (F ⋙ EtaleDerivedSections.cohomology X R q) (homOfLE h).op

/-- Naturality of the projections in the inverse system. -/
@[reassoc]
lemma map_adicCohomologyπ (q : ℕ) {F E : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R}
    (φ : F ⟶ E) (n : ℕ) :
    (adicCohomology X R q).map φ ≫ adicCohomologyπ q E n =
      adicCohomologyπ q F n ≫ (EtaleDerivedSections.cohomology X R q).map (φ.app (op n)) :=
  limMap_π _ (op n)

/-- Morphisms into `lim_m H^q(X, F_m)` are determined by their projections. -/
lemma adicCohomology_hom_ext (q : ℕ) {F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R}
    {M : ModuleCat.{u} R} {f g : M ⟶ (adicCohomology X R q).obj F}
    (h : ∀ n, f ≫ adicCohomologyπ q F n = g ≫ adicCohomologyπ q F n) : f = g :=
  limit.hom_ext fun n => h n.unop

variable (X R)

/-- `lim_m Γ(X, F_m)`. -/
def adicSections : (ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) ⥤ ModuleCat.{u} R :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (EtaleDerivedSections.sections X R) ⋙ lim

/-- In degree zero, `lim_m H^0(X, F_m) ≅ lim_m Γ(X, F_m)`. -/
def adicCohomologyZeroIso : adicCohomology X R 0 ≅ adicSections X R :=
  Functor.isoWhiskerRight
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (EtaleDerivedSections.cohomologyZeroIso X R)) lim

/-- Global sections commute with inverse limits of sheaves: `Γ(X, lim_m F_m) ≅ lim_m Γ(X, F_m)`. -/
def limitSectionsIso : lim ⋙ EtaleDerivedSections.sections X R ≅ adicSections X R :=
  preservesLimitNatIso (EtaleDerivedSections.sections X R)

/-- The comparison `H^q(X, lim_m F_m) ⟶ lim_m H^q(X, F_m)`. -/
def limitComparison (q : ℕ) :
    lim ⋙ EtaleDerivedSections.cohomology X R q ⟶ adicCohomology X R q where
  app F := limit.post F (EtaleDerivedSections.cohomology X R q)
  naturality _ _ _ := limit.map_post _ (EtaleDerivedSections.cohomology X R q)

/-- The projections of the comparison are the maps induced on `H^q` by the limit projections. -/
@[reassoc]
lemma limitComparison_π (q : ℕ) (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) (n : ℕ) :
    (limitComparison X R q).app F ≫ adicCohomologyπ q F n =
      (EtaleDerivedSections.cohomology X R q).map (limit.π F (op n)) :=
  limit.post_π _ _ _

/-- In degree zero, the comparison, followed by `adicCohomologyZeroIso`, is
`H^0(X, lim_m F_m) ≅ Γ(X, lim_m F_m)` followed by `limitSectionsIso`. -/
lemma limitComparison_zero :
    limitComparison X R 0 ≫ (adicCohomologyZeroIso X R).hom =
      Functor.whiskerLeft lim (EtaleDerivedSections.cohomologyZeroIso X R).hom ≫
        (limitSectionsIso X R).hom := by
  refine NatTrans.ext (funext fun F => limit.hom_ext fun n => ?_)
  change (limit.post F _ ≫ limMap _) ≫ limit.π _ n =
    ((EtaleDerivedSections.cohomologyZeroIso X R).hom.app (limit F) ≫
      (preservesLimitIso (EtaleDerivedSections.sections X R) F).hom) ≫ limit.π _ n
  rw [Category.assoc, limMap_π, limit.post_π_assoc, Category.assoc, preservesLimitIso_hom_π]
  exact (EtaleDerivedSections.cohomologyZeroIso X R).hom.naturality (limit.π F n)

/-- `H^0(X, -)` preserves limits of inverse systems, being isomorphic to global sections. -/
instance : PreservesLimitsOfShape ℕᵒᵖ (EtaleDerivedSections.cohomology X R 0) :=
  preservesLimitsOfShape_of_natIso (EtaleDerivedSections.cohomologyZeroIso X R).symm

/-- In degree zero, the comparison `H^0(X, lim_m F_m) ⟶ lim_m H^0(X, F_m)` is an isomorphism. -/
instance : IsIso (limitComparison X R 0) := by
  have (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) :
      IsIso ((limitComparison X R 0).app F) := by
    change IsIso (limit.post F (EtaleDerivedSections.cohomology X R 0))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Adic

section Ideal

variable {X R} (I : Ideal R)

/-- `lim_n H^q(X, F / I ^ n F)`, where `F / I ^ n F` is the sheafified sectionwise reduction
of `F` modulo `I ^ n` (`EtaleAdicSystem.functor`). -/
def idealAdicCohomology (q : ℕ) : EtaleDerivedSections.ModuleSheaf X R ⥤ ModuleCat.{u} R :=
  EtaleAdicSystem.functor X I ⋙ adicCohomology X R q

/-- `idealAdicCohomology I q` of `F` is the limit of the modules `H^q(X, F / I ^ n F)`. -/
lemma idealAdicCohomology_obj (q : ℕ) (F : EtaleDerivedSections.ModuleSheaf X R) :
    (idealAdicCohomology I q).obj F =
      limit ((EtaleAdicSystem.functor X I).obj F ⋙ EtaleDerivedSections.cohomology X R q) :=
  rfl

/-- In degree zero, `lim_n H^0(X, F / I ^ n F) ≅ Γ(X, lim_n F / I ^ n F)`. -/
def idealAdicCohomologyZeroIso :
    idealAdicCohomology I 0 ≅
      EtaleAdicSystem.functor X I ⋙ lim ⋙ EtaleDerivedSections.sections X R :=
  Functor.isoWhiskerLeft (EtaleAdicSystem.functor X I)
    (adicCohomologyZeroIso X R ≪≫ (limitSectionsIso X R).symm)

/-- The component of `idealAdicCohomologyZeroIso` at `F`, with target the sections of the
published inverse-limit sheaf `EtaleAdicSystem.inverseLimit X I F`. -/
def idealAdicCohomologyZeroInverseLimitIso (F : EtaleDerivedSections.ModuleSheaf X R) :
    (idealAdicCohomology I 0).obj F ≅
      (EtaleDerivedSections.sections X R).obj (EtaleAdicSystem.inverseLimit X I F) :=
  (idealAdicCohomologyZeroIso I).app F

/-- The comparison `H^q(X, lim_n F / I ^ n F) ⟶ lim_n H^q(X, F / I ^ n F)`. -/
def idealLimitComparison (q : ℕ) :
    EtaleAdicSystem.functor X I ⋙ lim ⋙ EtaleDerivedSections.cohomology X R q ⟶
      idealAdicCohomology I q :=
  Functor.whiskerLeft (EtaleAdicSystem.functor X I) (limitComparison X R q)

end Ideal

section Equivariant

variable {X} {G : Type w} [Group G] (ρ : G →* (Aut X)ᵐᵒᵖ)

/-- `lim_m H^q(X, F_m)` for an inverse system of `ρ`-equivariant sheaves, with the action of
`G` on each `H^q(X, F_m)` from `EtaleCohomologyAction.pullbackCohomologyFunctor`. -/
def equivariantAdicCohomology (q : ℕ) :
    (ℕᵒᵖ ⥤ EtaleCohomologyAction.EquivariantSheaf R ρ) ⥤ Action (ModuleCat.{u} R) G :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (EtaleCohomologyAction.pullbackCohomologyFunctor R ρ q) ⋙ lim

/-- The underlying module of `equivariantAdicCohomology` is `adicCohomology` of the underlying
inverse system of sheaves. -/
def equivariantAdicCohomologyForgetIso (q : ℕ) :
    equivariantAdicCohomology R ρ q ⋙ Action.forget (ModuleCat.{u} R) G ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj TranslationAction.Equivariant.forget ⋙
        adicCohomology X R q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (preservesLimitNatIso (Action.forget (ModuleCat.{u} R) G)) ≪≫
    Iso.refl _

/-- `lim_m Γ(X, F_m)` with the action of `G` from
`EtaleCohomologyAction.pullbackSectionsFunctor`. -/
def equivariantAdicSections :
    (ℕᵒᵖ ⥤ EtaleCohomologyAction.EquivariantSheaf R ρ) ⥤ Action (ModuleCat.{u} R) G :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (EtaleCohomologyAction.pullbackSectionsFunctor R ρ) ⋙
    lim

/-- In degree zero, `lim_m H^0(X, F_m) ≅ lim_m Γ(X, F_m)` as representations of `G`. -/
def equivariantAdicCohomologyZeroIso :
    equivariantAdicCohomology R ρ 0 ≅ equivariantAdicSections R ρ :=
  Functor.isoWhiskerRight
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
      (EtaleCohomologyAction.pullbackCohomologyZeroFunctorIso R ρ)) lim

variable {R} (I : Ideal R)

/-- `lim_n H^q(X, F / I ^ n F)` for a `ρ`-equivariant sheaf `F`, with the action of `G`
on each level, using the equivariant reductions `EtaleAdicSystem.equivariantFunctor`. -/
def equivariantIdealAdicCohomology (q : ℕ) :
    EtaleCohomologyAction.EquivariantSheaf R ρ ⥤ Action (ModuleCat.{u} R) G :=
  EtaleAdicSystem.equivariantFunctor I ρ ⋙ equivariantAdicCohomology R ρ q

/-- The underlying module of `equivariantIdealAdicCohomology` is `idealAdicCohomology` of the
underlying sheaf. -/
def equivariantIdealAdicCohomologyForgetIso (q : ℕ) :
    equivariantIdealAdicCohomology ρ I q ⋙ Action.forget (ModuleCat.{u} R) G ≅
      TranslationAction.Equivariant.forget ⋙ idealAdicCohomology I q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (EtaleAdicSystem.equivariantFunctor I ρ)
      (equivariantAdicCohomologyForgetIso R ρ q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (EtaleAdicSystem.equivariantFunctorForgetIso I ρ)
      (adicCohomology X R q) ≪≫
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

/-- Harris's `H^q(X, 𝓛̃) = lim_m H^q(X, 𝓛 / ℓ ^ m)` for the published étale sheaves
`harrisEtaleCoefficientSystem ρ p U ℓ X Y hY`. -/
def harrisEtaleAdicCohomology (q : ℕ) : ModuleCat.{u} (HarrisCoefficientIntegers L p) :=
  (adicCohomology X (HarrisCoefficientIntegers L p) q).obj
    (harrisEtaleCoefficientSystem ρ p U ℓ X Y hY)

/-- `harrisEtaleAdicCohomology` is the limit of the published inverse system
`harrisEtaleCohomologySystem` of the modules `H^q(X, 𝓛 / ℓ ^ m)`. -/
lemma harrisEtaleAdicCohomology_eq (q : ℕ) :
    harrisEtaleAdicCohomology ℓ ρ p U X Y hY q =
      limit (harrisEtaleCohomologySystem ρ p U ℓ X Y hY q) :=
  rfl

/-- In degree zero, `lim_m H^0(X, 𝓛 / ℓ ^ m) ≅ lim_m Γ(X, 𝓛 / ℓ ^ m)`. -/
def harrisEtaleAdicCohomologyZeroIso :
    harrisEtaleAdicCohomology ℓ ρ p U X Y hY 0 ≅
      limit (harrisEtaleSectionsSystem ρ p U ℓ X Y hY) :=
  lim.mapIso (harrisEtaleCohomologyZeroIso ρ p U ℓ X Y hY)

/-- In degree zero, `lim_m H^0(X, 𝓛 / ℓ ^ m) ≅ Γ(X, lim_m 𝓛 / ℓ ^ m)`. -/
def harrisEtaleAdicCohomologyZeroLimitIso :
    harrisEtaleAdicCohomology ℓ ρ p U X Y hY 0 ≅
      (EtaleDerivedSections.sections X (HarrisCoefficientIntegers L p)).obj
        (limit (harrisEtaleCoefficientSystem ρ p U ℓ X Y hY)) :=
  (adicCohomologyZeroIso X _).app _ ≪≫ ((limitSectionsIso X _).app _).symm

/-- When the section maps of the projections are surjective, degree-zero `ℓ`-adic cohomology
is the inverse limit of the `ℓ`-divisible system `harrisEtaleSectionsDivisibleSystem`. -/
def harrisEtaleAdicCohomologyZeroDivisibleIso [NeZero ℓ]
    (hΓ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((EtaleDerivedSections.sections X (HarrisCoefficientIntegers L p)).map
          ((DivisibleSystem.harrisEtaleDivisibleSystem ℓ ρ p U X Y hY).projection h))) :
    harrisEtaleAdicCohomology ℓ ρ p U X Y hY 0 ≅
      (DivisibleSystem.harrisEtaleSectionsDivisibleSystem ℓ ρ p U X Y hY hΓ).inverseLimit :=
  harrisEtaleAdicCohomologyZeroIso ℓ ρ p U X Y hY

end Harris

end EtaleAdicCohomology

end Langlands.Cohomology
