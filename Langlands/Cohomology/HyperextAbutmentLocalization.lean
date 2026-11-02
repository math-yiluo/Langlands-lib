import Langlands.Cohomology.HyperextInvariantsLocalization
import Langlands.Cohomology.HyperextHomLocalization

/-!
# Invariants of hyperext abutments and localization for finitely generated cohomology

Let `S` be a localization of a commutative ring `R` at a submonoid `M` (for example
`R = 𝒪`, the ring of integers of a finite extension of `ℚ_ℓ`, and `S` its fraction field). This
module combines `HyperextInvariantsLocalization` and `HyperextHomLocalization`: the base-change
maps on `Γ`-invariants of `Hom(H^{-n} K, W)` and, under the degeneration hypotheses of
`HyperextIsotypicDegenerationBaseChange`, of the abutment `Hom(K, W₀⟦n⟧)` are bijective when
`Hom(H^{-n} K, W)` has no `M`-torsion and the base-change map before taking invariants is
bijective. For extension of scalars of (smooth) representations both conditions follow from
finite generation of `H^{-n} K` over `R[G]` and the absence of `M`-torsion in `W`; no
finite-orbit hypothesis on the action of `Γ` is needed.

* `cohomologyHomInvariantsBaseChangeMap_bijective_of_isSMulRegular`,
  `abutmentInvariantsBaseChangeMap_bijective_of_isSMulRegular` and the linear equivalence
  `abutmentInvariantsLocalizationEquivOfIsSMulRegular`: for an exact semilinear functor along a
  localization.
* `repCohomologyHomInvariantsBaseChangeMap_bijective_of_finite`,
  `repAbutmentInvariantsBaseChangeMap_bijective_of_finite` and the linear equivalence
  `repAbutmentInvariantsLocalizationEquiv`: for extension of scalars of representations.
* `smoothCohomologyHomInvariantsBaseChangeMap_bijective_of_finite`,
  `smoothAbutmentInvariantsBaseChangeMap_bijective_of_finite` and the linear equivalence
  `smoothAbutmentInvariantsLocalizationEquivOfFinite`: for extension of scalars of smooth
  representations.

The finite generation of `H^{-n} K`, the absence of `M`-torsion in `W` and the degeneration
hypotheses remain hypotheses; this module does not verify them for any particular complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

namespace HyperextScalarExtension

open HyperextAbutment

universe w uR uS uG uC vC uD vD s s' t t' uΓ

section Derived

variable {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear R C] [HasDerivedCategory.{s} C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [Linear S D] [HasDerivedCategory.{s'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable (hF : IsSemilinear R S F)
variable {Γ : Type uΓ} [Group Γ]

include M

open DerivedCategory

/-- If `S` is a localization of `R` at `M`, `Hom(H^{-n} K, W)` has no `M`-torsion (the hypothesis
`hreg`) and `cohomologyHomBaseChangeMap` is bijective (the hypothesis `h`), then
`cohomologyHomInvariantsBaseChangeMap` is bijective. -/
theorem cohomologyHomInvariantsBaseChangeMap_bijective_of_isSMulRegular {K : DerivedCategory C}
    {W : C} (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ)
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    Function.Bijective (cohomologyHomInvariantsBaseChangeMap F hF ρ σ n) :=
  (invariantsLinearMap_bijective (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n) h).comp
    (invariantsBaseChangeMap_bijective_of_isSMulRegular S M
      (ρ := cohomologyHomRepresentation R ρ σ n) hreg)

variable [HasExt.{t} C] [HasExt.{t'} D]

/-- Under the degeneration hypotheses, if `S` is a localization of `R` at `M`,
`Hom(H^{-n} K, W)` has no `M`-torsion and `cohomologyHomBaseChangeMap` is bijective, then
`abutmentInvariantsBaseChangeMap` is bijective. -/
theorem abutmentInvariantsBaseChangeMap_bijective_of_isSMulRegular
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    Function.Bijective (abutmentInvariantsBaseChangeMap F hF ρ σ n) :=
  (abutmentInvariantsBaseChangeMap_bijective_iff F hF b hK hW hW' n ρ σ).2
    (cohomologyHomInvariantsBaseChangeMap_bijective_of_isSMulRegular M F hF ρ σ n hreg h)

/-- Under the hypotheses of `abutmentInvariantsBaseChangeMap_bijective_of_isSMulRegular`, the
`S`-linear equivalence `S ⊗[R] Hom(K, W₀⟦n⟧)^Γ ≃ Hom(F K, (F W)₀⟦n⟧)^Γ` given by
`abutmentInvariantsBaseChangeMap`. -/
def abutmentInvariantsLocalizationEquivOfIsSMulRegular
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    S ⊗[R] (abutmentRepresentation R ρ σ n).invariants ≃ₗ[S]
      (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
        ((F.mapAut W).comp σ) n).invariants :=
  LinearEquiv.ofBijective (abutmentInvariantsBaseChangeMap F hF ρ σ n)
    (abutmentInvariantsBaseChangeMap_bijective_of_isSMulRegular M F hF b hK hW hW' n ρ σ hreg h)

/-- The underlying map of `abutmentInvariantsLocalizationEquivOfIsSMulRegular` is
`abutmentInvariantsBaseChangeMap`. -/
@[simp]
lemma abutmentInvariantsLocalizationEquivOfIsSMulRegular_apply
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n)))
    (x : S ⊗[R] (abutmentRepresentation R ρ σ n).invariants) :
    abutmentInvariantsLocalizationEquivOfIsSMulRegular M F hF b hK hW hW' n ρ σ hreg h x =
      abutmentInvariantsBaseChangeMap F hF ρ σ n x :=
  rfl

end Derived

section Rep

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S] [Module.Flat R S]
  (M : Submonoid R) [IsLocalization M S]
  (G : Type uG) [Monoid G]
  [HasDerivedCategory.{s} (Rep.{w} R G)] [HasDerivedCategory.{s'} (Rep.{max uS w} S G)]
  {Γ : Type uΓ} [Group Γ]

include M

open DerivedCategory

/-- **Invariants of `Hom(H^{-n} K, W)` and localization for representations.** If `S` is a
localization of `R` at `M`, `H^{-n} K` is finitely generated over `R[G]` and `W` has no
`M`-torsion, then `cohomologyHomInvariantsBaseChangeMap` for extension of scalars of
representations is bijective. -/
theorem repCohomologyHomInvariantsBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (Rep.{w} R G)} {W : Rep.{w} R G} (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (n : ℤ) [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).ρ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective (cohomologyHomInvariantsBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) ρ σ n) :=
  cohomologyHomInvariantsBaseChangeMap_bijective_of_isSMulRegular M _ _ ρ σ n
    (fun m => repHom_isSMulRegular (hreg m))
    (repCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K (-n) hreg)

variable [HasExt.{t} (Rep.{w} R G)] [HasExt.{t'} (Rep.{max uS w} S G)]

/-- **Invariants of abutments and localization for representations.** Under the degeneration
hypotheses, if `S` is a localization of `R` at `M`, `H^{-n} K` is finitely generated over `R[G]`
and `W` has no `M`-torsion, then `abutmentInvariantsBaseChangeMap` for extension of scalars of
representations is bijective. -/
theorem repAbutmentInvariantsBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (Rep.{w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : Rep.{w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((repExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((repExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).ρ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective (abutmentInvariantsBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) ρ σ n) :=
  (abutmentInvariantsBaseChangeMap_bijective_iff _ _ b hK hW hW' n ρ σ).2
    (repCohomologyHomInvariantsBaseChangeMap_bijective_of_finite R S M G ρ σ n hreg)

/-- Under the hypotheses of `repAbutmentInvariantsBaseChangeMap_bijective_of_finite`,
`abutmentInvariantsBaseChangeMap` for extension of scalars of representations as an `S`-linear
equivalence. -/
def repAbutmentInvariantsLocalizationEquiv
    {K : DerivedCategory (Rep.{w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : Rep.{w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((repExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((repExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).ρ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    S ⊗[R] (abutmentRepresentation R ρ σ n).invariants ≃ₗ[S]
      (abutmentRepresentation S
        (((repExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
        (((repExtendScalars.{w} R S G).mapAut W).comp σ) n).invariants :=
  LinearEquiv.ofBijective _
    (repAbutmentInvariantsBaseChangeMap_bijective_of_finite R S M G b hK hW hW' n ρ σ hreg)

end Rep

section Smooth

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S] [Module.Flat R S]
  (M : Submonoid R) [IsLocalization M S]
  (G : Type uG) [Group G] [TopologicalSpace G]
  [HasDerivedCategory.{s} (SmoothRep.{uR, uG, w} R G)]
  [HasDerivedCategory.{s'} (SmoothRep.{uS, uG, max uS w} S G)]
  {Γ : Type uΓ} [Group Γ]

include M

open DerivedCategory

/-- `repCohomologyHomInvariantsBaseChangeMap_bijective_of_finite` for smooth representations:
if `S` is a localization of `R` at `M`, the underlying representation of `H^{-n} K` is finitely
generated over `R[G]` and `W` has no `M`-torsion, then
`smoothCohomologyHomInvariantsBaseChangeMap` is bijective. -/
theorem smoothCohomologyHomInvariantsBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} {W : SmoothRep.{uR, uG, w} R G}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).obj.ρ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective
      (smoothCohomologyHomInvariantsBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n) :=
  cohomologyHomInvariantsBaseChangeMap_bijective_of_isSMulRegular M
    (smoothRepExtendScalars.{w} R S G) (smoothRepExtendScalars_isSemilinear.{w} R S G) ρ σ n
    (fun m => smoothRepHom_isSMulRegular (hreg m))
    (smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K (-n) hreg)

variable [HasExt.{t} (SmoothRep.{uR, uG, w} R G)] [HasExt.{t'} (SmoothRep.{uS, uG, max uS w} S G)]

/-- **Invariants of abutments and localization for smooth representations.** Under the
degeneration hypotheses, if `S` is a localization of `R` at `M`, the underlying representation of
`H^{-n} K` is finitely generated over `R[G]` and `W` has no `M`-torsion, then
`smoothAbutmentInvariantsBaseChangeMap` is bijective. -/
theorem smoothAbutmentInvariantsBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K))
    {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).obj.ρ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective
      (smoothAbutmentInvariantsBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n) :=
  (abutmentInvariantsBaseChangeMap_bijective_iff (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) b hK hW hW' n ρ σ).2
    (smoothCohomologyHomInvariantsBaseChangeMap_bijective_of_finite R S M G ρ σ n hreg)

/-- Under the hypotheses of `smoothAbutmentInvariantsBaseChangeMap_bijective_of_finite`,
`smoothAbutmentInvariantsBaseChangeMap` as an `S`-linear equivalence. -/
def smoothAbutmentInvariantsLocalizationEquivOfFinite
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K))
    {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).obj.ρ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    S ⊗[R] (abutmentRepresentation R ρ σ n).invariants ≃ₗ[S]
      (abutmentRepresentation S
        (((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
        (((smoothRepExtendScalars.{w} R S G).mapAut W).comp σ) n).invariants :=
  LinearEquiv.ofBijective _
    (smoothAbutmentInvariantsBaseChangeMap_bijective_of_finite R S M G b hK hW hW' n ρ σ hreg)

end Smooth

end HyperextScalarExtension

end Langlands.Cohomology
