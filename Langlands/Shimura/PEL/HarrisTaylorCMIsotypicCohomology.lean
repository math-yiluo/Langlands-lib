import Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology
import Langlands.Shimura.IsotypicGaloisAction

/-! # Isotypic parts and multiplicity spaces of the cohomology of the actual CM tower

For a representation `ξ` of `GG(A_f)ᵐᵒᵖ`, the `ξ`-isotypic part of the shrinking-level cohomology
of the actual geometric CM tower with coefficients pulled back from `Spec F` carries the
restricted action of `Gal(F̄/F)`, and the multiplicity space `Hom(ξ, -)` of the cohomology is a
representation of `Gal(F̄/F)` by composition; both are natural in the sheaf. Evaluation
`ξ ⊗ Hom(ξ, H) → H[ξ]` is surjective and Galois-equivariant. The same holds for the
prime-to-`m` cohomology and representations of `GG(A_f^{(m)})ᵐᵒᵖ`, where the fixed vectors of
the isotypic part under a prime-to-`m` level are Hecke modules with the commuting Galois action.
See `HarrisTaylorCMIsotypicCohomology.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe uU

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry Langlands.Geometry.EtalePullback
open CompactOpenLevel RestrictedSplitLevelTowerCohomology
open Langlands.Geometry.EtaleDerivedSections
open Langlands.Shimura.IsotypicGaloisAction
open Langlands.Cohomology.HyperextAbutment (isotypicPart)


variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})
  (q : CMRepresentabilityStatement D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})
  (R : Type) [CommRing R]

local notation "base" => Spec (CommRingCat.of F)
local notation "G" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "Fbar" => AlgebraicClosure F
local notation "Gamma" => (Fbar ≃ₐ[F] Fbar)
local notation "galoisCohomologyFunctor" => cmSmallLevelGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R

/-! ## The shrinking-level cohomology -/

section SmallLevel

variable {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ U)

/-- The `ξ`-isotypic part of the shrinking-level cohomology of the actual geometric CM tower with
coefficients pulled back from `Spec F`, with the restricted actions of `GG(A_f)ᵐᵒᵖ` and
`Gal(F̄/F)`, natural in the sheaf. -/
def cmSmallLevelIsotypicCohomologyFunctor (d : ℕ) :
    ModuleSheaf base R ⥤ Action (SmoothRep.{0, 0, 0} R G) Gamma :=
  galoisCohomologyFunctor d ⋙ isotypicActionFunctor ξ Gamma

local notation "isotypicCohomology" => cmSmallLevelIsotypicCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R ξ

@[simp] theorem cmSmallLevelIsotypicCohomologyFunctor_obj_V (d : ℕ) (M : ModuleSheaf base R) :
    ((isotypicCohomology d).obj M).V = isotypicObj ξ ((galoisCohomologyFunctor d).obj M).V :=
  rfl

/-- A Galois element acts on the `ξ`-isotypic part by the restriction of its action on the
cohomology. -/
theorem cmSmallLevelIsotypicCohomologyFunctor_ρ (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma) :
    ((isotypicCohomology d).obj M).ρ σ =
      isotypicMap ξ (((galoisCohomologyFunctor d).obj M).ρ σ) :=
  rfl

/-- The inclusion of the `ξ`-isotypic part into the cohomology, equivariant for `GG(A_f)ᵐᵒᵖ`
and `Gal(F̄/F)` and natural in the sheaf. -/
def cmSmallLevelIsotypicCohomologyι (d : ℕ) :
    isotypicCohomology d ⟶ galoisCohomologyFunctor d :=
  Functor.whiskerLeft _ (isotypicActionι ξ Gamma) ≫ (Functor.rightUnitor _).hom

@[simp] theorem cmSmallLevelIsotypicCohomologyι_app_apply (d : ℕ) (M : ModuleSheaf base R)
    (x : isotypicPart ξ ((galoisCohomologyFunctor d).obj M).V.representation) :
    SmoothRep.hom ((cmSmallLevelIsotypicCohomologyι D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid criterion R ξ
        d).app M).hom x = x.1 :=
  rfl

theorem cmSmallLevelIsotypicCohomologyι_app_injective (d : ℕ) (M : ModuleSheaf base R) :
    Function.Injective (SmoothRep.hom ((cmSmallLevelIsotypicCohomologyι D C preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
      criterion R ξ d).app M).hom) :=
  fun _ _ hxy => isotypicι_app_injective ξ _ hxy

/-- The multiplicity spaces `Hom(ξ, H^d)` of intertwining maps from `ξ` into the shrinking-level
cohomology, as representations of `Gal(F̄/F)` acting by composition, natural in the sheaf. -/
def cmSmallLevelMultiplicityFunctor (d : ℕ) : ModuleSheaf base R ⥤ Rep.{uU} R Gamma :=
  galoisCohomologyFunctor d ⋙ multiplicityRepFunctor ξ Gamma

local notation "multiplicityCohomology" => cmSmallLevelMultiplicityFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R ξ

/-- A Galois element acts on an intertwining map by composition with its action on the
cohomology. -/
@[simp] theorem cmSmallLevelMultiplicityFunctor_ρ_apply (d : ℕ) (M : ModuleSheaf base R)
    (σ : Gamma) (φ : ξ.IntertwiningMap ((galoisCohomologyFunctor d).obj M).V.representation) :
    ((multiplicityCohomology d).obj M).ρ σ φ =
      (SmoothRep.hom (((galoisCohomologyFunctor d).obj M).ρ σ)).comp φ :=
  rfl

/-- Every vector of the `ξ`-isotypic part of the cohomology is a sum of values of intertwining
maps from `ξ`: evaluation `ξ ⊗ Hom(ξ, H^d) → H^d[ξ]` is surjective. -/
theorem cmSmallLevelIsotypicEvaluation_surjective (d : ℕ) (M : ModuleSheaf base R) :
    Function.Surjective (isotypicEvaluation ξ ((galoisCohomologyFunctor d).obj M).V) :=
  isotypicEvaluation_surjective ξ _

/-- Evaluation intertwines the Galois action on the multiplicity space with the Galois action on
the `ξ`-isotypic part of the cohomology. -/
theorem cmSmallLevelIsotypicEvaluation_galois (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma) :
    isotypicEvaluation ξ ((galoisCohomologyFunctor d).obj M).V ∘ₗ
        LinearMap.lTensor U
          (multiplicityRepresentation ξ Gamma ((galoisCohomologyFunctor d).obj M) σ) =
      isotypicGaloisRepresentation ξ Gamma ((galoisCohomologyFunctor d).obj M) σ ∘ₗ
        isotypicEvaluation ξ ((galoisCohomologyFunctor d).obj M).V :=
  isotypicEvaluation_galois ξ Gamma _ σ

end SmallLevel

/-! ## The prime-to-`m` cohomology -/

section PrimeTo

variable (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)

local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

variable {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ U)

/-- The `ξ`-isotypic part of the prime-to-`m` colimit cohomology of sheaves pulled back from
`Spec F`, with the restricted actions of `GG(A_f^{(m)})ᵐᵒᵖ` and `Gal(F̄/F)`, natural in the
sheaf. -/
def cmPrimeToIsotypicCohomologyFunctor (d : ℕ) :
    ModuleSheaf base R ⥤
      Action (SmoothRep.{0, 0, 0} R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) Gamma :=
  primeToGaloisCohomologyFunctor d ⋙ isotypicActionFunctor ξ Gamma

local notation "primeToIsotypicCohomology" => cmPrimeToIsotypicCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R m hm K₀ ξ

@[simp] theorem cmPrimeToIsotypicCohomologyFunctor_obj_V (d : ℕ) (M : ModuleSheaf base R) :
    ((primeToIsotypicCohomology d).obj M).V =
      isotypicObj ξ ((primeToGaloisCohomologyFunctor d).obj M).V :=
  rfl

/-- A Galois element acts on the `ξ`-isotypic part by the restriction of its action on the
cohomology. -/
theorem cmPrimeToIsotypicCohomologyFunctor_ρ (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma) :
    ((primeToIsotypicCohomology d).obj M).ρ σ =
      isotypicMap ξ (((primeToGaloisCohomologyFunctor d).obj M).ρ σ) :=
  rfl

/-- The inclusion of the `ξ`-isotypic part into the prime-to-`m` cohomology, equivariant for
`GG(A_f^{(m)})ᵐᵒᵖ` and `Gal(F̄/F)` and natural in the sheaf. -/
def cmPrimeToIsotypicCohomologyι (d : ℕ) :
    primeToIsotypicCohomology d ⟶ primeToGaloisCohomologyFunctor d :=
  Functor.whiskerLeft _ (isotypicActionι ξ Gamma) ≫ (Functor.rightUnitor _).hom

@[simp] theorem cmPrimeToIsotypicCohomologyι_app_apply (d : ℕ) (M : ModuleSheaf base R)
    (x : isotypicPart ξ ((primeToGaloisCohomologyFunctor d).obj M).V.representation) :
    SmoothRep.hom ((cmPrimeToIsotypicCohomologyι D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm K₀
        ξ d).app M).hom x = x.1 :=
  rfl

theorem cmPrimeToIsotypicCohomologyι_app_injective (d : ℕ) (M : ModuleSheaf base R) :
    Function.Injective (SmoothRep.hom ((cmPrimeToIsotypicCohomologyι D C preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
      criterion R m hm K₀ ξ d).app M).hom) :=
  fun _ _ hxy => isotypicι_app_injective ξ _ hxy

/-- The multiplicity spaces `Hom(ξ, H^d)` of intertwining maps from `ξ` into the prime-to-`m`
cohomology, as representations of `Gal(F̄/F)` acting by composition, natural in the sheaf. -/
def cmPrimeToMultiplicityFunctor (d : ℕ) : ModuleSheaf base R ⥤ Rep.{uU} R Gamma :=
  primeToGaloisCohomologyFunctor d ⋙ multiplicityRepFunctor ξ Gamma

local notation "primeToMultiplicityCohomology" => cmPrimeToMultiplicityFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R m hm K₀ ξ

/-- A Galois element acts on an intertwining map by composition with its action on the
cohomology. -/
@[simp] theorem cmPrimeToMultiplicityFunctor_ρ_apply (d : ℕ) (M : ModuleSheaf base R)
    (σ : Gamma)
    (φ : ξ.IntertwiningMap ((primeToGaloisCohomologyFunctor d).obj M).V.representation) :
    ((primeToMultiplicityCohomology d).obj M).ρ σ φ =
      (SmoothRep.hom (((primeToGaloisCohomologyFunctor d).obj M).ρ σ)).comp φ :=
  rfl

/-- Evaluation `ξ ⊗ Hom(ξ, H^d) → H^d[ξ]` on the prime-to-`m` cohomology is surjective. -/
theorem cmPrimeToIsotypicEvaluation_surjective (d : ℕ) (M : ModuleSheaf base R) :
    Function.Surjective (isotypicEvaluation ξ ((primeToGaloisCohomologyFunctor d).obj M).V) :=
  isotypicEvaluation_surjective ξ _

/-- Evaluation intertwines the Galois action on the multiplicity space with the Galois action on
the `ξ`-isotypic part of the prime-to-`m` cohomology. -/
theorem cmPrimeToIsotypicEvaluation_galois (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma) :
    isotypicEvaluation ξ ((primeToGaloisCohomologyFunctor d).obj M).V ∘ₗ
        LinearMap.lTensor U
          (multiplicityRepresentation ξ Gamma ((primeToGaloisCohomologyFunctor d).obj M) σ) =
      isotypicGaloisRepresentation ξ Gamma ((primeToGaloisCohomologyFunctor d).obj M) σ ∘ₗ
        isotypicEvaluation ξ ((primeToGaloisCohomologyFunctor d).obj M).V :=
  isotypicEvaluation_galois ξ Gamma _ σ

/-! ### Hecke modules -/

variable (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)

/-- The `K'`-fixed vectors of the `ξ`-isotypic part of the prime-to-`m` cohomology, as modules
over the Hecke algebra of `K'` with the commuting Galois action, natural in the sheaf. -/
def cmPrimeToIsotypicHeckeModuleFunctor (d : ℕ) :
    ModuleSheaf base R ⥤
      Action (ModuleCat.{0} (LevelHecke.LevelHeckeAlgebra R K'.subgroup)) Gamma :=
  primeToIsotypicCohomology d ⋙ LevelHecke.heckeModuleActionFunctor R Gamma K'.subgroup

/-- Each Galois element commutes with every element of the Hecke algebra of `K'` on the
`K'`-fixed vectors of the `ξ`-isotypic part. -/
theorem cmPrimeToIsotypicHeckeModule_ρ_smul (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma)
    (a : LevelHecke.LevelHeckeAlgebra R K'.subgroup)
    (x : fixedVectors ((primeToIsotypicCohomology d).obj M).V.obj.ρ K'.subgroup) :
    (((cmPrimeToIsotypicHeckeModuleFunctor D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm
        K₀ ξ K' d).obj M).ρ σ).hom (a • x) =
      a • (((cmPrimeToIsotypicHeckeModuleFunctor D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm
        K₀ ξ K' d).obj M).ρ σ).hom x :=
  LevelHecke.heckeModuleActionFunctor_ρ_smul Gamma K'.subgroup _ σ a x

end PrimeTo

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
