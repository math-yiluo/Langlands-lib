/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Perfect
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
public import WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport
public import WeilConjectures.EtaleCohomology.PoincareDuality.CompactSupportPerfect
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedForget
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar

/-!
# The global sections are perfect at the point

Let `k` be a separably closed field, `X` a separated scheme of finite type over `k` with
structure morphism `a_X : X ⟶ Spec k`, and `K` a bounded constructible complex on `X` of finite
Tor amplitude. This file proves that the ordinary and the compactly supported cohomology
complexes `RΓ(X, K)` and `RΓ_c(X, K)`, and their duals `RHom(-, Λ)`, are *perfect point
complexes* (`DerivedCategory.IsPerfect`), at each coefficient stage of the `ℓ`-adic formalism:
at the finite stages `Λ = A_{E,n}`, at the integral stage `𝒪_E`, at the rational stage `E`
and at `ℚ̄_ℓ` (blueprint `lemma-perfect-complexes-geometric-point`).

## Main statements

At a finite coefficient ring `Λ` whose exponent is invertible on `k`:

- `AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`: `RΓ_c(X, K)` is perfect.
- `AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections`: `RΓ(X, K)` is perfect.
- `AlgebraicGeometry.Etale.isPerfect_ihom_compactlySupportedGlobalSections`,
  `AlgebraicGeometry.Etale.isPerfect_ihom_rightDerivedGlobalSections`: so are their duals.

At the integral stage `𝒪_E`, for a derived complete `K` whose reductions `K ⊗ᴸ 𝒪_E/𝔪_Eⁿ` are
bounded constructible of Tor amplitude in one common interval:

- `AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_integral`,
  `AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections_integral` and the duals.

At the rational stage `E`, the cohomology of these complexes and of their duals tensored up to
`E`:

- `AlgebraicGeometry.Etale.rationalHomology_globalSections`.

At `ℚ̄_ℓ`, for `k` algebraically closed, `ℓ` different from its characteristic and pro-étale
complexes with constructible `ℓ`-adic cohomology sheaves, in
`WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfectAdic`:

- `AlgebraicGeometry.ProEtale.isPerfect_compactlySupportedGlobalSections_adic`,
  `AlgebraicGeometry.ProEtale.isPerfect_rightDerivedGlobalSections_adic`,
  `AlgebraicGeometry.ProEtale.isPerfect_ihom_compactlySupportedGlobalSections_adic`,
  `AlgebraicGeometry.ProEtale.isPerfect_ihom_rightDerivedGlobalSections_adic`.

## Implementation notes

The finite stage follows the blueprint: `RΓ_c(X, K)` is bounded with finite cohomology and of
finite Tor amplitude (`lemma-perfect-complexes-geometric-point`), hence perfect over the Noetherian
ring `Λ` (`DerivedCategory.isPerfect_of_finiteTorAmplitude`). For `RΓ(X, K)` choose a
compactification `X ⟶[j] X̄ ⟶[ā] Spec k` of `a_X`. Then `RΓ(X, K) ≅ RΓ(X̄, Rj_* K)` (Leray) and
`RΓ(X̄, -) ≅ RΓ_c(X̄, -)` since `ā` is proper, and `Rj_* K` is again bounded constructible of
finite Tor amplitude (`sk-thm-sf-direct-image-tor-amplitude`), so the compactly supported case
applies to `Rj_* K` on `X̄`. The integral stage is reduced to its compactly supported case in
the same way.

The rational stage `E = 𝒪_E[1/ℓ]` is the rationalization of the integral stage
(`DerivedCategoryDerivedCompleteRational`), whose objects come from integral ones. There is no
derived category of `E`-modules receiving the rationalized global sections in the repository,
so the rational statements are made on cohomology: `E ⊗_{𝒪_E} Hⁱ(C)` is finite dimensional and
vanishes outside a finite interval, for `C` any of the integral complexes above. By flatness of
`E` over `𝒪_E` these are the cohomology spaces of `C ⊗ᴸ_{𝒪_E} E`, and over a field this is
perfectness (`DerivedCategory.isPerfect_iff`).

At `ℚ̄_ℓ` the coefficients are the pro-étale `ℚ̄_ℓ`-sheaves `WeilCoefficients l` of the Weil
sheaf formalism, and bounded constructible means bounded with cohomology sheaves
`ℓ`-adically constructible (`ProEtale.DerivedCategory.boundedAdicConstructible`),
as in the definition of `AlgebraicGeometry.WeilComplex`. This stage is not deduced from the
integral one (there is no comparison of `ℚ̄_ℓ,X`-modules with `ℓ`-adic towers in the
repository) but proved directly, for `k` algebraically closed as in the blueprint setting
`prose-01-10`: the derived pushforward to `Spec k` of an object of `D^b_c(X, ℚ̄_ℓ)` is in
`D^b_c(Spec k, ℚ̄_ℓ)` by the pro-étale finiteness theorem
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`), and the global sections of such an
object are perfect, the global sections functor on `Spec k` being exact and constructible
sheaves on `Spec k` having finite dimensional global sections.
-/

@[expose] public section

universe w u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor TensorProduct

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [HasCompactification aX]

include aX in
/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point. This is also blueprint `lemma-perfect-complexes-geometric-point` (Point perfectness of
global sections), at the finite stage.

**`RΓ(X, K)` is perfect.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`, the ordinary cohomology
complex `RΓ(X, K)` is a perfect complex of `Λ`-modules. For a compactification
`X ⟶[j] X̄ ⟶[ā] Spec k` of `a_X`, `RΓ(X, K) ≅ RΓ(X̄, Rj_* K) ≅ RΓ_c(X̄, Rj_* K)`, `ā` being
proper, and `Rj_* K ∈ Dctf(X̄, Λ)` (`lemma-perfect-complexes-geometric-point--5`). -/
theorem isPerfect_rightDerivedGlobalSections [QuasiCompact aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K).IsPerfect := by
  let c := HasCompactification.compactification aX
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have : HasInvertibleExponent Λ c.Z := HasInvertibleExponent.of_hom c.g
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  obtain ⟨hbc, a, b, hta⟩ := hK
  obtain ⟨N, hN0, hNΛ, hNY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := c.Z)
  have : NeZero N := ⟨hN0.ne'⟩
  have hN := nsmul_id_eq_zero_of_natCast_eq_zero hNΛ K
  have : IsNoetherianRing Λ := inferInstance
  have hK' : DerivedCategory.boundedConstructibleFiniteTor Λ c.Z
      ((R((c.i)_*[ModuleCat.{u + 1} Λ])).obj K) :=
    ⟨boundedConstructible_rightDerivedLowerStar_of_finite Λ aX c.g c.i c.comm.symm hbc,
      a, b + 2 * (d : ℤ),
      torAmplitudeIn_rightDerivedLowerStar _ aX c.g c.i c.comm.symm d hd a b N hN hNY hbc hta⟩
  exact (isPerfect_compactlySupportedGlobalSections Λ c.g _ hK').of_iso
    ((compactlySupportedGlobalSectionsIsoOfIsProper _ c.g).app _ ≪≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ c.i).app K)

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point. This is also blueprint `lemma-perfect-complexes-geometric-point` (Point perfectness of
global sections), at the finite stage.

**The dual of `RΓ_c(X, K)` is perfect.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`, the dual
`RHom_Λ(RΓ_c(X, K), Λ)` is a perfect complex of `Λ`-modules. -/
theorem isPerfect_ihom_compactlySupportedGlobalSections
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K)).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_compactlySupportedGlobalSections Λ aX K hK).ihom_unit

include aX in
/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point. This is also blueprint `lemma-perfect-complexes-geometric-point` (Point perfectness of
global sections), at the finite stage.

**The dual of `RΓ(X, K)` is perfect.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`, the dual
`RHom_Λ(RΓ(X, K), Λ)` is a perfect complex of `Λ`-modules. -/
theorem isPerfect_ihom_rightDerivedGlobalSections [QuasiCompact aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_rightDerivedGlobalSections Λ aX K hK).ihom_unit

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Point perfectness of global sections, the
finite stage `Λ = A_{E,n}`.

Let `Λ` be a finite ring whose exponent is invertible in the separably closed field `k`, let `X`
be separated of finite type over `k` (neither proper nor smooth) and `K ∈ Dctf(X, Λ)`. Then the
four complexes `RΓ(X, K)`, `RΓ_c(X, K)`, `RΓ(X, K)^∨` and `RΓ_c(X, K)^∨` are perfect point
complexes: bounded complexes of finite projective `Λ`-modules up to quasi-isomorphism. For
proper `X` the two cases are identified by
`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsIsoOfIsProper`.

The explicit Tor amplitude `[a, b + 2d]` of the blueprint is not recorded. -/
theorem isPerfect_globalSections [QuasiCompact aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K).IsPerfect ∧
      ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K).IsPerfect ∧
      ((ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj
        (𝟙_ _)).IsPerfect ∧
      ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K)).obj
        (𝟙_ _)).IsPerfect :=
  ⟨isPerfect_rightDerivedGlobalSections Λ aX K hK,
    isPerfect_compactlySupportedGlobalSections Λ aX K hK,
    isPerfect_ihom_rightDerivedGlobalSections Λ aX K hK,
    isPerfect_ihom_compactlySupportedGlobalSections Λ aX K hK⟩

end Finite

section Integral

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_pointPerfect
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- The integral stage `D^b_c(X, Λ)` of the `ℓ`-adic formalism, for `Λ = 𝒪_E` and `I = 𝔪_E`, as
an object property of `D(X_ét, Λ)`: the objects `K` which are derived complete for `I` and whose
reductions `K ⊗ᴸ Λ/Iⁿ⁺¹` are bounded constructible of Tor amplitude in one common interval
`[a, b]`. -/
def DerivedCategory.boundedConstructibleIntegral (X : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ DerivedCategory.derivedComplete X.smallEtaleTopology I K ∧
    ∃ a b : ℤ, ∀ n : ℕ,
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)

variable {I}

/-- An element `r ∈ J` kills the reduction `K ⊗ᴸ (Λ/J)_X`. (A copy of
`AlgebraicGeometry.Etale.smul_id_reductionModIdeal`, whose file imports this one.) -/
private lemma smul_id_reductionModIdeal' {X : Scheme.{u}} {J : Ideal Λ} {r : Λ} (hr : r ∈ J)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    r • 𝟙 ((reductionModIdeal Λ X J).obj K) = 0 := by
  have hM : r • 𝟙 (ModuleCat.of Λ (Λ ⧸ J)) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul (Ideal.Quotient.mk J),
      Ideal.Quotient.eq_zero_iff_mem]
    exact J.mul_mem_right _ hr
  change r • 𝟙 (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj _) = 0
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul,
    ← (_root_.DerivedCategory.singleFunctor _ 0).map_id, ← Functor.map_smul,
    ← (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map_id, ← Functor.map_smul, hM,
    Functor.map_zero, Functor.map_zero, Functor.map_zero]

/-- For a nonzerodivisor `ϖ` generating `I`, the third vertex of a distinguished triangle on the
multiplication `ϖ : K ⟶ K` is the reduction `K ⊗ᴸ (Λ/I)_X`: tensor the distinguished triangle
`Λ ⟶ Λ ⟶ Λ/I ⟶ Λ⟦1⟧` with `K`. -/
lemma nonempty_iso_reductionModIdeal_of_distTriang {X : Scheme.{u}} {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hϖI : I = Ideal.span {ϖ})
    {K K₁ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {g : K ⟶ K₁} {h : K₁ ⟶ K⟦(1 : ℤ)⟧} (hT : Triangle.mk (ϖ • 𝟙 K) g h ∈ distTriang _) :
    Nonempty (K₁ ≅ (reductionModIdeal Λ X I).obj K) := by
  let F := (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K
  let T := _root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ hϖI 1
  have hT' : F.mapTriangle.obj T ∈ distTriang _ :=
    F.map_distinguished _ (_root_.DerivedCategory.quotPowTriangle_distinguished _ hϖ hϖI 1)
  let e : (Ideal.quotPowFunctor I).obj (op 1) ≅ ModuleCat.of Λ (Λ ⧸ I) :=
    (Submodule.quotEquivOfEq _ _ (pow_one _)).toModuleIso
  let u : F.obj T.obj₁ ≅ K := derivedTensorSingleUnitIso K
  have hmor : (F.mapTriangle.obj T).mor₁ = ϖ • 𝟙 (F.obj T.obj₁) := by
    change F.map T.mor₁ = _
    rw [_root_.DerivedCategory.quotPowTriangle_mor₁, pow_one, Functor.map_smul,
      CategoryTheory.Functor.map_id]
  obtain ⟨φ, -⟩ := exists_iso_of_arrow_iso _ _ hT hT'
    (Arrow.isoMk u.symm u.symm (by
      change u.inv ≫ (F.mapTriangle.obj T).mor₁ = (ϖ • 𝟙 K) ≫ u.inv
      rw [hmor, Linear.comp_smul, Linear.smul_comp]
      exact congrArg (ϖ • ·) ((Category.comp_id u.inv).trans (Category.id_comp u.inv).symm)))
  exact ⟨Triangle.π₃.mapIso φ ≪≫ F.mapIso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso e))⟩

/-- The reduction modulo the zero ideal is the identity: `K ⊗ᴸ (Λ/0)_X ≅ K`. -/
noncomputable def reductionModIdealBotIso {X : Scheme.{u}}
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (reductionModIdeal Λ X ⊥).obj K ≅ K :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
      ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
          (Submodule.quotEquivOfEqBot (⊥ : Submodule Λ Λ) rfl).toModuleIso)) ≪≫
    derivedTensorSingleUnitIso K

variable [IsDomain Λ] [IsPrincipalIdealRing Λ] {k : Type u} [Field k] [IsSepClosed k]

/-- **The transfer of the algebraic perfectness criterion to the point.** Let `Λ` be a principal
ideal domain, complete for the ideal generated by a nonzerodivisor `ϖ`. If an object `N` of
`D(Spec(k)_ét, Λ)` is right orthogonal to the objects on which `ϖ` acts invertibly, and the
reduction `N₁ = cone(ϖ : N ⟶ N)` has perfect derived global sections, then so has `N`. Evaluation
at the point is a `Λ`-linear triangulated equivalence `D(Spec(k)_ét, Λ) ≌ D(Λ)`, so this is
`DerivedCategory.isPerfect_obj_of_rightOrthogonal_of_isPerfect_obj₃`. -/
theorem isPerfect_rightDerivedGlobalSections_of_rightOrthogonal {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) [IsAdicComplete (Ideal.span {ϖ}) Λ]
    {N N₁ : _root_.DerivedCategory
      (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : (_root_.DerivedCategory.smulInvertible (Spec (.of k)).smallEtaleTopology
      ϖ).rightOrthogonal N)
    {g : N ⟶ N₁} {h : N₁ ⟶ N⟦(1 : ℤ)⟧} (hT : Triangle.mk (ϖ • 𝟙 N) g h ∈ distTriang _)
    (hN₁ : ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj N₁).IsPerfect) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj N).IsPerfect := by
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).IsTriangulated :=
    inferInstanceAs (Sheaf.Γ (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).Linear Λ :=
    inferInstanceAs ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.Linear Λ)
  exact _root_.DerivedCategory.isPerfect_obj_of_rightOrthogonal_of_isPerfect_obj₃ _ hϖ hT
    (fun _ f hL ↦ hN f hL) hN₁

variable [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]

/-- **The integral stage at the point.** Let `Λ` be a principal ideal domain, complete for the
ideal `I` generated by a nonzerodivisor `ϖ`, with `Λ/I` finite of exponent invertible in `k`.
Let `K ∈ D(X_ét, Λ)` have reduction `K ⊗ᴸ (Λ/I)_X` bounded constructible of finite Tor
amplitude. Let `N ∈ D(Spec(k)_ét, Λ)` be right orthogonal to the objects on which `ϖ` acts
invertibly, and `φ : Ra_! K ⟶ N` a map whose cone is an object on which `ϖ` acts invertibly (for
instance the map to the derived completion of `Ra_! K`). Then `RΓ(Spec k, N)` is perfect.

The reduction of `φ` is an isomorphism, so the reduction of `N` is
`Ra_! K ⊗ᴸ Λ/I ≅ Ra_!(K ⊗ᴸ Λ/I)`, whose global sections are perfect by the finite stage
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_of_nsmul_eq_zero`. -/
theorem isPerfect_rightDerivedGlobalSections_of_rightOrthogonal_of_hom {ϖ : Λ} [Finite (Λ ⧸ I)]
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hϖI : I = Ideal.span {ϖ}) [IsAdicComplete (Ideal.span {ϖ}) Λ]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
    [HasCompactification aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      ((reductionModIdeal Λ X I).obj K))
    {a b : ℤ} (hKt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      ((reductionModIdeal Λ X I).obj K))
    (N : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hN : (_root_.DerivedCategory.smulInvertible (Spec (.of k)).smallEtaleTopology
      ϖ).rightOrthogonal N)
    (φ : (R(aX)_![ModuleCat.{u + 1} Λ]).obj K ⟶ N)
    (hφ : ∀ (Y : _root_.DerivedCategory
        (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) (g : N ⟶ Y)
        (h : Y ⟶ ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)⟦(1 : ℤ)⟧),
        Triangle.mk φ g h ∈ distTriang _ →
          _root_.DerivedCategory.smulInvertible (Spec (.of k)).smallEtaleTopology ϖ Y) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj N).IsPerfect := by
  have hϖmem : ϖ ∈ I := hϖI ▸ Ideal.mem_span_singleton_self ϖ
  obtain ⟨N₁, g, h, hT⟩ := distinguished_cocone_triangle (ϖ • 𝟙 N)
  refine isPerfect_rightDerivedGlobalSections_of_rightOrthogonal hϖ hN hT ?_
  obtain ⟨e₁⟩ := nonempty_iso_reductionModIdeal_of_distTriang hϖ hϖI hT
  -- the reduction of `φ` is an isomorphism
  let F := reductionModIdeal Λ (Spec (.of k)) I
  have : F.Linear Λ := inferInstanceAs
    (((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).flip.obj _).Linear Λ)
  obtain ⟨Y, g', h', hY⟩ := distinguished_cocone_triangle φ
  have hYinv : IsIso (ϖ • 𝟙 Y) := hφ Y g' h' hY
  have hFY : IsZero (F.obj Y) := by
    have hinv : IsIso (ϖ • 𝟙 (F.obj Y)) := by
      rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
      infer_instance
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (ϖ • 𝟙 (F.obj Y)),
      smul_id_reductionModIdeal' hϖmem Y, Limits.comp_zero, Limits.comp_zero]
  have hFφ : IsIso (F.map φ) :=
    (Triangle.isZero₃_iff_isIso₁ _ (F.map_distinguished _ hY)).1 hFY
  obtain ⟨e₂⟩ := nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_isPrincipal (Λ := Λ) aX
    I ⟨⟨ϖ, hϖI⟩⟩
  -- the reduction of `K` is killed by the exponent `m` of `Λ/I`
  obtain ⟨m, hm0, hmΛ, hmk⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ ⧸ I)
    (X := Spec (.of k))
  have hmI : (m : Λ) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hmΛ
  have : NeZero m := ⟨hm0.ne'⟩
  exact (isPerfect_compactlySupportedGlobalSections_of_nsmul_eq_zero Λ aX _ I m hmI
    (fun _ hr ↦ smul_id_reductionModIdeal' hr K) hmk ⟨hK, a, b, hKt⟩).of_iso
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).mapIso
      ((e₂.app K).symm ≪≫ asIso (F.map φ) ≪≫ e₁.symm))

variable [IsAdicComplete I Λ] [Finite (Λ ⧸ I)]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [HasCompactification aX]

omit [IsDomain Λ] [IsPrincipalIdealRing Λ] [IsSepClosed k] in
/-- For `I = 0`, the ring `Λ ≅ Λ/I` is finite of exponent invertible in `k`, so the integral
stage is the finite stage. -/
lemma finite_and_hasInvertibleExponent_of_eq_bot (h : I = ⊥) :
    Finite Λ ∧ HasInvertibleExponent Λ (Spec (.of k)) := by
  subst h
  let e : (Λ ⧸ (⊥ : Ideal Λ)) ≃+* Λ := RingEquiv.quotientBot Λ
  refine ⟨Finite.of_equiv _ e.toEquiv, ?_⟩
  obtain ⟨m, hm0, hmΛ, hmk⟩ := HasInvertibleExponent.exists_isUnit_natCast
    (Λ := Λ ⧸ (⊥ : Ideal Λ)) (X := Spec (.of k))
  exact ⟨m, hm0, by simpa using congrArg e hmΛ, hmk⟩

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point.

**`RΓ_c(X, K)` is perfect at the integral stage.** Let `Λ` be a principal ideal domain, complete
for an ideal `I` with `Λ/I` finite of exponent invertible in `k`; this is the integral stage
`Λ = 𝒪_E`, `I = 𝔪_E` for `E` finite over `ℚ_ℓ`. For `K ∈ D^b_c(X, Λ)`, the integral compactly
supported cohomology is perfect. Following the blueprint, the integral `Ra_! K` is the derived limit
`R lim_n Ra_!(K) ⊗ᴸ Λ/Iⁿ ≅ R lim_n Ra_!(K ⊗ᴸ Λ/Iⁿ)` of the finite-level compactly supported direct
images, given here by any homotopy limit cone `c` of the tower of reductions of the étale
`Ra_! K`; the integral `RΓ_c(X, K)` is `RΓ(Spec k, c.pt)`.

The étale `Ra_! K` itself need not be derived complete, and `RΓ(Spec k, Ra_! K)` need not be
perfect: for `X = 𝔸¹` and `K = R lim_n (Λ/Iⁿ)_X`, which lies in `D^b_c(X, Λ)`, its `H²` is not
finitely generated (an étale neighbourhood of `∞` in `ℙ¹` of positive genus contributes
non-torsion classes which no smaller neighbourhood kills).

The completion `c.pt` is right orthogonal to the objects on which a generator `ϖ` of `I` acts
invertibly, and its reduction modulo `ϖ` is `Ra_!(K ⊗ᴸ Λ/I)`, perfect by the finite stage; so it
is perfect by `DerivedCategory.isPerfect_of_rightOrthogonal_of_isPerfect_obj₃`. -/
theorem isPerfect_compactlySupportedGlobalSections_integral (hI : I.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K)
    (c : Cone (_root_.DerivedCategory.derivedCompletionDiagram (Spec (.of k)).smallEtaleTopology
      I ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)))
    (hc : Pretriangulated.IsHomotopyLimit c) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj c.pt).IsPerfect := by
  obtain ⟨-, a, b, hab⟩ := hK
  obtain ⟨hbc, hta⟩ := hab 0
  rw [zero_add, pow_one] at hbc hta
  obtain ⟨ϖ, hϖI⟩ := hI.principal
  replace hϖI : I = Ideal.span {ϖ} := hϖI
  by_cases h0 : ϖ = 0
  · -- `I = 0`: `Λ` is finite and every object is derived complete
    obtain rfl : I = ⊥ := by rw [hϖI, h0, Ideal.span_singleton_eq_bot]
    obtain ⟨_, _⟩ := finite_and_hasInvertibleExponent_of_eq_bot (k := k) (I := (⊥ : Ideal Λ)) rfl
    obtain ⟨e, -⟩ := hc.exists_iso (_root_.DerivedCategory.derivedComplete_bot _)
    exact (isPerfect_compactlySupportedGlobalSections Λ aX _ ⟨hbc, a, b, hta⟩).of_iso
      ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).mapIso
        (reductionModIdealBotIso K) ≪≫
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).mapIso e.symm)
  have hϖ : ϖ ∈ nonZeroDivisors Λ := mem_nonZeroDivisors_of_ne_zero h0
  have : IsAdicComplete (Ideal.span {ϖ}) Λ := hϖI ▸ inferInstance
  obtain ⟨hN, φ, hφ⟩ :=
    _root_.DerivedCategory.rightOrthogonal_and_exists_smulInvertible_cone_of_isHomotopyLimit hϖ
      hϖI _ hc
  exact isPerfect_rightDerivedGlobalSections_of_rightOrthogonal_of_hom hϖ hϖI aX K hbc hta c.pt
    hN φ hφ

omit [IsSeparated aX] in
/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point.

**`RΓ(X, K)` is perfect at the integral stage.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_integral`, the cohomology
`RΓ(X, K)` is a perfect complex of `Λ`-modules. For a compactification
`X ⟶[j] X̄ ⟶[ā] Spec k` of `a_X` one has `RΓ(X, K) ≅ RΓ(Spec k, Rā_! Rj_* K)`, and `Rj_* K` is
again in `D^b_c(X̄, Λ)`: `Rj_*` preserves derived completeness, commutes with the reductions, and
carries Tor amplitude `[a, b]` to `[a, b + 2 dim X]`. As `ā` is proper, `Rā_! Rj_* K ≅ Rā_* Rj_* K`
is derived complete, so it is its own derived completion, and the argument of the compactly
supported case applies. -/
theorem isPerfect_rightDerivedGlobalSections_integral [QuasiCompact aX] (hI : I.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K).IsPerfect := by
  obtain ⟨ϖ, hϖI⟩ := hI.principal
  replace hϖI : I = Ideal.span {ϖ} := hϖI
  by_cases h0 : ϖ = 0
  · obtain rfl : I = ⊥ := by rw [hϖI, h0, Ideal.span_singleton_eq_bot]
    obtain ⟨_, _⟩ := finite_and_hasInvertibleExponent_of_eq_bot (k := k) (I := (⊥ : Ideal Λ)) rfl
    obtain ⟨-, a, b, hab⟩ := hK
    obtain ⟨hbc, hta⟩ := hab 0
    rw [zero_add, pow_one] at hbc hta
    exact (isPerfect_rightDerivedGlobalSections Λ aX _ ⟨hbc, a, b, hta⟩).of_iso
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).mapIso (reductionModIdealBotIso K))
  have hϖ : ϖ ∈ nonZeroDivisors Λ := mem_nonZeroDivisors_of_ne_zero h0
  have : IsAdicComplete (Ideal.span {ϖ}) Λ := hϖI ▸ inferInstance
  let c := HasCompactification.compactification aX
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  obtain ⟨hc, a, b, hab⟩ := hK
  have hK' : DerivedCategory.boundedConstructibleIntegral I c.Z
      ((R((c.i)_*[ModuleCat.{u + 1} Λ])).obj K) := by
    refine ⟨derivedComplete_rightDerivedLowerStar I hI c.i K hc, a, b + 2 * (d : ℤ),
      fun n ↦ ?_⟩
    obtain ⟨x, hx⟩ := hI.principal
    have hJ : (I ^ (n + 1)).IsPrincipal :=
      ⟨⟨x ^ (n + 1), by rw [hx, Ideal.submodule_span_eq, Ideal.span_singleton_pow]⟩⟩
    obtain ⟨e⟩ := nonempty_iso_reductionModIdeal_rightDerivedLowerStar Λ c.i _ hJ
    obtain ⟨hbc, hta⟩ := hab n
    -- the reduction is killed by `N = mⁿ⁺¹`, for `m` the exponent of `Λ/I`
    have : HasInvertibleExponent (Λ ⧸ I) c.Z := HasInvertibleExponent.of_hom c.g
    obtain ⟨m, hm0, hmΛ, hmY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ ⧸ I)
      (X := c.Z)
    have hmI : (m : Λ) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact hmΛ
    have : NeZero (m ^ (n + 1)) := ⟨pow_ne_zero _ hm0.ne'⟩
    have hNY : IsUnit ((m ^ (n + 1) : ℕ) : Γ(c.Z, ⊤)) := by
      rw [Nat.cast_pow]; exact hmY.pow _
    have hN := nsmul_id_reductionModIdeal (J := I ^ (n + 1)) (N := m ^ (n + 1))
      (by rw [Nat.cast_pow]; exact Ideal.pow_mem_pow hmI _) K
    have : Finite (Λ ⧸ I ^ (n + 1)) := Ideal.finite_quotient_pow (IsNoetherian.noetherian I) _
    exact ⟨(DerivedCategory.boundedConstructible _ _).prop_of_iso (e.app K).symm
        (boundedConstructible_rightDerivedLowerStar Λ (I ^ (n + 1)) aX c.g c.i c.comm.symm _
          (by rw [Nat.cast_pow]; exact Ideal.pow_mem_pow hmI _) hNY
          (fun r hr ↦ smul_id_reductionModIdeal hr K) hbc),
      (DerivedCategory.torAmplitudeIn _ _ _ _).prop_of_iso (e.app K).symm
        (torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing _ aX c.g c.i c.comm.symm d hd a b
          _ hN hNY hbc hta)⟩
  obtain ⟨hLc, a', b', hL⟩ := hK'
  obtain ⟨hbc', hta'⟩ := hL 0
  rw [zero_add, pow_one] at hbc' hta'
  let L := (R((c.i)_*[ModuleCat.{u + 1} Λ])).obj K
  -- `Rā_! L ≅ Rā_* L` is right orthogonal to the objects on which `ϖ` acts invertibly
  have hLorth : (_root_.DerivedCategory.smulInvertible c.Z.smallEtaleTopology ϖ).rightOrthogonal
      L := (_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ hϖI L).1 hLc
  have hN : (_root_.DerivedCategory.smulInvertible (Spec (.of k)).smallEtaleTopology
      ϖ).rightOrthogonal ((R(c.g)_![ModuleCat.{u + 1} Λ]).obj L) := by
    intro Z f hZ
    have := rightOrthogonal_smulInvertible_rightDerivedLowerStar ϖ c.g L hLorth
      (f ≫ ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ c.g).app L).hom) hZ
    rwa [Preadditive.IsIso.comp_right_eq_zero] at this
  refine (isPerfect_rightDerivedGlobalSections_of_rightOrthogonal_of_hom hϖ hϖI c.g L hbc' hta'
    _ hN (𝟙 _) fun Y g h hY ↦ ?_).of_iso
    ((compactlySupportedGlobalSectionsIsoOfIsProper _ c.g).app _ ≪≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ c.i).app K)
  have hY0 : IsZero Y := (Triangle.isZero₃_iff_isIso₁ _ hY).2 (inferInstanceAs (IsIso (𝟙 _)))
  exact ⟨⟨0, hY0.eq_of_src _ _, hY0.eq_of_src _ _⟩⟩

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point.

**The dual of `RΓ_c(X, K)` is perfect at the integral stage.** Here `RΓ_c(X, K)` is the integral
compactly supported cohomology `RΓ(Spec k, c.pt)` of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_integral`. -/
theorem isPerfect_ihom_compactlySupportedGlobalSections_integral (hI : I.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K)
    (c : Cone (_root_.DerivedCategory.derivedCompletionDiagram (Spec (.of k)).smallEtaleTopology
      I ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)))
    (hc : Pretriangulated.IsHomotopyLimit c) :
    ((ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj c.pt)).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_compactlySupportedGlobalSections_integral aX hI K hK c hc).ihom_unit

omit [IsSeparated aX] in
/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point.

**The dual of `RΓ(X, K)` is perfect at the integral stage.** -/
theorem isPerfect_ihom_rightDerivedGlobalSections_integral [QuasiCompact aX]
    (hI : I.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    ((ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_rightDerivedGlobalSections_integral aX hI K hK).ihom_unit

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point. This is also blueprint `lemma-perfect-complexes-geometric-point` (Point perfectness of
global sections), at the field stage `E`.

**The rational stage.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_integral`, let `E` be a
field which is a `Λ`-algebra (for `Λ = 𝒪_E` the fraction field `E`, so that `K ⊗ E` is an
object of the rational stage `D^b_c(X, E)`). The spaces `E ⊗_Λ Hⁱ_c(X, K)` and
`E ⊗_Λ Hⁱ(X, K)`, as well as those of the duals of `RΓ_c(X, K)` and `RΓ(X, K)`, are finite
dimensional and vanish outside a finite interval: the rationalized complexes are perfect
complexes of `E`-vector spaces. Here `RΓ_c(X, K)` is the integral compactly supported cohomology
`RΓ(Spec k, c.pt)`. This is flat extension of scalars from the integral stage. -/
theorem rationalHomology_globalSections [QuasiCompact aX] (hI : I.IsPrincipal)
    (E : Type*) [Field E] [Algebra Λ E]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K)
    (c : Cone (_root_.DerivedCategory.derivedCompletionDiagram (Spec (.of k)).smallEtaleTopology
      I ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)))
    (hc : Pretriangulated.IsHomotopyLimit c) :
    ∀ C ∈ ({(rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj c.pt,
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K,
        (ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj c.pt)).obj
          (𝟙_ _),
        (ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj (𝟙_ _)} :
          Set (_root_.DerivedCategory (ModuleCat.{u + 1} Λ))),
      (∀ i, FiniteDimensional E
        (E ⊗[Λ] (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj C)) ∧
      ∃ a b : ℤ, ∀ i, i < a ∨ b < i →
        Subsingleton
          (E ⊗[Λ] (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj C) := by
  intro C hC
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  rcases hC with rfl | rfl | rfl | rfl
  · exact (isPerfect_compactlySupportedGlobalSections_integral aX hI K hK c hc).tensor_homology E
  · exact (isPerfect_rightDerivedGlobalSections_integral aX hI K hK).tensor_homology E
  · exact (isPerfect_ihom_compactlySupportedGlobalSections_integral aX hI K hK c
      hc).tensor_homology E
  · exact (isPerfect_ihom_rightDerivedGlobalSections_integral aX hI K hK).tensor_homology E

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Point perfectness of global sections, the
integral stage `Λ = 𝒪_E`.

In the situation of `AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_integral`
(`Λ` a complete Noetherian domain for a principal ideal `I` with finite residue ring of exponent
invertible in `k`, and `K ∈ D^b_c(X, Λ)`), the four complexes `RΓ(X, K)`, `RΓ_c(X, K)` and their
duals are perfect complexes of `Λ`-modules. Here `RΓ_c(X, K)` is the integral compactly supported
cohomology `RΓ(Spec k, c.pt)`, for `c` a homotopy limit cone of the tower of reductions of the
étale `Ra_! K`. The field stage `E` is `AlgebraicGeometry.Etale.rationalHomology_globalSections`. -/
theorem isPerfect_globalSections_integral [QuasiCompact aX]
    (hI : I.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K)
    (c : Cone (_root_.DerivedCategory.derivedCompletionDiagram (Spec (.of k)).smallEtaleTopology
      I ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)))
    (hc : Pretriangulated.IsHomotopyLimit c) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K).IsPerfect ∧
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj c.pt).IsPerfect ∧
      ((ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj
        (𝟙_ _)).IsPerfect ∧
      ((ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj c.pt)).obj
        (𝟙_ _)).IsPerfect :=
  ⟨isPerfect_rightDerivedGlobalSections_integral aX hI K hK,
    isPerfect_compactlySupportedGlobalSections_integral aX hI K hK c hc,
    isPerfect_ihom_rightDerivedGlobalSections_integral aX hI K hK,
    isPerfect_ihom_compactlySupportedGlobalSections_integral aX hI K hK c hc⟩

end Integral

end Etale

/-- A module over `ULift ℚ̄_ℓ` whose underlying `ℚ̄_ℓ`-vector space is finite dimensional is a
finite module. -/
lemma WeilCoefficients.finite_of_finiteDimensional (l : ℕ) [Fact l.Prime]
    (M : WeilCoefficients.{u} l) [h : FiniteDimensional (PadicAlgCl l) ((toModuleCat l).obj M)] :
    Module.Finite (ULift.{u + 1} (PadicAlgCl l)) M := by
  obtain ⟨s, hs⟩ := h.fg_top
  refine ⟨⟨s, eq_top_iff.2 ?_⟩⟩
  rintro x -
  have hx : x ∈ Submodule.span (PadicAlgCl l) (s : Set ((toModuleCat l).obj M)) := hs ▸ trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
  | smul c y _ hy => exact Submodule.smul_mem _ (ULift.up c) hy

namespace ProEtale

section Point

variable (l : ℕ) [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field `K`, the global sections functor on pro-étale sheaves of
`ℚ̄_ℓ`-modules on `Spec K` is exact. -/
instance preservesFiniteColimits_Γ_of_isAlgClosed :
    PreservesFiniteColimits
      (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)) := by
  have h := (Functor.preservesFiniteLimits_tfae
    (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l))).out 4 1
  have h' := (Functor.preservesFiniteColimits_tfae
    (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l))).out 1 4
  exact h'.1 fun S hS ↦ ⟨(h.1 inferInstance S hS).1, by have := hS.epi_g; infer_instance⟩

/-- Over an algebraically closed field `K`: for `M ∈ D^b_c(Spec K, ℚ̄_ℓ)` the derived global
sections of the underlying complex of sheaves of `ℚ̄_ℓ`-modules form a perfect complex. The
global sections functor is exact, so `Hⁿ(RΓ(Spec K, M)) = Γ(Spec K, Hⁿ(M))`, which vanishes
outside the amplitude of `M` and is finite dimensional, `Hⁿ(M)` being constructible
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.finiteDimensional_globalSections`). -/
theorem isPerfect_rightDerivedGlobalSections_forget_of_isAlgClosed
    (M : _root_.DerivedCategory (AdicSheaf l (Spec (.of K))))
    (hM : DerivedCategory.boundedAdicConstructible l _ M) :
    ((rightDerivedGlobalSections (WeilCoefficients.{u} l) (Spec (.of K))).obj
      ((AdicSheaf.forget _).mapDerivedCategory.obj M)).IsPerfect := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hM
  have e (n : ℤ) : (_root_.DerivedCategory.homologyFunctor _ n).obj
      ((rightDerivedGlobalSections (WeilCoefficients.{u} l) (Spec (.of K))).obj
        ((AdicSheaf.forget _).mapDerivedCategory.obj M)) ≅
      (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).obj
        ((_root_.DerivedCategory.homologyFunctor _ n).obj M).X :=
    (Functor.rightDerivedFunctorHomologyFunctorIso _ n).symm.app _ ≪≫
      (Sheaf.Γ _ _).mapIso
        (((AdicSheaf.forget _).mapDerivedCategoryHomologyFunctorIso n).app M).symm
  rw [_root_.DerivedCategory.isPerfect_iff]
  refine ⟨⟨a, b, ?_, ?_⟩, fun n ↦ ?_⟩
  · rw [_root_.DerivedCategory.isGE_iff]
    intro n hn
    exact (Functor.map_isZero _ (Functor.map_isZero (AdicSheaf.forget _)
      ((_root_.DerivedCategory.isGE_iff M a).1 ha n hn))).of_iso (e n)
  · rw [_root_.DerivedCategory.isLE_iff]
    intro n hn
    exact (Functor.map_isZero _ (Functor.map_isZero (AdicSheaf.forget _)
      ((_root_.DerivedCategory.isLE_iff M b).1 hb n hn))).of_iso (e n)
  · have := IsAdicConstructibleSheaf.finiteDimensional_globalSections (hc n)
    have := WeilCoefficients.finite_of_finiteDimensional l
      ((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).obj
        ((_root_.DerivedCategory.homologyFunctor _ n).obj M).X)
    exact Module.Finite.equiv (e n).toLinearEquiv.symm

end Point

end ProEtale

end AlgebraicGeometry
