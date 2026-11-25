/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.IntegralDegreewise
public import WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Unit
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.CompositionPairing
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-!
# Adic reconstruction and scalar extension of the Poincaré pairing

Let `k` be a separably closed field, `a : X ⟶ Spec k` a morphism admitting a compactification
for which `Ra_!` has a right adjoint, `γ : T[2d] ≅ Ra^! Λ` a purity isomorphism (`T = Λ_X(d)`)
and `K ∈ D(X_ét, Λ)` perfect over `Λ_X`. This file proves blueprint
`theorem-poincare-duality--6` in the form the repository can express.

* The adjoint `β_K^♯ : RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨` of the derived Poincaré pairing
  (`AlgebraicGeometry.Etale.poincareAdjoint`) is an isomorphism over every coefficient ring
  `Λ`, in particular over `𝒪_E`; its inverse is the duality isomorphism
  `RΓ_c(X, K)^∨ ≅ RΓ(X, K^∨(d))[2d]`, also read in `D(Λ)`.
* For a nonzerodivisor `ϖ` and `A_n = Λ/(ϖ)ⁿ`, the reductions `β_K^♯ ⊗ᴸ A_n` are isomorphisms
  `RΓ(X, K^∨(d)_n)[2d] ≅ RHom(RΓ_c(X, K), A_n)` — the finite-level dualities — and they are
  compatible with the transition maps `A_m ⟶ A_n`: they form a morphism of towers.
* At the integral stage `Λ = 𝒪_E`, source and target of `β_K^♯` are derived complete, so
  `β_K^♯` is the realization of its tower of reductions (an isomorphism of the adic category
  `D_comp(Spec k, 𝒪_E)`), and localization `𝒪_E ⟶ E` as well as finite extension `E ⊆ L` of
  the coefficient field carry it to isomorphisms of `D_comp(Spec k, E)`, `D_comp(Spec k, 𝒪_L)`
  and `D_comp(Spec k, L)`.

## Main definitions

- `AlgebraicGeometry.Etale.poincareAdjoint`: the adjoint `β_K^♯` of the derived Poincaré
  pairing.
- `AlgebraicGeometry.Etale.reductionModIdealMap`: the transition `K ⊗ᴸ Λ/J ⟶ K ⊗ᴸ Λ/J'` for
  `J ≤ J'`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_poincareAdjoint`,
  `AlgebraicGeometry.Etale.nonempty_iso_ihom_compactlySupportedGlobalSections`: the duality
  isomorphism, in `D(Spec k_ét, Λ)` and in `D(Λ)`.
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_poincareAdjoint`,
  `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_poincareAdjoint_source`,
  `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_poincareAdjoint_target`,
  `AlgebraicGeometry.Etale.poincareAdjoint_reduction_naturality`: the finite-level dualities
  are the reductions of `β_K^♯`, and they form a morphism of towers.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_integral`: the pairing `β_K` and the
  pairings `β_{K_n}` of all its finite levels are perfect.
- `AlgebraicGeometry.Etale.adicReconstruction_scalarExtension`: the integral stage and the
  transport to `E` and to finite extensions of `E`.

## Implementation notes

As everywhere in the repository, the finite stage `A_n` is read inside `D(X_ét, Λ)` through
`K ↦ K ⊗ᴸ (Λ/(ϖ)ⁿ)_X`; the `A_n`-dual of `RΓ_c(X, K_n)` is then `RHom_Λ(RΓ_c(X, K), A_n)`. The
identification of the transported isomorphisms over `E` and `L` with the Poincaré pairings of
the base-changed complexes, and the transport of the degree-indexing maps, the relative form
and the Frobenius squares, need the compatibility of `Ra_!`, `Ra_*`, `RHom` and `⊗ᴸ` with
derived base change, which the repository does not have; they are not stated.
-/

@[expose] public section

universe w u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Transition

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The transition `K ⊗ᴸ (Λ/J)_X ⟶ K ⊗ᴸ (Λ/J')_X` between reductions, induced by the
projection `Λ/J ⟶ Λ/J'` for `J ≤ J'` (for `J = (ϖ)ᵐ`, `J' = (ϖ)ⁿ`, `n ≤ m`, the transition
`A_m ⟶ A_n` of the tower of finite stages). -/
noncomputable def reductionModIdealMap {J J' : Ideal Λ} (h : J ≤ J') :
    reductionModIdeal Λ X J ⟶ reductionModIdeal Λ X J' :=
  (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.map
    ((_root_.DerivedCategory.singleFunctor _ 0).map
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        (ModuleCat.ofHom (Submodule.factor h))))

end Transition

section General

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {Y : Scheme.{u}}

/-- The tensor–internal-hom adjoint `D ⟶ RHom(C, Λ_Y)` of a pairing `b : C ⊗ᴸ D ⟶ Λ_Y` in
`D(Y_ét)`. It is an isomorphism exactly when `b` is perfect
(`AlgebraicGeometry.Etale.IsPerfectPairing`). Like that definition, it is stated for a general
coefficient category, so that the kernel need not compare tensor products at `ModuleCat Λ`. -/
noncomputable def pairingAdjoint {C D : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (b : ((derivedTensor A Y).obj C).obj D ⟶ 𝟙_ _) : D ⟶ (ihom C).obj (𝟙_ _) :=
  MonoidalClosed.curry (C := _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) b

lemma IsPerfectPairing.isIso_pairingAdjoint
    {C D : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {b : ((derivedTensor A Y).obj C).obj D ⟶ 𝟙_ _} (hb : IsPerfectPairing b) :
    IsIso (pairingAdjoint b) :=
  hb.isIso

/-- The coefficient dual `RHom(C, Λ_Y)` is the internal hom `[C, Λ_Y]`, stated for a general
coefficient category so that the kernel compares the two only generically. -/
noncomputable def coefficientDualIsoIhom
    (C : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (DerivedCategory.coefficientDual A Y).obj (op C) ≅ (ihom C).obj (𝟙_ _) :=
  Iso.refl _

end General

section Adjoint

variable {k : Type u} [Field k] [IsSepClosed k] {Λ : Type (u + 1)} [CommRing Λ]
  {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [HasCompactification a]
  {G : DerivedCategoryModule Λ (Spec (.of k)) ⥤ DerivedCategoryModule Λ X}
  (adj : R(a)_![ModuleCat.{u + 1} Λ] ⊣ G) {d : ℕ} {T : DerivedCategoryModule Λ X}
  (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _)) (K : DerivedCategoryModule Λ X)

/-- The second variable `K^∨ ⊗ᴸ T` of the derived Poincaré pairing (`K^∨(d)` for
`T = Λ_X(d)`). -/
noncomputable abbrev poincareSecondVariable : DerivedCategoryModule Λ X :=
  ((derivedTensor _ X).obj ((DerivedCategory.coefficientDual _ X).obj (op K))).obj T

/-- Blueprint `theorem-poincare-duality--6`: the adjoint

`β_K^♯ : RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨ = RHom(RΓ_c(X, K), Λ)`

of the derived Poincaré pairing `β_K` (`AlgebraicGeometry.Etale.poincarePairing`), read in
`D(Spec k_ét, Λ)`. -/
noncomputable def poincareAdjoint :=
  pairingAdjoint (A := ModuleCat.{u + 1} Λ) (poincarePairing adj γ K)

variable {K}

/-- Blueprint `theorem-poincare-duality--6`: Adic reconstruction and
scalar extension (perfectness over every coefficient ring).

For `K` perfect over `Λ_X`, the adjoint `β_K^♯` of the derived Poincaré pairing is an
isomorphism, over every coefficient ring `Λ`, in particular over `𝒪_E`; its inverse is the
duality isomorphism `RΓ_c(X, K)^∨ ≅ RΓ(X, K^∨(d))[2d]`
(`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable`). -/
theorem isIso_poincareAdjoint (hKd : IsDualizable K) : IsIso (poincareAdjoint a adj γ K) :=
  (isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable a adj γ hKd).isIso_pairingAdjoint

include adj γ in
/-- Blueprint `theorem-poincare-duality--6`: Adic reconstruction and
scalar extension (the duality isomorphism in `D(Λ)`).

For `K` perfect over `Λ_X`, there is an isomorphism of complexes of `Λ`-modules
`RΓ_c(X, K)^∨ ≅ RΓ(X, K^∨(d))[2d]`, obtained from the inverse of `β_K^♯` by evaluation at the
point, which commutes with duals. -/
theorem nonempty_iso_ihom_compactlySupportedGlobalSections (hKd : IsDualizable K) :
    Nonempty ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K)).obj
        (𝟙_ _) ≅
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        (poincareSecondVariable (T := T) K))⟦(2 * d : ℤ)⟧) := by
  have := isIso_poincareAdjoint a adj γ hKd
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  obtain ⟨e⟩ := nonempty_iso_rightDerivedGlobalSections_coefficientDual_of_isEquivalence _ _
    ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)
  exact ⟨e.symm ≪≫ RΓ.mapIso (coefficientDualIsoIhom _) ≪≫
    RΓ.mapIso (asIso (poincareAdjoint a adj γ K)).symm ≪≫
    (RΓ.commShiftIso (2 * d : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 * d : ℤ)).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ a).app _)⟩

variable {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)

/-- Blueprint `theorem-poincare-duality--6`: Adic reconstruction and
scalar extension (the finite-level dualities are the reductions of `β_K^♯`).

Let `ϖ` be a nonzerodivisor of `Λ` (a uniformizer of `𝒪_E`) and `A_n = Λ/(ϖ)ⁿ`, read through
`K ↦ K_n = K ⊗ᴸ (A_n)_X`. For `K` perfect over `Λ_X` and every `n`, the reduction
`β_K^♯ ⊗ᴸ A_n` is an isomorphism. By
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_poincareAdjoint_source` and
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_poincareAdjoint_target` its source is
`RΓ(X, K^∨(d)_n)[2d]` and its target `RHom(RΓ_c(X, K), A_n)`, the `A_n`-dual of
`RΓ_c(X, K_n) ≅ RΓ_c(X, K) ⊗ᴸ A_n`: the reduction is the finite-level duality, and these form
a morphism of towers (`AlgebraicGeometry.Etale.poincareAdjoint_reduction_naturality`). -/
theorem isIso_reductionModIdeal_map_poincareAdjoint (hKd : IsDualizable K) (J : Ideal Λ) :
    IsIso ((reductionModIdeal Λ (Spec (.of k)) J).map (poincareAdjoint a adj γ K)) := by
  have := isIso_poincareAdjoint a adj γ hKd
  infer_instance

omit [IsSepClosed k] in
/-- Blueprint `theorem-poincare-duality--6`: the reductions of `β_K^♯`
along the finite stages form a morphism of towers: for `J ≤ J'` (for example
`(ϖ)ᵐ ≤ (ϖ)ⁿ` for `n ≤ m`) they commute with the transitions `Λ/J ⟶ Λ/J'`. -/
theorem poincareAdjoint_reduction_naturality {J J' : Ideal Λ} (h : J ≤ J') :
    (reductionModIdeal Λ (Spec (.of k)) J).map (poincareAdjoint a adj γ K) ≫
        (reductionModIdealMap Λ (Spec (.of k)) h).app _ =
      (reductionModIdealMap Λ (Spec (.of k)) h).app _ ≫
        (reductionModIdeal Λ (Spec (.of k)) J').map (poincareAdjoint a adj γ K) :=
  (reductionModIdealMap Λ (Spec (.of k)) h).naturality (poincareAdjoint a adj γ K)

include hϖ in
omit [IsSepClosed k] [HasCompactification a] in
/-- Blueprint `theorem-poincare-duality--6`: the source of the reduction
of `β_K^♯` is `RΓ(X, K^∨(d)_n)[2d]`. -/
theorem nonempty_iso_reductionModIdeal_poincareAdjoint_source (n : ℕ) :
    Nonempty ((reductionModIdeal Λ (Spec (.of k)) (Ideal.span {ϖ} ^ n)).obj
        (((R((a)_*[ModuleCat.{u + 1} Λ])).obj (poincareSecondVariable (T := T) K))⟦(2 * d : ℤ)⟧) ≅
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj
        (poincareSecondVariable (T := T) K)))⟦(2 * d : ℤ)⟧) := by
  obtain ⟨e⟩ := nonempty_iso_map_reductionModIdeal
    (R((a)_*[ModuleCat.{u + 1} Λ]) ⋙ shiftFunctor _ (2 * d : ℤ)) hϖ n
    (poincareSecondVariable (T := T) K)
  exact ⟨e.symm⟩

include hϖ in
omit [IsSepClosed k] in
/-- Blueprint `theorem-poincare-duality--6`: the target of the reduction
of `β_K^♯` is `RHom(RΓ_c(X, K), A_n)`, and `RΓ_c(X, K_n) ≅ RΓ_c(X, K) ⊗ᴸ A_n`. -/
theorem nonempty_iso_reductionModIdeal_poincareAdjoint_target (n : ℕ) :
    Nonempty ((reductionModIdeal Λ (Spec (.of k)) (Ideal.span {ϖ} ^ n)).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) _).obj (op ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))).obj
          (𝟙_ _)) ≅
      ((derivedHom (ModuleCat.{u + 1} Λ) _).obj (op ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))).obj
        ((reductionModIdeal Λ (Spec (.of k)) (Ideal.span {ϖ} ^ n)).obj (𝟙_ _))) ∧
      Nonempty ((R(a)_![ModuleCat.{u + 1} Λ]).obj
          ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) ≅
        (reductionModIdeal Λ (Spec (.of k)) (Ideal.span {ϖ} ^ n)).obj
          ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)) :=
  ⟨nonempty_iso_reductionModIdeal_derivedHom_obj hϖ n _ _,
    nonempty_iso_map_reductionModIdeal (R(a)_![ModuleCat.{u + 1} Λ]) hϖ n K⟩

end Adjoint

section IntegralPairing

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The reduction `K ⊗ᴸ (Λ/ϖⁿ)_X` of a dualizable (that is, perfect over `Λ_X`) object `K` of
`D(X_ét, Λ)` is dualizable, for `ϖ` a nonzerodivisor of `Λ`: `(Λ/ϖⁿ)_X` is dualizable
(`AlgebraicGeometry.Etale.isDualizable_constantSingle_quotient_span_pow`). -/
theorem isDualizable_reductionModIdeal {X : Scheme.{u}} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (n : ℕ) {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    IsDualizable ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) := by
  rw [reductionModIdeal, Functor.flip_obj_obj]
  exact DerivedCategory.isDualizable_derivedTensor hK
    (isDualizable_constantSingle_quotient_span_pow hϖ n X)

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  [HasCompactification a]
  {G : DerivedCategoryModule Λ (Spec (.of k)) ⥤ DerivedCategoryModule Λ X}
  (adj : R(a)_![ModuleCat.{u + 1} Λ] ⊣ G) {d : ℕ}

/-- Blueprint `theorem-poincare-duality--6`: Adic reconstruction and scalar
extension (perfectness of the integral pairing and of its finite levels).

Let `k` be separably closed, `Λ = 𝒪_E` (any commutative ring), `ϖ` a nonzerodivisor of `Λ`,
`a : X ⟶ Spec k` admitting a compactification with a right adjoint `Ra^!` of `Ra_!`, and
`γ : V[2d] ≅ Ra^! Λ` a purity isomorphism (`V = Λ_X(d)`). For `K` perfect over `Λ_X`, the
`𝒪_E`-valued derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ_{𝒪_E} RΓ(X, K^∨(d))[2d] ⟶ 𝒪_E`

is perfect, and so are the pairings `β_{K_n}` of the finite levels `K_n = K ⊗ᴸ (𝒪_E/ϖⁿ)_X`. -/
theorem isPerfectPairing_poincarePairing_integral
    {V : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : V⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) :
    IsPerfectPairing (poincarePairing adj γ K) ∧
      ∀ n : ℕ, IsPerfectPairing
        (poincarePairing adj γ ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K)) :=
  ⟨isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable a adj γ hK, fun n ↦
    isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable a adj γ
      (isDualizable_reductionModIdeal hϖ n hK)⟩

end IntegralPairing

section Unit

variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ] {ϖ : Λ}
  {I : Ideal Λ} [IsAdicComplete I Λ] {k : Type u} [Field k] [IsSepClosed k]

/-- Over a separably closed field `k`, the unit `Λ_s` of `D(Spec(k)_ét, Λ)` is derived complete
for an ideal `I = (ϖ)` of a principal ideal domain `Λ` which is `I`-adically complete. Evaluation
at the point is a `Λ`-linear equivalence `D(Spec(k)_ét, Λ) ≌ D(Λ)` carrying `Λ_s` to `Λ[0]`, and
`Λ[0]` receives no nonzero morphism from an object on which `ϖ` acts invertibly
(`DerivedCategory.eq_zero_of_isIso_smul_of_singleFunctor`). -/
theorem derivedComplete_unit_of_isSepClosed (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (hI : I = Ideal.span {ϖ}) :
    _root_.DerivedCategory.derivedComplete (Spec (.of k)).smallEtaleTopology I
      (𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) := by
  subst hI
  rw [_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ rfl]
  intro Z f (hZ : IsIso (ϖ • 𝟙 Z))
  let Γ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  have : Γ.Linear Λ := inferInstanceAs
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.Linear Λ)
  have hZ' : IsIso (ϖ • 𝟙 (Γ.obj Z)) := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance
  have h := _root_.DerivedCategory.eq_zero_of_isIso_smul_of_singleFunctor hZ'
    (Γ.map f ≫ (rightDerivedGlobalSectionsUnitIso Λ k).hom)
  rw [Preadditive.IsIso.comp_right_eq_zero] at h
  exact Γ.map_injective (by rw [h, Functor.map_zero])

end Unit

section Integral

variable (l : ℕ) [Fact l.Prime] (E L : Type w) [Field E] [Field L]
  [Algebra E (PadicAlgCl l)] [Algebra L (PadicAlgCl l)] [Algebra E L]
  [IsScalarTower E L (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] L] [Small.{u + 1} E] [Small.{u + 1} L]
  {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  [HasCompactification a]
  {G : DerivedCategoryModule (Shrink.{u + 1} (PadicAlgCl.integers l E)) (Spec (.of k)) ⥤
    DerivedCategoryModule (Shrink.{u + 1} (PadicAlgCl.integers l E)) X}
  (adj : R(a)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))] ⊣ G)
  {d : ℕ} {T : DerivedCategoryModule (Shrink.{u + 1} (PadicAlgCl.integers l E)) X}
  (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _))
  {K : DerivedCategoryModule (Shrink.{u + 1} (PadicAlgCl.integers l E)) X}

/-- Blueprint `theorem-poincare-duality--6`: Adic reconstruction and
scalar extension (the integral stage and the scalar extension).

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, `𝒪_E` its ring of integers, `L ⊇ E` a
further finite extension, and `K ∈ D(X_ét, 𝒪_E)` perfect over `𝒪_{E,X}`. The constant complex `𝒪_E`
of the point is derived complete (`AlgebraicGeometry.Etale.derivedComplete_unit_of_isSepClosed`),
hence so is `RΓ_c(X, K)^∨`, and the adjoint
`β_K^♯ : RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨` of the `𝒪_E`-valued derived Poincaré pairing is an
isomorphism between derived complete objects: it is an isomorphism `e` of the adic category
`D_comp(Spec k, 𝒪_E)`, so `β_K^♯` is the realization of its tower of reductions, the
finite-level dualities (`AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_poincareAdjoint`).
Its inverse is the duality isomorphism `RΓ_c(X, K)^∨ ≅ RΓ(X, K^∨(d))[2d]` over `𝒪_E`.
Localization `𝒪_E ⟶ E` (`DerivedCategoryDerivedCompleteRational.fromIntegral`) and the finite
coefficient-field extension `E ⊆ L`, both integrally
(`AlgebraicGeometry.Etale.derivedCompleteIntegralScalarExtension`) and rationally
(`AlgebraicGeometry.Etale.derivedCompleteRationalScalarExtension`), carry `e` to
isomorphisms: the duality isomorphism over `E` and over `L`. -/
theorem adicReconstruction_scalarExtension (hKd : IsDualizable K) :
    ∃ (P Q : DerivedCategoryDerivedCompleteIntegral (Spec (.of k)).smallEtaleTopology l E)
      (e : P ≅ Q),
      Arrow.mk ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).map e.hom) =
        Arrow.mk (poincareAdjoint a adj γ K) ∧
      IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map e.hom) ∧
      IsIso ((derivedCompleteIntegralScalarExtension l E L).map e.hom) ∧
      IsIso ((derivedCompleteRationalScalarExtension l E L).map
        ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map e.hom)) := by
  obtain ⟨ϖ, hϖ, hI⟩ :=
    PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  have : IsPrincipalIdealRing (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
    IsPrincipalIdealRing.of_surjective (PadicAlgCl.shrinkRingEquiv l E).toRingHom
      (PadicAlgCl.shrinkRingEquiv l E).surjective
  have := isIso_poincareAdjoint a adj γ hKd
  let f := poincareAdjoint a adj γ K
  have ht : DerivedCategory.derivedCompleteIntegral _ l E (Arrow.mk f).right :=
    derivedComplete_derivedHom _ hϖ hI (derivedComplete_unit_of_isSepClosed hϖ hI)
  have hs : DerivedCategory.derivedCompleteIntegral _ l E (Arrow.mk f).left := by
    change _root_.DerivedCategory.derivedComplete _ (PadicAlgCl.maximalIdealShrink l E) _ at ht ⊢
    rw [_root_.DerivedCategory.derivedComplete_eq_rightOrthogonal hϖ hI] at ht ⊢
    exact ObjectProperty.prop_of_iso _ (asIso f).symm ht
  let P : DerivedCategoryDerivedCompleteIntegral (Spec (.of k)).smallEtaleTopology l E := ⟨_, hs⟩
  let Q : DerivedCategoryDerivedCompleteIntegral (Spec (.of k)).smallEtaleTopology l E := ⟨_, ht⟩
  let e : P ≅ Q := (ObjectProperty.fullyFaithfulι _).preimageIso (asIso f)
  refine ⟨P, Q, e, ?_, inferInstance, inferInstance, inferInstance⟩
  exact congrArg Arrow.mk
    ((ObjectProperty.fullyFaithfulι (DerivedCategory.derivedCompleteIntegral _ l E)).map_preimage
      (X := P) (Y := Q) f)

end Integral

end Etale

end AlgebraicGeometry
