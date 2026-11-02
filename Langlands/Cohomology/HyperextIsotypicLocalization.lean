import Langlands.Cohomology.HyperextHomLocalization
import Langlands.Cohomology.HyperextIsotypicDegenerationBaseChange

/-!
# Isotypic parts and multiplicity spaces of hyperext groups and localization

Let `S` be a localization of a commutative ring `R` at a submonoid `M` (for example
`R = 𝒪`, the ring of integers of a finite extension of `ℚ_ℓ`, and `S` its fraction field), and
let `τ` be a representation of a group `Γ` over `R` that is finitely generated over the group
algebra `R[Γ]`. For a representation `ρ` on a module without `M`-torsion, this module proves that
the base-change maps on multiplicity spaces, `S ⊗[R] Hom_Γ(τ, ρ) → Hom_Γ(S ⊗[R] τ, S ⊗[R] ρ)`,
and on isotypic parts, from `S ⊗[R]` the `τ`-isotypic part of `ρ` to the `S ⊗[R] τ`-isotypic part
of `S ⊗[R] ρ`, are bijective. Combined with `HyperextIsotypicDegenerationBaseChange` and
`HyperextHomLocalization`, this gives the corresponding statements for hyperext groups.

* `intertwiningMapCompLinearMap_bijective`, `isotypicIntertwiningMap_bijective`: composition
  with, and restriction to isotypic parts of, a bijective intertwining map are bijective.
* `multiplicityBaseChangeMap_injective`, `multiplicityBaseChangeMap_surjective`,
  `multiplicityBaseChangeMap_bijective` and the linear equivalence `multiplicityBaseChangeEquiv`:
  multiplicity spaces and localization.
* `isotypicBaseChangeMap_surjective_of_finite`, `isotypicBaseChangeMap_bijective_of_finite` and
  the linear equivalence `isotypicBaseChangeEquivOfFinite`: isotypic parts and localization.
* `cohomologyHomMultiplicityBaseChangeMap_bijective_of_isSMulRegular`,
  `cohomologyHomIsotypicBaseChangeMap_bijective_of_isSMulRegular` and, under the degeneration
  hypotheses, `abutmentMultiplicityBaseChangeMap_bijective_of_isSMulRegular`,
  `abutmentIsotypicBaseChangeMap_bijective_of_isSMulRegular` with the equivalences
  `abutmentMultiplicityLocalizationEquivOfIsSMulRegular` and
  `abutmentIsotypicLocalizationEquivOfIsSMulRegular`: for an exact semilinear functor along a
  localization.
* `cohomologyHomIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular`,
  `abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular` and
  `abutmentIsotypicProdLocalizationEquivOfIsSMulRegular`: the same for the `τ`-isotypic parts for
  `Γ` of actions of `Γ × Δ`, as representations of `Δ`.
* The versions `rep…_of_finite`, `repAbutmentMultiplicityLocalizationEquiv`,
  `repAbutmentIsotypicLocalizationEquiv`, `repAbutmentIsotypicProdLocalizationEquiv` for
  extension of scalars of representations, and
  `smooth…_of_finite`, `smoothAbutmentMultiplicityLocalizationEquiv`,
  `smoothAbutmentIsotypicLocalizationEquiv`, `smoothAbutmentIsotypicProdLocalizationEquiv` for
  smooth representations, where the hypotheses on
  `Hom(H^{-n} K, W)` follow from finite generation of `H^{-n} K` over `R[G]` and the absence of
  `M`-torsion in `W`.

Finite generation of `τ` and of `H^{-n} K`, the absence of `M`-torsion and the degeneration
hypotheses remain hypotheses; this module does not verify them for any particular complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

namespace HyperextScalarExtension

open HyperextAbutment

universe w uR uS uG uC vC uD vD s s' t t' uΓ uΔ

section Bijective

variable {R : Type uR} [CommRing R] {Γ : Type uΓ} [Group Γ] {U V W : Type*} [AddCommGroup U]
  [Module R U] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Composition with a bijective intertwining map is bijective. -/
lemma intertwiningMapCompLinearMap_bijective (τ : Representation R Γ U)
    {ρ : Representation R Γ V} {σ : Representation R Γ W} (φ : ρ.IntertwiningMap σ)
    (hφ : Function.Bijective φ) :
    Function.Bijective (intertwiningMapCompLinearMap τ φ) := by
  refine ⟨fun f g h => Representation.IntertwiningMap.ext (LinearMap.ext fun u => hφ.1 ?_),
    fun g => ?_⟩
  · exact congrArg (fun k : τ.IntertwiningMap σ => k u) h
  · let e := φ.ofBijective hφ
    refine ⟨e.symm.toIntertwiningMap.comp g,
      Representation.IntertwiningMap.ext (LinearMap.ext fun u => ?_)⟩
    exact e.apply_symm_apply (g u)

/-- The restriction to `τ`-isotypic parts of a bijective intertwining map is bijective. -/
lemma isotypicIntertwiningMap_bijective (τ : Representation R Γ U) {ρ : Representation R Γ V}
    {σ : Representation R Γ W} (φ : ρ.IntertwiningMap σ) (hφ : Function.Bijective φ) :
    Function.Bijective (isotypicIntertwiningMap τ φ) := by
  refine ⟨fun x y h => Subtype.ext (hφ.1 (congrArg Subtype.val h)), fun y => ?_⟩
  let e := φ.ofBijective hφ
  refine ⟨⟨e.symm y, intertwiningMap_apply_mem_isotypicPart τ e.symm.toIntertwiningMap y.2⟩,
    Subtype.ext ?_⟩
  exact e.apply_symm_apply (y : W)

end Bijective

section Algebra

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]
  {Γ : Type uΓ} [Group Γ] {U V : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V]
  [Module R V]

include M

/-- **Multiplicity spaces and localization, injectivity.** If `S` is a localization of `R` at `M`
and `V` has no `M`-torsion, then
`multiplicityBaseChangeMap S τ ρ : S ⊗[R] Hom_Γ(τ, ρ) → Hom_Γ(S ⊗[R] τ, S ⊗[R] ρ)` is
injective. -/
theorem multiplicityBaseChangeMap_injective {τ : Representation R Γ U}
    {ρ : Representation R Γ V} (hV : ∀ m : M, IsSMulRegular V (m : R)) :
    Function.Injective (multiplicityBaseChangeMap S τ ρ) := by
  have := isLocalizedModule_mk_one S M (τ.IntertwiningMap ρ)
  have hinj := mk_one_injective_of_isSMulRegular S M hV
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  obtain ⟨⟨φ, m⟩, hm⟩ := IsLocalizedModule.surj M (TensorProduct.mk R S (τ.IntertwiningMap ρ) 1) t
  replace hm : algebraMap R S (m : R) • t = (1 : S) ⊗ₜ[R] φ := by
    rw [algebraMap_smul, ← Submonoid.smul_def]; exact hm
  have hφ : φ = 0 := by
    have h1 := congrArg (multiplicityBaseChangeMap S τ ρ) hm
    rw [map_smul, ht, smul_zero, multiplicityBaseChangeMap_tmul, one_smul] at h1
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun u => hinj ?_)
    have h2 := congrArg (fun f => f ((1 : S) ⊗ₜ[R] u)) h1
    exact h2.symm.trans (TensorProduct.tmul_zero _ _).symm
  rw [hφ, TensorProduct.tmul_zero] at hm
  exact (IsLocalization.map_units S m).smul_eq_zero.1 hm

/-- **Multiplicity spaces and localization, surjectivity.** If `S` is a localization of `R` at
`M`, `τ` is finitely generated over the group algebra `R[Γ]` and `V` has no `M`-torsion, then
`multiplicityBaseChangeMap S τ ρ` is surjective. -/
theorem multiplicityBaseChangeMap_surjective {τ : Representation R Γ U}
    {ρ : Representation R Γ V} [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hV : ∀ m : M, IsSMulRegular V (m : R)) :
    Function.Surjective (multiplicityBaseChangeMap S τ ρ) := by
  classical
  have := isLocalizedModule_mk_one S M V
  have hinj := mk_one_injective_of_isSMulRegular S M hV
  intro g
  obtain ⟨t, ht⟩ := exists_finset_eq_top_of_finite_asModule τ
  let g' : S ⊗[R] U →ₗ[S] S ⊗[R] V := g.toLinearMap
  have hg' : ∀ z, g' z = g z := fun z => rfl
  obtain ⟨b, hb⟩ := IsLocalizedModule.exist_integer_multiples M (TensorProduct.mk R S V 1) t
    (fun u => g' ((1 : S) ⊗ₜ[R] u))
  let L : U →ₗ[R] S ⊗[R] V :=
    (b : R) • ((g'.restrictScalars R) ∘ₗ TensorProduct.mk R S U 1)
  have hL : ∀ u, L u = (b : R) • g' ((1 : S) ⊗ₜ[R] u) := fun u => rfl
  have hLρ : ∀ (γ : Γ) (u : U), L (τ γ u) = baseChangeRepresentation S ρ γ (L u) := by
    intro γ u
    rw [hL, hL, LinearMap.map_smul_of_tower]
    congr 1
    rw [hg', hg', ← baseChangeRepresentation_apply_tmul]
    exact Representation.IntertwiningMap.isIntertwining _ _ g γ ((1 : S) ⊗ₜ[R] u)
  have hrange : ∀ u, L u ∈ LinearMap.range (TensorProduct.mk R S V 1) := by
    have hN := ht ((LinearMap.range (TensorProduct.mk R S V 1)).comap L) (fun γ v hv => by
      obtain ⟨y, hy⟩ := hv
      refine ⟨ρ γ y, ?_⟩
      change (1 : S) ⊗ₜ[R] ρ γ y = L (τ γ v)
      rw [hLρ, ← hy]
      rfl) (fun u hu => by
        change L u ∈ LinearMap.range (TensorProduct.mk R S V 1)
        rw [hL]
        exact hb u hu)
    intro u
    have hu : u ∈ (LinearMap.range (TensorProduct.mk R S V 1)).comap L := hN ▸ Submodule.mem_top
    exact hu
  let e := LinearEquiv.ofInjective (TensorProduct.mk R S V 1) hinj
  let f : U →ₗ[R] V := e.symm.toLinearMap ∘ₗ L.codRestrict _ hrange
  have hf : ∀ u, (1 : S) ⊗ₜ[R] f u = L u := fun u =>
    congrArg Subtype.val (e.apply_symm_apply ⟨L u, hrange u⟩)
  have hfρ : ∀ (γ : Γ) (u : U), f (τ γ u) = ρ γ (f u) := fun γ u => hinj (by
    change (1 : S) ⊗ₜ[R] f (τ γ u) = (1 : S) ⊗ₜ[R] ρ γ (f u)
    rw [hf, hLρ, ← hf]
    rfl)
  let φ : τ.IntertwiningMap ρ := ⟨f, fun γ => LinearMap.ext fun u => hfρ γ u⟩
  have hφ : ∀ u, φ u = f u := fun u => rfl
  let a : S := IsLocalization.mk' S (1 : R) b
  have ha : a * algebraMap R S (b : R) = 1 := by
    rw [IsLocalization.mk'_spec, map_one]
  refine ⟨a ⊗ₜ[R] φ, ?_⟩
  rw [multiplicityBaseChangeMap_tmul]
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_)
  induction z using TensorProduct.inductionOn with
  | tmul s u =>
    change a • (s ⊗ₜ[R] φ u) = g' (s ⊗ₜ[R] u)
    calc a • (s ⊗ₜ[R] φ u) = (a * s) • ((1 : S) ⊗ₜ[R] f u) := by
          rw [hφ, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
            smul_eq_mul, mul_one]
      _ = (a * s) • ((b : R) • g' ((1 : S) ⊗ₜ[R] u)) := by rw [hf, hL]
      _ = s • ((a * algebraMap R S (b : R)) • g' ((1 : S) ⊗ₜ[R] u)) := by
          rw [← algebraMap_smul S (b : R), smul_smul, smul_smul, mul_comm a s, mul_assoc]
      _ = g' (s ⊗ₜ[R] u) := by
          rw [ha, one_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ x y).symm)

/-- **Multiplicity spaces and localization.** If `S` is a localization of `R` at `M`, `τ` is
finitely generated over `R[Γ]` and `V` has no `M`-torsion, then `multiplicityBaseChangeMap S τ ρ`
is bijective. -/
theorem multiplicityBaseChangeMap_bijective {τ : Representation R Γ U}
    {ρ : Representation R Γ V} [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hV : ∀ m : M, IsSMulRegular V (m : R)) :
    Function.Bijective (multiplicityBaseChangeMap S τ ρ) :=
  ⟨multiplicityBaseChangeMap_injective S M hV, multiplicityBaseChangeMap_surjective S M hV⟩

/-- Under the hypotheses of `multiplicityBaseChangeMap_bijective`, the `S`-linear equivalence
`S ⊗[R] Hom_Γ(τ, ρ) ≃ Hom_Γ(S ⊗[R] τ, S ⊗[R] ρ)` given by `multiplicityBaseChangeMap`. -/
def multiplicityBaseChangeEquiv {τ : Representation R Γ U} {ρ : Representation R Γ V}
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule] (hV : ∀ m : M, IsSMulRegular V (m : R)) :
    S ⊗[R] τ.IntertwiningMap ρ ≃ₗ[S]
      (baseChangeRepresentation S τ).IntertwiningMap (baseChangeRepresentation S ρ) :=
  LinearEquiv.ofBijective _ (multiplicityBaseChangeMap_bijective S M hV)

/-- The underlying map of `multiplicityBaseChangeEquiv` is `multiplicityBaseChangeMap`. -/
@[simp]
lemma multiplicityBaseChangeEquiv_apply {τ : Representation R Γ U} {ρ : Representation R Γ V}
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule] (hV : ∀ m : M, IsSMulRegular V (m : R))
    (x : S ⊗[R] τ.IntertwiningMap ρ) :
    multiplicityBaseChangeEquiv S M hV x = multiplicityBaseChangeMap S τ ρ x :=
  rfl

/-- **Isotypic parts and localization, surjectivity.** If `S` is a localization of `R` at `M`,
`τ` is finitely generated over `R[Γ]` and `V` has no `M`-torsion, then
`isotypicBaseChangeMap S τ ρ` onto the `S ⊗[R] τ`-isotypic part of `S ⊗[R] ρ` is surjective. -/
theorem isotypicBaseChangeMap_surjective_of_finite (τ : Representation R Γ U)
    {ρ : Representation R Γ V} [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hV : ∀ m : M, IsSMulRegular V (m : R)) :
    Function.Surjective (isotypicBaseChangeMap S τ ρ) := by
  let N : Submodule S (S ⊗[R] V) := LinearMap.range ((isotypicPart τ ρ).subtype.baseChange S)
  have hN : isotypicPart (baseChangeRepresentation S τ) (baseChangeRepresentation S ρ) ≤ N := by
    refine (isotypicPart_le_iff _ _).2 fun g z => ?_
    obtain ⟨t, rfl⟩ := multiplicityBaseChangeMap_surjective S M hV g
    induction t using TensorProduct.inductionOn with
    | tmul s f =>
      induction z using TensorProduct.inductionOn with
      | tmul s' u =>
        refine ⟨(s * s') ⊗ₜ[R] ⟨f u, apply_mem_isotypicPart f u⟩, ?_⟩
        change (s * s') ⊗ₜ[R] f u = s • (s' ⊗ₜ[R] f u)
        rw [TensorProduct.smul_tmul', smul_eq_mul]
      | add x y hx hy => rw [map_add]; exact N.add_mem hx hy
    | add x y hx hy => rw [map_add]; exact N.add_mem hx hy
  intro y
  obtain ⟨x, hx⟩ := hN y.2
  exact ⟨x, Subtype.ext ((coe_isotypicBaseChangeMap S τ ρ x).trans hx)⟩

/-- **Isotypic parts and localization.** If `S` is a localization of `R` at `M`, `τ` is finitely
generated over `R[Γ]` and `V` has no `M`-torsion, then `isotypicBaseChangeMap S τ ρ` is
bijective. -/
theorem isotypicBaseChangeMap_bijective_of_finite (τ : Representation R Γ U)
    {ρ : Representation R Γ V} [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hV : ∀ m : M, IsSMulRegular V (m : R)) :
    Function.Bijective (isotypicBaseChangeMap S τ ρ) :=
  have : Module.Flat R S := IsLocalization.flat S M
  ⟨isotypicBaseChangeMap_injective S τ ρ, isotypicBaseChangeMap_surjective_of_finite S M τ hV⟩

/-- Under the hypotheses of `isotypicBaseChangeMap_bijective_of_finite`, the `S`-linear
equivalence from `S ⊗[R]` the `τ`-isotypic part of `ρ` to the `S ⊗[R] τ`-isotypic part of
`S ⊗[R] ρ` given by `isotypicBaseChangeMap`. -/
def isotypicBaseChangeEquivOfFinite (τ : Representation R Γ U) {ρ : Representation R Γ V}
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule] (hV : ∀ m : M, IsSMulRegular V (m : R)) :
    S ⊗[R] isotypicPart τ ρ ≃ₗ[S]
      isotypicPart (baseChangeRepresentation S τ) (baseChangeRepresentation S ρ) :=
  LinearEquiv.ofBijective _ (isotypicBaseChangeMap_bijective_of_finite S M τ hV)

/-- The underlying map of `isotypicBaseChangeEquivOfFinite` is `isotypicBaseChangeMap`. -/
@[simp]
lemma isotypicBaseChangeEquivOfFinite_apply (τ : Representation R Γ U)
    {ρ : Representation R Γ V} [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hV : ∀ m : M, IsSMulRegular V (m : R)) (x : S ⊗[R] isotypicPart τ ρ) :
    isotypicBaseChangeEquivOfFinite S M τ hV x = isotypicBaseChangeMap S τ ρ x :=
  rfl

end Algebra

section Derived

variable {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear R C] [HasDerivedCategory.{s} C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [Linear S D] [HasDerivedCategory.{s'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable (hF : IsSemilinear R S F)
variable {Γ : Type uΓ} [Group Γ] {U : Type*} [AddCommGroup U] [Module R U]

include M

open DerivedCategory

/-- If `S` is a localization of `R` at `M`, `τ` is finitely generated over `R[Γ]`,
`Hom(H^{-n} K, W)` has no `M`-torsion (the hypothesis `hreg`) and `cohomologyHomBaseChangeMap` is
bijective (the hypothesis `h`), then `cohomologyHomMultiplicityBaseChangeMap` is bijective. -/
theorem cohomologyHomMultiplicityBaseChangeMap_bijective_of_isSMulRegular
    {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ)
    (τ : Representation R Γ U) [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    Function.Bijective (cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ) :=
  (intertwiningMapCompLinearMap_bijective _
    (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n) h).comp
    (multiplicityBaseChangeMap_bijective S M (ρ := cohomologyHomRepresentation R ρ σ n) hreg)

/-- If `S` is a localization of `R` at `M`, `τ` is finitely generated over `R[Γ]`,
`Hom(H^{-n} K, W)` has no `M`-torsion (the hypothesis `hreg`) and `cohomologyHomBaseChangeMap` is
bijective (the hypothesis `h`), then `cohomologyHomIsotypicBaseChangeMap` is bijective. -/
theorem cohomologyHomIsotypicBaseChangeMap_bijective_of_isSMulRegular
    {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ)
    (τ : Representation R Γ U) [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    Function.Bijective (cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ) :=
  (isotypicIntertwiningMap_bijective _
    (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n) h).comp
    (isotypicBaseChangeMap_bijective_of_finite S M τ
      (ρ := cohomologyHomRepresentation R ρ σ n) hreg)

variable {Δ : Type uΔ} [Group Δ]

/-- For actions of `Γ × Δ` on `K` and `W`: if `S` is a localization of `R` at `M`, `τ` is
finitely generated over `R[Γ]`, `Hom(H^{-n} K, W)` has no `M`-torsion (the hypothesis `hreg`) and
`cohomologyHomBaseChangeMap` is bijective (the hypothesis `h`), then
`cohomologyHomIsotypicProdBaseChangeIntertwiningMap` is bijective. -/
theorem cohomologyHomIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular
    {K : DerivedCategory C} {W : C} (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (n : ℤ)
    (τ : Representation R Γ U) [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    Function.Bijective (cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ) :=
  (isotypicIntertwiningMap_bijective _
    (intertwiningMapComp (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n)
      (MonoidHom.inl Γ Δ)) h).comp
    (isotypicBaseChangeMap_bijective_of_finite S M τ
      (ρ := (cohomologyHomRepresentation R ρ σ n).comp (MonoidHom.inl Γ Δ)) hreg)

variable [HasExt.{t} C] [HasExt.{t'} D]

/-- Under the degeneration hypotheses and the hypotheses of
`cohomologyHomMultiplicityBaseChangeMap_bijective_of_isSMulRegular`,
`abutmentMultiplicityBaseChangeMap` is bijective. -/
theorem abutmentMultiplicityBaseChangeMap_bijective_of_isSMulRegular
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    Function.Bijective (abutmentMultiplicityBaseChangeMap F hF ρ σ n τ) :=
  (abutmentMultiplicityBaseChangeMap_bijective_iff F hF b hK hW hW' n ρ σ τ).2
    (cohomologyHomMultiplicityBaseChangeMap_bijective_of_isSMulRegular M F hF ρ σ n τ hreg h)

/-- Under the hypotheses of `abutmentMultiplicityBaseChangeMap_bijective_of_isSMulRegular`, the
`S`-linear equivalence `S ⊗[R] Hom_Γ(τ, Hom(K, W₀⟦n⟧)) ≃ Hom_Γ(S ⊗[R] τ, Hom(F K, (F W)₀⟦n⟧))`
given by `abutmentMultiplicityBaseChangeMap`. -/
def abutmentMultiplicityLocalizationEquivOfIsSMulRegular
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    S ⊗[R] τ.IntertwiningMap (abutmentRepresentation R ρ σ n) ≃ₗ[S]
      (baseChangeRepresentation S τ).IntertwiningMap
        (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n) :=
  LinearEquiv.ofBijective _
    (abutmentMultiplicityBaseChangeMap_bijective_of_isSMulRegular M F hF b hK hW hW' n ρ σ τ
      hreg h)

/-- Under the degeneration hypotheses and the hypotheses of
`cohomologyHomIsotypicBaseChangeMap_bijective_of_isSMulRegular`,
`abutmentIsotypicBaseChangeMap` is bijective. -/
theorem abutmentIsotypicBaseChangeMap_bijective_of_isSMulRegular
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    Function.Bijective (abutmentIsotypicBaseChangeMap F hF ρ σ n τ) :=
  (abutmentIsotypicBaseChangeMap_bijective_iff F hF b hK hW hW' n ρ σ τ).2
    (cohomologyHomIsotypicBaseChangeMap_bijective_of_isSMulRegular M F hF ρ σ n τ hreg h)

/-- Under the hypotheses of `abutmentIsotypicBaseChangeMap_bijective_of_isSMulRegular`, the
Library's `abutmentIsotypicBaseChangeEquiv`: the equivalence of representations of `Γ` from the
base change of the `τ`-isotypic part of `Hom(K, W₀⟦n⟧)` to the `S ⊗[R] τ`-isotypic part of
`Hom(F K, (F W)₀⟦n⟧)` given by `abutmentIsotypicBaseChangeMap`. -/
def abutmentIsotypicLocalizationEquivOfIsSMulRegular
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    (baseChangeRepresentation S (isotypicRepresentation τ (abutmentRepresentation R ρ σ n))).Equiv
      (isotypicRepresentation (baseChangeRepresentation S τ)
        (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n)) :=
  abutmentIsotypicBaseChangeEquiv F hF b hK hW hW' n ρ σ τ
    (cohomologyHomIsotypicBaseChangeMap_bijective_of_isSMulRegular M F hF ρ σ n τ hreg h)

/-- For actions of `Γ × Δ` on `K` and `W`: under the degeneration hypotheses and the hypotheses
of `cohomologyHomIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular`,
`abutmentIsotypicProdBaseChangeIntertwiningMap` is bijective. -/
theorem abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    Function.Bijective (abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ) :=
  (abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_iff F hF b hK hW hW' n ρ σ τ).2
    (cohomologyHomIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular M F hF ρ σ n τ
      hreg h)

/-- Under the hypotheses of
`abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular`, the Library's
`abutmentIsotypicProdBaseChangeEquiv`: the equivalence of representations of `Δ` from the base
change of the `τ`-isotypic part of `Hom(K, W₀⟦n⟧)` to the `S ⊗[R] τ`-isotypic part of
`Hom(F K, (F W)₀⟦n⟧)`. -/
def abutmentIsotypicProdLocalizationEquivOfIsSMulRegular
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular ((homologyFunctor C (-n)).obj K ⟶ W) (m : R))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    (baseChangeRepresentation S
        (isotypicProdRepresentation τ (abutmentRepresentation R ρ σ n))).Equiv
      (isotypicProdRepresentation (baseChangeRepresentation S τ)
        (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n)) :=
  abutmentIsotypicProdBaseChangeEquiv F hF b hK hW hW' n ρ σ τ
    (cohomologyHomIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular M F hF ρ σ n τ
      hreg h)

end Derived

section Rep

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S] [Module.Flat R S]
  (M : Submonoid R) [IsLocalization M S]
  (G : Type uG) [Monoid G]
  [HasDerivedCategory.{s} (Rep.{w} R G)] [HasDerivedCategory.{s'} (Rep.{max uS w} S G)]
  {Γ : Type uΓ} [Group Γ] {U : Type*} [AddCommGroup U] [Module R U]

include M

open DerivedCategory

/-- **Multiplicity spaces of `Hom(H^{-n} K, W)` and localization for representations.** If `S` is
a localization of `R` at `M`, `H^{-n} K` is finitely generated over `R[G]`, `τ` is finitely
generated over `R[Γ]` and `W` has no `M`-torsion, then `cohomologyHomMultiplicityBaseChangeMap`
for extension of scalars of representations is bijective. -/
theorem repCohomologyHomMultiplicityBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (Rep.{w} R G)} {W : Rep.{w} R G} (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (n : ℤ) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule] (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective (cohomologyHomMultiplicityBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) ρ σ n τ) :=
  cohomologyHomMultiplicityBaseChangeMap_bijective_of_isSMulRegular M _ _ ρ σ n τ
    (fun m => repHom_isSMulRegular (hreg m))
    (repCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K (-n) hreg)

/-- **Isotypic parts of `Hom(H^{-n} K, W)` and localization for representations.** Under the
hypotheses of `repCohomologyHomMultiplicityBaseChangeMap_bijective_of_finite`,
`cohomologyHomIsotypicBaseChangeMap` for extension of scalars of representations is
bijective. -/
theorem repCohomologyHomIsotypicBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (Rep.{w} R G)} {W : Rep.{w} R G} (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (n : ℤ) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule] (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective (cohomologyHomIsotypicBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) ρ σ n τ) :=
  cohomologyHomIsotypicBaseChangeMap_bijective_of_isSMulRegular M _ _ ρ σ n τ
    (fun m => repHom_isSMulRegular (hreg m))
    (repCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K (-n) hreg)

variable [HasExt.{t} (Rep.{w} R G)] [HasExt.{t'} (Rep.{max uS w} S G)]

/-- **Multiplicity spaces of abutments and localization for representations.** Under the
degeneration hypotheses and the hypotheses of
`repCohomologyHomMultiplicityBaseChangeMap_bijective_of_finite`,
`abutmentMultiplicityBaseChangeMap` for extension of scalars of representations is bijective. -/
theorem repAbutmentMultiplicityBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (Rep.{w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : Rep.{w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((repExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((repExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective (abutmentMultiplicityBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) ρ σ n τ) :=
  (abutmentMultiplicityBaseChangeMap_bijective_iff _ _ b hK hW hW' n ρ σ τ).2
    (repCohomologyHomMultiplicityBaseChangeMap_bijective_of_finite R S M G ρ σ n τ hreg)

/-- **Isotypic parts of abutments and localization for representations.** Under the degeneration
hypotheses and the hypotheses of `repCohomologyHomIsotypicBaseChangeMap_bijective_of_finite`,
`abutmentIsotypicBaseChangeMap` for extension of scalars of representations is bijective. -/
theorem repAbutmentIsotypicBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (Rep.{w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : Rep.{w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((repExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((repExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective (abutmentIsotypicBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) ρ σ n τ) :=
  (abutmentIsotypicBaseChangeMap_bijective_iff _ _ b hK hW hW' n ρ σ τ).2
    (repCohomologyHomIsotypicBaseChangeMap_bijective_of_finite R S M G ρ σ n τ hreg)

/-- Under the hypotheses of `repAbutmentMultiplicityBaseChangeMap_bijective_of_finite`,
`abutmentMultiplicityBaseChangeMap` for extension of scalars of representations as an `S`-linear
equivalence. -/
def repAbutmentMultiplicityLocalizationEquiv
    {K : DerivedCategory (Rep.{w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : Rep.{w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((repExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((repExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    S ⊗[R] τ.IntertwiningMap (abutmentRepresentation R ρ σ n) ≃ₗ[S]
      (baseChangeRepresentation S τ).IntertwiningMap
        (abutmentRepresentation S
          (((repExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
          (((repExtendScalars.{w} R S G).mapAut W).comp σ) n) :=
  LinearEquiv.ofBijective _
    (repAbutmentMultiplicityBaseChangeMap_bijective_of_finite R S M G b hK hW hW' n ρ σ τ hreg)

/-- Under the hypotheses of `repAbutmentIsotypicBaseChangeMap_bijective_of_finite`, the Library's
`abutmentIsotypicBaseChangeEquiv` for extension of scalars of representations. -/
def repAbutmentIsotypicLocalizationEquiv
    {K : DerivedCategory (Rep.{w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : Rep.{w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((repExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((repExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    (baseChangeRepresentation S (isotypicRepresentation τ (abutmentRepresentation R ρ σ n))).Equiv
      (isotypicRepresentation (baseChangeRepresentation S τ)
        (abutmentRepresentation S
          (((repExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
          (((repExtendScalars.{w} R S G).mapAut W).comp σ) n)) :=
  abutmentIsotypicBaseChangeEquiv _ _ b hK hW hW' n ρ σ τ
    (repCohomologyHomIsotypicBaseChangeMap_bijective_of_finite R S M G ρ σ n τ hreg)

variable {Δ : Type uΔ} [Group Δ]

/-- **Isotypic parts for `Γ × Δ` and localization for representations.** For actions of `Γ × Δ`
on `K` and `W`, under the degeneration hypotheses, if `S` is a localization of `R` at `M`,
`H^{-n} K` is finitely generated over `R[G]`, `τ` is finitely generated over `R[Γ]` and `W` has
no `M`-torsion, then `abutmentIsotypicProdBaseChangeIntertwiningMap` for extension of scalars of
representations is bijective. -/
theorem repAbutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_finite
    {K : DerivedCategory (Rep.{w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : Rep.{w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((repExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((repExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective (abutmentIsotypicProdBaseChangeIntertwiningMap
      (repExtendScalars.{w} R S G) (repExtendScalars_isSemilinear.{w} R S G) ρ σ n τ) :=
  abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular M _ _ b hK hW hW' n ρ
    σ τ (fun m => repHom_isSMulRegular (hreg m))
    (repCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K (-n) hreg)

/-- Under the hypotheses of `repAbutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_finite`,
the Library's `abutmentIsotypicProdBaseChangeEquiv` for extension of scalars of representations:
an equivalence of representations of `Δ`. -/
def repAbutmentIsotypicProdLocalizationEquiv
    {K : DerivedCategory (Rep.{w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : Rep.{w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((repExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((repExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    (baseChangeRepresentation S
        (isotypicProdRepresentation τ (abutmentRepresentation R ρ σ n))).Equiv
      (isotypicProdRepresentation (baseChangeRepresentation S τ)
        (abutmentRepresentation S
          (((repExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
          (((repExtendScalars.{w} R S G).mapAut W).comp σ) n)) :=
  abutmentIsotypicProdLocalizationEquivOfIsSMulRegular M _ _ b hK hW hW' n ρ σ τ
    (fun m => repHom_isSMulRegular (hreg m))
    (repCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K (-n) hreg)

end Rep

section Smooth

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S] [Module.Flat R S]
  (M : Submonoid R) [IsLocalization M S]
  (G : Type uG) [Group G] [TopologicalSpace G]
  [HasDerivedCategory.{s} (SmoothRep.{uR, uG, w} R G)]
  [HasDerivedCategory.{s'} (SmoothRep.{uS, uG, max uS w} S G)]
  {Γ : Type uΓ} [Group Γ] {U : Type*} [AddCommGroup U] [Module R U]

include M

open DerivedCategory

/-- `repCohomologyHomMultiplicityBaseChangeMap_bijective_of_finite` for smooth representations:
`cohomologyHomMultiplicityBaseChangeMap` for extension of scalars of smooth representations is
bijective if `S` is a localization of `R` at `M`, the underlying representation of `H^{-n} K` is
finitely generated over `R[G]`, `τ` is finitely generated over `R[Γ]` and `W` has no
`M`-torsion. -/
theorem smoothCohomologyHomMultiplicityBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} {W : SmoothRep.{uR, uG, w} R G}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).obj.ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule] (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective (cohomologyHomMultiplicityBaseChangeMap (smoothRepExtendScalars.{w} R S G)
      (smoothRepExtendScalars_isSemilinear.{w} R S G) ρ σ n τ) :=
  cohomologyHomMultiplicityBaseChangeMap_bijective_of_isSMulRegular M _ _ ρ σ n τ
    (fun m => smoothRepHom_isSMulRegular (hreg m))
    (smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K (-n) hreg)

/-- `repCohomologyHomIsotypicBaseChangeMap_bijective_of_finite` for smooth representations: under
the hypotheses of `smoothCohomologyHomMultiplicityBaseChangeMap_bijective_of_finite`, the
Library's `smoothCohomologyHomIsotypicBaseChangeMap` is bijective. -/
theorem smoothCohomologyHomIsotypicBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} {W : SmoothRep.{uR, uG, w} R G}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).obj.ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule] (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective
      (smoothCohomologyHomIsotypicBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n τ) :=
  cohomologyHomIsotypicBaseChangeMap_bijective_of_isSMulRegular M _ _ ρ σ n τ
    (fun m => smoothRepHom_isSMulRegular (hreg m))
    (smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K (-n) hreg)

variable [HasExt.{t} (SmoothRep.{uR, uG, w} R G)] [HasExt.{t'} (SmoothRep.{uS, uG, max uS w} S G)]

/-- **Multiplicity spaces of abutments and localization for smooth representations.** Under the
degeneration hypotheses and the hypotheses of
`smoothCohomologyHomMultiplicityBaseChangeMap_bijective_of_finite`,
`abutmentMultiplicityBaseChangeMap` for extension of scalars of smooth representations is
bijective. -/
theorem smoothAbutmentMultiplicityBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).obj.ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective (abutmentMultiplicityBaseChangeMap (smoothRepExtendScalars.{w} R S G)
      (smoothRepExtendScalars_isSemilinear.{w} R S G) ρ σ n τ) :=
  (abutmentMultiplicityBaseChangeMap_bijective_iff _ _ b hK hW hW' n ρ σ τ).2
    (smoothCohomologyHomMultiplicityBaseChangeMap_bijective_of_finite R S M G ρ σ n τ hreg)

/-- **Isotypic parts of abutments and localization for smooth representations.** Under the
degeneration hypotheses and the hypotheses of
`smoothCohomologyHomIsotypicBaseChangeMap_bijective_of_finite`, the Library's
`smoothAbutmentIsotypicBaseChangeMap` is bijective. -/
theorem smoothAbutmentIsotypicBaseChangeMap_bijective_of_finite
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).obj.ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective
      (smoothAbutmentIsotypicBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n τ) :=
  (smoothAbutmentIsotypicBaseChangeMap_bijective_iff R S G b hK hW hW' n ρ σ τ).2
    (smoothCohomologyHomIsotypicBaseChangeMap_bijective_of_finite R S M G ρ σ n τ hreg)

/-- Under the hypotheses of `smoothAbutmentMultiplicityBaseChangeMap_bijective_of_finite`,
`abutmentMultiplicityBaseChangeMap` for extension of scalars of smooth representations as an
`S`-linear equivalence. -/
def smoothAbutmentMultiplicityLocalizationEquiv
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).obj.ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    S ⊗[R] τ.IntertwiningMap (abutmentRepresentation R ρ σ n) ≃ₗ[S]
      (baseChangeRepresentation S τ).IntertwiningMap
        (abutmentRepresentation S
          (((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
          (((smoothRepExtendScalars.{w} R S G).mapAut W).comp σ) n) :=
  LinearEquiv.ofBijective _
    (smoothAbutmentMultiplicityBaseChangeMap_bijective_of_finite R S M G b hK hW hW' n ρ σ τ hreg)

/-- Under the hypotheses of `smoothAbutmentIsotypicBaseChangeMap_bijective_of_finite`, the
Library's `smoothAbutmentIsotypicBaseChangeEquiv`. -/
def smoothAbutmentIsotypicLocalizationEquiv
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).obj.ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    (baseChangeRepresentation S
        (isotypicRepresentation τ (abutmentRepresentation R ρ σ n))).Equiv
      (isotypicRepresentation (baseChangeRepresentation S τ)
        (abutmentRepresentation S
          (((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
          (((smoothRepExtendScalars.{w} R S G).mapAut W).comp σ) n)) :=
  smoothAbutmentIsotypicBaseChangeEquiv R S G b hK hW hW' n ρ σ τ
    (smoothCohomologyHomIsotypicBaseChangeMap_bijective_of_finite R S M G ρ σ n τ hreg)

variable {Δ : Type uΔ} [Group Δ]

/-- **Isotypic parts for `Γ × Δ` and localization for smooth representations.** For actions of
`Γ × Δ` on `K` and `W`, under the degeneration hypotheses, if `S` is a localization of `R` at
`M`, the underlying representation of `H^{-n} K` is finitely generated over `R[G]`, `τ` is
finitely generated over `R[Γ]` and `W` has no `M`-torsion, then
`abutmentIsotypicProdBaseChangeIntertwiningMap` for extension of scalars of smooth
representations is bijective. -/
theorem smoothAbutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_finite
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K))
    {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).obj.ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective (abutmentIsotypicProdBaseChangeIntertwiningMap
      (smoothRepExtendScalars.{w} R S G) (smoothRepExtendScalars_isSemilinear.{w} R S G) ρ σ n τ) :=
  abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular M _ _ b hK hW hW' n ρ
    σ τ (fun m => smoothRepHom_isSMulRegular (hreg m))
    (smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K (-n) hreg)

/-- Under the hypotheses of
`smoothAbutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_finite`, the Library's
`abutmentIsotypicProdBaseChangeEquiv` for extension of scalars of smooth representations: an
equivalence of representations of `Δ`. -/
def smoothAbutmentIsotypicProdLocalizationEquiv
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K))
    {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U)
    [Module.Finite (MonoidAlgebra R G) ((homologyFunctor _ (-n)).obj K).obj.ρ.asModule]
    [Module.Finite (MonoidAlgebra R Γ) τ.asModule]
    (hreg : ∀ m : M, IsSMulRegular W (m : R)) :
    (baseChangeRepresentation S
        (isotypicProdRepresentation τ (abutmentRepresentation R ρ σ n))).Equiv
      (isotypicProdRepresentation (baseChangeRepresentation S τ)
        (abutmentRepresentation S
          (((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
          (((smoothRepExtendScalars.{w} R S G).mapAut W).comp σ) n)) :=
  abutmentIsotypicProdLocalizationEquivOfIsSMulRegular M _ _ b hK hW hW' n ρ σ τ
    (fun m => smoothRepHom_isSMulRegular (hreg m))
    (smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K (-n) hreg)

end Smooth

end HyperextScalarExtension

end Langlands.Cohomology
