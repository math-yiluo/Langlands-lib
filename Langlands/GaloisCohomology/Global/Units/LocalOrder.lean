import Langlands.GaloisCohomology.Global.BrauerSequence.FiniteComparison
import Langlands.GaloisCohomology.Global.BrauerSequence.Hasse
import Langlands.ClassFieldTheory.Global.LocalUnitVanishing
import Langlands.GaloisCohomology.Global.Units.DivisorModule
import Langlands.Cohomology.Profinite.InflationRestriction.DegreeOne
import Langlands.ClassFieldTheory.Global.CompletionTower
import Langlands.GaloisCohomology.Global.Units.Divisor

/-!
# The order of a local class at an unramified place

Let `K` be a number field, `v` a finite place, `M / K` a finite Galois extension and
`j : M →ₐ[K] K̄_v` an embedding, with place `w` of `M` (`placeOfAlgHom j`) unramified over
`v`. A class `b ∈ H²(Gal(M/K), Mˣ)` has two images in the cohomology of `Gal(K̄_v/K_v)`:

* its local class `map j b ∈ H²(K_v, K̄_vˣ)` (coefficients through `j`, `localUnitsHomOf`);
* its order class in `H²(K_v, ℤ)` (coefficients through the normalized order at `w`,
  `localOrderHom`).

`localUnitsHomOf_eq_zero_iff_localOrderHom_eq_zero`: one vanishes exactly when the other does. The
proof passes to the completion `M_w`: the local class is the inflation of the Library's local
component `unitsLocalMap v w 2` of the class, inflation of `H²` of units is injective (the Library's
relative invariants are injective), the order class is the inflation of the image of that component
in `H²(Gal(M_w/K_v), ℤ)` (and inflation of `H²` with coefficients `ℤ` along a surjection is
injective, by `H¹` with coefficients `ℚ/ℤ`), and the order map `H²(Gal(M_w/K_v), M_wˣ) → H²(ℤ)` is
injective because `H²(Gal(M_w/K_v), U_w) = 0` for the units `U_w` of the unramified extension (the
Library's `isZero_H2_localUnits`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory CategoryTheory.Limits Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain
open Langlands.ClassFieldTheory.Local Langlands.ClassFieldTheory.Global
  Langlands.Global.CompletionPadic
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

attribute [local instance] Langlands.Global.AdelicFunctoriality.isGalois_adicCompletion

universe u

noncomputable section

section IntegralH2

variable {G Γ : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group Γ]
  [TopologicalSpace Γ] [IsTopologicalGroup Γ] (r : G →ₜ* Γ)

/-- The identity of `A`, from the trivial `Γ`-module restricted along `r` to the trivial
`G`-module. -/
def trivialResHom (A : Type u) [AddCommGroup A] :
    Rep.res (r : G →* Γ) (trivialModule Γ A) ⟶ trivialModule G A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup Γ] in
theorem trivialResHom_hom_apply (A : Type u) [AddCommGroup A] (a : A) :
    (trivialResHom r A).hom a = a :=
  rfl

/-- The identity maps on `0 → ℤ → ℚ → ℚ/ℤ → 0`, from `Γ` restricted along `r` to `G`. -/
def trivialResSequence :
    (trivialSequence Γ).map (Rep.resFunctor (r : G →* Γ)) ⟶ trivialSequence G where
  τ₁ := trivialResHom r _
  τ₂ := trivialResHom r _
  τ₃ := trivialResHom r _
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    rfl
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    rfl

/-- `H¹` with trivial coefficients is injective along a surjection. -/
theorem map_trivialResHom_one_injective (hr : Function.Surjective r) (A : Type u) [AddCommGroup A] :
    Function.Injective (map r (trivialResHom r A) 1).hom := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 y
  rw [cohomologyπ_map_apply] at hy
  obtain ⟨b, hb⟩ := (homologyπ_succ_eq_zero_iff (cochains (trivialModule G A)) 0 _).1 hy
  have hd : ((cochains (trivialModule G A)).d 0 1).hom b = 0 := by
    apply cochainOf_injective
    rw [cochainOf_d, cochainOf_zero]
    funext g
    rw [inhomogeneousD_zero_apply]
    exact sub_self _
  have h0 : cochainOf (trivialModule G A)
      (cocycleι (trivialModule G A) 1 (cocyclesMap r (trivialResHom r A) 1 z)) = 0 := by
    change cochainOf _ (((cochains (trivialModule G A)).iCycles 1).hom _) = 0
    rw [← hb, hd, cochainOf_zero]
  rw [cochainOf_cocycleι_cocyclesMap] at h0
  have hz : cochainOf (trivialModule Γ A) (cocycleι (trivialModule Γ A) 1 z) = 0 := by
    funext g
    obtain ⟨σ, hσ⟩ := hr (g 0)
    have hg : g = ⇑r ∘ fun _ => σ := funext fun i => by rw [Fin.fin_one_eq_zero i]; exact hσ.symm
    have := congrFun h0 fun _ => σ
    rw [hg]
    exact this
  have hz' : z = 0 := by
    apply cocycleι_injective
    apply cochainOf_injective
    rw [hz, map_zero, cochainOf_zero]
  rw [hz', map_zero]

/-- `H²` with coefficients `ℤ` is injective along a surjection onto a finite discrete group. -/
theorem map_trivialResHom_two_injective [CompactSpace G] [TotallyDisconnectedSpace G]
    [DiscreteTopology Γ] [Finite Γ] (hr : Function.Surjective r) :
    Function.Injective (map r (trivialResHom r (ULift.{u} ℤ)) 2).hom := by
  have : CompactSpace Γ := Finite.compactSpace
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hSΓ := trivialSequence_shortExact Γ
  have hSG := trivialSequence_shortExact G
  obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hSΓ 1 2 rfl) x
    ((ModuleCat.subsingleton_of_isZero (isZero_cohomology_trivialModule_rat Γ (by norm_num))).elim
      _ _)
  have e := congrArg (fun ψ => ψ.hom y) (δ_comp_map r (trivialResSequence r) hSΓ hSG 1 2 rfl)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at e
  change (map r (trivialResHom r (ULift.{u} ℤ)) 2).hom ((δ hSΓ 1 2 rfl).hom y) =
    (δ hSG 1 2 rfl).hom ((map r (trivialResHom r (ULift.{u} QZ)) 1).hom y) at e
  rw [hx] at e
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hSG 1 2 rfl) _ e.symm
  have ht0 : t = 0 := (ModuleCat.subsingleton_of_isZero
    (isZero_cohomology_trivialModule_rat G le_rfl)).elim _ _
  rw [ht0, map_zero] at ht
  have hy : y = 0 := map_trivialResHom_one_injective r hr _ (ht.symm.trans (map_zero _).symm)
  rw [hy]
  exact map_zero _

end IntegralH2

section IntegralTrivial

variable (Γ : Type u) [Group Γ]

/-- The Library's trivial module `ℤ` and `trivialModule Γ (ULift ℤ)` are the same module. -/
def integralTrivialHom :
    Rep.trivial IntegerScalars.{u} Γ IntegerScalars.{u} ⟶ trivialModule Γ (ULift.{u} ℤ) :=
  Rep.ofHom ⟨{ toFun := fun n => n, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun _ => rfl⟩

end IntegralTrivial

/-- The map induced in degree two of Mathlib's group cohomology by a morphism of representations. -/
abbrev groupCohomologyTwoMap {Γ : Type u} [Group Γ] {A B : Rep.{u} IntegerScalars.{u} Γ}
    (f : A ⟶ B) : groupCohomology A 2 ⟶ groupCohomology B 2 :=
  groupCohomology.map (MonoidHom.id Γ) f 2

section Local

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  {M : Type u} [Field M] [NumberField M] [Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (v.adicCompletion K))

/-- `K̄_v` as an algebra over the completion `M_w` at the place `w` of `j`, through the embedding
extending `j`. -/
abbrev completionAlgebraOf :
    Algebra ((placeOfAlgHom j).1.adicCompletion M) (AlgebraicClosure (v.adicCompletion K)) :=
  (completionEmbeddingOfAlgHom j).toRingHom.toAlgebra

theorem isScalarTower_completionAlgebraOf :
    letI := completionAlgebraOf v j
    IsScalarTower (v.adicCompletion K) ((placeOfAlgHom j).1.adicCompletion M)
      (AlgebraicClosure (v.adicCompletion K)) :=
  letI := completionAlgebraOf v j
  IsScalarTower.of_algHom (completionEmbeddingOfAlgHom j)

/-- The exponent of the normalized valuation of `M_w` (the place `w` of `j`) at a unit of `M`: the
order at `w` with the opposite sign. -/
def placeExponent (x : Mˣ) : ℤ :=
  Multiplicative.toAdd (unitsExponent (placeOfAlgHom j).1
    (Units.map (algebraMap M ((placeOfAlgHom j).1.adicCompletion M)).toMonoidHom x))

theorem placeExponent_mul (x y : Mˣ) :
    placeExponent v j (x * y) = placeExponent v j x + placeExponent v j y := by
  simp only [placeExponent, map_mul, toAdd_mul]

theorem placeExponent_one : placeExponent v j 1 = 0 := by
  simp [placeExponent]

/-- `placeExponent` as an additive map. -/
def placeExponentHom : Additive Mˣ →+ ULift.{u} ℤ where
  toFun x := ULift.up (placeExponent v j (Additive.toMul x))
  map_zero' := ULift.ext (placeExponent_one v j)
  map_add' x y := ULift.ext (placeExponent_mul v j _ _)

/-- The valuation of `M` at the place of `j` is the exponential of `placeExponent`. -/
theorem valuation_eq_exp_placeExponent (x : Mˣ) :
    (placeOfAlgHom j).1.valuation M (x : M) = WithZero.exp (placeExponent v j x) := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', placeExponent, ← valued_units]
  rfl

/-- The place of `j ∘ g` for an automorphism `g` of `M` is the pull-back of the place of `j`. -/
theorem placeOfAlgHom_comp_algEquiv (g : M ≃ₐ[K] M) :
    (placeOfAlgHom (j.comp (g : M →ₐ[K] M))).1 =
      Langlands.Global.AdelicFunctoriality.finitePlaceEquiv g.toRingEquiv (placeOfAlgHom j).1 := by
  set W := (placeOfAlgHom j).1
  set W' := Langlands.Global.AdelicFunctoriality.finitePlaceEquiv g.toRingEquiv W
  have hW' : W'.asIdeal.LiesOver v.asIdeal := by
    constructor
    have hW : W.asIdeal.LiesOver v.asIdeal := (placeOfAlgHom j).2
    ext a
    rw [hW.over, Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
      Langlands.Global.AdelicFunctoriality.finitePlaceEquiv_mem]
    have : RingOfIntegers.mapRingEquiv g.toRingEquiv (algebraMap (𝓞 K) (𝓞 M) a) =
        algebraMap (𝓞 K) (𝓞 M) a := by
      apply RingOfIntegers.ext
      change g (algebraMap K M a) = algebraMap K M a
      exact g.commutes a
    rw [this]
  let e := Langlands.Global.AdelicFunctoriality.finiteCompletionEquiv g.toRingEquiv W
  have he : ∀ a : v.adicCompletion K, e (algebraMap (v.adicCompletion K) (W'.adicCompletion M) a) =
      algebraMap (v.adicCompletion K) (W.adicCompletion M) a := by
    intro a
    have h1 : Continuous fun a : v.adicCompletion K =>
        e (algebraMap (v.adicCompletion K) (W'.adicCompletion M) a) :=
      (Langlands.Global.AdelicFunctoriality.continuous_finiteCompletionEquiv _ _).comp
        (Langlands.Global.AdelicFunctoriality.FiniteExtension.continuous_completionMap v W')
    have h2 : Continuous fun a : v.adicCompletion K =>
        algebraMap (v.adicCompletion K) (W.adicCompletion M) a :=
      Langlands.Global.AdelicFunctoriality.FiniteExtension.continuous_completionMap v W
    have heq := (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v)).equalizer h1 h2 (funext fun k => by
      simp only [Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply K M (W'.adicCompletion M),
        Langlands.Global.AdelicFunctoriality.finiteCompletionEquiv_coe]
      rw [IsScalarTower.algebraMap_apply K M (W.adicCompletion M)]
      exact congrArg (algebraMap M (W.adicCompletion M)) (g.commutes k))
    exact congrFun heq a
  let c : W'.adicCompletion M →ₐ[v.adicCompletion K] AlgebraicClosure (v.adicCompletion K) :=
    (completionEmbeddingOfAlgHom j).comp
      { e.toRingHom with commutes' := fun a => he a }
  have := eq_placeOfAlgHom (j.comp (g : M →ₐ[K] M)) (w := ⟨W', hW'⟩) c fun x => by
    change completionEmbeddingOfAlgHom j (e (algebraMap M (W'.adicCompletion M) x)) = j (g x)
    rw [Langlands.Global.AdelicFunctoriality.finiteCompletionEquiv_coe,
      completionEmbeddingOfAlgHom_algebraMap]
    rfl
  exact (congrArg Subtype.val this).symm

/-- The exponent at the place of `j ∘ g` of `x` is the exponent at the place of `j` of `g x`. -/
theorem placeExponent_comp_algEquiv (g : M ≃ₐ[K] M) (x : Mˣ) :
    placeExponent v (j.comp (g : M →ₐ[K] M)) x = placeExponent v j (Units.map (g : M →* M) x) := by
  apply WithZero.exp_injective
  rw [← valuation_eq_exp_placeExponent, ← valuation_eq_exp_placeExponent,
    placeOfAlgHom_comp_algEquiv, Langlands.Global.AdelicFunctoriality.finitePlaceEquiv_valuation]
  rfl

section Tower

variable {L : Type u} [Field L] [NumberField L] [Algebra K L] [Algebra L M] [IsScalarTower K L M]

/-- In a tower `K ⊆ L ⊆ M`, the place of `M` of `j` lies above the place of `L` of the restriction of
`j` to `L`. -/
theorem placeOfAlgHom_under :
    (placeOfAlgHom j).1.under (𝓞 L) = (placeOfAlgHom (j.comp (IsScalarTower.toAlgHom K L M))).1 := by
  set W := (placeOfAlgHom j).1
  set w₀ := W.under (𝓞 L)
  have hW : W.asIdeal.LiesOver v.asIdeal := (placeOfAlgHom j).2
  have hw₀ : w₀.asIdeal.LiesOver v.asIdeal := by
    constructor
    change v.asIdeal = (W.asIdeal.under (𝓞 L)).under (𝓞 K)
    rw [Ideal.under_under]
    exact hW.over
  have hc := CompletionTower.isScalarTower_completion v w₀ W
  let c : w₀.adicCompletion L →ₐ[v.adicCompletion K] AlgebraicClosure (v.adicCompletion K) :=
    (completionEmbeddingOfAlgHom j).comp
      (IsScalarTower.toAlgHom (v.adicCompletion K) (w₀.adicCompletion L) (W.adicCompletion M))
  have := eq_placeOfAlgHom (j.comp (IsScalarTower.toAlgHom K L M)) (w := ⟨w₀, hw₀⟩) c fun x => by
    change completionEmbeddingOfAlgHom j
      (Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap w₀ W
        (algebraMap L (w₀.adicCompletion L) x)) = j (algebraMap L M x)
    rw [Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap_coe,
      completionEmbeddingOfAlgHom_algebraMap]
  exact congrArg Subtype.val this

/-- In a tower `K ⊆ L ⊆ M` with the place of `j` unramified over `K`, the exponent of an element of
`L` at the place of `j` is its exponent at the place of the restriction of `j`. -/
theorem placeExponent_algebraMap (hu : Algebra.IsUnramifiedAt (𝓞 K) (placeOfAlgHom j).1.asIdeal)
    (x : Lˣ) :
    placeExponent v j (Units.map (algebraMap L M : L →* M) x) =
      placeExponent v (j.comp (IsScalarTower.toAlgHom K L M)) x := by
  apply WithZero.exp_injective
  rw [← valuation_eq_exp_placeExponent, ← valuation_eq_exp_placeExponent, ← placeOfAlgHom_under]
  exact valuation_algebraMap_under (placeOfAlgHom j).1 hu (x : L)

end Tower

variable [IsGalois K M]

/-- The place of `j ∘ τ` is the place of `j` exactly when `τ` lies in the image of the
decomposition homomorphism of `j`. -/
theorem placeOfAlgHom_comp_eq_iff (τ : Gal(M/K)) :
    placeOfAlgHom (j.comp (τ : M →ₐ[K] M)) = placeOfAlgHom j ↔
      τ ∈ (decompositionHom (v.adicCompletion K) j :
        Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →* Gal(M/K)).range := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := exists_algEquiv_of_placeOfAlgHom_eq j (j.comp (τ : M →ₐ[K] M)) h.symm
    refine ⟨σ, AlgEquiv.ext fun x => j.injective ?_⟩
    change j (decompositionHom (v.adicCompletion K) j σ x) = j (τ x)
    rw [decompositionHom_apply]
    exact (hσ x).symm
  · rintro ⟨σ, rfl⟩
    have : j.comp ((decompositionHom (v.adicCompletion K) j σ : Gal(M/K)) : M →ₐ[K] M) =
        (((σ : AlgebraicClosure (v.adicCompletion K) →ₐ[v.adicCompletion K]
          AlgebraicClosure (v.adicCompletion K)).restrictScalars K).comp j) :=
      AlgHom.ext fun x => decompositionHom_apply j σ x
    refine (congrArg placeOfAlgHom this).trans ?_
    exact placeOfAlgHom_comp j σ

/-- The decomposition homomorphism of the Library at the place of `j`, as a continuous
homomorphism of the finite Galois groups. -/
def localDecompositionHomOf :
    Gal((placeOfAlgHom j).1.adicCompletion M/v.adicCompletion K) →ₜ* Gal(M/K) :=
  ⟨FundamentalClass.decompositionHom v (placeOfAlgHom j).1, continuous_of_discreteTopology⟩

/-- Restriction to `M_w` of the decomposition homomorphism of `j`: the decomposition homomorphism of
`j` factors through the restriction `Gal(K̄_v/K_v) → Gal(M_w/K_v)`. -/
theorem decompositionHom_eq_comp :
    letI := completionAlgebraOf v j
    haveI := isScalarTower_completionAlgebraOf v j
    decompositionHom (v.adicCompletion K) j =
      (localDecompositionHomOf v j).comp (BrauerComparison.normalKrullRestriction (v.adicCompletion K)
        ((placeOfAlgHom j).1.adicCompletion M) (AlgebraicClosure (v.adicCompletion K))) := by
  let := completionAlgebraOf v j
  have := isScalarTower_completionAlgebraOf v j
  refine ContinuousMonoidHom.ext fun σ => AlgEquiv.ext fun x => ?_
  apply j.injective
  change j ((decompositionHom (v.adicCompletion K) j σ) x) =
    j (FundamentalClass.decompositionHom v (placeOfAlgHom j).1
      ((AlgEquiv.restrictNormalHom ((placeOfAlgHom j).1.adicCompletion M)) σ) x)
  rw [decompositionHom_apply, ← completionEmbeddingOfAlgHom_algebraMap j (FundamentalClass.decompositionHom
    v (placeOfAlgHom j).1 ((AlgEquiv.restrictNormalHom ((placeOfAlgHom j).1.adicCompletion M)) σ) x),
    algebraMap_decompositionHom]
  have h2 := AlgEquiv.restrictNormal_commutes σ ((placeOfAlgHom j).1.adicCompletion M)
    (algebraMap M ((placeOfAlgHom j).1.adicCompletion M) x)
  change completionEmbeddingOfAlgHom j _ = _ at h2
  erw [h2, completionEmbeddingOfAlgHom_algebraMap j]

/-- The coefficient map `Mˣ → K̄_vˣ` of `j`, as a morphism of modules of `Gal(K̄_v/K_v)`. -/
def localUnitsHomOf :
    Rep.res (decompositionHom (v.adicCompletion K) j :
        Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →* Gal(M/K))
      (unitsModule K M) ⟶
      unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive
      (Units.map (j : M →* AlgebraicClosure (v.adicCompletion K)))) :
      Additive Mˣ →ₗ[ULift.{u} ℤ] Additive (AlgebraicClosure (v.adicCompletion K))ˣ), fun σ => by
    ext x
    exact Units.ext (decompositionHom_apply j σ ((Additive.toMul (show Additive Mˣ from x) : Mˣ) : M))⟩

theorem placeExponent_decompositionHom
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) (x : Mˣ) :
    placeExponent v j (galUnitsHom K M (decompositionHom (v.adicCompletion K) j σ) x) =
      placeExponent v j x := by
  let := completionAlgebraOf v j
  have := isScalarTower_completionAlgebraOf v j
  have hσ := DFunLike.congr_fun (decompositionHom_eq_comp v j) σ
  unfold placeExponent
  rw [← unitsExponent_localAut v (placeOfAlgHom j).1
    ((AlgEquiv.restrictNormalHom ((placeOfAlgHom j).1.adicCompletion M)) σ)
    (Units.map (algebraMap M ((placeOfAlgHom j).1.adicCompletion M)).toMonoidHom x)]
  refine congrArg (fun y => Multiplicative.toAdd (unitsExponent (placeOfAlgHom j).1 y)) ?_
  apply Units.ext
  change algebraMap M _ ((decompositionHom (v.adicCompletion K) j σ) (x : M)) = _
  rw [hσ]
  exact algebraMap_decompositionHom v (placeOfAlgHom j).1 _ (x : M)

/-- The exponent at the place of `j`, as a morphism to `ℤ` with trivial action of
`Gal(K̄_v/K_v)`. -/
def localExponentHom :
    Rep.res (decompositionHom (v.adicCompletion K) j :
        Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →* Gal(M/K))
      (unitsModule K M) ⟶
      trivialModule Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) (ULift.{u} ℤ) :=
  Rep.ofHom ⟨uliftIntLinearMap (placeExponentHom v j), fun σ => by
    ext x
    exact placeExponent_decompositionHom v j σ (Additive.toMul x)⟩

theorem localExponentHom_hom_apply (x : Additive Mˣ) :
    (localExponentHom v j).hom x = ULift.up (placeExponent v j (Additive.toMul x)) :=
  rfl

/-- The coefficient map `Mˣ → M_wˣ` along `localDecompositionHomOf`. -/
def completionUnitsHomOf :
    Rep.res (localDecompositionHomOf v j :
        Gal((placeOfAlgHom j).1.adicCompletion M/v.adicCompletion K) →* Gal(M/K)) (unitsModule K M) ⟶
      unitsModule (v.adicCompletion K) ((placeOfAlgHom j).1.adicCompletion M) :=
  Rep.ofHom ⟨unitsLocalizationLinear v (placeOfAlgHom j).1, fun σ => by
    ext x
    exact congrArg Additive.ofMul (Units.ext
      (algebraMap_decompositionHom v (placeOfAlgHom j).1 σ ((@Additive.toMul M ˣ x : Mˣ) : M)))⟩

/-- The valuation exponent `M_wˣ → ℤ` as a morphism to `trivialModule`. -/
def completionExponentHom :
    unitsModule (v.adicCompletion K) ((placeOfAlgHom j).1.adicCompletion M) ⟶
      trivialModule Gal((placeOfAlgHom j).1.adicCompletion M/v.adicCompletion K) (ULift.{u} ℤ) :=
  unitsExponentMorphism v (placeOfAlgHom j).1 ≫ integralTrivialHom _

/-- The local class of `j` factors through the completion `M_w`. -/
theorem map_localUnitsHomOf (b : cohomology (unitsModule K M) 2) :
    letI := completionAlgebraOf v j
    haveI := isScalarTower_completionAlgebraOf v j
    (map (decompositionHom (v.adicCompletion K) j) (localUnitsHomOf v j) 2).hom b =
      (unitsTowerMap (v.adicCompletion K) ((placeOfAlgHom j).1.adicCompletion M)
        (AlgebraicClosure (v.adicCompletion K)) 2).hom
        ((map (localDecompositionHomOf v j) (completionUnitsHomOf v j) 2).hom b) := by
  let := completionAlgebraOf v j
  have := isScalarTower_completionAlgebraOf v j
  have e := congrArg (fun F => F.hom b) (map_comp (localDecompositionHomOf v j)
    (completionUnitsHomOf v j)
    (BrauerComparison.normalKrullRestriction (v.adicCompletion K)
        ((placeOfAlgHom j).1.adicCompletion M) (AlgebraicClosure (v.adicCompletion K)))
    (underlyingHom _ (BrauerComparison.continuousUnitInflationCoefficients (v.adicCompletion K)
        ((placeOfAlgHom j).1.adicCompletion M) (AlgebraicClosure (v.adicCompletion K)))) 2)
  refine Eq.trans ?_ e
  refine congrArg (fun F => F.hom b) (map_congr (A := unitsModule K M)
    (B := unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) _ _
    (decompositionHom_eq_comp v j) (fun x => ?_) 2)
  apply Additive.toMul.injective
  apply Units.ext
  exact (completionEmbeddingOfAlgHom_algebraMap j _).symm

/-- The order class of `j` factors through the completion `M_w`. -/
theorem map_localExponentHom (b : cohomology (unitsModule K M) 2) :
    letI := completionAlgebraOf v j
    haveI := isScalarTower_completionAlgebraOf v j
    (map (decompositionHom (v.adicCompletion K) j) (localExponentHom v j) 2).hom b =
      (map (BrauerComparison.normalKrullRestriction (v.adicCompletion K)
          ((placeOfAlgHom j).1.adicCompletion M) (AlgebraicClosure (v.adicCompletion K)))
        (trivialResHom _ (ULift.{u} ℤ)) 2).hom
        ((map (localDecompositionHomOf v j) (completionUnitsHomOf v j ≫ completionExponentHom v j)
          2).hom b) := by
  let := completionAlgebraOf v j
  have := isScalarTower_completionAlgebraOf v j
  have e := congrArg (fun F => F.hom b) (map_comp (localDecompositionHomOf v j)
    (completionUnitsHomOf v j ≫ completionExponentHom v j)
    (BrauerComparison.normalKrullRestriction (v.adicCompletion K)
        ((placeOfAlgHom j).1.adicCompletion M) (AlgebraicClosure (v.adicCompletion K)))
    (trivialResHom _ (ULift.{u} ℤ)) 2)
  refine Eq.trans ?_ e
  refine congrArg (fun F => F.hom b) (map_congr (localExponentHom v j) _
    (decompositionHom_eq_comp v j) (fun x => ?_) 2)
  apply ULift.ext
  change placeExponent v j (Additive.toMul x) = Multiplicative.toAdd (unitsExponent (placeOfAlgHom j).1
    (Units.map (algebraMap M ((placeOfAlgHom j).1.adicCompletion M)).toMonoidHom (Additive.toMul x)))
  rfl

/-- Inflation of `H²` of units from `M_w` to `K̄_v` is injective (the Library's relative invariants
are injective). -/
theorem unitsTowerMap_two_injective :
    letI := completionAlgebraOf v j
    haveI := isScalarTower_completionAlgebraOf v j
    Function.Injective (unitsTowerMap (v.adicCompletion K) ((placeOfAlgHom j).1.adicCompletion M)
      (AlgebraicClosure (v.adicCompletion K)) 2).hom := by
  let := completionAlgebraOf v j
  have := isScalarTower_completionAlgebraOf v j
  have : FiniteDimensional (v.adicCompletion K) ((placeOfAlgHom j).1.adicCompletion M) :=
    Langlands.Global.AdelicFunctoriality.FiniteExtension.local_finite v (placeOfAlgHom j).1
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have hI := brauerInvariantFamily_spec.{u} (residuePrime v)
  set b' := (isoGroupCohomology (unitsModule (v.adicCompletion K)
    ((placeOfAlgHom j).1.adicCompletion M)) 2).hom.hom c with hb'
  have hcb : c = (isoGroupCohomology (unitsModule (v.adicCompletion K)
      ((placeOfAlgHom j).1.adicCompletion M)) 2).inv.hom b' := by
    rw [hb', Iso.hom_inv_id_apply]
  have h := finiteInvariant_unitsTowerMap v ((placeOfAlgHom j).1.adicCompletion M)
    (brauerInvariantFamily.{u} (residuePrime v)) hI.2 hI.1.2.2.1 b'
  rw [← hcb, hc, map_zero] at h
  have hb0 : b' = 0 := (hI.1.2.1 (padicField v) ((placeOfAlgHom j).1.adicCompletion M)).1
    (h.symm.trans (map_zero _).symm)
  rw [hcb, hb0, map_zero]

variable {v j} in
/-- The order map `H²(Gal(M_w/K_v), M_wˣ) → H²(Gal(M_w/K_v), ℤ)` is injective at an unramified
place. -/
theorem coeffMap_completionExponentHom_two_injective
    (he : (placeOfAlgHom j).1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Function.Injective (coeffMap (completionExponentHom v j) 2).hom := by
  have : FiniteDimensional (v.adicCompletion K) ((placeOfAlgHom j).1.adicCompletion M) :=
    Langlands.Global.AdelicFunctoriality.FiniteExtension.local_finite v (placeOfAlgHom j).1
  set w := (placeOfAlgHom j).1
  have hI := brauerInvariantFamily_spec.{u} (residuePrime v)
  obtain ⟨hinj, hrange⟩ := hI.1.2.1 (padicField v) (w.adicCompletion M)
  have hpos : 0 < Module.finrank (v.adicCompletion K) (w.adicCompletion M) := Module.finrank_pos
  have hset : Set.range ((brauerInvariantFamily.{u} (residuePrime v)).relative (padicField v)
      (w.adicCompletion M)) =
      (denominatorSubgroup (Module.finrank (v.adicCompletion K) (w.adicCompletion M)) :
        Set RationalModIntegers) := by
    rw [← AddMonoidHom.coe_range, hrange]
  let e : relativeCohomology (padicField v).Carrier (w.adicCompletion M) 2 ≃
      ZMod (Module.finrank (v.adicCompletion K) (w.adicCompletion M)) :=
    (Equiv.ofInjective _ hinj).trans ((Set.equivOfEq hset).trans
      (denominatorEquiv _ hpos).toEquiv.symm)
  have : NeZero (Module.finrank (v.adicCompletion K) (w.adicCompletion M)) := ⟨hpos.ne'⟩
  have : Finite (relativeCohomology (padicField v).Carrier (w.adicCompletion M) 2) :=
    Finite.of_equiv _ e.symm
  have hcard : Nat.card (relativeCohomology (padicField v).Carrier (w.adicCompletion M) 2) ≤
      Module.finrank (v.adicCompletion K) (w.adicCompletion M) := by
    rw [Nat.card_congr e, Nat.card_zmod]
  have hz := isZero_H2_localUnits v w he hcard
  -- injectivity of the exponent in Mathlib's group cohomology
  have hexp : Function.Injective
      (groupCohomologyTwoMap (unitsExponentMorphism v w)).hom := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).1 (groupCohomology.mapShortComplex₂_exact
      (unitsValuationSequence_shortExact v w) 2) y hy
    rw [← hx, (ModuleCat.subsingleton_of_isZero hz).elim x 0]
    exact map_zero _
  have hint : Function.Injective
      (groupCohomologyTwoMap (integralTrivialHom Gal(w.adicCompletion M/v.adicCompletion K))).hom := by
    let g : trivialModule (w.adicCompletion M ≃ₐ[v.adicCompletion K] w.adicCompletion M)
        (ULift.{u} ℤ) ⟶ Rep.trivial IntegerScalars.{u}
          (w.adicCompletion M ≃ₐ[v.adicCompletion K] w.adicCompletion M) IntegerScalars.{u} :=
      Rep.ofHom ⟨{ toFun := fun n => n, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
        fun _ => rfl⟩
    have hgf : integralTrivialHom _ ≫ g = 𝟙 _ := by ext; rfl
    intro y y' hyy
    have := congrArg (groupCohomologyTwoMap g).hom hyy
    rwa [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, hgf,
      groupCohomology.map_id, ModuleCat.id_apply, ModuleCat.id_apply] at this
  have hiso := isoGroupCohomology (unitsModule (v.adicCompletion K) (w.adicCompletion M)) 2
  intro c c' hcc
  apply (isoGroupCohomology (unitsModule (v.adicCompletion K) (w.adicCompletion M)) 2).toLinearEquiv.injective
  have key := congrArg (fun F => F.hom c) (map_comp_toGroupCohomology
    (ContinuousMonoidHom.id (w.adicCompletion M ≃ₐ[v.adicCompletion K] w.adicCompletion M))
    (completionExponentHom v j) 2)
  have key' := congrArg (fun F => F.hom c') (map_comp_toGroupCohomology
    (ContinuousMonoidHom.id (w.adicCompletion M ≃ₐ[v.adicCompletion K] w.adicCompletion M))
    (completionExponentHom v j) 2)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at key key'
  have h2 := key.symm.trans ((congrArg (fun x => (toGroupCohomology _ 2).hom x) hcc).trans key')
  change (groupCohomologyTwoMap (completionExponentHom v j)).hom ((toGroupCohomology _ 2).hom c) =
      (groupCohomologyTwoMap (completionExponentHom v j)).hom ((toGroupCohomology _ 2).hom c') at h2
  rw [groupCohomologyTwoMap, completionExponentHom, groupCohomology.map_id_comp, ModuleCat.comp_apply,
    ModuleCat.comp_apply] at h2
  exact hexp (hint h2)

/-- **Local class and order class.** At a place `w` of `j` unramified over `v`, a class of
`H²(Gal(M/K), Mˣ)` has zero local class in `H²(K_v, K̄_vˣ)` if and only if its order class in
`H²(K_v, ℤ)` is zero. -/
theorem map_localUnitsHomOf_eq_zero_iff
    (he : (placeOfAlgHom j).1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (b : cohomology (unitsModule K M) 2) :
    (map (decompositionHom (v.adicCompletion K) j) (localUnitsHomOf v j) 2).hom b = 0 ↔
      (map (decompositionHom (v.adicCompletion K) j) (localExponentHom v j) 2).hom b = 0 := by
  let := completionAlgebraOf v j
  have := isScalarTower_completionAlgebraOf v j
  have : CharZero (v.adicCompletion K) := charZero_adicCompletion v
  have : IsGalois (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) :=
    IsGalois.mk
  have : CompactSpace Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) :=
    galois_compactSpace _ _
  have : FiniteDimensional (v.adicCompletion K) ((placeOfAlgHom j).1.adicCompletion M) :=
    Langlands.Global.AdelicFunctoriality.FiniteExtension.local_finite v (placeOfAlgHom j).1
  have hr : Function.Surjective (BrauerComparison.normalKrullRestriction (v.adicCompletion K)
      ((placeOfAlgHom j).1.adicCompletion M) (AlgebraicClosure (v.adicCompletion K))) :=
    AlgEquiv.restrictNormalHom_surjective _
  rw [map_localUnitsHomOf, map_localExponentHom, ← map_comp_coeffMap]
  set c := (map (localDecompositionHomOf v j) (completionUnitsHomOf v j) 2).hom b
  change _ = 0 ↔ (map _ (trivialResHom _ (ULift.{u} ℤ)) 2).hom
    ((coeffMap (completionExponentHom v j) 2).hom c) = 0
  constructor
  · intro h
    have hc : c = 0 := (unitsTowerMap_two_injective v j) (h.trans (map_zero _).symm)
    rw [hc, map_zero, map_zero]
  · intro h
    have h1 := map_trivialResHom_two_injective _ hr (h.trans (map_zero _).symm)
    have hc : c = 0 := coeffMap_completionExponentHom_two_injective he (h1.trans (map_zero _).symm)
    rw [hc, map_zero]

end Local

end

end Langlands.GaloisCohomology
