import Langlands.Cohomology.HyperextIsotypicBaseChange
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Hom groups of representations and localization

Let `S` be a localization of a commutative ring `R` at a submonoid `M` (for example
`R = 𝒪`, the ring of integers of a finite extension of `ℚ_ℓ`, and `S` its fraction field). This
module proves that the comparison maps `S ⊗[R] Hom(X, Y) → Hom(S ⊗[R] X, S ⊗[R] Y)` for
extension of scalars of representations and of smooth representations are bijective when `X` is
finitely generated over the monoid algebra `R[G]` and `Y` has no `M`-torsion. Applied to
`X = H^q K`, this proves that the Library's `cohomologyHomBaseChangeMap` is bijective for
extension of scalars of (smooth) representations under these hypotheses.

* `isLocalizedModule_mk_one`, `mk_one_injective_of_isSMulRegular`: `v ↦ 1 ⊗ v : V → S ⊗[R] V`
  is a localization at `M`, injective when `V` has no `M`-torsion.
* `invariantsBaseChangeMap_surjective_of_isSMulRegular`,
  `invariantsBaseChangeMap_bijective_of_isSMulRegular` and the linear equivalence
  `invariantsBaseChangeEquivOfIsSMulRegular`: invariants commute with localization for
  representations on modules without `M`-torsion.
* `exists_finset_eq_top_of_finite_asModule`: a finite generating set of a representation that is
  finitely generated over `R[G]`.
* `homBaseChangeMap`: the comparison map `S ⊗[R] Hom(X, Y) → Hom(F X, F Y)`,
  `s ⊗ f ↦ s • F.map f`, of a semilinear functor `F`; `cohomologyHomBaseChangeMap_apply_eq` and
  `cohomologyHomBaseChangeMap_bijective_iff` identify `cohomologyHomBaseChangeMap` with
  `homBaseChangeMap` for `H^q K` up to composition with an isomorphism.
* `repHomBaseChangeMap_injective`, `repHomBaseChangeMap_surjective`,
  `repHomBaseChangeMap_bijective` and the linear equivalence `repHomBaseChangeEquiv`: the case
  of extension of scalars of representations;
  `repCohomologyHomBaseChangeMap_bijective_of_isLocalization` applies it to `H^q K`.
* `repHom_isSMulRegular`, `smoothRepHom_isSMulRegular`: `Hom(X, Y)` has no `r`-torsion when `Y`
  has none.
* `smoothHomBaseChangeMap_hom`, `smoothHomBaseChangeMap_bijective_iff`,
  `smoothHomBaseChangeMap_bijective` and
  `smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization`: the versions for extension of
  scalars of smooth representations.

The finite generation of `H^q K` over `R[G]` and the absence of `M`-torsion in `W` remain
hypotheses; this module does not verify them for any particular complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

namespace HyperextScalarExtension

universe w uR uS uG uC vC uD vD s s' uΓ

section Algebra

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]

include M

/-- If `S` is a localization of `R` at `M`, then `v ↦ 1 ⊗ v : V → S ⊗[R] V` is a localization
of `V` at `M`. -/
lemma isLocalizedModule_mk_one (V : Type*) [AddCommGroup V] [Module R V] :
    IsLocalizedModule M (TensorProduct.mk R S V 1) :=
  (isLocalizedModule_iff_isBaseChange M S _).2 (TensorProduct.isBaseChange R V S)

/-- If `S` is a localization of `R` at `M` and multiplication by every element of `M` is
injective on `V`, then `v ↦ 1 ⊗ v : V → S ⊗[R] V` is injective. -/
lemma mk_one_injective_of_isSMulRegular {V : Type*} [AddCommGroup V] [Module R V]
    (hV : ∀ m : M, IsSMulRegular V (m : R)) : Function.Injective (TensorProduct.mk R S V 1) := by
  have := isLocalizedModule_mk_one S M V
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff M (TensorProduct.mk R S V 1)).1 hv
  refine hV c ?_
  change (c : R) • v = (c : R) • 0
  rw [smul_zero, ← Submonoid.smul_def]
  exact hc

variable {Γ : Type uΓ} [Group Γ] {V : Type*} [AddCommGroup V] [Module R V]

/-- **Invariants commute with localization for modules without `M`-torsion.** If `S` is a
localization of `R` at `M` and multiplication by every element of `M` is injective on `V`, then
`invariantsBaseChangeMap S ρ : S ⊗[R] ρ^Γ → (S ⊗[R] ρ)^Γ` is surjective. -/
theorem invariantsBaseChangeMap_surjective_of_isSMulRegular {ρ : Representation R Γ V}
    (hV : ∀ m : M, IsSMulRegular V (m : R)) :
    Function.Surjective (invariantsBaseChangeMap S ρ) := by
  have := isLocalizedModule_mk_one S M V
  have hinj := mk_one_injective_of_isSMulRegular S M hV
  rintro ⟨x, hx⟩
  obtain ⟨⟨v, m⟩, hm⟩ := IsLocalizedModule.surj M (TensorProduct.mk R S V 1) x
  replace hm : (m : R) • x = (1 : S) ⊗ₜ[R] v := by
    rw [← Submonoid.smul_def]; exact hm
  have hv : v ∈ ρ.invariants := (Representation.mem_invariants ρ v).2 fun γ => hinj (by
    change (1 : S) ⊗ₜ[R] ρ γ v = (1 : S) ⊗ₜ[R] v
    rw [← baseChangeRepresentation_apply_tmul, ← hm, LinearMap.map_smul_of_tower,
      (Representation.mem_invariants _ x).1 hx γ])
  let u : S := IsLocalization.mk' S (1 : R) m
  have hu : u * algebraMap R S (m : R) = 1 := by
    rw [IsLocalization.mk'_spec, map_one]
  refine ⟨u ⊗ₜ[R] ⟨v, hv⟩, Subtype.ext ?_⟩
  change u ⊗ₜ[R] v = x
  calc u ⊗ₜ[R] v = u • ((1 : S) ⊗ₜ[R] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = u • ((m : R) • x) := by rw [hm]
    _ = (u * algebraMap R S (m : R)) • x := by rw [mul_smul, algebraMap_smul]
    _ = x := by rw [hu, one_smul]

/-- If `S` is a localization of `R` at `M` and `V` has no `M`-torsion, then
`invariantsBaseChangeMap S ρ` is bijective. -/
theorem invariantsBaseChangeMap_bijective_of_isSMulRegular {ρ : Representation R Γ V}
    (hV : ∀ m : M, IsSMulRegular V (m : R)) :
    Function.Bijective (invariantsBaseChangeMap S ρ) :=
  have : Module.Flat R S := IsLocalization.flat S M
  ⟨invariantsBaseChangeMap_injective S ρ,
    invariantsBaseChangeMap_surjective_of_isSMulRegular S M hV⟩

/-- For a localization `S` of `R` at `M` and a representation on a module without `M`-torsion,
the `S`-linear equivalence `S ⊗[R] ρ^Γ ≃ (S ⊗[R] ρ)^Γ` given by `invariantsBaseChangeMap`. -/
def invariantsBaseChangeEquivOfIsSMulRegular {ρ : Representation R Γ V}
    (hV : ∀ m : M, IsSMulRegular V (m : R)) :
    S ⊗[R] ρ.invariants ≃ₗ[S] (baseChangeRepresentation S ρ).invariants :=
  LinearEquiv.ofBijective (invariantsBaseChangeMap S ρ)
    (invariantsBaseChangeMap_bijective_of_isSMulRegular S M hV)

/-- The underlying map of `invariantsBaseChangeEquivOfIsSMulRegular` is
`invariantsBaseChangeMap`. -/
@[simp]
lemma invariantsBaseChangeEquivOfIsSMulRegular_apply {ρ : Representation R Γ V}
    (hV : ∀ m : M, IsSMulRegular V (m : R)) (x : S ⊗[R] ρ.invariants) :
    invariantsBaseChangeEquivOfIsSMulRegular S M hV x = invariantsBaseChangeMap S ρ x :=
  rfl

end Algebra

section Generators

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G] {V : Type*} [AddCommGroup V]
  [Module R V]

/-- If `ρ` is finitely generated as a module over the group algebra `R[G]`, there is a finite set
`t` of vectors such that every `G`-stable `R`-submodule containing `t` is everything. -/
lemma exists_finset_eq_top_of_finite_asModule (ρ : Representation R G V)
    [Module.Finite (MonoidAlgebra R G) ρ.asModule] :
    ∃ t : Finset V, ∀ N : Submodule R V, (∀ (g : G), ∀ v ∈ N, ρ g v ∈ N) →
      (t : Set V) ⊆ N → N = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule (MonoidAlgebra R G) ρ.asModule).FG)
  refine ⟨t.image ρ.asModuleEquiv, fun N hN htN => ?_⟩
  let N' : Submodule (MonoidAlgebra R G) ρ.asModule :=
    { carrier := ρ.asModuleEquiv ⁻¹' N
      add_mem' := fun {a b} ha hb => by
        change ρ.asModuleEquiv (a + b) ∈ N
        rw [map_add]
        exact N.add_mem ha hb
      zero_mem' := by
        change ρ.asModuleEquiv 0 ∈ N
        rw [map_zero]
        exact N.zero_mem
      smul_mem' := fun a v hv => by
        change ρ.asModuleEquiv (a • v) ∈ N
        induction a using MonoidAlgebra.induction_on with
        | of g =>
          rw [ρ.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
          exact hN g _ hv
        | add a b ha hb =>
          rw [add_smul, map_add]
          exact N.add_mem ha hb
        | smul r a ha =>
          rw [smul_assoc, map_smul]
          exact N.smul_mem r ha }
  have hle : (⊤ : Submodule (MonoidAlgebra R G) ρ.asModule) ≤ N' := by
    rw [← ht, Submodule.span_le]
    intro v hv
    exact htN (Finset.mem_image_of_mem _ hv)
  refine eq_top_iff.2 fun v _ => ?_
  have h := hle (Submodule.mem_top (x := ρ.asModuleEquiv.symm v))
  change ρ.asModuleEquiv (ρ.asModuleEquiv.symm v) ∈ N at h
  rwa [LinearEquiv.apply_symm_apply] at h

end Generators

section Hom

variable {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] [Algebra R S]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear R C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [Linear S D]
variable (F : C ⥤ D) [F.Additive]

/-- The `S`-linear comparison map `S ⊗[R] Hom(X, Y) → Hom(F X, F Y)`, `s ⊗ f ↦ s • F.map f`, of
an additive semilinear functor `F`. -/
def homBaseChangeMap (hF : IsSemilinear R S F) (X Y : C) :
    S ⊗[R] (X ⟶ Y) →ₗ[S] (F.obj X ⟶ F.obj Y) :=
  baseChangeLift F.mapAddHom (fun r f => hF r f)

@[simp]
theorem homBaseChangeMap_tmul (hF : IsSemilinear R S F) {X Y : C} (s : S) (f : X ⟶ Y) :
    homBaseChangeMap F hF X Y (s ⊗ₜ f) = s • F.map f := rfl

section Derived

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [HasDerivedCategory.{s} C] [HasDerivedCategory.{s'} D]

/-- `cohomologyHomBaseChangeMap` is `homBaseChangeMap` for `H^q K` and `W`, followed by
composition with the comparison `H^q (F K) ≅ F (H^q K)` of `exactDerivedHomologyIso`. -/
theorem cohomologyHomBaseChangeMap_apply_eq (hF : IsSemilinear R S F) (K : DerivedCategory C)
    (W : C) (q : ℤ) (t : S ⊗[R] ((DerivedCategory.homologyFunctor C q).obj K ⟶ W)) :
    cohomologyHomBaseChangeMap F hF K W q t =
      (exactDerivedHomologyIso F q).hom.app K ≫
        homBaseChangeMap F hF ((DerivedCategory.homologyFunctor C q).obj K) W t := by
  induction t using TensorProduct.inductionOn with
  | tmul s φ =>
    rw [cohomologyHomBaseChangeMap_tmul, homBaseChangeMap_tmul, cohomologyHomMap_apply,
      Linear.comp_smul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, Preadditive.comp_add]

/-- `cohomologyHomBaseChangeMap F hF K W q` is bijective if and only if `homBaseChangeMap` is
bijective for `H^q K` and `W`. -/
theorem cohomologyHomBaseChangeMap_bijective_iff (hF : IsSemilinear R S F)
    (K : DerivedCategory C) (W : C) (q : ℤ) :
    Function.Bijective (cohomologyHomBaseChangeMap F hF K W q) ↔
      Function.Bijective
        (homBaseChangeMap F hF ((DerivedCategory.homologyFunctor C q).obj K) W) := by
  let e := (exactDerivedHomologyIso F q).app K
  have he : Function.Bijective (fun g : F.obj ((DerivedCategory.homologyFunctor C q).obj K) ⟶
      F.obj W => e.hom ≫ g) :=
    ⟨fun g g' h => (cancel_epi e.hom).1 h, fun g => ⟨e.inv ≫ g, e.hom_inv_id_assoc g⟩⟩
  have h : ⇑(cohomologyHomBaseChangeMap F hF K W q) =
      (fun g => e.hom ≫ g) ∘ homBaseChangeMap F hF _ W :=
    funext (cohomologyHomBaseChangeMap_apply_eq F hF K W q)
  rw [h]
  exact he.of_comp_iff' _

end Derived

end Hom

section Rep

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S] {G : Type uG} [Monoid G]

include M

/-- **Hom groups of representations and localization, injectivity.** If `S` is a localization of
`R` at `M` and `Y` has no `M`-torsion, then
`S ⊗[R] Hom_G(X, Y) → Hom_G(S ⊗[R] X, S ⊗[R] Y)` is injective. -/
theorem repHomBaseChangeMap_injective {X Y : Rep.{w} R G}
    (hY : ∀ m : M, IsSMulRegular Y (m : R)) :
    Function.Injective (homBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) X Y) := by
  have := isLocalizedModule_mk_one S M (X ⟶ Y)
  have hinj := mk_one_injective_of_isSMulRegular S M hY
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  obtain ⟨⟨φ, m⟩, hm⟩ := IsLocalizedModule.surj M (TensorProduct.mk R S (X ⟶ Y) 1) t
  replace hm : algebraMap R S (m : R) • t = (1 : S) ⊗ₜ[R] φ := by
    rw [algebraMap_smul, ← Submonoid.smul_def]; exact hm
  have hφ : φ = 0 := by
    have h1 := congrArg (homBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) X Y) hm
    rw [map_smul, ht, smul_zero, homBaseChangeMap_tmul, one_smul] at h1
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => hinj ?_))
    have h2 := congrArg (fun f => f.hom ((1 : S) ⊗ₜ[R] x)) h1
    exact h2.symm.trans (TensorProduct.tmul_zero _ _).symm
  rw [hφ, TensorProduct.tmul_zero] at hm
  exact (IsLocalization.map_units S m).smul_eq_zero.1 hm

/-- **Hom groups of representations and localization, surjectivity.** If `S` is a localization of
`R` at `M`, `X` is finitely generated over the monoid algebra `R[G]` and `Y` has no `M`-torsion,
then `S ⊗[R] Hom_G(X, Y) → Hom_G(S ⊗[R] X, S ⊗[R] Y)` is surjective. -/
theorem repHomBaseChangeMap_surjective {X Y : Rep.{w} R G}
    [Module.Finite (MonoidAlgebra R G) X.ρ.asModule]
    (hY : ∀ m : M, IsSMulRegular Y (m : R)) :
    Function.Surjective (homBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) X Y) := by
  classical
  have := isLocalizedModule_mk_one S M Y
  have hinj := mk_one_injective_of_isSMulRegular S M hY
  intro g
  obtain ⟨t, ht⟩ := exists_finset_eq_top_of_finite_asModule X.ρ
  let g' : S ⊗[R] X →ₗ[S] S ⊗[R] Y := g.hom.toLinearMap
  have hg' : ∀ z, g' z = g.hom z := fun z => rfl
  obtain ⟨b, hb⟩ := IsLocalizedModule.exist_integer_multiples M (TensorProduct.mk R S Y 1) t
    (fun x => g' ((1 : S) ⊗ₜ[R] x))
  let L : X →ₗ[R] S ⊗[R] Y :=
    (b : R) • ((g'.restrictScalars R) ∘ₗ TensorProduct.mk R S X 1)
  have hL : ∀ x, L x = (b : R) • g' ((1 : S) ⊗ₜ[R] x) := fun x => rfl
  have hLρ : ∀ (γ : G) (x : X), L (X.ρ γ x) = baseChangeRepresentation S Y.ρ γ (L x) := by
    intro γ x
    rw [hL, hL, LinearMap.map_smul_of_tower]
    congr 1
    exact (hg' _).trans ((Rep.hom_comm_apply g γ ((1 : S) ⊗ₜ[R] x)).trans
      (congrArg _ (hg' _).symm))
  have hrange : ∀ x, L x ∈ LinearMap.range (TensorProduct.mk R S Y 1) := by
    have hN := ht ((LinearMap.range (TensorProduct.mk R S Y 1)).comap L) (fun γ v hv => by
      obtain ⟨y, hy⟩ := hv
      refine ⟨Y.ρ γ y, ?_⟩
      change (1 : S) ⊗ₜ[R] Y.ρ γ y = L (X.ρ γ v)
      rw [hLρ, ← hy]
      rfl) (fun x hx => by
        change L x ∈ LinearMap.range (TensorProduct.mk R S Y 1)
        rw [hL]
        exact hb x hx)
    intro x
    have hx : x ∈ (LinearMap.range (TensorProduct.mk R S Y 1)).comap L := hN ▸ Submodule.mem_top
    exact hx
  let e := LinearEquiv.ofInjective (TensorProduct.mk R S Y 1) hinj
  let f : X →ₗ[R] Y := e.symm.toLinearMap ∘ₗ L.codRestrict _ hrange
  have hf : ∀ x, (1 : S) ⊗ₜ[R] f x = L x := fun x =>
    congrArg Subtype.val (e.apply_symm_apply ⟨L x, hrange x⟩)
  have hfρ : ∀ (γ : G) (x : X), f (X.ρ γ x) = Y.ρ γ (f x) := fun γ x => hinj (by
    change (1 : S) ⊗ₜ[R] f (X.ρ γ x) = (1 : S) ⊗ₜ[R] Y.ρ γ (f x)
    rw [hf, hLρ, ← hf]
    rfl)
  let φ : X ⟶ Y := ConcreteCategory.ofHom (C := Rep.{w} R G)
    ⟨f, fun γ => LinearMap.ext fun x => hfρ γ x⟩
  have hφ : ∀ x, φ.hom x = f x := fun x => rfl
  let u : S := IsLocalization.mk' S (1 : R) b
  have hu : u * algebraMap R S (b : R) = 1 := by
    rw [IsLocalization.mk'_spec, map_one]
  refine ⟨u ⊗ₜ[R] φ, ?_⟩
  rw [homBaseChangeMap_tmul]
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
  change S ⊗[R] X at z
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    change u • (s ⊗ₜ[R] φ.hom x) = g' (s ⊗ₜ[R] x)
    calc u • (s ⊗ₜ[R] φ.hom x) = (u * s) • ((1 : S) ⊗ₜ[R] f x) := by
          rw [hφ, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
            smul_eq_mul, mul_one]
      _ = (u * s) • ((b : R) • g' ((1 : S) ⊗ₜ[R] x)) := by rw [hf, hL]
      _ = s • ((u * algebraMap R S (b : R)) • g' ((1 : S) ⊗ₜ[R] x)) := by
          rw [← algebraMap_smul S (b : R), smul_smul, smul_smul, mul_comm u s, mul_assoc]
      _ = g' (s ⊗ₜ[R] x) := by
          rw [hu, one_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add a c ha hc => exact (map_add _ a c).trans ((congrArg₂ (· + ·) ha hc).trans
      (map_add _ a c).symm)

/-- **Hom groups of representations and localization.** If `S` is a localization of `R` at `M`,
`X` is finitely generated over `R[G]` and `Y` has no `M`-torsion, then
`S ⊗[R] Hom_G(X, Y) → Hom_G(S ⊗[R] X, S ⊗[R] Y)` is bijective. -/
theorem repHomBaseChangeMap_bijective {X Y : Rep.{w} R G}
    [Module.Finite (MonoidAlgebra R G) X.ρ.asModule]
    (hY : ∀ m : M, IsSMulRegular Y (m : R)) :
    Function.Bijective (homBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) X Y) :=
  ⟨repHomBaseChangeMap_injective S M hY, repHomBaseChangeMap_surjective S M hY⟩

/-- Under the hypotheses of `repHomBaseChangeMap_bijective`, the `S`-linear equivalence
`S ⊗[R] Hom_G(X, Y) ≃ Hom_G(S ⊗[R] X, S ⊗[R] Y)` given by `homBaseChangeMap`. -/
def repHomBaseChangeEquiv {X Y : Rep.{w} R G} [Module.Finite (MonoidAlgebra R G) X.ρ.asModule]
    (hY : ∀ m : M, IsSMulRegular Y (m : R)) :
    S ⊗[R] (X ⟶ Y) ≃ₗ[S]
      ((repExtendScalars.{w} R S G).obj X ⟶ (repExtendScalars.{w} R S G).obj Y) :=
  LinearEquiv.ofBijective _ (repHomBaseChangeMap_bijective S M hY)

/-- The underlying map of `repHomBaseChangeEquiv` is `homBaseChangeMap`. -/
@[simp]
lemma repHomBaseChangeEquiv_apply {X Y : Rep.{w} R G}
    [Module.Finite (MonoidAlgebra R G) X.ρ.asModule] (hY : ∀ m : M, IsSMulRegular Y (m : R))
    (t : S ⊗[R] (X ⟶ Y)) :
    repHomBaseChangeEquiv S M hY t = homBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) X Y t :=
  rfl

section Derived

variable [Module.Flat R S] [HasDerivedCategory.{s} (Rep.{w} R G)]
  [HasDerivedCategory.{s'} (Rep.{max uS w} S G)]

/-- **Hom out of cohomology and localization.** If `S` is a localization of `R` at `M`, the
cohomology representation `H^q K` is finitely generated over `R[G]` and `W` has no `M`-torsion,
then `cohomologyHomBaseChangeMap` for extension of scalars of representations,
`S ⊗[R] Hom_G(H^q K, W) → Hom_G(H^q (S ⊗[R] K), S ⊗[R] W)`, is bijective. -/
theorem repCohomologyHomBaseChangeMap_bijective_of_isLocalization
    (K : DerivedCategory (Rep.{w} R G)) {W : Rep.{w} R G} (q : ℤ)
    [Module.Finite (MonoidAlgebra R G) ((DerivedCategory.homologyFunctor _ q).obj K).ρ.asModule]
    (hW : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective (cohomologyHomBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) K W q) :=
  (cohomologyHomBaseChangeMap_bijective_iff _ _ K W q).2 (repHomBaseChangeMap_bijective S M hW)

end Derived

end Rep

section Torsion

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]

/-- If multiplication by `r` is injective on `Y`, then it is injective on `Hom_G(X, Y)`. -/
lemma repHom_isSMulRegular {X Y : Rep.{w} R G} {r : R} (hY : IsSMulRegular Y r) :
    IsSMulRegular (X ⟶ Y) r := fun _ _ h =>
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x =>
    hY (congrArg (fun φ : X ⟶ Y => φ.hom x) h)))

/-- If multiplication by `r` is injective on the smooth representation `Y`, then it is injective
on `Hom(X, Y)` in the category of smooth representations. -/
lemma smoothRepHom_isSMulRegular {G : Type uG} [Group G] [TopologicalSpace G]
    {X Y : SmoothRep.{uR, uG, w} R G} {r : R} (hY : IsSMulRegular Y r) :
    IsSMulRegular (X ⟶ Y) r := fun _ _ h =>
  ObjectProperty.hom_ext _ (repHom_isSMulRegular (X := X.obj) (Y := Y.obj) hY
    (congrArg (fun φ : X ⟶ Y => φ.hom) h))

end Torsion

section Smooth

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  {G : Type uG} [Group G] [TopologicalSpace G]

/-- `homBaseChangeMap` for extension of scalars of smooth representations agrees with
`homBaseChangeMap` for extension of scalars of the underlying representations, through the
identification of morphisms of smooth representations with morphisms of representations. -/
theorem smoothHomBaseChangeMap_hom (X Y : SmoothRep.{uR, uG, w} R G) (t : S ⊗[R] (X ⟶ Y)) :
    (homBaseChangeMap (smoothRepExtendScalars.{w} R S G)
      (smoothRepExtendScalars_isSemilinear.{w} R S G) X Y t).hom =
    homBaseChangeMap (repExtendScalars.{w} R S G) (repExtendScalars_isSemilinear.{w} R S G)
      X.obj Y.obj
      ((InducedCategory.homLinearEquiv (C := Rep.{w} R G) (F := ObjectProperty.FullSubcategory.obj)
        (X := X) (Y := Y)).baseChange R S _ _ t) := by
  induction t using TensorProduct.inductionOn with
  | tmul s f => rfl
  | add a b ha hb =>
    rw [map_add]
    exact (congrArg₂ (· + ·) ha hb).trans
      ((map_add _ _ _).symm.trans (congrArg _ (map_add _ _ _).symm))

/-- `homBaseChangeMap` for smooth representations is bijective if and only if it is bijective
for the underlying representations. -/
theorem smoothHomBaseChangeMap_bijective_iff (X Y : SmoothRep.{uR, uG, w} R G) :
    Function.Bijective (homBaseChangeMap (smoothRepExtendScalars.{w} R S G)
      (smoothRepExtendScalars_isSemilinear.{w} R S G) X Y) ↔
    Function.Bijective (homBaseChangeMap (repExtendScalars.{w} R S G)
      (repExtendScalars_isSemilinear.{w} R S G) X.obj Y.obj) := by
  let eR := InducedCategory.homLinearEquiv (R := R) (C := Rep.{w} R G)
    (F := ObjectProperty.FullSubcategory.obj) (X := X) (Y := Y)
  let eS := InducedCategory.homLinearEquiv (R := S) (C := Rep.{max uS w} S G)
    (F := ObjectProperty.FullSubcategory.obj) (X := (smoothRepExtendScalars.{w} R S G).obj X)
    (Y := (smoothRepExtendScalars.{w} R S G).obj Y)
  have h : ⇑eS ∘ ⇑(homBaseChangeMap (smoothRepExtendScalars.{w} R S G)
      (smoothRepExtendScalars_isSemilinear.{w} R S G) X Y) =
      ⇑(homBaseChangeMap (repExtendScalars.{w} R S G)
        (repExtendScalars_isSemilinear.{w} R S G) X.obj Y.obj) ∘ ⇑(eR.baseChange R S _ _) :=
    funext (smoothHomBaseChangeMap_hom S X Y)
  rw [← eS.bijective.of_comp_iff', h]
  exact Function.Bijective.of_comp_iff _ (eR.baseChange R S _ _).bijective

variable (M : Submonoid R) [IsLocalization M S]

include M

/-- `repHomBaseChangeMap_bijective` for smooth representations. -/
theorem smoothHomBaseChangeMap_bijective {X Y : SmoothRep.{uR, uG, w} R G}
    [Module.Finite (MonoidAlgebra R G) X.obj.ρ.asModule]
    (hY : ∀ m : M, IsSMulRegular Y (m : R)) :
    Function.Bijective (homBaseChangeMap (smoothRepExtendScalars.{w} R S G)
      (smoothRepExtendScalars_isSemilinear.{w} R S G) X Y) :=
  (smoothHomBaseChangeMap_bijective_iff S X Y).2 (repHomBaseChangeMap_bijective S M hY)

variable [Module.Flat R S] [HasDerivedCategory.{s} (SmoothRep.{uR, uG, w} R G)]
  [HasDerivedCategory.{s'} (SmoothRep.{uS, uG, max uS w} S G)]

/-- **Hom out of cohomology of smooth representations and localization.** If `S` is a
localization of `R` at `M`, the underlying representation of `H^q K` is finitely generated over
`R[G]` and `W` has no `M`-torsion, then `smoothCohomologyHomBaseChangeMap R S G K W q` is
bijective. -/
theorem smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization
    (K : DerivedCategory (SmoothRep.{uR, uG, w} R G)) {W : SmoothRep.{uR, uG, w} R G} (q : ℤ)
    [Module.Finite (MonoidAlgebra R G)
      ((DerivedCategory.homologyFunctor _ q).obj K).obj.ρ.asModule]
    (hW : ∀ m : M, IsSMulRegular W (m : R)) :
    Function.Bijective
      (smoothCohomologyHomBaseChangeMap.{w, uR, uS, uG, s, s'} R S G K W q) :=
  (cohomologyHomBaseChangeMap_bijective_iff _ _ K W q).2 (smoothHomBaseChangeMap_bijective S M hW)

end Smooth

end HyperextScalarExtension

end Langlands.Cohomology
