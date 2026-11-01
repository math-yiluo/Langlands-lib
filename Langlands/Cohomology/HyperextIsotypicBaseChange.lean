import Langlands.Cohomology.HyperextScalarExtension
import Langlands.Cohomology.HyperextDegenerationIsotypic

/-!
# Extension of scalars of isotypic parts

Let `R → S` be an algebra of commutative rings and `Γ` a group. For representations `τ` and `ρ`
of `Γ` over `R`, this module compares the `τ`-isotypic part of `ρ`
(`HyperextAbutment.isotypicPart`) after extension of scalars with the `S ⊗[R] τ`-isotypic part of
`S ⊗[R] ρ` (`baseChangeRepresentation`), and applies this to the representations of
`HyperextDegenerationIsotypic` on `Hom(K, W₀⟦n⟧)` and `Hom(H^{-n} K, W)` and to the comparison maps
of `HyperextScalarExtension` along a semilinear exact functor `F`.

* `baseChangeIntertwiningMap S f`, `multiplicityBaseChangeMap S τ ρ`: base change of intertwining
  maps, and the `S`-linear map `S ⊗[R] Hom_Γ(τ, ρ) → Hom_Γ(S ⊗[R] τ, S ⊗[R] ρ)`.
* `isotypicBaseChangeMap S τ ρ`: the `S`-linear map
  `S ⊗[R] (τ-isotypic part of ρ) → (S ⊗[R] τ)-isotypic part of S ⊗[R] ρ`, `s ⊗ v ↦ s ⊗ v`,
  injective for flat `S` (`isotypicBaseChangeMap_injective`), an intertwining map
  (`isotypicBaseChangeIntertwiningMap`) natural in `ρ` (`isotypicBaseChangeMap_naturality`).
* `invariantsBaseChangeMap S ρ`: the `S`-linear map `S ⊗[R] ρ^Γ → (S ⊗[R] ρ)^Γ`, injective for
  flat `S`.
* `abutmentMap_abutmentAction`, `cohomologyHomMap_cohomologyHomAction`: the comparison maps along
  `F` intertwine the actions of `Γ` over `C` with the actions induced by `F` over `D`.
* `abutmentBaseChangeIntertwiningMap`, `cohomologyHomBaseChangeIntertwiningMap`: the base-change
  maps of `HyperextScalarExtension` as intertwining maps, and `abutmentIsotypicBaseChangeMap`,
  `cohomologyHomIsotypicBaseChangeMap`: their restrictions to `τ`-isotypic parts, with the
  specializations `smoothAbutmentIsotypicBaseChangeMap` and
  `smoothCohomologyHomIsotypicBaseChangeMap` to extension of scalars of smooth representations
  along a flat `R → S`.

None of these maps is claimed to be surjective or bijective. For flat `S` the isotypic and
invariant maps are injective, but extension of scalars need not commute with isotypic parts, and
the module proves no such statement.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

namespace HyperextScalarExtension

open HyperextAbutment

universe w uR uS uG uC vC uD vD s s' uΓ

section Algebra

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  {Γ : Type uΓ} [Group Γ] {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V]
  [Module R V] [AddCommGroup W] [Module R W]

/-- The base change `f.baseChange S` of an intertwining map `f : τ → ρ`, as an intertwining map
`S ⊗[R] τ → S ⊗[R] ρ`. -/
def baseChangeIntertwiningMap {τ : Representation R Γ U} {ρ : Representation R Γ V}
    (f : τ.IntertwiningMap ρ) :
    (baseChangeRepresentation S τ).IntertwiningMap (baseChangeRepresentation S ρ) where
  toLinearMap := f.toLinearMap.baseChange S
  isIntertwining' γ := by
    change f.toLinearMap.baseChange S ∘ₗ (τ γ).baseChange S =
      (ρ γ).baseChange S ∘ₗ f.toLinearMap.baseChange S
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, f.isIntertwining' γ]

/-- `baseChangeIntertwiningMap S f` sends `s ⊗ u` to `s ⊗ f u`. -/
@[simp]
lemma baseChangeIntertwiningMap_tmul {τ : Representation R Γ U} {ρ : Representation R Γ V}
    (f : τ.IntertwiningMap ρ) (s : S) (u : U) :
    baseChangeIntertwiningMap S f (s ⊗ₜ u) = s ⊗ₜ f u :=
  rfl

/-- The `S`-linear map `S ⊗[R] Hom_Γ(τ, ρ) → Hom_Γ(S ⊗[R] τ, S ⊗[R] ρ)`,
`s ⊗ f ↦ s • f.baseChange S`. -/
def multiplicityBaseChangeMap (τ : Representation R Γ U) (ρ : Representation R Γ V) :
    S ⊗[R] τ.IntertwiningMap ρ →ₗ[S]
      (baseChangeRepresentation S τ).IntertwiningMap (baseChangeRepresentation S ρ) :=
  baseChangeLift
    { toFun := baseChangeIntertwiningMap S
      map_zero' := Representation.IntertwiningMap.ext (by exact LinearMap.baseChange_zero)
      map_add' := fun f g => Representation.IntertwiningMap.ext
        (by exact LinearMap.baseChange_add _ _) }
    fun r f => Representation.IntertwiningMap.ext <| LinearMap.ext fun x => by
      induction x using TensorProduct.inductionOn with
      | tmul s u =>
        change s ⊗ₜ (r • f u) = algebraMap R S r • (s ⊗ₜ[R] f u)
        rw [algebraMap_smul, TensorProduct.tmul_smul]
      | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `multiplicityBaseChangeMap S τ ρ` sends `s ⊗ f` to `s • baseChangeIntertwiningMap S f`. -/
@[simp]
lemma multiplicityBaseChangeMap_tmul (τ : Representation R Γ U) (ρ : Representation R Γ V)
    (s : S) (f : τ.IntertwiningMap ρ) :
    multiplicityBaseChangeMap S τ ρ (s ⊗ₜ f) = s • baseChangeIntertwiningMap S f :=
  rfl

variable (τ : Representation R Γ U)

/-- For `v` in the `τ`-isotypic part of `ρ`, `s ⊗ v` lies in the `S ⊗[R] τ`-isotypic part of
`S ⊗[R] ρ`. -/
lemma tmul_mem_isotypicPart {ρ : Representation R Γ V} (s : S) {v : V}
    (hv : v ∈ isotypicPart τ ρ) :
    s ⊗ₜ[R] v ∈ isotypicPart (baseChangeRepresentation S τ) (baseChangeRepresentation S ρ) := by
  refine (isotypicPart_le_iff τ ρ (N := ((isotypicPart (baseChangeRepresentation S τ)
    (baseChangeRepresentation S ρ)).restrictScalars R).comap (TensorProduct.mk R S V s))).2
    (fun f u => ?_) hv
  exact apply_mem_isotypicPart (baseChangeIntertwiningMap S f) (s ⊗ₜ u)

/-- The `S`-linear map `S ⊗[R] (τ-isotypic part of ρ) → (S ⊗[R] τ)-isotypic part of S ⊗[R] ρ`,
`s ⊗ v ↦ s ⊗ v`. -/
def isotypicBaseChangeMap (ρ : Representation R Γ V) :
    S ⊗[R] isotypicPart τ ρ →ₗ[S]
      isotypicPart (baseChangeRepresentation S τ) (baseChangeRepresentation S ρ) :=
  LinearMap.codRestrict _ ((isotypicPart τ ρ).subtype.baseChange S) fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul s v => exact tmul_mem_isotypicPart S τ s v.2
    | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- `isotypicBaseChangeMap S τ ρ` sends `s ⊗ v` to `s ⊗ v`. -/
@[simp]
lemma coe_isotypicBaseChangeMap_tmul (ρ : Representation R Γ V) (s : S)
    (v : isotypicPart τ ρ) :
    (isotypicBaseChangeMap S τ ρ (s ⊗ₜ v) : S ⊗[R] V) = s ⊗ₜ (v : V) :=
  rfl

/-- The underlying map of `isotypicBaseChangeMap` is the base change of the inclusion. -/
lemma coe_isotypicBaseChangeMap (ρ : Representation R Γ V) (x : S ⊗[R] isotypicPart τ ρ) :
    (isotypicBaseChangeMap S τ ρ x : S ⊗[R] V) = (isotypicPart τ ρ).subtype.baseChange S x :=
  rfl

/-- For flat `S`, `isotypicBaseChangeMap` is injective. -/
lemma isotypicBaseChangeMap_injective [Module.Flat R S] (ρ : Representation R Γ V) :
    Function.Injective (isotypicBaseChangeMap S τ ρ) := by
  intro x y h
  have h' := congrArg Subtype.val h
  rw [coe_isotypicBaseChangeMap, coe_isotypicBaseChangeMap,
    LinearMap.baseChange_eq_ltensor] at h'
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (isotypicPart τ ρ).injective_subtype h'

/-- `isotypicBaseChangeMap` intertwines the base change of the representation on the isotypic
part with the representation on the isotypic part of the base change. -/
def isotypicBaseChangeIntertwiningMap (ρ : Representation R Γ V) :
    (baseChangeRepresentation S (isotypicRepresentation τ ρ)).IntertwiningMap
      (isotypicRepresentation (baseChangeRepresentation S τ) (baseChangeRepresentation S ρ)) where
  toLinearMap := isotypicBaseChangeMap S τ ρ
  isIntertwining' γ := LinearMap.ext fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul s v => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `isotypicBaseChangeMap` is natural for intertwining maps `φ : ρ → σ`. -/
lemma isotypicBaseChangeMap_naturality {ρ : Representation R Γ V} {σ : Representation R Γ W}
    (φ : ρ.IntertwiningMap σ) (x : S ⊗[R] isotypicPart τ ρ) :
    isotypicIntertwiningMap (baseChangeRepresentation S τ) (baseChangeIntertwiningMap S φ)
        (isotypicBaseChangeMap S τ ρ x) =
      isotypicBaseChangeMap S τ σ ((isotypicIntertwiningMap τ φ).toLinearMap.baseChange S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s v => rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

variable {τ} in
/-- For an invariant vector `v`, `s ⊗ v` is invariant. -/
lemma tmul_mem_invariants {ρ : Representation R Γ V} (s : S) {v : V} (hv : v ∈ ρ.invariants) :
    s ⊗ₜ[R] v ∈ (baseChangeRepresentation S ρ).invariants := fun γ => by
  rw [baseChangeRepresentation_apply_tmul, hv γ]

/-- The `S`-linear map `S ⊗[R] ρ^Γ → (S ⊗[R] ρ)^Γ`, `s ⊗ v ↦ s ⊗ v`. -/
def invariantsBaseChangeMap (ρ : Representation R Γ V) :
    S ⊗[R] ρ.invariants →ₗ[S] (baseChangeRepresentation S ρ).invariants :=
  LinearMap.codRestrict _ (ρ.invariants.subtype.baseChange S) fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul s v => exact tmul_mem_invariants S s v.2
    | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- `invariantsBaseChangeMap S ρ` sends `s ⊗ v` to `s ⊗ v`. -/
@[simp]
lemma coe_invariantsBaseChangeMap_tmul (ρ : Representation R Γ V) (s : S) (v : ρ.invariants) :
    (invariantsBaseChangeMap S ρ (s ⊗ₜ v) : S ⊗[R] V) = s ⊗ₜ (v : V) :=
  rfl

/-- For flat `S`, `invariantsBaseChangeMap` is injective. -/
lemma invariantsBaseChangeMap_injective [Module.Flat R S] (ρ : Representation R Γ V) :
    Function.Injective (invariantsBaseChangeMap S ρ) := by
  intro x y h
  have h' := congrArg Subtype.val h
  change ρ.invariants.subtype.baseChange S x = ρ.invariants.subtype.baseChange S y at h'
  rw [LinearMap.baseChange_eq_ltensor] at h'
  exact Module.Flat.lTensor_preserves_injective_linearMap _ ρ.invariants.injective_subtype h'

end Algebra

section Derived

variable {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] [Algebra R S]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear R C] [HasDerivedCategory.{s} C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [Linear S D] [HasDerivedCategory.{s'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable {Γ : Type uΓ} [Group Γ]

open DerivedCategory

/-- `abutmentMap` is natural in `K`: precomposition with `φ : K' ⟶ K`. -/
lemma abutmentMap_precomp {K' K : DerivedCategory C} (φ : K' ⟶ K) (W : C) (n : ℤ)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    abutmentMap F K' W n (φ ≫ f) = F.mapDerivedCategory.map φ ≫ abutmentMap F K W n f := by
  simp only [abutmentMap_apply, ShiftedHom.map, Functor.map_comp, Category.assoc]

/-- `abutmentMap` intertwines `abutmentAction ρ σ n` with the action induced by `F` on
`Hom(F K, (F W)₀⟦n⟧)`. -/
lemma abutmentMap_abutmentAction {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (γ : Γ) (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    abutmentMap F K W n (abutmentAction ρ σ n γ f) =
      abutmentAction ((F.mapDerivedCategory.mapAut K).comp ρ) ((F.mapAut W).comp σ) n γ
        (abutmentMap F K W n f) := by
  rw [abutmentAction_apply, abutmentAction_apply, postcomp_apply, precomp_apply,
    postcomp_apply, precomp_apply, abutmentMap_comp_single, abutmentMap_precomp]
  rfl

/-- `cohomologyHomMap` intertwines `cohomologyHomAction ρ σ n` with the action induced by `F`
on `Hom(H^{-n}(F K), F W)`. -/
lemma cohomologyHomMap_cohomologyHomAction {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (γ : Γ) (g : (homologyFunctor C (-n)).obj K ⟶ W) :
    cohomologyHomMap F K W (-n) (cohomologyHomAction ρ σ n γ g) =
      cohomologyHomAction ((F.mapDerivedCategory.mapAut K).comp ρ) ((F.mapAut W).comp σ) n γ
        (cohomologyHomMap F K W (-n) g) := by
  rw [cohomologyHomAction_apply, cohomologyHomAction_apply, cohomologyHomMap_apply,
    cohomologyHomMap_apply, Functor.map_comp, Functor.map_comp]
  have h := (exactDerivedHomologyIso F (-n)).hom.naturality (ρ γ).inv
  simp only [Functor.comp_map] at h
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ F.map g ≫ F.map (σ γ).hom) h.symm).trans
    ?_)
  simp only [Category.assoc]
  rfl

variable (hF : IsSemilinear R S F)

/-- `abutmentBaseChangeMap` as an intertwining map from the base change of
`abutmentRepresentation R ρ σ n` to the representation of `Γ` on `Hom(F K, (F W)₀⟦n⟧)`. -/
def abutmentBaseChangeIntertwiningMap {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) :
    (baseChangeRepresentation S (abutmentRepresentation R ρ σ n)).IntertwiningMap
      (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
        ((F.mapAut W).comp σ) n) where
  toLinearMap := abutmentBaseChangeMap F hF K W n
  isIntertwining' γ := LinearMap.ext fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul s f =>
      change abutmentBaseChangeMap F hF K W n (s ⊗ₜ abutmentAction ρ σ n γ f) =
        abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n γ (abutmentBaseChangeMap F hF K W n (s ⊗ₜ f))
      rw [abutmentBaseChangeMap_tmul, abutmentBaseChangeMap_tmul, map_smul,
        abutmentMap_abutmentAction]
      rfl
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

/-- `cohomologyHomBaseChangeMap` as an intertwining map from the base change of
`cohomologyHomRepresentation R ρ σ n` to the representation of `Γ` on
`Hom(H^{-n}(F K), F W)`. -/
def cohomologyHomBaseChangeIntertwiningMap {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) :
    (baseChangeRepresentation S (cohomologyHomRepresentation R ρ σ n)).IntertwiningMap
      (cohomologyHomRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
        ((F.mapAut W).comp σ) n) where
  toLinearMap := cohomologyHomBaseChangeMap F hF K W (-n)
  isIntertwining' γ := LinearMap.ext fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul s g =>
      change cohomologyHomBaseChangeMap F hF K W (-n) (s ⊗ₜ cohomologyHomAction ρ σ n γ g) =
        cohomologyHomRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n γ (cohomologyHomBaseChangeMap F hF K W (-n) (s ⊗ₜ g))
      rw [cohomologyHomBaseChangeMap_tmul, cohomologyHomBaseChangeMap_tmul, map_smul,
        cohomologyHomMap_cohomologyHomAction]
      rfl
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

variable {U : Type*} [AddCommGroup U] [Module R U]

/-- The base-change map on `τ`-isotypic parts of abutments:
`S ⊗[R] (τ-isotypic part of Hom(K, W₀⟦n⟧)) → (S ⊗[R] τ)-isotypic part of Hom(F K, (F W)₀⟦n⟧)`. -/
def abutmentIsotypicBaseChangeMap {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U) :
    S ⊗[R] isotypicPart τ (abutmentRepresentation R ρ σ n) →ₗ[S]
      isotypicPart (baseChangeRepresentation S τ)
        (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n) :=
  (isotypicIntertwiningMap (baseChangeRepresentation S τ)
    (abutmentBaseChangeIntertwiningMap F hF ρ σ n)).toLinearMap ∘ₗ
    isotypicBaseChangeMap S τ (abutmentRepresentation R ρ σ n)

/-- `abutmentIsotypicBaseChangeMap` sends `s ⊗ f` to `s • abutmentMap F K W n f`. -/
@[simp]
lemma coe_abutmentIsotypicBaseChangeMap_tmul {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U) (s : S)
    (f : isotypicPart τ (abutmentRepresentation R ρ σ n)) :
    (abutmentIsotypicBaseChangeMap F hF ρ σ n τ (s ⊗ₜ f) :
        ShiftedHom (F.mapDerivedCategory.obj K) ((singleFunctor D 0).obj (F.obj W)) n) =
      s • abutmentMap F K W n f :=
  rfl

/-- The base-change map on `τ`-isotypic parts of `Hom(H^{-n} K, W)`:
`S ⊗[R] (τ-isotypic part of Hom(H^{-n} K, W)) →
(S ⊗[R] τ)-isotypic part of Hom(H^{-n}(F K), F W)`. -/
def cohomologyHomIsotypicBaseChangeMap {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U) :
    S ⊗[R] isotypicPart τ (cohomologyHomRepresentation R ρ σ n) →ₗ[S]
      isotypicPart (baseChangeRepresentation S τ)
        (cohomologyHomRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n) :=
  (isotypicIntertwiningMap (baseChangeRepresentation S τ)
    (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n)).toLinearMap ∘ₗ
    isotypicBaseChangeMap S τ (cohomologyHomRepresentation R ρ σ n)

/-- `cohomologyHomIsotypicBaseChangeMap` sends `s ⊗ g` to `s • cohomologyHomMap F K W (-n) g`. -/
@[simp]
lemma coe_cohomologyHomIsotypicBaseChangeMap_tmul {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U) (s : S)
    (g : isotypicPart τ (cohomologyHomRepresentation R ρ σ n)) :
    (cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ (s ⊗ₜ g) :
        (homologyFunctor D (-n)).obj (F.mapDerivedCategory.obj K) ⟶ F.obj W) =
      s • cohomologyHomMap F K W (-n) g :=
  rfl

end Derived

section Smooth

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S] [Module.Flat R S]
  (G : Type uG) [Group G] [TopologicalSpace G]
  [HasDerivedCategory.{s} (SmoothRep.{uR, uG, w} R G)]
  [HasDerivedCategory.{s'} (SmoothRep.{uS, uG, max uS w} S G)]
  {Γ : Type uΓ} [Group Γ] {U : Type*} [AddCommGroup U] [Module R U]

open DerivedCategory

/-- `abutmentIsotypicBaseChangeMap` for extension of scalars of smooth representations along a
flat `R → S`. -/
def smoothAbutmentIsotypicBaseChangeMap {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)}
    {W : SmoothRep.{uR, uG, w} R G} (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ)
    (τ : Representation R Γ U) :
    S ⊗[R] isotypicPart τ (abutmentRepresentation R ρ σ n) →ₗ[S]
      isotypicPart (baseChangeRepresentation S τ)
        (abutmentRepresentation S
          (((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
          (((smoothRepExtendScalars.{w} R S G).mapAut W).comp σ) n) :=
  abutmentIsotypicBaseChangeMap (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) ρ σ n τ

/-- `cohomologyHomIsotypicBaseChangeMap` for extension of scalars of smooth representations along
a flat `R → S`. -/
def smoothCohomologyHomIsotypicBaseChangeMap {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)}
    {W : SmoothRep.{uR, uG, w} R G} (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ)
    (τ : Representation R Γ U) :
    S ⊗[R] isotypicPart τ (cohomologyHomRepresentation R ρ σ n) →ₗ[S]
      isotypicPart (baseChangeRepresentation S τ)
        (cohomologyHomRepresentation S
          (((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
          (((smoothRepExtendScalars.{w} R S G).mapAut W).comp σ) n) :=
  cohomologyHomIsotypicBaseChangeMap (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) ρ σ n τ

end Smooth

end HyperextScalarExtension

end Langlands.Cohomology
