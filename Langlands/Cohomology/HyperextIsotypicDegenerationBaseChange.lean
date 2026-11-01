import Langlands.Cohomology.HyperextScalarEdgeMap
import Langlands.Cohomology.HyperextIsotypicBaseChange

/-!
# Isotypic degeneration isomorphisms and extension of scalars

Let `R → S` be an algebra of commutative rings, `F : C ⥤ D` an exact functor that is semilinear
along `R → S`, `Γ` a group acting on `K : DerivedCategory C` and on `W : C`, and `τ` a
representation of `Γ` over `R`. This module proves that the base-change maps of
`HyperextIsotypicBaseChange` on `τ`-isotypic parts, and the corresponding maps on multiplicity
spaces and on `Γ`-invariants, commute with the edge maps, and hence with the degeneration
isomorphisms of `HyperextDegenerationIsotypic` over `R` and over `S`.

* `intertwiningMapCompLinearMap`, `intertwiningMapComp`, `invariantsLinearMap`,
  `isotypicProdIntertwiningMap`, `isotypicProdBaseChangeIntertwiningMap`: auxiliary
  constructions for representations.
* `abutmentIsotypicBaseChangeIntertwiningMap`, `cohomologyHomIsotypicBaseChangeIntertwiningMap`:
  the isotypic base-change maps as intertwining maps. `abutmentMultiplicityBaseChangeMap` and
  `cohomologyHomMultiplicityBaseChangeMap` are the base-change maps on multiplicity spaces, and
  `abutmentInvariantsBaseChangeMap` and `cohomologyHomInvariantsBaseChangeMap` those on
  `Γ`-invariants. `abutmentIsotypicProdBaseChangeIntertwiningMap` and
  `cohomologyHomIsotypicProdBaseChangeIntertwiningMap` are the versions for actions of `Γ × Δ`,
  as intertwining maps for `Δ`.
* `edgeMapIntertwiningMap_comp_abutmentBaseChangeIntertwiningMap`,
  `isotypicEdgeMap_abutmentIsotypicBaseChangeMap`,
  `multiplicityEdgeMap_abutmentMultiplicityBaseChangeMap`,
  `invariantsEdgeMap_abutmentInvariantsBaseChangeMap`,
  `isotypicProdEdgeMap_abutmentIsotypicProdBaseChangeIntertwiningMap`: compatibility with the
  edge maps.
* `degenerationIsotypicEquiv_abutmentIsotypicBaseChangeMap`,
  `degenerationMultiplicityEquiv_abutmentMultiplicityBaseChangeMap`,
  `degenerationInvariantsLinearEquiv_abutmentInvariantsBaseChangeMap`,
  `degenerationIsotypicProdEquiv_abutmentIsotypicProdBaseChangeIntertwiningMap` and the
  `_eq_degeneration` forms: compatibility with the degeneration isomorphisms. Under the
  degeneration hypotheses, a base-change map on abutments is bijective if and only if the
  corresponding map on `Hom(H^{-n} K, W)` is (`_bijective_iff`; for isotypic parts also
  `_injective_iff` and `_surjective_iff`).
* `abutmentIsotypicBaseChangeEquiv`, `abutmentIsotypicProdBaseChangeEquiv` and
  `smoothAbutmentIsotypicBaseChangeEquiv`: equivalences of representations;
  `abutmentInvariantsBaseChangeEquiv` and `smoothAbutmentInvariantsBaseChangeEquiv`: linear
  equivalences of invariants. Each one takes a hypothesis `h` that the corresponding map on
  `Hom(H^{-n} K, W)` is bijective.

This module does not prove any base-change map bijective. Extension of scalars need not commute
with isotypic parts or with invariants, and the bijectivity hypotheses `h` remain open
obligations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

namespace HyperextScalarExtension

open HyperextAbutment

universe w uR uS uG uC vC uD vD s s' t t' uΓ uΔ

section Algebra

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  {Γ : Type uΓ} [Group Γ] {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V]
  [Module R V] [AddCommGroup W] [Module R W]

/-- Composition with an intertwining map `φ : ρ → σ`, as an `R`-linear map from the
intertwining maps `τ → ρ` to the intertwining maps `τ → σ`. -/
def intertwiningMapCompLinearMap (τ : Representation R Γ U) {ρ : Representation R Γ V}
    {σ : Representation R Γ W} (φ : ρ.IntertwiningMap σ) :
    τ.IntertwiningMap ρ →ₗ[R] τ.IntertwiningMap σ where
  toFun f := φ.comp f
  map_add' f g := by
    ext u
    exact map_add φ (f u) (g u)
  map_smul' r f := by
    ext u
    exact map_smul φ r (f u)

/-- `intertwiningMapCompLinearMap τ φ f` is `φ ∘ f`. -/
@[simp]
lemma intertwiningMapCompLinearMap_apply_apply (τ : Representation R Γ U)
    {ρ : Representation R Γ V} {σ : Representation R Γ W} (φ : ρ.IntertwiningMap σ)
    (f : τ.IntertwiningMap ρ) (u : U) :
    intertwiningMapCompLinearMap τ φ f u = φ (f u) :=
  rfl

/-- An intertwining map of representations of `Γ` as an intertwining map of the
representations of `Γ'` obtained by composing with a group homomorphism `φ : Γ' →* Γ`. -/
def intertwiningMapComp {Γ' : Type*} [Group Γ'] {ρ : Representation R Γ V}
    {σ : Representation R Γ W} (f : ρ.IntertwiningMap σ) (φ : Γ' →* Γ) :
    Representation.IntertwiningMap (ρ.comp φ) (σ.comp φ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := f.isIntertwining' (φ g)

/-- The restriction of an intertwining map `φ : ρ → σ` to `Γ`-invariants, as an `R`-linear map
`ρ^Γ → σ^Γ`. -/
def invariantsLinearMap {ρ : Representation R Γ V} {σ : Representation R Γ W}
    (φ : ρ.IntertwiningMap σ) : ρ.invariants →ₗ[R] σ.invariants :=
  φ.toLinearMap.restrict fun v hv => (Representation.mem_invariants σ _).2 fun γ =>
    (Representation.IntertwiningMap.isIntertwining _ _ φ γ v).symm.trans
      (congrArg φ ((Representation.mem_invariants ρ _).1 hv γ))

/-- `invariantsLinearMap φ` is `φ` on underlying elements. -/
@[simp]
lemma coe_invariantsLinearMap_apply {ρ : Representation R Γ V} {σ : Representation R Γ W}
    (φ : ρ.IntertwiningMap σ) (x : ρ.invariants) : (invariantsLinearMap φ x : W) = φ x :=
  rfl

variable {Δ : Type uΔ} [Group Δ]

/-- For an intertwining map `φ : ρ → σ` of representations of `Γ × Δ`, its restriction to the
`τ`-isotypic parts for `Γ`, as an intertwining map of the representations of `Δ` on these
parts. -/
def isotypicProdIntertwiningMap (τ : Representation R Γ U) {ρ : Representation R (Γ × Δ) V}
    {σ : Representation R (Γ × Δ) W} (φ : ρ.IntertwiningMap σ) :
    (isotypicProdRepresentation τ ρ).IntertwiningMap (isotypicProdRepresentation τ σ) where
  toLinearMap :=
    (isotypicIntertwiningMap τ (intertwiningMapComp φ (MonoidHom.inl Γ Δ))).toLinearMap
  isIntertwining' δ := LinearMap.ext fun x =>
    Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ φ (1, δ) x)

/-- `isotypicProdIntertwiningMap τ φ` is `φ` on underlying elements. -/
@[simp]
lemma coe_isotypicProdIntertwiningMap_apply (τ : Representation R Γ U)
    {ρ : Representation R (Γ × Δ) V} {σ : Representation R (Γ × Δ) W}
    (φ : ρ.IntertwiningMap σ) (x : isotypicPart τ (ρ.comp (MonoidHom.inl Γ Δ))) :
    (isotypicProdIntertwiningMap τ φ x : W) = φ x :=
  rfl

/-- For a representation `ρ` of `Γ × Δ`, `isotypicBaseChangeMap` for the restriction of `ρ` to
`Γ` as an intertwining map of representations of `Δ`, from the base change of the
representation of `Δ` on the `τ`-isotypic part to the representation of `Δ` on the
`S ⊗[R] τ`-isotypic part of the base change. -/
def isotypicProdBaseChangeIntertwiningMap (τ : Representation R Γ U)
    (ρ : Representation R (Γ × Δ) V) :
    (baseChangeRepresentation S (isotypicProdRepresentation τ ρ)).IntertwiningMap
      (isotypicProdRepresentation (baseChangeRepresentation S τ)
        (baseChangeRepresentation S ρ)) where
  toLinearMap := isotypicBaseChangeMap S τ (ρ.comp (MonoidHom.inl Γ Δ))
  isIntertwining' δ := LinearMap.ext fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul s v => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `isotypicProdBaseChangeIntertwiningMap S τ ρ` sends `s ⊗ v` to `s ⊗ v`. -/
@[simp]
lemma coe_isotypicProdBaseChangeIntertwiningMap_tmul (τ : Representation R Γ U)
    (ρ : Representation R (Γ × Δ) V) (s : S)
    (v : isotypicPart τ (ρ.comp (MonoidHom.inl Γ Δ))) :
    (isotypicProdBaseChangeIntertwiningMap S τ ρ (s ⊗ₜ v) : S ⊗[R] V) = s ⊗ₜ (v : V) :=
  rfl

end Algebra

section Derived

variable {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] [Algebra R S]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear R C] [HasDerivedCategory.{s} C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [Linear S D] [HasDerivedCategory.{s'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable (hF : IsSemilinear R S F)
variable {Γ : Type uΓ} [Group Γ] {U : Type*} [AddCommGroup U] [Module R U]

open DerivedCategory

/-- The edge maps over `R` and over `S` intertwine `abutmentBaseChangeIntertwiningMap` and
`cohomologyHomBaseChangeIntertwiningMap`. -/
theorem edgeMapIntertwiningMap_comp_abutmentBaseChangeIntertwiningMap {K : DerivedCategory C}
    {W : C} (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) :
    (edgeMapIntertwiningMap S ((F.mapDerivedCategory.mapAut K).comp ρ) ((F.mapAut W).comp σ)
        n).comp (abutmentBaseChangeIntertwiningMap F hF ρ σ n) =
      (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n).comp
        (baseChangeIntertwiningMap S (edgeMapIntertwiningMap R ρ σ n)) :=
  Representation.IntertwiningMap.ext (edgeMapLinearMap_comp_abutmentBaseChangeMap F hF K W n)

/-! ### Isotypic parts -/

/-- `abutmentIsotypicBaseChangeMap` as an intertwining map from the base change of the
representation of `Γ` on the `τ`-isotypic part of `Hom(K, W₀⟦n⟧)` to the representation of `Γ`
on the `S ⊗[R] τ`-isotypic part of `Hom(F K, (F W)₀⟦n⟧)`. -/
def abutmentIsotypicBaseChangeIntertwiningMap {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U) :
    (baseChangeRepresentation S
        (isotypicRepresentation τ (abutmentRepresentation R ρ σ n))).IntertwiningMap
      (isotypicRepresentation (baseChangeRepresentation S τ)
        (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n)) :=
  (isotypicIntertwiningMap (baseChangeRepresentation S τ)
    (abutmentBaseChangeIntertwiningMap F hF ρ σ n)).comp
    (isotypicBaseChangeIntertwiningMap S τ (abutmentRepresentation R ρ σ n))

/-- The underlying map of `abutmentIsotypicBaseChangeIntertwiningMap` is
`abutmentIsotypicBaseChangeMap`. -/
@[simp]
lemma abutmentIsotypicBaseChangeIntertwiningMap_apply {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U)
    (x : S ⊗[R] isotypicPart τ (abutmentRepresentation R ρ σ n)) :
    abutmentIsotypicBaseChangeIntertwiningMap F hF ρ σ n τ x =
      abutmentIsotypicBaseChangeMap F hF ρ σ n τ x :=
  rfl

/-- `cohomologyHomIsotypicBaseChangeMap` as an intertwining map from the base change of the
representation of `Γ` on the `τ`-isotypic part of `Hom(H^{-n} K, W)` to the representation of
`Γ` on the `S ⊗[R] τ`-isotypic part of `Hom(H^{-n}(F K), F W)`. -/
def cohomologyHomIsotypicBaseChangeIntertwiningMap {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U) :
    (baseChangeRepresentation S
        (isotypicRepresentation τ (cohomologyHomRepresentation R ρ σ n))).IntertwiningMap
      (isotypicRepresentation (baseChangeRepresentation S τ)
        (cohomologyHomRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n)) :=
  (isotypicIntertwiningMap (baseChangeRepresentation S τ)
    (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n)).comp
    (isotypicBaseChangeIntertwiningMap S τ (cohomologyHomRepresentation R ρ σ n))

/-- The underlying map of `cohomologyHomIsotypicBaseChangeIntertwiningMap` is
`cohomologyHomIsotypicBaseChangeMap`. -/
@[simp]
lemma cohomologyHomIsotypicBaseChangeIntertwiningMap_apply {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U)
    (x : S ⊗[R] isotypicPart τ (cohomologyHomRepresentation R ρ σ n)) :
    cohomologyHomIsotypicBaseChangeIntertwiningMap F hF ρ σ n τ x =
      cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ x :=
  rfl

/-- The edge maps on `τ`-isotypic parts intertwine `abutmentIsotypicBaseChangeMap` and
`cohomologyHomIsotypicBaseChangeMap`. -/
theorem isotypicEdgeMap_abutmentIsotypicBaseChangeMap {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U)
    (x : S ⊗[R] isotypicPart τ (abutmentRepresentation R ρ σ n)) :
    isotypicIntertwiningMap (baseChangeRepresentation S τ)
        (edgeMapIntertwiningMap S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n) (abutmentIsotypicBaseChangeMap F hF ρ σ n τ x) =
      cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ
        ((isotypicIntertwiningMap τ (edgeMapIntertwiningMap R ρ σ n)).toLinearMap.baseChange S
          x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s f =>
    exact Subtype.ext
      (edgeMap_abutmentBaseChangeMap F hF K W n
        (s ⊗ₜ (f : ShiftedHom K ((singleFunctor C 0).obj W) n)))
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-! ### Multiplicity spaces -/

/-- The base-change map on multiplicity spaces of abutments:
`S ⊗[R] Hom_Γ(τ, Hom(K, W₀⟦n⟧)) → Hom_Γ(S ⊗[R] τ, Hom(F K, (F W)₀⟦n⟧))`, sending `s ⊗ f` to
`s • (abutmentBaseChangeMap ∘ f.baseChange S)`. -/
def abutmentMultiplicityBaseChangeMap {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U) :
    S ⊗[R] τ.IntertwiningMap (abutmentRepresentation R ρ σ n) →ₗ[S]
      (baseChangeRepresentation S τ).IntertwiningMap
        (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n) :=
  intertwiningMapCompLinearMap (baseChangeRepresentation S τ)
      (abutmentBaseChangeIntertwiningMap F hF ρ σ n) ∘ₗ
    multiplicityBaseChangeMap S τ (abutmentRepresentation R ρ σ n)

/-- `abutmentMultiplicityBaseChangeMap` sends `s ⊗ f` to
`s • (abutmentBaseChangeMap ∘ f.baseChange S)`. -/
@[simp]
lemma abutmentMultiplicityBaseChangeMap_tmul_apply {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U) (s : S)
    (f : τ.IntertwiningMap (abutmentRepresentation R ρ σ n)) (u : S ⊗[R] U) :
    abutmentMultiplicityBaseChangeMap F hF ρ σ n τ (s ⊗ₜ f) u =
      abutmentBaseChangeMap F hF K W n (s • f.toLinearMap.baseChange S u) :=
  rfl

/-- The base-change map on multiplicity spaces of `Hom(H^{-n} K, W)`:
`S ⊗[R] Hom_Γ(τ, Hom(H^{-n} K, W)) → Hom_Γ(S ⊗[R] τ, Hom(H^{-n}(F K), F W))`, sending `s ⊗ g`
to `s • (cohomologyHomBaseChangeMap ∘ g.baseChange S)`. -/
def cohomologyHomMultiplicityBaseChangeMap {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U) :
    S ⊗[R] τ.IntertwiningMap (cohomologyHomRepresentation R ρ σ n) →ₗ[S]
      (baseChangeRepresentation S τ).IntertwiningMap
        (cohomologyHomRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n) :=
  intertwiningMapCompLinearMap (baseChangeRepresentation S τ)
      (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n) ∘ₗ
    multiplicityBaseChangeMap S τ (cohomologyHomRepresentation R ρ σ n)

/-- `cohomologyHomMultiplicityBaseChangeMap` sends `s ⊗ g` to
`s • (cohomologyHomBaseChangeMap ∘ g.baseChange S)`. -/
@[simp]
lemma cohomologyHomMultiplicityBaseChangeMap_tmul_apply {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U) (s : S)
    (g : τ.IntertwiningMap (cohomologyHomRepresentation R ρ σ n)) (u : S ⊗[R] U) :
    cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ (s ⊗ₜ g) u =
      cohomologyHomBaseChangeMap F hF K W (-n) (s • g.toLinearMap.baseChange S u) :=
  rfl

/-- Composition with the edge maps over `R` and over `S` intertwines
`abutmentMultiplicityBaseChangeMap` and `cohomologyHomMultiplicityBaseChangeMap`. -/
theorem multiplicityEdgeMap_abutmentMultiplicityBaseChangeMap {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (τ : Representation R Γ U)
    (x : S ⊗[R] τ.IntertwiningMap (abutmentRepresentation R ρ σ n)) :
    intertwiningMapCompLinearMap (baseChangeRepresentation S τ)
        (edgeMapIntertwiningMap S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n) (abutmentMultiplicityBaseChangeMap F hF ρ σ n τ x) =
      cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ
        ((intertwiningMapCompLinearMap τ (edgeMapIntertwiningMap R ρ σ n)).baseChange S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s f =>
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun u => ?_)
    induction u using TensorProduct.inductionOn with
    | tmul t v => exact edgeMap_abutmentBaseChangeMap F hF K W n ((s • t) ⊗ₜ f v)
    | add u u' hu hu' =>
      exact (map_add _ u u').trans ((congrArg₂ (· + ·) hu hu').trans (map_add _ u u').symm)
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-! ### Invariants -/

/-- The base-change map on `Γ`-invariants of abutments,
`S ⊗[R] Hom(K, W₀⟦n⟧)^Γ → Hom(F K, (F W)₀⟦n⟧)^Γ`: `invariantsBaseChangeMap` followed by the
restriction of `abutmentBaseChangeIntertwiningMap` to invariants. -/
def abutmentInvariantsBaseChangeMap {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) :
    S ⊗[R] (abutmentRepresentation R ρ σ n).invariants →ₗ[S]
      (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
        ((F.mapAut W).comp σ) n).invariants :=
  invariantsLinearMap (abutmentBaseChangeIntertwiningMap F hF ρ σ n) ∘ₗ
    invariantsBaseChangeMap S (abutmentRepresentation R ρ σ n)

/-- `abutmentInvariantsBaseChangeMap` sends `s ⊗ f` to `s • abutmentMap F K W n f`. -/
@[simp]
lemma coe_abutmentInvariantsBaseChangeMap_tmul {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (s : S)
    (f : (abutmentRepresentation R ρ σ n).invariants) :
    (abutmentInvariantsBaseChangeMap F hF ρ σ n (s ⊗ₜ f) :
        ShiftedHom (F.mapDerivedCategory.obj K) ((singleFunctor D 0).obj (F.obj W)) n) =
      s • abutmentMap F K W n f :=
  rfl

/-- The base-change map on `Γ`-invariants of `Hom(H^{-n} K, W)`,
`S ⊗[R] Hom(H^{-n} K, W)^Γ → Hom(H^{-n}(F K), F W)^Γ`: `invariantsBaseChangeMap` followed by
the restriction of `cohomologyHomBaseChangeIntertwiningMap` to invariants. -/
def cohomologyHomInvariantsBaseChangeMap {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) :
    S ⊗[R] (cohomologyHomRepresentation R ρ σ n).invariants →ₗ[S]
      (cohomologyHomRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
        ((F.mapAut W).comp σ) n).invariants :=
  invariantsLinearMap (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n) ∘ₗ
    invariantsBaseChangeMap S (cohomologyHomRepresentation R ρ σ n)

/-- `cohomologyHomInvariantsBaseChangeMap` sends `s ⊗ g` to `s • cohomologyHomMap F K W (-n) g`. -/
@[simp]
lemma coe_cohomologyHomInvariantsBaseChangeMap_tmul {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (s : S)
    (g : (cohomologyHomRepresentation R ρ σ n).invariants) :
    (cohomologyHomInvariantsBaseChangeMap F hF ρ σ n (s ⊗ₜ g) :
        (homologyFunctor D (-n)).obj (F.mapDerivedCategory.obj K) ⟶ F.obj W) =
      s • cohomologyHomMap F K W (-n) g :=
  rfl

/-- The edge maps on `Γ`-invariants intertwine `abutmentInvariantsBaseChangeMap` and
`cohomologyHomInvariantsBaseChangeMap`. -/
theorem invariantsEdgeMap_abutmentInvariantsBaseChangeMap {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ)
    (x : S ⊗[R] (abutmentRepresentation R ρ σ n).invariants) :
    invariantsLinearMap
        (edgeMapIntertwiningMap S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n) (abutmentInvariantsBaseChangeMap F hF ρ σ n x) =
      cohomologyHomInvariantsBaseChangeMap F hF ρ σ n
        ((invariantsLinearMap (edgeMapIntertwiningMap R ρ σ n)).baseChange S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s f =>
    exact Subtype.ext
      (edgeMap_abutmentBaseChangeMap F hF K W n
        (s ⊗ₜ (f : ShiftedHom K ((singleFunctor C 0).obj W) n)))
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-! ### Commuting actions of `Γ × Δ` -/

variable {Δ : Type uΔ} [Group Δ]

/-- For actions of `Γ × Δ` on `K` and `W`: `abutmentIsotypicBaseChangeMap` for the restricted
actions of `Γ`, as an intertwining map of the representations of `Δ` on the base change of the
`τ`-isotypic part of `Hom(K, W₀⟦n⟧)` and on the `S ⊗[R] τ`-isotypic part of
`Hom(F K, (F W)₀⟦n⟧)`. -/
def abutmentIsotypicProdBaseChangeIntertwiningMap {K : DerivedCategory C} {W : C}
    (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (n : ℤ) (τ : Representation R Γ U) :
    (baseChangeRepresentation S
        (isotypicProdRepresentation τ (abutmentRepresentation R ρ σ n))).IntertwiningMap
      (isotypicProdRepresentation (baseChangeRepresentation S τ)
        (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n)) :=
  (isotypicProdIntertwiningMap (baseChangeRepresentation S τ)
    (abutmentBaseChangeIntertwiningMap F hF ρ σ n)).comp
    (isotypicProdBaseChangeIntertwiningMap S τ (abutmentRepresentation R ρ σ n))

/-- `abutmentIsotypicProdBaseChangeIntertwiningMap` sends `s ⊗ f` to `s • abutmentMap F K W n f`. -/
@[simp]
lemma coe_abutmentIsotypicProdBaseChangeIntertwiningMap_tmul {K : DerivedCategory C} {W : C}
    (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (n : ℤ) (τ : Representation R Γ U) (s : S)
    (f : isotypicPart τ ((abutmentRepresentation R ρ σ n).comp (MonoidHom.inl Γ Δ))) :
    (abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ (s ⊗ₜ f) :
        ShiftedHom (F.mapDerivedCategory.obj K) ((singleFunctor D 0).obj (F.obj W)) n) =
      s • abutmentMap F K W n f :=
  rfl

/-- For actions of `Γ × Δ` on `K` and `W`: `cohomologyHomIsotypicBaseChangeMap` for the
restricted actions of `Γ`, as an intertwining map of the representations of `Δ` on the base
change of the `τ`-isotypic part of `Hom(H^{-n} K, W)` and on the `S ⊗[R] τ`-isotypic part of
`Hom(H^{-n}(F K), F W)`. -/
def cohomologyHomIsotypicProdBaseChangeIntertwiningMap {K : DerivedCategory C} {W : C}
    (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (n : ℤ) (τ : Representation R Γ U) :
    (baseChangeRepresentation S
        (isotypicProdRepresentation τ (cohomologyHomRepresentation R ρ σ n))).IntertwiningMap
      (isotypicProdRepresentation (baseChangeRepresentation S τ)
        (cohomologyHomRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n)) :=
  (isotypicProdIntertwiningMap (baseChangeRepresentation S τ)
    (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n)).comp
    (isotypicProdBaseChangeIntertwiningMap S τ (cohomologyHomRepresentation R ρ σ n))

/-- `cohomologyHomIsotypicProdBaseChangeIntertwiningMap` sends `s ⊗ g` to
`s • cohomologyHomMap F K W (-n) g`. -/
@[simp]
lemma coe_cohomologyHomIsotypicProdBaseChangeIntertwiningMap_tmul {K : DerivedCategory C}
    {W : C} (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (n : ℤ) (τ : Representation R Γ U)
    (s : S)
    (g : isotypicPart τ ((cohomologyHomRepresentation R ρ σ n).comp (MonoidHom.inl Γ Δ))) :
    (cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ (s ⊗ₜ g) :
        (homologyFunctor D (-n)).obj (F.mapDerivedCategory.obj K) ⟶ F.obj W) =
      s • cohomologyHomMap F K W (-n) g :=
  rfl

/-- The edge maps on `τ`-isotypic parts for `Γ` intertwine
`abutmentIsotypicProdBaseChangeIntertwiningMap` and
`cohomologyHomIsotypicProdBaseChangeIntertwiningMap`. -/
theorem isotypicProdEdgeMap_abutmentIsotypicProdBaseChangeIntertwiningMap
    {K : DerivedCategory C} {W : C} (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (n : ℤ)
    (τ : Representation R Γ U)
    (x : S ⊗[R] isotypicPart τ ((abutmentRepresentation R ρ σ n).comp (MonoidHom.inl Γ Δ))) :
    isotypicProdIntertwiningMap (baseChangeRepresentation S τ)
        (edgeMapIntertwiningMap S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n) (abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ x) =
      cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ
        ((isotypicProdIntertwiningMap τ (edgeMapIntertwiningMap R ρ σ n)).toLinearMap.baseChange
          S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s f =>
    exact Subtype.ext
      (edgeMap_abutmentBaseChangeMap F hF K W n
        (s ⊗ₜ (f : ShiftedHom K ((singleFunctor C 0).obj W) n)))
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

variable [HasExt.{t} C] [HasExt.{t'} D]

/-! ### Degeneration isomorphisms -/

/-- **The isotypic degeneration isomorphisms commute with extension of scalars.** Under the
degeneration hypotheses for `K`, `W` and for `F K`, `F W`, the degeneration isomorphism over
`S` on `S ⊗[R] τ`-isotypic parts after `abutmentIsotypicBaseChangeMap` equals
`cohomologyHomIsotypicBaseChangeMap` after the base change of the degeneration isomorphism over
`R` on `τ`-isotypic parts. -/
theorem degenerationIsotypicEquiv_abutmentIsotypicBaseChangeMap {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    (x : S ⊗[R] isotypicPart τ (abutmentRepresentation R ρ σ n)) :
    degenerationIsotypicEquiv S b (fun i hi => mapDerivedCategory_homology_isZero F K (hK i hi))
        hW' n ((F.mapDerivedCategory.mapAut K).comp ρ) ((F.mapAut W).comp σ)
        (baseChangeRepresentation S τ) (abutmentIsotypicBaseChangeMap F hF ρ σ n τ x) =
      cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ
        ((degenerationIsotypicEquiv R b hK hW n ρ σ τ).toLinearMap.baseChange S x) :=
  isotypicEdgeMap_abutmentIsotypicBaseChangeMap F hF ρ σ n τ x

/-- Under the degeneration hypotheses, `abutmentIsotypicBaseChangeMap` is
`cohomologyHomIsotypicBaseChangeMap` transported along the isotypic degeneration isomorphisms
over `R` and over `S`. -/
theorem abutmentIsotypicBaseChangeMap_eq_degeneration {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U) :
    abutmentIsotypicBaseChangeMap F hF ρ σ n τ =
      (degenerationIsotypicEquiv S b (fun i hi => mapDerivedCategory_homology_isZero F K (hK i hi))
          hW' n ((F.mapDerivedCategory.mapAut K).comp ρ) ((F.mapAut W).comp σ)
          (baseChangeRepresentation S τ)).toLinearEquiv.symm.toLinearMap ∘ₗ
        cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ ∘ₗ
        ((degenerationIsotypicEquiv R b hK hW n ρ σ τ).toLinearEquiv.baseChange R S _
          _).toLinearMap :=
  LinearMap.ext fun x => (LinearEquiv.eq_symm_apply _).2
    (degenerationIsotypicEquiv_abutmentIsotypicBaseChangeMap F hF b hK hW hW' n ρ σ τ x)

/-- Under the degeneration hypotheses, `abutmentIsotypicBaseChangeMap` is bijective if and only
if `cohomologyHomIsotypicBaseChangeMap` is. -/
theorem abutmentIsotypicBaseChangeMap_bijective_iff {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U) :
    Function.Bijective (abutmentIsotypicBaseChangeMap F hF ρ σ n τ) ↔
      Function.Bijective (cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ) := by
  rw [abutmentIsotypicBaseChangeMap_eq_degeneration F hF b hK hW hW' n ρ σ τ]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective,
    EquivLike.bijective_comp]

/-- Under the degeneration hypotheses, `abutmentIsotypicBaseChangeMap` is injective if and only
if `cohomologyHomIsotypicBaseChangeMap` is. -/
theorem abutmentIsotypicBaseChangeMap_injective_iff {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U) :
    Function.Injective (abutmentIsotypicBaseChangeMap F hF ρ σ n τ) ↔
      Function.Injective (cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ) := by
  rw [abutmentIsotypicBaseChangeMap_eq_degeneration F hF b hK hW hW' n ρ σ τ]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective,
    EquivLike.injective_comp]

/-- Under the degeneration hypotheses, `abutmentIsotypicBaseChangeMap` is surjective if and only
if `cohomologyHomIsotypicBaseChangeMap` is. -/
theorem abutmentIsotypicBaseChangeMap_surjective_iff {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U) :
    Function.Surjective (abutmentIsotypicBaseChangeMap F hF ρ σ n τ) ↔
      Function.Surjective (cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ) := by
  rw [abutmentIsotypicBaseChangeMap_eq_degeneration F hF b hK hW hW' n ρ σ τ]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
    EquivLike.surjective_comp]

/-- Under the degeneration hypotheses, and if `cohomologyHomIsotypicBaseChangeMap` is bijective
(the hypothesis `h`), `abutmentIsotypicBaseChangeMap` as an equivalence of representations of
`Γ` from the base change of the `τ`-isotypic part of `Hom(K, W₀⟦n⟧)` to the
`S ⊗[R] τ`-isotypic part of `Hom(F K, (F W)₀⟦n⟧)`. -/
def abutmentIsotypicBaseChangeEquiv {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    (h : Function.Bijective (cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ)) :
    (baseChangeRepresentation S (isotypicRepresentation τ (abutmentRepresentation R ρ σ n))).Equiv
      (isotypicRepresentation (baseChangeRepresentation S τ)
        (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n)) :=
  (abutmentIsotypicBaseChangeIntertwiningMap F hF ρ σ n τ).ofBijective
    ((abutmentIsotypicBaseChangeMap_bijective_iff F hF b hK hW hW' n ρ σ τ).2 h)

/-- The underlying map of `abutmentIsotypicBaseChangeEquiv` is
`abutmentIsotypicBaseChangeMap`. -/
@[simp]
lemma abutmentIsotypicBaseChangeEquiv_apply {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    (h : Function.Bijective (cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ))
    (x : S ⊗[R] isotypicPart τ (abutmentRepresentation R ρ σ n)) :
    abutmentIsotypicBaseChangeEquiv F hF b hK hW hW' n ρ σ τ h x =
      abutmentIsotypicBaseChangeMap F hF ρ σ n τ x :=
  rfl

/-- **The degeneration isomorphisms on multiplicity spaces commute with extension of
scalars.** Under the degeneration hypotheses for `K`, `W` and for `F K`, `F W`,
`degenerationMultiplicityEquiv` over `S` after `abutmentMultiplicityBaseChangeMap` equals
`cohomologyHomMultiplicityBaseChangeMap` after the base change of
`degenerationMultiplicityEquiv` over `R`. -/
theorem degenerationMultiplicityEquiv_abutmentMultiplicityBaseChangeMap {K : DerivedCategory C}
    (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    (x : S ⊗[R] τ.IntertwiningMap (abutmentRepresentation R ρ σ n)) :
    degenerationMultiplicityEquiv S b
        (fun i hi => mapDerivedCategory_homology_isZero F K (hK i hi)) hW' n
        ((F.mapDerivedCategory.mapAut K).comp ρ) ((F.mapAut W).comp σ)
        (baseChangeRepresentation S τ) (abutmentMultiplicityBaseChangeMap F hF ρ σ n τ x) =
      cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ
        ((degenerationMultiplicityEquiv R b hK hW n ρ σ τ).toLinearMap.baseChange S x) :=
  multiplicityEdgeMap_abutmentMultiplicityBaseChangeMap F hF ρ σ n τ x

/-- Under the degeneration hypotheses, `abutmentMultiplicityBaseChangeMap` is
`cohomologyHomMultiplicityBaseChangeMap` transported along the degeneration isomorphisms on
multiplicity spaces over `R` and over `S`. -/
theorem abutmentMultiplicityBaseChangeMap_eq_degeneration {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U) :
    abutmentMultiplicityBaseChangeMap F hF ρ σ n τ =
      (degenerationMultiplicityEquiv S b
          (fun i hi => mapDerivedCategory_homology_isZero F K (hK i hi)) hW' n
          ((F.mapDerivedCategory.mapAut K).comp ρ) ((F.mapAut W).comp σ)
          (baseChangeRepresentation S τ)).symm.toLinearMap ∘ₗ
        cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ ∘ₗ
        ((degenerationMultiplicityEquiv R b hK hW n ρ σ τ).baseChange R S _ _).toLinearMap :=
  LinearMap.ext fun x => (LinearEquiv.eq_symm_apply _).2
    (degenerationMultiplicityEquiv_abutmentMultiplicityBaseChangeMap F hF b hK hW hW' n ρ σ τ x)

/-- Under the degeneration hypotheses, `abutmentMultiplicityBaseChangeMap` is bijective if and
only if `cohomologyHomMultiplicityBaseChangeMap` is. -/
theorem abutmentMultiplicityBaseChangeMap_bijective_iff {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U) :
    Function.Bijective (abutmentMultiplicityBaseChangeMap F hF ρ σ n τ) ↔
      Function.Bijective (cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ) := by
  rw [abutmentMultiplicityBaseChangeMap_eq_degeneration F hF b hK hW hW' n ρ σ τ]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective,
    EquivLike.bijective_comp]

/-- **The degeneration isomorphisms on invariants commute with extension of scalars.** Under
the degeneration hypotheses for `K`, `W` and for `F K`, `F W`, `degenerationInvariantsLinearEquiv`
over `S` after `abutmentInvariantsBaseChangeMap` equals `cohomologyHomInvariantsBaseChangeMap`
after the base change of `degenerationInvariantsLinearEquiv` over `R`. -/
theorem degenerationInvariantsLinearEquiv_abutmentInvariantsBaseChangeMap
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (x : S ⊗[R] (abutmentRepresentation R ρ σ n).invariants) :
    degenerationInvariantsLinearEquiv S b
        (fun i hi => mapDerivedCategory_homology_isZero F K (hK i hi)) hW' n
        ((F.mapDerivedCategory.mapAut K).comp ρ) ((F.mapAut W).comp σ)
        (abutmentInvariantsBaseChangeMap F hF ρ σ n x) =
      cohomologyHomInvariantsBaseChangeMap F hF ρ σ n
        ((degenerationInvariantsLinearEquiv R b hK hW n ρ σ).toLinearMap.baseChange S x) :=
  invariantsEdgeMap_abutmentInvariantsBaseChangeMap F hF ρ σ n x

/-- Under the degeneration hypotheses, `abutmentInvariantsBaseChangeMap` is
`cohomologyHomInvariantsBaseChangeMap` transported along the degeneration isomorphisms on
invariants over `R` and over `S`. -/
theorem abutmentInvariantsBaseChangeMap_eq_degeneration
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) :
    abutmentInvariantsBaseChangeMap F hF ρ σ n =
      (degenerationInvariantsLinearEquiv S b
          (fun i hi => mapDerivedCategory_homology_isZero F K (hK i hi)) hW' n
          ((F.mapDerivedCategory.mapAut K).comp ρ) ((F.mapAut W).comp σ)).symm.toLinearMap ∘ₗ
        cohomologyHomInvariantsBaseChangeMap F hF ρ σ n ∘ₗ
        ((degenerationInvariantsLinearEquiv R b hK hW n ρ σ).baseChange R S _ _).toLinearMap :=
  LinearMap.ext fun x => (LinearEquiv.eq_symm_apply _).2
    (degenerationInvariantsLinearEquiv_abutmentInvariantsBaseChangeMap F hF b hK hW hW' n ρ σ x)

/-- Under the degeneration hypotheses, `abutmentInvariantsBaseChangeMap` is bijective if and only
if `cohomologyHomInvariantsBaseChangeMap` is. -/
theorem abutmentInvariantsBaseChangeMap_bijective_iff
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) :
    Function.Bijective (abutmentInvariantsBaseChangeMap F hF ρ σ n) ↔
      Function.Bijective (cohomologyHomInvariantsBaseChangeMap F hF ρ σ n) := by
  rw [abutmentInvariantsBaseChangeMap_eq_degeneration F hF b hK hW hW' n ρ σ]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective,
    EquivLike.bijective_comp]

/-- Under the degeneration hypotheses, and if `cohomologyHomInvariantsBaseChangeMap` is bijective
(the hypothesis `h`), `abutmentInvariantsBaseChangeMap` as an `S`-linear equivalence from the
base change of the `Γ`-invariants of `Hom(K, W₀⟦n⟧)` to the `Γ`-invariants of
`Hom(F K, (F W)₀⟦n⟧)`. -/
def abutmentInvariantsBaseChangeEquiv
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (h : Function.Bijective (cohomologyHomInvariantsBaseChangeMap F hF ρ σ n)) :
    S ⊗[R] (abutmentRepresentation R ρ σ n).invariants ≃ₗ[S]
      (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
        ((F.mapAut W).comp σ) n).invariants :=
  LinearEquiv.ofBijective (abutmentInvariantsBaseChangeMap F hF ρ σ n)
    ((abutmentInvariantsBaseChangeMap_bijective_iff F hF b hK hW hW' n ρ σ).2 h)

/-- The underlying map of `abutmentInvariantsBaseChangeEquiv` is
`abutmentInvariantsBaseChangeMap`. -/
@[simp]
lemma abutmentInvariantsBaseChangeEquiv_apply
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (h : Function.Bijective (cohomologyHomInvariantsBaseChangeMap F hF ρ σ n))
    (x : S ⊗[R] (abutmentRepresentation R ρ σ n).invariants) :
    abutmentInvariantsBaseChangeEquiv F hF b hK hW hW' n ρ σ h x =
      abutmentInvariantsBaseChangeMap F hF ρ σ n x :=
  rfl

/-- For actions of `Γ × Δ` on `K` and `W`, under the degeneration hypotheses:
`degenerationIsotypicProdEquiv` over `S` after `abutmentIsotypicProdBaseChangeIntertwiningMap`
equals `cohomologyHomIsotypicProdBaseChangeIntertwiningMap` after the base change of
`degenerationIsotypicProdEquiv` over `R`. -/
theorem degenerationIsotypicProdEquiv_abutmentIsotypicProdBaseChangeIntertwiningMap
    {K : DerivedCategory C} (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K))
    {W : C} (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U)
    (x : S ⊗[R] isotypicPart τ ((abutmentRepresentation R ρ σ n).comp (MonoidHom.inl Γ Δ))) :
    degenerationIsotypicProdEquiv S b
        (fun i hi => mapDerivedCategory_homology_isZero F K (hK i hi)) hW' n
        ((F.mapDerivedCategory.mapAut K).comp ρ) ((F.mapAut W).comp σ)
        (baseChangeRepresentation S τ)
        (abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ x) =
      cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ
        ((degenerationIsotypicProdEquiv R b hK hW n ρ σ τ).toLinearMap.baseChange S x) :=
  isotypicProdEdgeMap_abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ x

/-- For actions of `Γ × Δ` on `K` and `W`, under the degeneration hypotheses:
`abutmentIsotypicProdBaseChangeIntertwiningMap` is
`cohomologyHomIsotypicProdBaseChangeIntertwiningMap` transported along
`degenerationIsotypicProdEquiv` over `R` and over `S`. -/
theorem abutmentIsotypicProdBaseChangeIntertwiningMap_eq_degeneration {K : DerivedCategory C}
    (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U) :
    (abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ).toLinearMap =
      (degenerationIsotypicProdEquiv S b
          (fun i hi => mapDerivedCategory_homology_isZero F K (hK i hi)) hW' n
          ((F.mapDerivedCategory.mapAut K).comp ρ) ((F.mapAut W).comp σ)
          (baseChangeRepresentation S τ)).toLinearEquiv.symm.toLinearMap ∘ₗ
        (cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ).toLinearMap ∘ₗ
        ((degenerationIsotypicProdEquiv R b hK hW n ρ σ τ).toLinearEquiv.baseChange R S _
          _).toLinearMap :=
  LinearMap.ext fun x => (LinearEquiv.eq_symm_apply _).2
    (degenerationIsotypicProdEquiv_abutmentIsotypicProdBaseChangeIntertwiningMap F hF b hK hW
      hW' n ρ σ τ x)

/-- For actions of `Γ × Δ` on `K` and `W`, under the degeneration hypotheses:
`abutmentIsotypicProdBaseChangeIntertwiningMap` is bijective if and only if
`cohomologyHomIsotypicProdBaseChangeIntertwiningMap` is. -/
theorem abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_iff {K : DerivedCategory C}
    (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U) :
    Function.Bijective (abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ) ↔
      Function.Bijective (cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ) := by
  change
    Function.Bijective (abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ).toLinearMap ↔
      Function.Bijective
        (cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ).toLinearMap
  rw [abutmentIsotypicProdBaseChangeIntertwiningMap_eq_degeneration F hF b hK hW hW' n ρ σ τ]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective,
    EquivLike.bijective_comp]

/-- For actions of `Γ × Δ` on `K` and `W`, under the degeneration hypotheses and if
`cohomologyHomIsotypicProdBaseChangeIntertwiningMap` is bijective (the hypothesis `h`):
`abutmentIsotypicProdBaseChangeIntertwiningMap` as an equivalence of representations of `Δ`. -/
def abutmentIsotypicProdBaseChangeEquiv {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U)
    (h : Function.Bijective (cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ)) :
    (baseChangeRepresentation S
        (isotypicProdRepresentation τ (abutmentRepresentation R ρ σ n))).Equiv
      (isotypicProdRepresentation (baseChangeRepresentation S τ)
        (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
          ((F.mapAut W).comp σ) n)) :=
  (abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ).ofBijective
    ((abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_iff F hF b hK hW hW' n ρ σ τ).2 h)

/-- The underlying map of `abutmentIsotypicProdBaseChangeEquiv` is
`abutmentIsotypicProdBaseChangeIntertwiningMap`. -/
@[simp]
lemma abutmentIsotypicProdBaseChangeEquiv_apply {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U)
    (h : Function.Bijective (cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ))
    (x : S ⊗[R] isotypicPart τ ((abutmentRepresentation R ρ σ n).comp (MonoidHom.inl Γ Δ))) :
    abutmentIsotypicProdBaseChangeEquiv F hF b hK hW hW' n ρ σ τ h x =
      abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ x :=
  rfl

end Derived

section Smooth

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S] [Module.Flat R S]
  (G : Type uG) [Group G] [TopologicalSpace G]
  [HasDerivedCategory.{s} (SmoothRep.{uR, uG, w} R G)]
  [HasDerivedCategory.{s'} (SmoothRep.{uS, uG, max uS w} S G)]
  {Γ : Type uΓ} [Group Γ] {U : Type*} [AddCommGroup U] [Module R U]

open DerivedCategory

/-- `abutmentInvariantsBaseChangeMap` for extension of scalars of smooth representations along a
flat `R → S`. -/
def smoothAbutmentInvariantsBaseChangeMap {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)}
    {W : SmoothRep.{uR, uG, w} R G} (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) :
    S ⊗[R] (abutmentRepresentation R ρ σ n).invariants →ₗ[S]
      (abutmentRepresentation S
        (((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
        (((smoothRepExtendScalars.{w} R S G).mapAut W).comp σ) n).invariants :=
  abutmentInvariantsBaseChangeMap (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) ρ σ n

/-- `cohomologyHomInvariantsBaseChangeMap` for extension of scalars of smooth representations
along a flat `R → S`. -/
def smoothCohomologyHomInvariantsBaseChangeMap {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)}
    {W : SmoothRep.{uR, uG, w} R G} (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) :
    S ⊗[R] (cohomologyHomRepresentation R ρ σ n).invariants →ₗ[S]
      (cohomologyHomRepresentation S
        (((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
        (((smoothRepExtendScalars.{w} R S G).mapAut W).comp σ) n).invariants :=
  cohomologyHomInvariantsBaseChangeMap (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) ρ σ n

variable [HasExt.{t} (SmoothRep.{uR, uG, w} R G)] [HasExt.{t'} (SmoothRep.{uS, uG, max uS w} S G)]

/-- `abutmentIsotypicBaseChangeMap_bijective_iff` for extension of scalars of smooth
representations along a flat `R → S`. -/
theorem smoothAbutmentIsotypicBaseChangeMap_bijective_iff
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K))
    {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U) :
    Function.Bijective
        (smoothAbutmentIsotypicBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n τ) ↔
      Function.Bijective
        (smoothCohomologyHomIsotypicBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n τ) :=
  abutmentIsotypicBaseChangeMap_bijective_iff (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) b hK hW hW' n ρ σ τ

/-- `abutmentIsotypicBaseChangeEquiv` for extension of scalars of smooth representations along a
flat `R → S`: under the degeneration hypotheses and if `smoothCohomologyHomIsotypicBaseChangeMap`
is bijective (the hypothesis `h`), `smoothAbutmentIsotypicBaseChangeMap` as an equivalence of
representations of `Γ`. -/
def smoothAbutmentIsotypicBaseChangeEquiv
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K))
    {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    (h : Function.Bijective
      (smoothCohomologyHomIsotypicBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n τ)) :
    (baseChangeRepresentation S
        (isotypicRepresentation τ (abutmentRepresentation R ρ σ n))).Equiv
      (isotypicRepresentation (baseChangeRepresentation S τ)
        (abutmentRepresentation S
          (((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
          (((smoothRepExtendScalars.{w} R S G).mapAut W).comp σ) n)) :=
  abutmentIsotypicBaseChangeEquiv (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) b hK hW hW' n ρ σ τ h

/-- `abutmentInvariantsBaseChangeMap_bijective_iff` for extension of scalars of smooth
representations along a flat `R → S`. -/
theorem smoothAbutmentInvariantsBaseChangeMap_bijective_iff
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K))
    {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W) :
    Function.Bijective
        (smoothAbutmentInvariantsBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n) ↔
      Function.Bijective
        (smoothCohomologyHomInvariantsBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n) :=
  abutmentInvariantsBaseChangeMap_bijective_iff (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) b hK hW hW' n ρ σ

/-- `abutmentInvariantsBaseChangeEquiv` for extension of scalars of smooth representations along
a flat `R → S`: under the degeneration hypotheses and if
`smoothCohomologyHomInvariantsBaseChangeMap` is bijective (the hypothesis `h`),
`smoothAbutmentInvariantsBaseChangeMap` as an `S`-linear equivalence. -/
def smoothAbutmentInvariantsBaseChangeEquiv
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
    (h : Function.Bijective
      (smoothCohomologyHomInvariantsBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n)) :
    S ⊗[R] (abutmentRepresentation R ρ σ n).invariants ≃ₗ[S]
      (abutmentRepresentation S
        (((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
        (((smoothRepExtendScalars.{w} R S G).mapAut W).comp σ) n).invariants :=
  abutmentInvariantsBaseChangeEquiv (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) b hK hW hW' n ρ σ h

end Smooth

end HyperextScalarExtension

end Langlands.Cohomology
