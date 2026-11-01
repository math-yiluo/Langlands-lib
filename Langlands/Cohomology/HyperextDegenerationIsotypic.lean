import Langlands.Cohomology.HyperextDegenerationEquivariance
import Langlands.Cohomology.HyperextEdgeMapLinear
import Langlands.Cohomology.HyperextDegeneration.Proof
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Isotypic parts of the degeneration isomorphism

Let `R` be a commutative ring, `C` an `R`-linear abelian category, `K` an object of its derived
category and `W` an object of `C`, and let a group `Γ` act on `K` and on `W` by automorphisms.
Write `W₀` for `W` placed in degree `0`. This module makes the actions of
`HyperextDegenerationEquivariance` on `Hom(K, W₀⟦n⟧)` and on `Hom(H^{-n} K, W)` into
`R`-linear representations and restricts the degeneration isomorphism to isotypic parts.

* `isotypicPart τ ρ`: for representations `τ` and `ρ` of `Γ` over `R`, the sum of the images of
  all intertwining maps `τ → ρ`, with its representation `isotypicRepresentation τ ρ`; it is
  functorial for intertwining maps (`isotypicIntertwiningMap`, `isotypicEquiv`). For the trivial
  representation on `R` it is the submodule of invariants (`isotypicPart_trivial`).
* `intertwiningMapEquiv` and `invariantsLinearEquiv`: an equivalence of representations induces
  `R`-linear equivalences of multiplicity spaces `Hom_Γ(τ, -)` and of invariants.
* `isotypicProdRepresentation τ ρ`: for a representation `ρ` of `Γ × Δ`, the representation of
  `Δ` on the `τ`-isotypic part of the restriction of `ρ` to `Γ` (`isotypicProdEquiv`).
* `homRepresentation`, `abutmentRepresentation`, `cohomologyHomRepresentation`,
  `edgeMapIntertwiningMap`: the representations on groups of morphisms and the edge map as an
  intertwining map.
* `degenerationEquiv`: the edge map as an equivalence of representations, under the hypotheses
  of `HyperextDegenerationStatement` (bounded-above cohomology of `K`, vanishing of
  `Ext^i(H^k K, W)` for `i > 0`). Bijectivity is the Library's theorem
  `hyperextDegenerationStatement_proof`, so no hypothesis `h` is needed.
* `degenerationIsotypicEquiv`, `degenerationMultiplicityEquiv`,
  `degenerationInvariantsLinearEquiv`, `degenerationIsotypicProdEquiv`, and the smooth variants
  `smoothDegeneration…` with the `Ext` hypothesis stated with smooth Ext groups.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

namespace HyperextAbutment

universe w' w v u uΓ

section Isotypic

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] {U V W : Type*}
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The `τ`-isotypic part of a representation `ρ`: the sum of the images of all intertwining
maps `τ → ρ`. -/
def isotypicPart (τ : Representation R Γ U) (ρ : Representation R Γ V) : Submodule R V :=
  ⨆ f : τ.IntertwiningMap ρ, LinearMap.range f.toLinearMap

variable (τ : Representation R Γ U)

/-- The range of every intertwining map `τ → ρ` lies in the `τ`-isotypic part of `ρ`. -/
lemma range_le_isotypicPart (ρ : Representation R Γ V) (f : τ.IntertwiningMap ρ) :
    LinearMap.range f.toLinearMap ≤ isotypicPart τ ρ :=
  le_iSup (fun f : τ.IntertwiningMap ρ => LinearMap.range f.toLinearMap) f

variable {τ} in
/-- Every value of an intertwining map `τ → ρ` lies in the `τ`-isotypic part of `ρ`. -/
lemma apply_mem_isotypicPart {ρ : Representation R Γ V} (f : τ.IntertwiningMap ρ) (u : U) :
    f u ∈ isotypicPart τ ρ :=
  range_le_isotypicPart τ ρ f (LinearMap.mem_range_self f.toLinearMap u)

/-- The `τ`-isotypic part of `ρ` lies in a submodule `N` iff all values of all intertwining
maps `τ → ρ` lie in `N`. -/
lemma isotypicPart_le_iff (ρ : Representation R Γ V) {N : Submodule R V} :
    isotypicPart τ ρ ≤ N ↔ ∀ (f : τ.IntertwiningMap ρ) (u : U), f u ∈ N := by
  refine ⟨fun h f u => h (apply_mem_isotypicPart f u), fun h => iSup_le fun f => ?_⟩
  intro x hx
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hx
  exact h f u

variable {ρ : Representation R Γ V} {σ : Representation R Γ W}

/-- An intertwining map `ρ → σ` sends the `τ`-isotypic part of `ρ` into the `τ`-isotypic part
of `σ`. -/
lemma intertwiningMap_apply_mem_isotypicPart (φ : ρ.IntertwiningMap σ) {v : V}
    (hv : v ∈ isotypicPart τ ρ) : φ v ∈ isotypicPart τ σ :=
  (isotypicPart_le_iff τ ρ (N := (isotypicPart τ σ).comap φ.toLinearMap)).2
    (fun f u => apply_mem_isotypicPart (φ.comp f) u) hv

/-- The image of the `τ`-isotypic part of `ρ` under an intertwining map `ρ → σ` lies in the
`τ`-isotypic part of `σ`. -/
lemma map_isotypicPart_le (φ : ρ.IntertwiningMap σ) :
    (isotypicPart τ ρ).map φ.toLinearMap ≤ isotypicPart τ σ :=
  Submodule.map_le_iff_le_comap.2 fun _ hv => intertwiningMap_apply_mem_isotypicPart τ φ hv

/-- The `τ`-isotypic part of `ρ` is stable under the action of `Γ`. -/
lemma apply_mem_isotypicPart_of_mem (γ : Γ) {v : V} (hv : v ∈ isotypicPart τ ρ) :
    ρ γ v ∈ isotypicPart τ ρ := by
  refine (isotypicPart_le_iff τ ρ (N := (isotypicPart τ ρ).comap (ρ γ))).2 (fun f u => ?_) hv
  change ρ γ (f u) ∈ isotypicPart τ ρ
  rw [← Representation.IntertwiningMap.isIntertwining]
  exact apply_mem_isotypicPart f (τ γ u)

variable (ρ) in
/-- The `τ`-isotypic part of `ρ` as a subrepresentation of `ρ`. -/
def isotypicSubrepresentation : Subrepresentation ρ where
  toSubmodule := isotypicPart τ ρ
  apply_mem_toSubmodule γ _ hv := apply_mem_isotypicPart_of_mem τ γ hv

variable (ρ) in
/-- The representation of `Γ` on the `τ`-isotypic part of `ρ`, restricted from `ρ`. -/
def isotypicRepresentation : Representation R Γ (isotypicPart τ ρ) :=
  (isotypicSubrepresentation τ ρ).toRepresentation

variable (ρ) in
/-- `Γ` acts on the `τ`-isotypic part of `ρ` through `ρ`. -/
@[simp]
lemma coe_isotypicRepresentation_apply (γ : Γ) (x : isotypicPart τ ρ) :
    (isotypicRepresentation τ ρ γ x : V) = ρ γ x :=
  rfl

/-- The restriction of an intertwining map `ρ → σ` to the `τ`-isotypic parts. -/
def isotypicIntertwiningMap (φ : ρ.IntertwiningMap σ) :
    (isotypicRepresentation τ ρ).IntertwiningMap (isotypicRepresentation τ σ) where
  toLinearMap :=
    φ.toLinearMap.restrict (fun _ hv => intertwiningMap_apply_mem_isotypicPart τ φ hv)
  isIntertwining' γ := LinearMap.ext fun x =>
    Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ φ γ x)

/-- `isotypicIntertwiningMap τ φ` is `φ` on underlying elements. -/
@[simp]
lemma coe_isotypicIntertwiningMap_apply (φ : ρ.IntertwiningMap σ) (x : isotypicPart τ ρ) :
    (isotypicIntertwiningMap τ φ x : W) = φ x :=
  rfl

/-- An equivalence of representations `ρ ≃ σ` restricts to an equivalence of the
representations on the `τ`-isotypic parts. -/
def isotypicEquiv (e : ρ.Equiv σ) :
    (isotypicRepresentation τ ρ).Equiv (isotypicRepresentation τ σ) :=
  Representation.Equiv.mk
    { toFun := fun x =>
        ⟨e x, intertwiningMap_apply_mem_isotypicPart τ e.toIntertwiningMap x.2⟩
      invFun := fun y =>
        ⟨e.symm y, intertwiningMap_apply_mem_isotypicPart τ e.symm.toIntertwiningMap y.2⟩
      map_add' := fun x y => Subtype.ext (map_add e (x : V) y)
      map_smul' := fun r x => Subtype.ext (map_smul e r (x : V))
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }
    (fun γ => LinearMap.ext fun x =>
      Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap γ x))

/-- `isotypicEquiv τ e` is `e` on underlying elements. -/
@[simp]
lemma coe_isotypicEquiv_apply (e : ρ.Equiv σ) (x : isotypicPart τ ρ) :
    (isotypicEquiv τ e x : W) = e x :=
  rfl

/-- An equivalence of representations `ρ ≃ σ` maps the `τ`-isotypic part of `ρ` onto the
`τ`-isotypic part of `σ`. -/
lemma map_isotypicPart_eq (e : ρ.Equiv σ) :
    (isotypicPart τ ρ).map e.toIntertwiningMap.toLinearMap = isotypicPart τ σ := by
  refine le_antisymm (map_isotypicPart_le τ e.toIntertwiningMap) fun y hy => ?_
  exact ⟨e.symm y, intertwiningMap_apply_mem_isotypicPart τ e.symm.toIntertwiningMap hy,
    e.apply_symm_apply y⟩

/-- Composition with an equivalence of representations `ρ ≃ σ` is an `R`-linear equivalence
from the intertwining maps `τ → ρ` to the intertwining maps `τ → σ` (the multiplicity
spaces of `τ`). -/
def intertwiningMapEquiv (e : ρ.Equiv σ) : τ.IntertwiningMap ρ ≃ₗ[R] τ.IntertwiningMap σ where
  toFun f := e.toIntertwiningMap.comp f
  invFun g := e.symm.toIntertwiningMap.comp g
  map_add' f g := by
    ext u
    exact map_add e (f u) (g u)
  map_smul' r f := by
    ext u
    exact map_smul e r (f u)
  left_inv f := by
    ext u
    exact e.symm_apply_apply (f u)
  right_inv g := by
    ext u
    exact e.apply_symm_apply (g u)

/-- `intertwiningMapEquiv τ e f` is `e ∘ f`. -/
@[simp]
lemma intertwiningMapEquiv_apply_apply (e : ρ.Equiv σ) (f : τ.IntertwiningMap ρ) (u : U) :
    intertwiningMapEquiv τ e f u = e (f u) :=
  rfl

omit τ in
/-- An equivalence of representations `ρ ≃ σ` restricts to an `R`-linear equivalence of the
submodules of `Γ`-invariant elements. -/
def invariantsLinearEquiv (e : ρ.Equiv σ) : ρ.invariants ≃ₗ[R] σ.invariants where
  toFun x := ⟨e x, (Representation.mem_invariants σ _).2 fun γ =>
    (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap γ x).symm.trans
      (congrArg e ((Representation.mem_invariants ρ _).1 x.2 γ))⟩
  invFun y := ⟨e.symm y, (Representation.mem_invariants ρ _).2 fun γ =>
    (Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap γ y).symm.trans
      (congrArg e.symm ((Representation.mem_invariants σ _).1 y.2 γ))⟩
  map_add' x y := Subtype.ext (map_add e (x : V) y)
  map_smul' r x := Subtype.ext (map_smul e r (x : V))
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)

omit τ in
/-- `invariantsLinearEquiv e` is `e` on underlying elements. -/
@[simp]
lemma coe_invariantsLinearEquiv_apply (e : ρ.Equiv σ) (x : ρ.invariants) :
    (invariantsLinearEquiv e x : W) = e x :=
  rfl

omit τ in
variable (ρ) in
/-- For a `Γ`-invariant element `v`, the intertwining map from the trivial representation on
`R` to `ρ` sending `r` to `r • v`. -/
def invariantsIntertwiningMap {v : V} (hv : v ∈ ρ.invariants) :
    (Representation.trivial R Γ R).IntertwiningMap ρ where
  toLinearMap := LinearMap.toSpanSingleton R V v
  isIntertwining' γ := LinearMap.ext fun r => by
    simp only [LinearMap.coe_comp, Function.comp_apply, Representation.trivial_apply,
      LinearMap.toSpanSingleton_apply, map_smul, (Representation.mem_invariants ρ v).1 hv γ]

omit τ in
variable (ρ) in
/-- The isotypic part for the trivial representation of `Γ` on `R` is the submodule of
`Γ`-invariant elements. -/
lemma isotypicPart_trivial : isotypicPart (Representation.trivial R Γ R) ρ = ρ.invariants := by
  refine le_antisymm ((isotypicPart_le_iff _ ρ).2 fun f r =>
    (Representation.mem_invariants ρ _).2 fun γ => ?_) fun v hv => ?_
  · rw [← Representation.IntertwiningMap.isIntertwining, Representation.trivial_apply]
  · have h : invariantsIntertwiningMap ρ hv 1 = v := one_smul R v
    exact h ▸ apply_mem_isotypicPart _ 1

end Isotypic

section Product

variable {R : Type*} [CommRing R] {Γ Δ : Type*} [Group Γ] [Group Δ] {U V W : Type*}
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- An equivalence of representations of `Γ` is an equivalence of the representations of `Γ'`
obtained by composing with a group homomorphism `φ : Γ' →* Γ`. -/
def equivComp {Γ' : Type*} [Group Γ'] {ρ : Representation R Γ V} {σ : Representation R Γ W}
    (e : ρ.Equiv σ) (φ : Γ' →* Γ) : Representation.Equiv (ρ.comp φ) (σ.comp φ) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v =>
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (φ g) v

/-- For a representation `ρ` of `Γ × Δ` and `δ : Δ`, the action `ρ (1, δ)` as an intertwining
map of the restriction of `ρ` to `Γ`. -/
def inrIntertwiningMap (ρ : Representation R (Γ × Δ) V) (δ : Δ) :
    Representation.IntertwiningMap (ρ.comp (MonoidHom.inl Γ Δ)) (ρ.comp (MonoidHom.inl Γ Δ)) where
  toLinearMap := ρ (1, δ)
  isIntertwining' γ := by
    change ρ (1, δ) * ρ (γ, 1) = ρ (γ, 1) * ρ (1, δ)
    rw [← map_mul, ← map_mul]
    simp only [Prod.mk_mul_mk, one_mul, mul_one]

variable (τ : Representation R Γ U)

/-- For a representation `ρ` of `Γ × Δ`, the `τ`-isotypic part of the restriction of `ρ` to `Γ`
as a subrepresentation of the restriction of `ρ` to `Δ`. -/
def isotypicProdSubrepresentation (ρ : Representation R (Γ × Δ) V) :
    Subrepresentation (ρ.comp (MonoidHom.inr Γ Δ)) where
  toSubmodule := isotypicPart τ (ρ.comp (MonoidHom.inl Γ Δ))
  apply_mem_toSubmodule δ _ hv :=
    intertwiningMap_apply_mem_isotypicPart τ (inrIntertwiningMap ρ δ) hv

/-- For a representation `ρ` of `Γ × Δ`, the representation of `Δ` on the `τ`-isotypic part
of the restriction of `ρ` to `Γ`. -/
def isotypicProdRepresentation (ρ : Representation R (Γ × Δ) V) :
    Representation R Δ (isotypicPart τ (ρ.comp (MonoidHom.inl Γ Δ))) :=
  (isotypicProdSubrepresentation τ ρ).toRepresentation

/-- `δ : Δ` acts on the `τ`-isotypic part through `ρ (1, δ)`. -/
@[simp]
lemma coe_isotypicProdRepresentation_apply (ρ : Representation R (Γ × Δ) V) (δ : Δ)
    (x : isotypicPart τ (ρ.comp (MonoidHom.inl Γ Δ))) :
    (isotypicProdRepresentation τ ρ δ x : V) = ρ (1, δ) x :=
  rfl

/-- An equivalence of representations of `Γ × Δ` restricts to an equivalence of the
representations of `Δ` on the `τ`-isotypic parts for `Γ`. -/
def isotypicProdEquiv {ρ : Representation R (Γ × Δ) V} {σ : Representation R (Γ × Δ) W}
    (e : ρ.Equiv σ) : (isotypicProdRepresentation τ ρ).Equiv (isotypicProdRepresentation τ σ) :=
  Representation.Equiv.mk (isotypicEquiv τ (equivComp e (MonoidHom.inl Γ Δ))).toLinearEquiv
    fun δ => LinearMap.ext fun x =>
      Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (1, δ) x)

/-- `isotypicProdEquiv τ e` is `e` on underlying elements. -/
@[simp]
lemma coe_isotypicProdEquiv_apply {ρ : Representation R (Γ × Δ) V}
    {σ : Representation R (Γ × Δ) W} (e : ρ.Equiv σ)
    (x : isotypicPart τ (ρ.comp (MonoidHom.inl Γ Δ))) :
    (isotypicProdEquiv τ e x : W) = e x :=
  rfl

end Product

section HomRepresentation

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {Γ : Type uΓ} [Group Γ]

/-- For an `R`-linear category, actions `ρ : Γ →* Aut X` and `σ : Γ →* Aut Y` induce the
representation of `Γ` on `X ⟶ Y` sending `γ` to `f ↦ (ρ γ)⁻¹ ≫ f ≫ σ γ`; its underlying
additive action is `homAction ρ σ`. -/
def homRepresentation {X Y : C} (ρ : Γ →* Aut X) (σ : Γ →* Aut Y) :
    Representation R Γ (X ⟶ Y) where
  toFun γ :=
    { toFun := homAction ρ σ γ
      map_add' := map_add (homAction ρ σ γ)
      map_smul' := fun r f => by
        change (ρ γ).inv ≫ (r • f) ≫ (σ γ).hom = r • ((ρ γ).inv ≫ f ≫ (σ γ).hom)
        rw [Linear.smul_comp, Linear.comp_smul] }
  map_one' := LinearMap.ext fun f => DFunLike.congr_fun (map_one (homAction ρ σ)) f
  map_mul' γ δ := LinearMap.ext fun f => DFunLike.congr_fun (map_mul (homAction ρ σ) γ δ) f

/-- `γ` sends `f` to `(ρ γ).inv ≫ f ≫ (σ γ).hom`. -/
lemma homRepresentation_apply {X Y : C} (ρ : Γ →* Aut X) (σ : Γ →* Aut Y) (γ : Γ)
    (f : X ⟶ Y) : homRepresentation R ρ σ γ f = (ρ γ).inv ≫ f ≫ (σ γ).hom :=
  rfl

end HomRepresentation

section Derived

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{w} C] {Γ : Type uΓ} [Group Γ]

open DerivedCategory

/-- The representation of `Γ` on the abutment `Hom(K, W₀⟦n⟧)` with underlying additive action
`abutmentAction ρ σ n`. -/
def abutmentRepresentation {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (n : ℤ) : Representation R Γ (ShiftedHom K ((singleFunctor C 0).obj W) n) :=
  homRepresentation R ρ (((singleFunctor C 0 ⋙ shiftFunctor (DerivedCategory C) n).mapAut W).comp σ)

/-- The representation of `Γ` on `Hom(H^{-n} K, W)` with underlying additive action
`cohomologyHomAction ρ σ n`. -/
def cohomologyHomRepresentation {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) : Representation R Γ ((homologyFunctor C (-n)).obj K ⟶ W) :=
  homRepresentation R (((homologyFunctor C (-n)).mapAut K).comp ρ) σ

/-- `abutmentRepresentation` acts by `abutmentAction`. -/
lemma abutmentRepresentation_apply {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (γ : Γ) (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    abutmentRepresentation R ρ σ n γ f = abutmentAction ρ σ n γ f :=
  rfl

/-- `cohomologyHomRepresentation` acts by `cohomologyHomAction`. -/
lemma cohomologyHomRepresentation_apply {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (γ : Γ) (g : (homologyFunctor C (-n)).obj K ⟶ W) :
    cohomologyHomRepresentation R ρ σ n γ g = cohomologyHomAction ρ σ n γ g :=
  rfl

/-- The edge map `Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` as an intertwining map of
representations of `Γ`. -/
def edgeMapIntertwiningMap {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) :
    (abutmentRepresentation R ρ σ n).IntertwiningMap (cohomologyHomRepresentation R ρ σ n) where
  toLinearMap := edgeMapLinearMap R K W n
  isIntertwining' γ := LinearMap.ext fun f => edgeMap_abutmentAction ρ σ n γ f

/-- `edgeMapIntertwiningMap R ρ σ n` is the edge map. -/
@[simp]
lemma edgeMapIntertwiningMap_apply {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    edgeMapIntertwiningMap R ρ σ n f = HyperextDegeneration.edgeMap K W n f :=
  rfl

variable [HasExt.{w'} C]

/-- The degeneration isomorphism as an equivalence of representations of `Γ`: when the
cohomology of `K` vanishes above `b` and `Ext^i(H^k K, W)` vanishes for all `k` and all `i > 0`,
the edge map is an equivalence from `Hom(K, W₀⟦n⟧)` to `Hom(H^{-n} K, W)`. Bijectivity is the
Library's theorem `hyperextDegenerationStatement_proof`. -/
def degenerationEquiv {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) :
    (abutmentRepresentation R ρ σ n).Equiv (cohomologyHomRepresentation R ρ σ n) :=
  Representation.Equiv.mk
    (degenerationLinearEquiv R (hyperextDegenerationStatement_proof C) K b hK W hW n)
    fun γ => LinearMap.ext fun f => edgeMap_abutmentAction ρ σ n γ f

/-- `degenerationEquiv` is the edge map. -/
@[simp]
lemma degenerationEquiv_apply {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    degenerationEquiv R b hK hW n ρ σ f = HyperextDegeneration.edgeMap K W n f :=
  rfl

/-- The inverse of `degenerationEquiv`, followed by the edge map, is the identity. -/
@[simp]
lemma edgeMap_degenerationEquiv_symm_apply {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (g : (homologyFunctor C (-n)).obj K ⟶ W) :
    HyperextDegeneration.edgeMap K W n ((degenerationEquiv R b hK hW n ρ σ).symm g) = g :=
  (degenerationEquiv R b hK hW n ρ σ).apply_symm_apply g

variable {U : Type*} [AddCommGroup U] [Module R U]

/-- The degeneration isomorphism restricted to `τ`-isotypic parts: an equivalence of
representations of `Γ` from the `τ`-isotypic part of `Hom(K, W₀⟦n⟧)` to the `τ`-isotypic part
of `Hom(H^{-n} K, W)`, given by the edge map. -/
def degenerationIsotypicEquiv {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U) :
    (isotypicRepresentation τ (abutmentRepresentation R ρ σ n)).Equiv
      (isotypicRepresentation τ (cohomologyHomRepresentation R ρ σ n)) :=
  isotypicEquiv τ (degenerationEquiv R b hK hW n ρ σ)

/-- `degenerationIsotypicEquiv` is the edge map on underlying morphisms. -/
@[simp]
lemma coe_degenerationIsotypicEquiv_apply {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    (f : isotypicPart τ (abutmentRepresentation R ρ σ n)) :
    (degenerationIsotypicEquiv R b hK hW n ρ σ τ f : (homologyFunctor C (-n)).obj K ⟶ W) =
      HyperextDegeneration.edgeMap K W n f :=
  rfl

/-- The degeneration isomorphism on multiplicity spaces: composition with the edge map is an
`R`-linear equivalence from the intertwining maps `τ → Hom(K, W₀⟦n⟧)` to the intertwining maps
`τ → Hom(H^{-n} K, W)`. -/
def degenerationMultiplicityEquiv {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U) :
    τ.IntertwiningMap (abutmentRepresentation R ρ σ n) ≃ₗ[R]
      τ.IntertwiningMap (cohomologyHomRepresentation R ρ σ n) :=
  intertwiningMapEquiv τ (degenerationEquiv R b hK hW n ρ σ)

/-- `degenerationMultiplicityEquiv` is composition with the edge map. -/
@[simp]
lemma degenerationMultiplicityEquiv_apply_apply {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U)
    (f : τ.IntertwiningMap (abutmentRepresentation R ρ σ n)) (u : U) :
    degenerationMultiplicityEquiv R b hK hW n ρ σ τ f u = HyperextDegeneration.edgeMap K W n (f u) :=
  rfl

/-- The degeneration isomorphism restricted to `Γ`-invariants: an `R`-linear equivalence from
the `Γ`-invariant elements of `Hom(K, W₀⟦n⟧)` to the `Γ`-invariant elements of
`Hom(H^{-n} K, W)`, given by the edge map. -/
def degenerationInvariantsLinearEquiv {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) :
    (abutmentRepresentation R ρ σ n).invariants ≃ₗ[R]
      (cohomologyHomRepresentation R ρ σ n).invariants :=
  invariantsLinearEquiv (degenerationEquiv R b hK hW n ρ σ)

/-- `degenerationInvariantsLinearEquiv` is the edge map on underlying morphisms. -/
@[simp]
lemma coe_degenerationInvariantsLinearEquiv_apply {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (f : (abutmentRepresentation R ρ σ n).invariants) :
    (degenerationInvariantsLinearEquiv R b hK hW n ρ σ f : (homologyFunctor C (-n)).obj K ⟶ W) =
      HyperextDegeneration.edgeMap K W n f :=
  rfl

/-- For commuting actions of two groups, given by actions of `Γ × Δ` on `K` and `W`: the
degeneration isomorphism restricted to the `τ`-isotypic parts for `Γ`, as an equivalence of the
representations of `Δ` on these parts. -/
def degenerationIsotypicProdEquiv {Δ : Type*} [Group Δ] {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U) :
    (isotypicProdRepresentation τ (abutmentRepresentation R ρ σ n)).Equiv
      (isotypicProdRepresentation τ (cohomologyHomRepresentation R ρ σ n)) :=
  isotypicProdEquiv τ (degenerationEquiv R b hK hW n ρ σ)

/-- `degenerationIsotypicProdEquiv` is the edge map on underlying morphisms. -/
@[simp]
lemma coe_degenerationIsotypicProdEquiv_apply {Δ : Type*} [Group Δ] {K : DerivedCategory C}
    (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U)
    (f : isotypicPart τ ((abutmentRepresentation R ρ σ n).comp (MonoidHom.inl Γ Δ))) :
    (degenerationIsotypicProdEquiv R b hK hW n ρ σ τ f : (homologyFunctor C (-n)).obj K ⟶ W) =
      HyperextDegeneration.edgeMap K W n f :=
  rfl

end Derived

section Smooth

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R G)]
  [HasExt.{w'} (SmoothRep.{u, u, u} R G)] {Γ : Type uΓ} [Group Γ]
  {U : Type*} [AddCommGroup U] [Module R U]

open DerivedCategory

/-- `degenerationEquiv` for smooth representations, with the `Ext` hypothesis stated with the
smooth Ext groups. -/
def smoothDegenerationEquiv {K : DerivedCategory (SmoothRep.{u, u, u} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : SmoothRep.{u, u, u} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton ((SmoothExt.ext R G ((homologyFunctor _ k).obj K) i).obj W)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) :
    (abutmentRepresentation R ρ σ n).Equiv (cohomologyHomRepresentation R ρ σ n) :=
  degenerationEquiv R b hK (subsingleton_ext_of_smoothExt R G K W hW) n ρ σ

/-- `smoothDegenerationEquiv` is the edge map. -/
@[simp]
lemma smoothDegenerationEquiv_apply {K : DerivedCategory (SmoothRep.{u, u, u} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : SmoothRep.{u, u, u} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton ((SmoothExt.ext R G ((homologyFunctor _ k).obj K) i).obj W)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (f : ShiftedHom K ((singleFunctor _ 0).obj W) n) :
    smoothDegenerationEquiv R G b hK hW n ρ σ f = HyperextDegeneration.edgeMap K W n f :=
  rfl

/-- `degenerationIsotypicEquiv` for smooth representations, with the `Ext` hypothesis stated
with the smooth Ext groups. -/
def smoothDegenerationIsotypicEquiv {K : DerivedCategory (SmoothRep.{u, u, u} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : SmoothRep.{u, u, u} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton ((SmoothExt.ext R G ((homologyFunctor _ k).obj K) i).obj W)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U) :
    (isotypicRepresentation τ (abutmentRepresentation R ρ σ n)).Equiv
      (isotypicRepresentation τ (cohomologyHomRepresentation R ρ σ n)) :=
  isotypicEquiv τ (smoothDegenerationEquiv R G b hK hW n ρ σ)

/-- `degenerationMultiplicityEquiv` for smooth representations, with the `Ext` hypothesis
stated with the smooth Ext groups. -/
def smoothDegenerationMultiplicityEquiv {K : DerivedCategory (SmoothRep.{u, u, u} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : SmoothRep.{u, u, u} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton ((SmoothExt.ext R G ((homologyFunctor _ k).obj K) i).obj W)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (τ : Representation R Γ U) :
    τ.IntertwiningMap (abutmentRepresentation R ρ σ n) ≃ₗ[R]
      τ.IntertwiningMap (cohomologyHomRepresentation R ρ σ n) :=
  intertwiningMapEquiv τ (smoothDegenerationEquiv R G b hK hW n ρ σ)

/-- `degenerationInvariantsLinearEquiv` for smooth representations, with the `Ext` hypothesis
stated with the smooth Ext groups. -/
def smoothDegenerationInvariantsLinearEquiv {K : DerivedCategory (SmoothRep.{u, u, u} R G)}
    (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K))
    {W : SmoothRep.{u, u, u} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton ((SmoothExt.ext R G ((homologyFunctor _ k).obj K) i).obj W)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) :
    (abutmentRepresentation R ρ σ n).invariants ≃ₗ[R]
      (cohomologyHomRepresentation R ρ σ n).invariants :=
  invariantsLinearEquiv (smoothDegenerationEquiv R G b hK hW n ρ σ)

/-- `degenerationIsotypicProdEquiv` for smooth representations, with the `Ext` hypothesis
stated with the smooth Ext groups. -/
def smoothDegenerationIsotypicProdEquiv {Δ : Type*} [Group Δ]
    {K : DerivedCategory (SmoothRep.{u, u, u} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : SmoothRep.{u, u, u} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton ((SmoothExt.ext R G ((homologyFunctor _ k).obj K) i).obj W)) (n : ℤ)
    (ρ : Γ × Δ →* Aut K) (σ : Γ × Δ →* Aut W) (τ : Representation R Γ U) :
    (isotypicProdRepresentation τ (abutmentRepresentation R ρ σ n)).Equiv
      (isotypicProdRepresentation τ (cohomologyHomRepresentation R ρ σ n)) :=
  isotypicProdEquiv τ (smoothDegenerationEquiv R G b hK hW n ρ σ)

end Smooth

end HyperextAbutment

end Langlands.Cohomology
