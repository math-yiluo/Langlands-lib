import Langlands.Cohomology.DivisibleSystem
import Langlands.Cohomology.LinearHomComplex
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Hom inverse systems of `ℓ`-divisible systems

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, pp.311-312: the complexes (4.10.2) are sums of the modules
`T_m(j, ẽ) = Hom_{𝒪/ℓ^m 𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`, and Harris
studies the maps (4.10.3) `T_{m+1}(j, ẽ) ⟶ T_m(j, ẽ)` as `m` varies in order to check a
Mittag-Leffler condition.

For `ℓ`-divisible systems `T` and `W` in an `R`-linear abelian category, this module
constructs the corresponding inverse system `m ↦ Hom(T m, W m)`. The projection
`j : T m ⟶ T m'` is a cokernel of multiplication by `ℓ ^ m'` on `T m`, and a morphism
`f : T m ⟶ W m` followed by the projection `W m ⟶ W m'` is killed by `ℓ ^ m'`; the
transition map sends `f` to the morphism `T m' ⟶ W m'` through which this composite
factors. The limit of this inverse system is the module of morphisms of the inverse
systems `T.tower ⟶ W.tower`. The same construction is carried out degreewise on the Hom
complexes of `LinearHomComplex` for `ℓ`-divisible systems of cochain complexes; this is
the shape of Harris's inverse system of the complexes (4.10.2). The identification of
Harris's complexes (4.10.2) with Hom complexes of this kind is not formalized here.

Harris's surjectivity of the maps (4.10.3), which uses freeness of the modules involved,
and the Mittag-Leffler argument are not part of this module.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

universe w v u v₁ u₁ w₁

namespace DivisibleSystem

section Cokernel

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ} (T : DivisibleSystem C ℓ)

lemma projection_comp_projection {m'' m' m : ℕ} (h₁ : m'' ≤ m') (h₂ : m' ≤ m) :
    T.projection h₂ ≫ T.projection h₁ = T.projection (h₁.trans h₂) := by
  rw [← Functor.map_comp]
  rfl

lemma projection_refl (m : ℕ) : T.projection (le_refl m) = 𝟙 (T.obj m) :=
  T.tower.map_id (op m)

lemma powSMul_comp_projection {m' m : ℕ} (h : m' ≤ m) :
    powSMul ℓ m' (T.obj m) ≫ T.projection h = 0 := by
  rw [← comp_powSMul, T.powSMul_eq_zero, comp_zero]

/-- Exactness of `T m ⟶ T m ⟶ T m'`, given by multiplication by `ℓ ^ m'` and the
projection `j`. For `m' = 0` the first map is the identity. Otherwise the kernel of `j` is
the image of `i : T (m - m') ⟶ T m`, which is killed by `ℓ ^ (m - m')`, and by flatness
the `ℓ ^ (m - m')`-torsion of `T m` is contained in `ℓ ^ m' T m`. -/
lemma exact_powSMul_projection {m' m : ℕ} (h : m' ≤ m) :
    (ShortComplex.mk (powSMul ℓ m' (T.obj m)) (T.projection h)
      (T.powSMul_comp_projection h)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A (x : A ⟶ T.obj m) (hx : x ≫ T.projection h = 0)
  rcases Nat.eq_zero_or_pos m' with rfl | hm'
  · refine ⟨A, 𝟙 A, inferInstance, x, ?_⟩
    change 𝟙 A ≫ x = x ≫ powSMul ℓ 0 (T.obj m)
    rw [powSMul_zero, Category.id_comp, Category.comp_id]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hk : k < m' + k := by omega
  have hx' : x ≫ T.projection (Nat.sub_le (m' + k) k) = 0 := by
    have aux : ∀ (n : ℕ) (hn : n ≤ m' + k), n = m' → x ≫ T.projection hn = 0 := by
      rintro n hn rfl
      exact hx
    exact aux _ _ (by omega)
  obtain ⟨A₁, π₁, _, (y₁ : A₁ ⟶ T.obj k), (hy₁ : π₁ ≫ x = y₁ ≫ T.inclusion hk)⟩ :=
    (T.shortExact hk).exact.exact_up_to_refinements x hx'
  have hy₁' : (y₁ ≫ T.inclusion hk) ≫ powSMul ℓ k (T.obj (m' + k)) = 0 := by
    rw [Category.assoc, comp_powSMul, T.powSMul_eq_zero, zero_comp, comp_zero]
  obtain ⟨A₂, π₂, _, (y₂ : A₂ ⟶ T.obj (m' + k)),
    (hy₂ : π₂ ≫ y₁ ≫ T.inclusion hk = y₂ ≫ powSMul ℓ m' (T.obj (m' + k)))⟩ :=
    (T.flat m' k).exact_up_to_refinements _ hy₁'
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, y₂, ?_⟩
  change (π₂ ≫ π₁) ≫ x = y₂ ≫ powSMul ℓ m' (T.obj (m' + k))
  rw [Category.assoc, hy₁, hy₂]

/-- The projection `j : T m ⟶ T m'` is a cokernel of multiplication by `ℓ ^ m'` on
`T m`. -/
def projectionIsCokernelPowSMul {m' m : ℕ} (h : m' ≤ m) :
    IsColimit (CokernelCofork.ofπ (T.projection h) (T.powSMul_comp_projection h)) :=
  have : Epi (T.projection h) := T.epi_projection h
  (T.exact_powSMul_projection h).gIsCokernel

/-- A morphism `T m ⟶ Z` killed by `ℓ ^ m'` factors through the projection
`T m ⟶ T m'`; this is the factored morphism `T m' ⟶ Z`. -/
def descend {m' m : ℕ} (h : m' ≤ m) {Z : C} (g : T.obj m ⟶ Z)
    (hg : powSMul ℓ m' (T.obj m) ≫ g = 0) : T.obj m' ⟶ Z :=
  (CokernelCofork.IsColimit.desc' (T.projectionIsCokernelPowSMul h) g hg).1

@[reassoc (attr := simp)]
lemma projection_descend {m' m : ℕ} (h : m' ≤ m) {Z : C} (g : T.obj m ⟶ Z)
    (hg : powSMul ℓ m' (T.obj m) ≫ g = 0) : T.projection h ≫ T.descend h g hg = g :=
  (CokernelCofork.IsColimit.desc' (T.projectionIsCokernelPowSMul h) g hg).2

lemma descend_eq_iff {m' m : ℕ} (h : m' ≤ m) {Z : C} (g : T.obj m ⟶ Z)
    (hg : powSMul ℓ m' (T.obj m) ≫ g = 0) (g' : T.obj m' ⟶ Z) :
    T.descend h g hg = g' ↔ T.projection h ≫ g' = g := by
  have : Epi (T.projection h) := T.epi_projection h
  constructor
  · rintro rfl
    exact T.projection_descend h g hg
  · intro hg'
    rw [← cancel_epi (T.projection h), projection_descend, hg']

end Cokernel

section HomSystem

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} (T W : DivisibleSystem C ℓ)

lemma powSMul_comp_comp_projection {m' m : ℕ} (h : m' ≤ m) (f : T.obj m ⟶ W.obj m) :
    powSMul ℓ m' (T.obj m) ≫ f ≫ W.projection h = 0 := by
  rw [← Category.assoc, ← comp_powSMul, Category.assoc, W.powSMul_comp_projection, comp_zero]

/-- Harris 1999 (4.10.3): the transition `Hom(T m, W m) ⟶ Hom(T m', W m')` for `m' ≤ m`.
It sends `f` to the morphism `T m' ⟶ W m'` through which `f ≫ j` factors along the
projection `j : T m ⟶ T m'`. -/
def homTransition {m' m : ℕ} (h : m' ≤ m) (f : T.obj m ⟶ W.obj m) : T.obj m' ⟶ W.obj m' :=
  T.descend h (f ≫ W.projection h) (powSMul_comp_comp_projection T W h f)

@[reassoc (attr := simp)]
lemma projection_comp_homTransition {m' m : ℕ} (h : m' ≤ m) (f : T.obj m ⟶ W.obj m) :
    T.projection h ≫ homTransition T W h f = f ≫ W.projection h :=
  T.projection_descend h _ _

lemma homTransition_eq_iff {m' m : ℕ} (h : m' ≤ m) (f : T.obj m ⟶ W.obj m)
    (g : T.obj m' ⟶ W.obj m') :
    homTransition T W h f = g ↔ T.projection h ≫ g = f ≫ W.projection h :=
  T.descend_eq_iff h _ _ g

lemma homTransition_refl (m : ℕ) (f : T.obj m ⟶ W.obj m) :
    homTransition T W (le_refl m) f = f := by
  rw [homTransition_eq_iff, projection_refl, projection_refl, Category.id_comp,
    Category.comp_id]

lemma homTransition_trans {m'' m' m : ℕ} (h₁ : m'' ≤ m') (h₂ : m' ≤ m)
    (f : T.obj m ⟶ W.obj m) :
    homTransition T W h₁ (homTransition T W h₂ f) = homTransition T W (h₁.trans h₂) f := by
  rw [eq_comm, homTransition_eq_iff, ← projection_comp_projection T h₁ h₂, Category.assoc,
    projection_comp_homTransition, projection_comp_homTransition_assoc,
    projection_comp_projection]

/-- A morphism of the inverse systems `T.tower ⟶ W.tower` is fixed by the transitions. -/
lemma homTransition_app (α : T.tower ⟶ W.tower) {m' m : ℕ} (h : m' ≤ m) :
    homTransition T W h (α.app (op m)) = α.app (op m') := by
  rw [homTransition_eq_iff]
  exact α.naturality (homOfLE h).op

/-- The transition of `homTransition` as an `R`-linear map. -/
@[simps]
def homTransitionLinear {m' m : ℕ} (h : m' ≤ m) :
    (T.obj m ⟶ W.obj m) →ₗ[R] (T.obj m' ⟶ W.obj m') where
  toFun := homTransition T W h
  map_add' f g := by
    rw [homTransition_eq_iff, Preadditive.comp_add, projection_comp_homTransition,
      projection_comp_homTransition, Preadditive.add_comp]
  map_smul' r f := by
    rw [homTransition_eq_iff, Linear.comp_smul, projection_comp_homTransition,
      RingHom.id_apply, Linear.smul_comp]

/-- Harris 1999 (4.10.3): the inverse system of `R`-modules `m ↦ Hom(T m, W m)`. -/
@[simps obj]
def homSystem : ℕᵒᵖ ⥤ ModuleCat.{v} R where
  obj m := ModuleCat.of R (T.obj m.unop ⟶ W.obj m.unop)
  map φ := ModuleCat.ofHom (homTransitionLinear R T W (leOfHom φ.unop))
  map_id m := by
    ext f
    exact homTransition_refl T W m.unop f
  map_comp φ ψ := by
    ext f
    exact (homTransition_trans T W (leOfHom ψ.unop) (leOfHom φ.unop) f).symm

lemma homSystem_map_apply {m m' : ℕᵒᵖ} (φ : m ⟶ m') (f : T.obj m.unop ⟶ W.obj m.unop) :
    (homSystem R T W).map φ f = homTransition T W (leOfHom φ.unop) f :=
  rfl

/-- Evaluation at level `m` of a morphism of the inverse systems, as an `R`-linear map. -/
@[simps]
def towerHomEval (m : ℕ) : (T.tower ⟶ W.tower) →ₗ[R] (T.obj m ⟶ W.obj m) where
  toFun α := α.app (op m)
  map_add' _ _ := rfl
  map_smul' r α := NatTrans.app_smul (op m) r α

/-- The cone over `homSystem` whose apex is the module of morphisms of the inverse systems
`T.tower ⟶ W.tower`, with projections the components. -/
@[simps pt]
def homSystemCone : Cone (homSystem R T W) where
  pt := ModuleCat.of R (T.tower ⟶ W.tower)
  π :=
    { app m := ModuleCat.ofHom (towerHomEval R T W m.unop)
      naturality m m' φ := by
        ext α
        exact (homTransition_app T W α (leOfHom φ.unop)).symm }

/-- A compatible family of elements of the modules `Hom(T m, W m)` is a morphism of the
inverse systems. -/
@[simps]
def homSystemLift (s : Cone (homSystem R T W)) : s.pt →ₗ[R] (T.tower ⟶ W.tower) where
  toFun x :=
    { app m := s.π.app m x
      naturality m m' φ := by
        have hs : s.π.app m' x = (homSystem R T W).map φ (s.π.app m x) :=
          congrArg (fun g => g.hom x) (s.w φ).symm
        exact (hs.trans (homSystem_map_apply R T W φ _)) ▸
          (projection_comp_homTransition T W (leOfHom φ.unop) (s.π.app m x)) }
  map_add' x y := by
    ext m
    exact (s.π.app m).hom.map_add x y
  map_smul' r x := by
    ext m
    exact (s.π.app m).hom.map_smul r x

/-- The limit of the inverse system `homSystem` is the module of morphisms of the inverse
systems `T.tower ⟶ W.tower`. -/
def homSystemIsLimit : IsLimit (homSystemCone R T W) where
  lift s := ModuleCat.ofHom (homSystemLift R T W s)
  fac s m := by
    ext x
    rfl
  uniq s g hg := by
    ext x
    refine NatTrans.ext (funext fun m => ?_)
    exact congrArg (fun k => k.hom x) (hg m)

end HomSystem

section HomComplexSystem

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)

/-- The transition of graded morphisms: each component `T m ^ p ⟶ W m ^ q` is sent by the
transition of the degree `p` and degree `q` systems. -/
def cochainTransition {m' m : ℕ} (h : m' ≤ m) {n : ℤ} (z : Cochain (T.obj m) (W.obj m) n) :
    Cochain (T.obj m') (W.obj m') n :=
  Cochain.mk fun p q hpq => homTransition (T.degree p) (W.degree q) h (z.v p q hpq)

lemma cochainTransition_v {m' m : ℕ} (h : m' ≤ m) {n : ℤ} (z : Cochain (T.obj m) (W.obj m) n)
    (p q : ℤ) (hpq : p + n = q) :
    (cochainTransition T W h z).v p q hpq =
      homTransition (T.degree p) (W.degree q) h (z.v p q hpq) :=
  Cochain.mk_v _ _ _ _

lemma cochainTransition_eq_iff {m' m : ℕ} (h : m' ≤ m) {n : ℤ}
    (z : Cochain (T.obj m) (W.obj m) n) (z' : Cochain (T.obj m') (W.obj m') n) :
    cochainTransition T W h z = z' ↔
      (Cochain.ofHom (T.projection h)).comp z' (zero_add n) =
        z.comp (Cochain.ofHom (W.projection h)) (add_zero n) := by
  constructor
  · rintro rfl
    ext p q hpq
    rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      Cochain.ofHom_v, cochainTransition_v]
    exact projection_comp_homTransition (T.degree p) (W.degree q) h (z.v p q hpq)
  · intro hz
    ext p q hpq
    rw [cochainTransition_v]
    have := Cochain.congr_v hz p q hpq
    rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      Cochain.ofHom_v] at this
    exact (homTransition_eq_iff (T.degree p) (W.degree q) h (z.v p q hpq)
      (z'.v p q hpq)).2 this

lemma ofHom_comp_cochainTransition {m' m : ℕ} (h : m' ≤ m) {n : ℤ}
    (z : Cochain (T.obj m) (W.obj m) n) :
    (Cochain.ofHom (T.projection h)).comp (cochainTransition T W h z) (zero_add n) =
      z.comp (Cochain.ofHom (W.projection h)) (add_zero n) :=
  (cochainTransition_eq_iff T W h z _).1 rfl

lemma cochainTransition_refl (m : ℕ) {n : ℤ} (z : Cochain (T.obj m) (W.obj m) n) :
    cochainTransition T W (le_refl m) z = z := by
  ext p q hpq
  rw [cochainTransition_v]
  exact homTransition_refl (T.degree p) (W.degree q) m (z.v p q hpq)

lemma cochainTransition_trans {m'' m' m : ℕ} (h₁ : m'' ≤ m') (h₂ : m' ≤ m) {n : ℤ}
    (z : Cochain (T.obj m) (W.obj m) n) :
    cochainTransition T W h₁ (cochainTransition T W h₂ z) =
      cochainTransition T W (h₁.trans h₂) z := by
  ext p q hpq
  rw [cochainTransition_v, cochainTransition_v, cochainTransition_v]
  exact homTransition_trans (T.degree p) (W.degree q) h₁ h₂ (z.v p q hpq)

/-- The transition commutes with the differential of the Hom complexes. -/
lemma δ_cochainTransition {m' m : ℕ} (h : m' ≤ m) (n n' : ℤ)
    (z : Cochain (T.obj m) (W.obj m) n) :
    δ n n' (cochainTransition T W h z) = cochainTransition T W h (δ n n' z) := by
  symm
  rw [cochainTransition_eq_iff, ← δ_ofHom_comp, ofHom_comp_cochainTransition, δ_comp_ofHom]

/-- The transition of graded morphisms of degree `n`, as an `R`-linear map. -/
def cochainTransitionLinear {m' m : ℕ} (h : m' ≤ m) (n : ℤ) :
    Cochain (T.obj m) (W.obj m) n →ₗ[R] Cochain (T.obj m') (W.obj m') n where
  toFun := cochainTransition T W h
  map_add' z z' := by
    rw [cochainTransition_eq_iff, Cochain.comp_add, ofHom_comp_cochainTransition,
      ofHom_comp_cochainTransition, Cochain.add_comp]
  map_smul' r z := by
    rw [cochainTransition_eq_iff, Cochain.comp_smul, ofHom_comp_cochainTransition,
      RingHom.id_apply, Cochain.smul_comp]

lemma cochainTransitionLinear_apply {m' m : ℕ} (h : m' ≤ m) (n : ℤ)
    (z : Cochain (T.obj m) (W.obj m) n) :
    cochainTransitionLinear R T W h n z = cochainTransition T W h z :=
  rfl

/-- The transition chain map between the Hom complexes of levels `m` and `m'`. -/
def homComplexTransition {m' m : ℕ} (h : m' ≤ m) :
    LinearHomComplex.complex R (T.obj m) (W.obj m) ⟶
      LinearHomComplex.complex R (T.obj m') (W.obj m') where
  f n := ModuleCat.ofHom (cochainTransitionLinear R T W h n)
  comm' n n' _ := by
    ext z
    exact δ_cochainTransition T W h n n' z

/-- Harris 1999 (4.10.2), (4.10.3): the inverse system of Hom complexes
`m ↦ Hom^•(T m, W m)` of an `ℓ`-divisible system of cochain complexes `T` into an
`ℓ`-divisible system of cochain complexes `W`. -/
@[simps obj]
def homComplexSystem : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj m := LinearHomComplex.complex R (T.obj m.unop) (W.obj m.unop)
  map φ := homComplexTransition R T W (leOfHom φ.unop)
  map_id m := by
    ext n z
    exact cochainTransition_refl T W m.unop z
  map_comp φ ψ := by
    ext n z
    exact (cochainTransition_trans T W (leOfHom ψ.unop) (leOfHom φ.unop) z).symm

/-- `ℕᵒᵖ` is small, so `ModuleCat.{v} R` has limits of shape `ℕᵒᵖ` for every
universe `v`. -/
instance hasLimitsOfShape_natOp_moduleCat : HasLimitsOfShape ℕᵒᵖ (ModuleCat.{v} R) :=
  ModuleCat.hasLimitsOfShape

/-- The inverse limit of the Hom complexes `homComplexSystem`. In the proof of
Proposition 4.10 Harris passes to this limit using a Mittag-Leffler condition for the
complexes (4.10.2); that argument is not part of this module. -/
abbrev homComplexLimit : CochainComplex (ModuleCat.{v} R) ℤ :=
  limit (homComplexSystem R T W)

end HomComplexSystem

end DivisibleSystem

section Smooth

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G] {ℓ : ℕ}

/-- Harris 1999 (4.10.2), (4.10.3) for `ℓ`-divisible systems of cochain complexes of
smooth representations: the inverse system of the Hom complexes of equivariant maps. -/
abbrev smoothHomComplexSystem (T W : SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{w} R) ℤ :=
  DivisibleSystem.homComplexSystem R T W

end Smooth

end Langlands.Cohomology
