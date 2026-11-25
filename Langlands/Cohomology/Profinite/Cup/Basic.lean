import Langlands.Cohomology.Profinite.Comparison.Continuous
import Langlands.Cohomology.Profinite.Cup.Cochains

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory Limits MonoidalCategory TensorProduct groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]


variable [IsTopologicalGroup G]

section LocallyConstant

theorem isLocallyConstant_cupCochain {A B : Rep.{u} k G} [IsSmoothRep B] {p q n : ℕ}
    (h : p + q = n) {f : (Fin p → G) → A} {g : (Fin q → G) → B} (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) : IsLocallyConstant (cupCochain h f g) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpre : Continuous fun y : Fin n → G => fun i : Fin p => y ⟨i, by omega⟩ :=
    continuous_pi fun i => continuous_apply _
  have hsuf : Continuous fun y : Fin n → G => fun j : Fin q => y ⟨p + j, by omega⟩ :=
    continuous_pi fun j => continuous_apply _
  have hP : Continuous fun y : Fin n → G => Fin.partialProd y ⟨p, by omega⟩ :=
    (continuous_apply _).comp (continuous_partialProd (G := G) n)
  have e1 : ∀ᶠ y in nhds x, f (fun i : Fin p => y ⟨i, by omega⟩) =
      f (fun i : Fin p => x ⟨i, by omega⟩) :=
    hpre.continuousAt.eventually (hf.eventually_eq _)
  have e2 : ∀ᶠ y in nhds x, g (fun j : Fin q => y ⟨p + j, by omega⟩) =
      g (fun j : Fin q => x ⟨p + j, by omega⟩) :=
    hsuf.continuousAt.eventually (hg.eventually_eq _)
  have e3 : ∀ᶠ y in nhds x,
      B.ρ (Fin.partialProd y ⟨p, by omega⟩) (g fun j : Fin q => x ⟨p + j, by omega⟩) =
        B.ρ (Fin.partialProd x ⟨p, by omega⟩) (g fun j : Fin q => x ⟨p + j, by omega⟩) :=
    hP.continuousAt.eventually ((isLocallyConstant_apply B _).eventually_eq _)
  filter_upwards [e1, e2, e3] with y h1 h2 h3
  rw [cupCochain_apply, cupCochain_apply, h1, h2, h3]

variable {A B : Rep.{u} k G} {p q n : ℕ}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem cupCochain_zero_left (h : p + q = n) (g : (Fin q → G) → B) :
    cupCochain h (0 : (Fin p → G) → A) g = 0 :=
  (cupₗ h).map_zero₂ g

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem cupCochain_zero_right (h : p + q = n) (f : (Fin p → G) → A) :
    cupCochain h f (0 : (Fin q → G) → B) = 0 :=
  (cupₗ h f).map_zero

section Elements

variable (A) in

def cochainOf [IsSmoothRep A] {i : ℕ} (a : (cochains A).X i) : (Fin i → G) → A :=
  (a : locallyConstantCochains A i).1

variable (A) in

def mkCochain [IsSmoothRep A] {i : ℕ} (c : (Fin i → G) → A) (hc : IsLocallyConstant c) :
    (cochains A).X i :=
  (⟨c, hc⟩ : locallyConstantCochains A i)

variable [IsSmoothRep A]

@[simp]
theorem cochainOf_mkCochain {i : ℕ} (c : (Fin i → G) → A) (hc : IsLocallyConstant c) :
    cochainOf A (mkCochain A c hc) = c :=
  rfl

theorem isLocallyConstant_cochainOf {i : ℕ} (a : (cochains A).X i) :
    IsLocallyConstant (cochainOf A a) :=
  (a : locallyConstantCochains A i).2

theorem cochainOf_injective {i : ℕ} : Function.Injective (cochainOf A (i := i)) :=
  fun _ _ h => Subtype.ext h

@[simp]
theorem cochainOf_add {i : ℕ} (a b : (cochains A).X i) :
    cochainOf A (a + b) = cochainOf A a + cochainOf A b :=
  rfl

@[simp]
theorem cochainOf_smul {i : ℕ} (c : k) (a : (cochains A).X i) :
    cochainOf A (c • a) = c • cochainOf A a :=
  rfl

@[simp]
theorem cochainOf_zero {i : ℕ} : cochainOf A (0 : (cochains A).X i) = 0 :=
  rfl

theorem cochainOf_d {i : ℕ} (a : (cochains A).X i) :
    cochainOf A ((cochains A).d i (i + 1) a) =
      (inhomogeneousCochains.d A i).hom (cochainOf A a) := by
  rw [cochains_d]
  rfl

end Elements

variable [IsSmoothRep A] [IsSmoothRep B]

def cupLocallyConstant (h : p + q = n) :
    (cochains A).X p →ₗ[k] (cochains B).X q →ₗ[k] (cochains (A ⊗ B)).X n :=
  LinearMap.mk₂ k (fun f g => mkCochain (A ⊗ B) (cupCochain h (cochainOf A f) (cochainOf B g))
      (isLocallyConstant_cupCochain h (isLocallyConstant_cochainOf f)
        (isLocallyConstant_cochainOf g)))
    (fun f f' g => cochainOf_injective ((cupₗ h).map_add₂ (cochainOf A f) (cochainOf A f') (cochainOf B g)))
    (fun c f g => cochainOf_injective ((cupₗ h).map_smul₂ c (cochainOf A f) (cochainOf B g)))
    (fun f g g' => cochainOf_injective ((cupₗ h (cochainOf A f)).map_add (cochainOf B g) (cochainOf B g')))
    (fun c f g => cochainOf_injective ((cupₗ h (cochainOf A f)).map_smul c (cochainOf B g)))

@[simp]
theorem cochainOf_cupLocallyConstant (h : p + q = n) (f : (cochains A).X p)
    (g : (cochains B).X q) :
    cochainOf (A ⊗ B) (cupLocallyConstant h f g) = cupCochain h (cochainOf A f) (cochainOf B g) :=
  rfl

end LocallyConstant

section Cocycles

variable {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] {p q n : ℕ}

variable (A p) in

def cocycleι : cocycles A p →ₗ[k] (cochains A).X p :=
  ((cochains A).iCycles p).hom

theorem cocycleι_injective : Function.Injective (cocycleι A p) :=
  (ModuleCat.mono_iff_injective ((cochains A).iCycles p)).1 inferInstance

theorem d_cocycleι (x : cocycles A p) :
    (inhomogeneousCochains.d A p).hom (cochainOf A (cocycleι A p x)) = 0 := by
  rw [← cochainOf_d]
  have h := congrArg (fun φ => φ.hom x) ((cochains A).iCycles_d p (p + 1))
  exact congrArg (cochainOf A) h

theorem cochainOf_cocycleι_toCycles {i : ℕ} (a : (cochains A).X i) :
    cochainOf A (cocycleι A (i + 1) ((cochains A).toCycles i (i + 1) a)) =
      (inhomogeneousCochains.d A i).hom (cochainOf A a) := by
  rw [← cochainOf_d]
  exact congrArg (fun φ => cochainOf A (φ.hom a)) ((cochains A).toCycles_i i (i + 1))

theorem isCocycle_cupCochain (h : p + q = n) (x : cocycles A p) (y : cocycles B q) :
    (inhomogeneousCochains.d (A ⊗ B) n).hom
      (cupCochain h (cochainOf A (cocycleι A p x)) (cochainOf B (cocycleι B q y))) = 0 := by
  rw [d_cupCochain, d_cocycleι, d_cocycleι, cupCochain_zero_left, cupCochain_zero_right,
    smul_zero, add_zero]

def cupCocyclesAlt (h : p + q = n) (x : cocycles A p) (y : cocycles B q) : cocycles (A ⊗ B) n :=
  (cochains (A ⊗ B)).cyclesMk
    (cupLocallyConstant h (cocycleι A p x) (cocycleι B q y)) (n + 1) (by simp) (by
      apply cochainOf_injective (A := A ⊗ B)
      exact (cochainOf_d (A := A ⊗ B) _).trans (isCocycle_cupCochain h x y))

theorem cocycle_inclusion_cupCocycles (h : p + q = n) (x : cocycles A p) (y : cocycles B q) :
    cocycleι (A ⊗ B) n (cupCocyclesAlt h x y) =
      cupLocallyConstant h (cocycleι A p x) (cocycleι B q y) :=
  (cochains (A ⊗ B)).i_cyclesMk _ _ _ _

def cupCocycles (h : p + q = n) :
    cocycles A p →ₗ[k] cocycles B q →ₗ[k] cocycles (A ⊗ B) n :=
  LinearMap.mk₂ k (cupCocyclesAlt h)
    (fun x x' y => cocycleι_injective (by simp [cocycle_inclusion_cupCocycles]))
    (fun c x y => cocycleι_injective (by simp [cocycle_inclusion_cupCocycles]))
    (fun x y y' => cocycleι_injective (by simp [cocycle_inclusion_cupCocycles]))
    (fun c x y => cocycleι_injective (by simp [cocycle_inclusion_cupCocycles]))

@[simp]
theorem cocycleι_cupCocycles (h : p + q = n) (x : cocycles A p) (y : cocycles B q) :
    cocycleι (A ⊗ B) n (cupCocycles h x y) =
      cupLocallyConstant h (cocycleι A p x) (cocycleι B q y) :=
  cocycle_inclusion_cupCocycles h x y

theorem cupCocycles_toCycles_left (h : p + q = n) {i m : ℕ} (hi : i + 1 = p) (hm : i + q = m)
    (hmn : m + 1 = n) (a : (cochains A).X i) (y : cocycles B q) :
    cupCocycles h ((cochains A).toCycles i p a) y =
      (cochains (A ⊗ B)).toCycles m n (cupLocallyConstant hm a (cocycleι B q y)) := by
  subst hi hm hmn
  apply cocycleι_injective
  apply cochainOf_injective
  rw [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cochainOf_cocycleι_toCycles,
    cochainOf_cocycleι_toCycles, cochainOf_cupLocallyConstant, d_cupCochain, d_cocycleι,
    cupCochain_zero_right, smul_zero, add_zero]

theorem cupCocycles_toCycles_right (h : p + q = n) {j m : ℕ} (hj : j + 1 = q) (hm : p + j = m)
    (hmn : m + 1 = n) (x : cocycles A p) (b : (cochains B).X j) :
    cupCocycles h x ((cochains B).toCycles j q b) =
      (-1 : k) ^ p • (cochains (A ⊗ B)).toCycles m n
        (cupLocallyConstant hm (cocycleι A p x) b) := by
  subst hj hm hmn
  apply cocycleι_injective
  apply cochainOf_injective
  rw [map_smul, cochainOf_smul, cocycleι_cupCocycles, cochainOf_cupLocallyConstant,
    cochainOf_cocycleι_toCycles, cochainOf_cocycleι_toCycles, cochainOf_cupLocallyConstant,
    d_cupCochain, d_cocycleι, cupCochain_zero_left, zero_add, smul_smul, ← mul_pow, neg_one_mul,
    neg_neg, one_pow, one_smul]

end Cocycles

section Cohomology

variable {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] {p q n : ℕ}

theorem cohomologyπ_surjective (A : Rep.{u} k G) [IsSmoothRep A] (p : ℕ) :
    Function.Surjective (cohomologyπ A p) :=
  (ModuleCat.epi_iff_surjective ((cochains A).homologyπ p)).1 inferInstance

theorem cohomologyπ_toCycles (A : Rep.{u} k G) [IsSmoothRep A] (i p : ℕ)
    (a : (cochains A).X i) :
    cohomologyπ A p ((cochains A).toCycles i p a) = 0 :=
  congrArg (fun φ => φ.hom a) ((cochains A).toCycles_comp_homologyπ i p)

theorem cohomology_linearMap_ext {M : Type*} [AddCommGroup M] [Module k M]
    {f g : cohomology A p →ₗ[k] M} (hfg : ∀ x, f (cohomologyπ A p x) = g (cohomologyπ A p x)) :
    f = g := by
  ext z
  obtain ⟨x, rfl⟩ := cohomologyπ_surjective A p z
  exact hfg x

def cocyclesHom {M : Type u} [AddCommGroup M] [Module k M] (L : cocycles A p →ₗ[k] M) :
    (cochains A).cycles p ⟶ ModuleCat.of k M :=
  ModuleCat.ofHom L

theorem toCycles_cocyclesHom {M : Type u} [AddCommGroup M] [Module k M]
    (L : cocycles A p →ₗ[k] M)
    (hL : ∀ i, i + 1 = p → ∀ a, L ((cochains A).toCycles i p a) = 0) :
    (cochains A).toCycles ((ComplexShape.up ℕ).prev p) p ≫ cocyclesHom L = 0 := by
  by_cases hr : (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev p) p
  · ext a
    exact hL _ hr a
  · rw [(cochains A).toCycles_eq_zero hr]
    exact zero_comp

def descCohomologyHom {M : Type u} [AddCommGroup M] [Module k M] (L : cocycles A p →ₗ[k] M)
    (hL : ∀ i, i + 1 = p → ∀ a, L ((cochains A).toCycles i p a) = 0) :
    cohomology A p ⟶ ModuleCat.of k M :=
  ((cochains A).homologyIsCokernel _ p rfl).desc
    (CokernelCofork.ofπ (cocyclesHom L) (toCycles_cocyclesHom L hL))

theorem π_descCohomologyHom {M : Type u} [AddCommGroup M] [Module k M] (L : cocycles A p →ₗ[k] M)
    (hL : ∀ i, i + 1 = p → ∀ a, L ((cochains A).toCycles i p a) = 0) :
    cohomologyπ A p ≫ descCohomologyHom L hL = cocyclesHom L :=
  Cofork.IsColimit.π_desc ((cochains A).homologyIsCokernel _ p rfl)

def descCohomology {M : Type u} [AddCommGroup M] [Module k M] (L : cocycles A p →ₗ[k] M)
    (hL : ∀ i, i + 1 = p → ∀ a, L ((cochains A).toCycles i p a) = 0) :
    cohomology A p →ₗ[k] M :=
  (descCohomologyHom L hL).hom

@[simp]
theorem descCohomology_cohomologyπ {M : Type u} [AddCommGroup M] [Module k M]
    (L : cocycles A p →ₗ[k] M)
    (hL : ∀ i, i + 1 = p → ∀ a, L ((cochains A).toCycles i p a) = 0) (x : cocycles A p) :
    descCohomology L hL (cohomologyπ A p x) = L x :=
  ConcreteCategory.congr_hom (π_descCohomologyHom L hL) x

def cupCocyclesπ (h : p + q = n) :
    cocycles A p →ₗ[k] cocycles B q →ₗ[k] cohomology (A ⊗ B) n :=
  (cupCocycles h).compr₂ (cohomologyπ (A ⊗ B) n).hom

theorem cupCocyclesπ_apply (h : p + q = n) (x : cocycles A p) (y : cocycles B q) :
    cupCocyclesπ h x y = cohomologyπ (A ⊗ B) n (cupCocycles h x y) :=
  rfl

theorem cupCocyclesπ_toCycles_left (h : p + q = n) (i : ℕ) (hi : i + 1 = p)
    (a : (cochains A).X i) (y : cocycles B q) :
    cupCocyclesπ h ((cochains A).toCycles i p a) y = 0 := by
  rw [cupCocyclesπ_apply, cupCocycles_toCycles_left h hi rfl (by omega), cohomologyπ_toCycles]

theorem cupCocyclesπ_toCycles_right (h : p + q = n) (x : cocycles A p) (j : ℕ) (hj : j + 1 = q)
    (b : (cochains B).X j) :
    cupCocyclesπ h x ((cochains B).toCycles j q b) = 0 := by
  rw [cupCocyclesπ_apply, cupCocycles_toCycles_right h hj rfl (by omega), map_smul,
    cohomologyπ_toCycles, smul_zero]

def cupProductCocycleClass (h : p + q = n) : cohomology B q →ₗ[k] cocycles A p →ₗ[k] cohomology (A ⊗ B) n :=
  descCohomology (cupCocyclesπ h).flip fun j hj b => by
    ext x
    exact cupCocyclesπ_toCycles_right h x j hj b

theorem cup_cohomology_class (h : p + q = n) (x : cocycles A p) (y : cocycles B q) :
    cupProductCocycleClass h (cohomologyπ B q y) x = cupCocyclesπ h x y := by
  rw [cupProductCocycleClass, descCohomology_cohomologyπ]
  rfl

def cup (h : p + q = n) : cohomology A p →ₗ[k] cohomology B q →ₗ[k] cohomology (A ⊗ B) n :=
  descCohomology (cupProductCocycleClass h).flip fun i hi a => by
    apply cohomology_linearMap_ext
    intro y
    rw [LinearMap.flip_apply, cup_cohomology_class, cupCocyclesπ_toCycles_left h i hi]
    rfl

@[simp]
theorem cup_cohomologyπ (h : p + q = n) (x : cocycles A p) (y : cocycles B q) :
    cup h (cohomologyπ A p x) (cohomologyπ B q y) = cohomologyπ (A ⊗ B) n (cupCocycles h x y) := by
  rw [cup, descCohomology_cohomologyπ, LinearMap.flip_apply, cup_cohomology_class]
  rfl

end Cohomology

end Langlands.ProfiniteCohomology

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory groupCohomology

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

variable {A : Rep.{u} k G} [IsSmoothRep A] {p : ℕ}

omit [IsTopologicalGroup H] in

theorem cocycles_ext {x y : cocycles A p}
    (h : cochainOf A (cocycleι A p x) = cochainOf A (cocycleι A p y)) : x = y :=
  cocycleι_injective (cochainOf_injective h)

omit [IsTopologicalGroup H] in

@[elab_as_elim]
theorem cohomology_induction_on {C : cohomology A p → Prop} (z : cohomology A p)
    (h : ∀ x : cocycles A p, C (cohomologyπ A p x)) : C z := by
  obtain ⟨x, rfl⟩ := cohomologyπ_surjective A p z
  exact h x

section Map

variable {B : Rep.{u} k G} [IsSmoothRep B]

omit [IsTopologicalGroup H] in

theorem cochainOf_cocycleι_cyclesMap (f : A ⟶ B) (x : cocycles A p) :
    cochainOf B (cocycleι B p (HomologicalComplex.cyclesMap (coeffCochainsMap f) p x)) =
      fun g => f.hom (cochainOf A (cocycleι A p x) g) :=
  congrArg (fun ψ => cochainOf B (ψ.hom x)) (HomologicalComplex.cyclesMap_i (coeffCochainsMap f) p)

omit [IsTopologicalGroup H] in

theorem cohomologyMap_cohomologyπ (f : A ⟶ B) (x : cocycles A p) :
    coeffMap f p (cohomologyπ A p x) =
      cohomologyπ B p (HomologicalComplex.cyclesMap (coeffCochainsMap f) p x) :=
  ConcreteCategory.congr_hom (cohomologyπ_coeffMap f p) x

end Map

section MapAlong

variable {B : Rep.{u} k H} [IsSmoothRep B] (φ : H →ₜ* G)
  (f : Rep.res φ A ⟶ B)

theorem cochainOf_cocycleι_cocyclesMap (x : cocycles A p) :
    cochainOf B (cocycleι B p (cocyclesMap φ f p x)) =
      fun h => f.hom (cochainOf A (cocycleι A p x) (⇑φ ∘ h)) :=
  congrArg (fun ψ => cochainOf B (ψ.hom x))
    (HomologicalComplex.cyclesMap_i (cochainsMap φ f) p)

theorem map_cohomologyπ (x : cocycles A p) :
    map φ f p (cohomologyπ A p x) =
      cohomologyπ B p (cocyclesMap φ f p x) :=
  ConcreteCategory.congr_hom (cohomologyπ_map φ f p) x

end MapAlong

end Langlands.ProfiniteCohomology

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Associativity

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]

end Associativity

section Unit

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem d_oneCochain :
    (inhomogeneousCochains.d (𝟙_ (Rep.{u} k G)) 0).hom (oneCochain (k := k) (G := G)) = 0 := by
  funext g
  simp [inhomogeneousCochains.d_hom_apply, oneCochain]
  rfl

def unitCocycle : cocycles (𝟙_ (Rep.{u} k G)) 0 :=
  (cochains (𝟙_ (Rep.{u} k G))).cyclesMk
    (mkCochain (𝟙_ (Rep.{u} k G)) oneCochain (IsLocallyConstant.const _)) 1 (by simp) (by
      apply cochainOf_injective (A := 𝟙_ (Rep.{u} k G))
      exact (cochainOf_d (A := 𝟙_ (Rep.{u} k G)) _).trans d_oneCochain)

@[simp]
theorem cochainOf_cocycleι_unitCocycle :
    cochainOf _ (cocycleι _ 0 (unitCocycle (k := k) (G := G))) = oneCochain :=
  congrArg (cochainOf _) ((cochains (𝟙_ (Rep.{u} k G))).i_cyclesMk _ _ _ _)

def unitClass : cohomology (𝟙_ (Rep.{u} k G)) 0 :=
  cohomologyπ _ 0 unitCocycle

variable {A : Rep.{u} k G} [IsSmoothRep A]

theorem cohomologyMap_leftUnitor_unitClass_cup {q : ℕ} (x : cohomology A q) :
    coeffMap (λ_ A).hom q (cup (zero_add q) unitClass x) = x := by
  refine cohomology_induction_on x fun x => ?_
  rw [unitClass, cup_cohomologyπ, cohomologyMap_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap]
  simp only [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cochainOf_cocycleι_unitCocycle]
  funext g
  exact leftUnitor_oneCochain_cupCochain _ g

theorem cohomologyMap_rightUnitor_cup_unitClass {p : ℕ} (x : cohomology A p) :
    coeffMap (ρ_ A).hom p (cup (add_zero p) x unitClass) = x := by
  refine cohomology_induction_on x fun x => ?_
  rw [unitClass, cup_cohomologyπ, cohomologyMap_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap]
  simp only [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cochainOf_cocycleι_unitCocycle]
  funext g
  exact rightUnitor_cupCochain_oneCochain _ g

end Unit

end Langlands.ProfiniteCohomology
