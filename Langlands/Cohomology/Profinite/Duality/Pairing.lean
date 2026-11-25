import Langlands.Cohomology.Profinite.Cup.Connecting
import Langlands.Cohomology.Profinite.Dimension.Basic
import Langlands.Cohomology.Profinite.Duality.DualModule
import Mathlib.CategoryTheory.Limits.Shapes.Countable

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory Limits

universe u

section Additive

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem cohomologyMap_finsetSum {B C : Rep.{u} k G} [IsSmoothRep B] [IsSmoothRep C] {ι : Type*}
    (s : Finset ι) (f : ι → (B ⟶ C)) (m : ℕ) :
    coeffMap (∑ i ∈ s, f i) m = ∑ i ∈ s, coeffMap (f i) m := by
  classical
  induction s using Finset.induction with
  | empty => simp [coeffMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cohomologyMap_add, ih]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem dualMap_add (D : Rep.{u} k G) {A B : Rep.{u} k G} (f₁ f₂ : A ⟶ B) :
    dualMap D (f₁ + f₂) = dualMap D f₁ + dualMap D f₂ := by
  apply Rep.Hom.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro g
  apply LinearMap.ext
  intro a
  show g ((f₁ + f₂).hom a) = g (f₁.hom a) + g (f₂.hom a)
  rw [Rep.add_hom, Representation.IntertwiningMap.coe_add, Pi.add_apply, map_add]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem dualMap_zero (D : Rep.{u} k G) {A B : Rep.{u} k G} :
    dualMap D (0 : A ⟶ B) = 0 := by
  apply Rep.Hom.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro g
  apply LinearMap.ext
  intro a
  show g ((0 : A ⟶ B).hom a) = 0
  rw [Rep.zero_hom, Representation.IntertwiningMap.coe_zero, Pi.zero_apply, map_zero]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem dualMap_finsetSum (D : Rep.{u} k G) {A B : Rep.{u} k G} {ι : Type*} (s : Finset ι)
    (f : ι → (A ⟶ B)) : dualMap D (∑ i ∈ s, f i) = ∑ i ∈ s, dualMap D (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [dualMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dualMap_add, ih]

end Additive

section Natural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (D : Rep.{u} k G) [IsSmoothRep D] {n m r s : ℕ} (h : r + s = m) (t : cohomology D m →+ ZMod n)

theorem cupPairing_evalPairing_cohomologyMap {A B : Rep.{u} k G} [IsSmoothRep A]
    [IsSmoothRep B] [IsSmoothRep (dualRep D A)] [IsSmoothRep (dualRep D B)] (f : A ⟶ B)
    (x : cohomology A r) (y : cohomology (dualRep D B) s) :
    cupPairing (evalPairing D B) h (coeffMap f r x) y =
      cupPairing (evalPairing D A) h x (coeffMap (dualMap D f) s y) := by
  have hy : y = coeffMap (𝟙 (dualRep D B)) s y := by rw [coeffMap_id]; rfl
  have hx : x = coeffMap (𝟙 A) r x := by rw [coeffMap_id]; rfl
  conv_lhs => rw [hy]
  conv_rhs => rw [hx]
  rw [cupPairing_cohomologyMap, cupPairing_cohomologyMap, tensorHom_evalPairing]

theorem dualityMap_cohomologyMap {A B : Rep.{u} k G} [IsSmoothRep A]
    [IsSmoothRep B] [IsSmoothRep (dualRep D A)] [IsSmoothRep (dualRep D B)] (f : A ⟶ B)
    (x : cohomology A r) (y : cohomology (dualRep D B) s) :
    dualityMap D h t B (coeffMap f r x) y =
      dualityMap D h t A x (coeffMap (dualMap D f) s y) := by
  rw [dualityMap_apply, dualityMap_apply, cupPairing_evalPairing_cohomologyMap]

theorem bijective_dualityMap_of_sum {J : Type*} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsSmoothRep (X j)] [∀ j, IsSmoothRep (dualRep D (X j))] (P : Rep.{u} k G)
    [IsSmoothRep P] [IsSmoothRep (dualRep D P)] (i : ∀ j, X j ⟶ P) (p : ∀ j, P ⟶ X j)
    (hsum : ∑ j, p j ≫ i j = 𝟙 P) (hX : ∀ j, Function.Bijective (dualityMap D h t (X j))) :
    Function.Bijective (dualityMap D h t P) := by

  have hdecomp : ∀ x : cohomology P r,
      x = ∑ j, coeffMap (i j) r (coeffMap (p j) r x) := by
    intro x
    have e := congrArg (fun φ => (coeffMap φ r).hom x) hsum
    simp only [cohomologyMap_finsetSum, coeffMap_id, coeffMap_comp, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_id, LinearMap.id_apply] at e
    exact e.symm
  have hdual : ∀ y : cohomology (dualRep D P) s,
      ∑ j, coeffMap (dualMap D (p j)) s (coeffMap (dualMap D (i j)) s y) = y := by
    intro y
    have e := congrArg (fun φ => (coeffMap (dualMap D φ) s).hom y) hsum
    simp only [dualMap_finsetSum, dualMap_comp, cohomologyMap_finsetSum, dualMap_id,
      coeffMap_id, coeffMap_comp, ModuleCat.hom_sum, LinearMap.sum_apply,
      ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at e
    exact e
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hj : ∀ j, coeffMap (p j) r x = 0 := by
      intro j
      apply (hX j).1
      rw [map_zero]
      ext y
      rw [AddMonoidHom.zero_apply, dualityMap_cohomologyMap, hx, AddMonoidHom.zero_apply]
    rw [hdecomp x]
    simp [hj]
  · intro χ
    choose a ha using fun j => (hX j).2 (χ.comp (coeffMap (dualMap D (p j)) s).hom.toAddMonoidHom)
    refine ⟨∑ j, coeffMap (i j) r (a j), ?_⟩
    ext y
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    conv_rhs => rw [← hdual y, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dualityMap_cohomologyMap, ha j]
    rfl

end Natural

section Biproduct

variable {k G : Type u} [CommRing k] [Group G]

instance hasFiniteBiproducts_rep : HasFiniteBiproducts (Rep.{u} k G) :=
  HasFiniteBiproducts.of_hasFiniteProducts

theorem biproduct_eq_sum {J : Type} [Fintype J] (X : J → Rep.{u} k G) (x : ((⨁ X : Rep.{u} k G) : Type u)) :
    x = ∑ j, (biproduct.ι X j).hom ((biproduct.π X j).hom x) :=
  calc x = (𝟙 (⨁ X) : ⨁ X ⟶ ⨁ X).hom x := rfl
    _ = (∑ j, biproduct.π X j ≫ biproduct.ι X j : ⨁ X ⟶ ⨁ X).hom x := by
      rw [biproduct.total (f := X)]
    _ = _ := by
      rw [Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
      rfl

instance finite_biproduct {J : Type} [Fintype J] (X : J → Rep.{u} k G) [∀ j, Finite (X j)] :
    Finite ((⨁ X : Rep.{u} k G) : Type u) :=
  Finite.of_injective (fun x : ((⨁ X : Rep.{u} k G) : Type u) => fun j => (biproduct.π X j).hom x) fun x y hxy => by
    rw [biproduct_eq_sum X x, biproduct_eq_sum X y]
    exact Finset.sum_congr rfl fun j _ => congrArg (biproduct.ι X j).hom (congrFun hxy j)

variable [TopologicalSpace G] [IsTopologicalGroup G]

instance isSmoothRep_dualRep_biproduct (D : Rep.{u} k G) [IsSmoothRep D] {J : Type} [Fintype J]
    (X : J → Rep.{u} k G) [∀ j, IsSmoothRep (X j)] [∀ j, Finite (X j)] :
    IsSmoothRep (dualRep D (⨁ X)) :=
  isSmoothRep_dualRep D (⨁ X)

theorem bijective_dualityMap_biproduct (D : Rep.{u} k G) [IsSmoothRep D] {n : ℕ} {J : Type}
    [Fintype J] (X : J → Rep.{u} k G) [∀ j, IsSmoothRep (X j)] [∀ j, Finite (X j)] {r s : ℕ}
    (h : r + s = 2) (t : cohomology D 2 →+ ZMod n)
    (hX : ∀ j, Function.Bijective (dualityMap D h t (X j))) :
    Function.Bijective (dualityMap D h t (⨁ X)) :=
  bijective_dualityMap_of_sum D h t X (⨁ X) (biproduct.ι X) (biproduct.π X)
    (biproduct.total (f := X)) hX

end Biproduct

section Embedding

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

def fixingOpenSubgroup (M : Rep.{u} k Γ) [IsSmoothRep M] [Finite M] : OpenSubgroup Γ where
  toSubgroup := ⨅ m : M, vectorStabilizer M.ρ m
  isOpen' := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    rw [Subgroup.coe_iInf]
    exact Filter.iInter_mem.2 fun m => (IsSmoothRep.isOpen_stabilizer M m).mem_nhds (one_mem _)

theorem fixingOpenSubgroup_apply (M : Rep.{u} k Γ) [IsSmoothRep M] [Finite M] {w : Γ}
    (hw : w ∈ fixingOpenSubgroup M) (m : M) : M.ρ w m = m := by
  have : w ∈ ⨅ m : M, vectorStabilizer M.ρ m := hw
  rw [Subgroup.mem_iInf] at this
  exact this m

variable {n : ℕ}

def charHom (W : Subgroup Γ) (M : Rep.{u} (ULift.{u} ℤ) Γ) (hW : ∀ w ∈ W, ∀ m : M, M.ρ w m = m)
    (χ : M →+ ZMod n) : Rep.res W.subtype M ⟶ zmodRep.{u} W n :=
  Rep.ofHom ⟨(uliftIntLinearEquivAddHom (Rep.res W.subtype M) (zmodRep.{u} W n)).symm
    ((AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n).symm.toAddMonoidHom.comp χ), fun w => by
      refine LinearMap.ext fun m => ?_
      change ULift.up (χ (M.ρ w m)) = ULift.up (χ m)
      rw [hW w w.2 m]⟩

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem charHom_hom_apply (W : Subgroup Γ) (M : Rep.{u} (ULift.{u} ℤ) Γ)
    (hW : ∀ w ∈ W, ∀ m : M, M.ρ w m = m) (χ : M →+ ZMod n) (m : M) :
    (charHom W M hW χ).hom m = (ULift.up (χ m) : zmodRep.{u} W n) :=
  rfl

theorem exists_injective_biproduct_coind [NeZero n] (M : Rep.{u} (ULift.{u} ℤ) Γ)
    [IsSmoothRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    ∃ (W : OpenSubgroup Γ) (J : Type) (_ : Fintype J)
      (i : M ⟶ ⨁ fun _ : J => Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)),
      Function.Injective i.hom := by
  let W := fixingOpenSubgroup M
  have hW : ∀ w ∈ (W : Subgroup Γ), ∀ m : M, M.ρ w m = m :=
    fun w hw m => fixingOpenSubgroup_apply M hw m
  let e := (Finite.equivFin (M →+ ZMod n)).symm
  let F : ∀ _ : Fin (Nat.card (M →+ ZMod n)),
      M ⟶ Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n) :=
    fun j => Rep.resCoindToHom (W : Subgroup Γ).subtype M _ (charHom (W : Subgroup Γ) M hW (e j))
  refine ⟨W, Fin (Nat.card (M →+ ZMod n)), inferInstance, biproduct.lift F, ?_⟩
  intro a b hab
  by_contra hne
  obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hM (sub_ne_zero.2 hne)
  apply hχ
  have hj := congrArg (biproduct.π (fun _ : Fin (Nat.card (M →+ ZMod n)) =>
    Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) (e.symm χ)).hom hab
  change (biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom a =
    (biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom b at hj
  rw [biproduct.lift_π] at hj
  have h1 := congrArg (fun f => ULift.down (f.1 1 : ULift.{u} (ZMod n))) hj
  simp only [F, Rep.resCoindToHom_hom_apply_coe, map_one, Module.End.one_apply,
    Equiv.apply_symm_apply] at h1
  rw [charHom_hom_apply, charHom_hom_apply] at h1
  change χ a = χ b at h1
  rw [map_sub, h1, sub_self]

end Embedding

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory groupCohomology GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {S T : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃] [IsSmoothRep T.X₁] [IsSmoothRep T.X₂] [IsSmoothRep T.X₃]
  {C : Rep.{u} k G} [IsSmoothRep C]
  (μ₁ : S.X₁ ⊗ T.X₃ ⟶ C) (μ₂ : S.X₂ ⊗ T.X₂ ⟶ C) (μ₃ : S.X₃ ⊗ T.X₁ ⟶ C)

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep S.X₁] [IsSmoothRep S.X₂] [IsSmoothRep S.X₃] [IsSmoothRep T.X₁]
  [IsSmoothRep T.X₂] [IsSmoothRep T.X₃] [IsSmoothRep C] in

theorem cupCochain_pairing_left (h₁₂ : (S.f ⊗ₘ 𝟙 T.X₂) ≫ μ₂ = (𝟙 S.X₁ ⊗ₘ T.g) ≫ μ₁)
    {p q n : ℕ} (h : p + q = n) (a : (Fin p → G) → S.X₁) (b : (Fin q → G) → T.X₂)
    (σ : Fin n → G) :
    μ₂.hom (cupCochain h (fun τ => S.f.hom (a τ)) b σ) =
      μ₁.hom (cupCochain h a (fun τ => T.g.hom (b τ)) σ) := by
  have e := congrArg (fun φ : S.X₁ ⊗ T.X₂ ⟶ C => φ.hom (cupCochain h a b σ)) h₁₂
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply] at e
  rw [tensorHom_cupCochain, tensorHom_cupCochain] at e
  exact e

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep S.X₁] [IsSmoothRep S.X₂] [IsSmoothRep S.X₃] [IsSmoothRep T.X₁]
  [IsSmoothRep T.X₂] [IsSmoothRep T.X₃] [IsSmoothRep C] in

theorem cupCochain_pairing_right (h₂₃ : (𝟙 S.X₂ ⊗ₘ T.f) ≫ μ₂ = (S.g ⊗ₘ 𝟙 T.X₁) ≫ μ₃)
    {p q n : ℕ} (h : p + q = n) (a : (Fin p → G) → S.X₂) (b : (Fin q → G) → T.X₁)
    (σ : Fin n → G) :
    μ₂.hom (cupCochain h a (fun τ => T.f.hom (b τ)) σ) =
      μ₃.hom (cupCochain h (fun τ => S.g.hom (a τ)) b σ) := by
  have e := congrArg (fun φ : S.X₂ ⊗ T.X₁ ⟶ C => φ.hom (cupCochain h a b σ)) h₂₃
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply] at e
  rw [tensorHom_cupCochain, tensorHom_cupCochain] at e
  exact e

theorem cupPairing_δ_add_cupPairing_δ (h₁₂ : (S.f ⊗ₘ 𝟙 T.X₂) ≫ μ₂ = (𝟙 S.X₁ ⊗ₘ T.g) ≫ μ₁)
    (h₂₃ : (𝟙 S.X₂ ⊗ₘ T.f) ≫ μ₂ = (S.g ⊗ₘ 𝟙 T.X₁) ≫ μ₃) (hS : S.ShortExact) (hT : T.ShortExact)
    {p p' q q' n : ℕ} (hp : p + 1 = p') (hq : q + 1 = q') (h₁ : p' + q = n) (h₃ : p + q' = n)
    (x : cohomology S.X₃ p) (y : cohomology T.X₃ q) :
    cupPairing μ₁ h₁ (δ hS p p' hp x) y + (-1 : k) ^ p • cupPairing μ₃ h₃ x (δ hT q q' hq y) =
      0 := by
  subst hp hq
  obtain rfl : n = p + q + 1 := by omega
  obtain ⟨x₃, rfl⟩ := cohomologyπ_surjective S.X₃ p x
  obtain ⟨y₃, rfl⟩ := cohomologyπ_surjective T.X₃ q y
  have := hS.epi_g
  have := hT.epi_g
  obtain ⟨x₂, hx₂⟩ := (ModuleCat.epi_iff_surjective ((coeffCochainsMap S.g).f p)).1 inferInstance
    (cocycleι S.X₃ p x₃)
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d hS (p + 1) x₃ x₂ hx₂
  obtain ⟨y₂, hy₂⟩ := (ModuleCat.epi_iff_surjective ((coeffCochainsMap T.g).f q)).1 inferInstance
    (cocycleι T.X₃ q y₃)
  obtain ⟨y₁, hy₁⟩ := exists_cocycle_map_f_eq_d hT (q + 1) y₃ y₂ hy₂
  have hx₂' : (fun σ => S.g.hom (cochainOf S.X₂ x₂ σ)) = cochainOf S.X₃ (cocycleι S.X₃ p x₃) :=
    congrArg (cochainOf S.X₃) hx₂
  have hx₁' : (fun σ => S.f.hom (cochainOf S.X₁ (cocycleι S.X₁ (p + 1) x₁) σ)) =
      (inhomogeneousCochains.d S.X₂ p).hom (cochainOf S.X₂ x₂) :=
    (congrArg (cochainOf S.X₂) hx₁).trans (cochainOf_d x₂)
  have hy₂' : (fun σ => T.g.hom (cochainOf T.X₂ y₂ σ)) = cochainOf T.X₃ (cocycleι T.X₃ q y₃) :=
    congrArg (cochainOf T.X₃) hy₂
  have hy₁' : (fun σ => T.f.hom (cochainOf T.X₁ (cocycleι T.X₁ (q + 1) y₁) σ)) =
      (inhomogeneousCochains.d T.X₂ q).hom (cochainOf T.X₂ y₂) :=
    (congrArg (cochainOf T.X₂) hy₁).trans (cochainOf_d y₂)
  rw [δ_cohomologyπ_of_lift hS rfl x₃ x₂ hx₂ x₁ hx₁, δ_cohomologyπ_of_lift hT rfl y₃ y₂ hy₂ y₁ hy₁,
    cupPairing_cohomologyπ, cupPairing_cohomologyπ, ← map_smul, ← map_add]
  have key : HomologicalComplex.cyclesMap (coeffCochainsMap μ₁) (p + q + 1) (cupCocycles h₁ x₁ y₃) +
      (-1 : k) ^ p • HomologicalComplex.cyclesMap (coeffCochainsMap μ₃) (p + q + 1)
        (cupCocycles h₃ x₃ y₁) =
      (cochains C).toCycles (p + q) (p + q + 1)
        ((coeffCochainsMap μ₂).f (p + q) (cupLocallyConstant rfl x₂ y₂)) := by
    apply cocycleι_injective
    apply cochainOf_injective
    have hcomm := ConcreteCategory.congr_hom ((coeffCochainsMap μ₂).comm (p + q) (p + q + 1))
      (cupLocallyConstant rfl x₂ y₂)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomm
    rw [map_add, map_smul, cochainOf_add, cochainOf_smul, cochainOf_cocycleι_cyclesMap,
      cochainOf_cocycleι_cyclesMap, cocycleι_cupCocycles, cocycleι_cupCocycles,
      cochainOf_cocycleι_toCycles, ← cochainOf_d, hcomm, cochainOf_cochainsMap_f, cochainOf_d]
    simp only [cochainOf_cupLocallyConstant]
    rw [d_cupCochain, ← hx₁', ← hy₁']
    funext σ
    rw [Pi.add_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, map_add, map_smul,
      cupCochain_pairing_left μ₁ μ₂ h₁₂, cupCochain_pairing_right μ₂ μ₃ h₂₃, hx₂', hy₂']
  rw [key, cohomologyπ_toCycles]

theorem cupPairing_δ_eq (h₁₂ : (S.f ⊗ₘ 𝟙 T.X₂) ≫ μ₂ = (𝟙 S.X₁ ⊗ₘ T.g) ≫ μ₁)
    (h₂₃ : (𝟙 S.X₂ ⊗ₘ T.f) ≫ μ₂ = (S.g ⊗ₘ 𝟙 T.X₁) ≫ μ₃) (hS : S.ShortExact) (hT : T.ShortExact)
    {p p' q q' n : ℕ} (hp : p + 1 = p') (hq : q + 1 = q') (h₁ : p' + q = n) (h₃ : p + q' = n)
    (x : cohomology S.X₃ p) (y : cohomology T.X₃ q) :
    cupPairing μ₁ h₁ (δ hS p p' hp x) y =
      (-1 : k) ^ (p + 1) • cupPairing μ₃ h₃ x (δ hT q q' hq y) := by
  rw [eq_neg_of_add_eq_zero_left
    (cupPairing_δ_add_cupPairing_δ μ₁ μ₂ μ₃ h₁₂ h₂₃ hS hT hp hq h₁ h₃ x y), pow_succ, mul_neg_one,
    neg_smul]

end Langlands.ProfiniteCohomology
