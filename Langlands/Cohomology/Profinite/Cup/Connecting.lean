import Langlands.Cohomology.Profinite.Cup.Basic
import Langlands.Cohomology.Profinite.LongExactSequence

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Cochains

variable {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]

theorem cochainOf_cochainsMap_f (f : A ⟶ B) {i : ℕ} (a : (cochains A).X i) :
    cochainOf B ((coeffCochainsMap f).f i a) = fun σ => f.hom (cochainOf A a σ) :=
  rfl

end Cochains

section Connecting

variable {S : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃]

theorem δ_cohomologyπ_of_lift (hS : S.ShortExact) {i j : ℕ} (hij : i + 1 = j)
    (x₃ : cocycles S.X₃ i) (x₂ : (cochains S.X₂).X i)
    (hx₂ : (coeffCochainsMap S.g).f i x₂ = cocycleι S.X₃ i x₃) (x₁ : cocycles S.X₁ j)
    (hx₁ : (coeffCochainsMap S.f).f j (cocycleι S.X₁ j x₁) =
      (cochains S.X₂).d i j x₂) :
    δ hS i j hij (cohomologyπ S.X₃ i x₃) = cohomologyπ S.X₁ j x₁ := by
  have hx₃ : (cochains S.X₃).d i j (cocycleι S.X₃ i x₃) = 0 :=
    ConcreteCategory.congr_hom ((cochains S.X₃).iCycles_d i j) x₃
  have key := (cochainsShortComplex_shortExact hS).δ_apply i j hij (cocycleι S.X₃ i x₃) hx₃ x₂
    hx₂ (cocycleι S.X₁ j x₁) hx₁ (j + 1) (by simp)
  have e3 : (cochains S.X₃).cyclesMk (cocycleι S.X₃ i x₃) j
      ((ComplexShape.up ℕ).next_eq' hij) hx₃ = x₃ :=
    cocycleι_injective ((cochains S.X₃).i_cyclesMk _ _ _ _)
  have e1 : (cochains S.X₁).cyclesMk (cocycleι S.X₁ j x₁) (j + 1) (by simp)
      ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂
        (cocycleι S.X₁ j x₁) hx₁ (j + 1)) = x₁ :=
    cocycleι_injective ((cochains S.X₁).i_cyclesMk _ _ _ _)
  calc δ hS i j hij (cohomologyπ S.X₃ i x₃)
      = δ hS i j hij (cohomologyπ S.X₃ i ((cochains S.X₃).cyclesMk (cocycleι S.X₃ i x₃) j
          ((ComplexShape.up ℕ).next_eq' hij) hx₃)) := by rw [e3]
    _ = cohomologyπ S.X₁ j ((cochains S.X₁).cyclesMk (cocycleι S.X₁ j x₁) (j + 1)
          (by simp) ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂
            (cocycleι S.X₁ j x₁) hx₁ (j + 1))) := key
    _ = cohomologyπ S.X₁ j x₁ := by rw [e1]

theorem exists_cocycle_map_f_eq_d (hS : S.ShortExact) {i : ℕ} (j : ℕ)
    (x₃ : cocycles S.X₃ i) (x₂ : (cochains S.X₂).X i)
    (hx₂ : (coeffCochainsMap S.g).f i x₂ = cocycleι S.X₃ i x₃) :
    ∃ x₁ : cocycles S.X₁ j, (coeffCochainsMap S.f).f j (cocycleι S.X₁ j x₁) =
      (cochains S.X₂).d i j x₂ := by
  have hex := (HomologicalComplex.exact_iff_degreewise_exact _).1
    (cochainsShortComplex_shortExact hS).exact j
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hz : ((coeffCochainsMap S.g).f j).hom ((cochains S.X₂).d i j x₂) = 0 := by
    have hc := ConcreteCategory.congr_hom ((coeffCochainsMap S.g).comm i j) x₂
    have hd := ConcreteCategory.congr_hom ((cochains S.X₃).iCycles_d i j) x₃
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hc
    rw [ConcreteCategory.comp_apply] at hd
    rw [← hc, hx₂]
    exact hd
  obtain ⟨x₁, hx₁⟩ := hex _ hz
  have hx₁' : (coeffCochainsMap S.f).f j x₁ = (cochains S.X₂).d i j x₂ := hx₁
  refine ⟨(cochains S.X₁).cyclesMk x₁ (j + 1) (by simp)
    ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂ x₁ hx₁' (j + 1)), ?_⟩
  have e : cocycleι S.X₁ j ((cochains S.X₁).cyclesMk x₁ (j + 1) (by simp)
      ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂ x₁ hx₁'
        (j + 1))) = x₁ :=
    (cochains S.X₁).i_cyclesMk _ _ _ _
  rw [e]
  exact hx₁'

end Connecting

section TensorRight

variable {S : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃] (B : Rep.{u} k G) [IsSmoothRep B]

instance isSmoothRep_map_tensorRight_X₁ : IsSmoothRep (S.map (tensorRight B)).X₁ :=
  isSmoothRep_tensor S.X₁ B

instance isSmoothRep_map_tensorRight_X₂ : IsSmoothRep (S.map (tensorRight B)).X₂ :=
  isSmoothRep_tensor S.X₂ B

instance isSmoothRep_map_tensorRight_X₃ : IsSmoothRep (S.map (tensorRight B)).X₃ :=
  isSmoothRep_tensor S.X₃ B

variable {B}

theorem δ_cup_of_shortExact_tensorRight (hS : S.ShortExact)
    (hSB : (S.map (tensorRight B)).ShortExact) {p p' q n n' : ℕ} (hp : p + 1 = p')
    (hn : n + 1 = n') (h : p + q = n) (h' : p' + q = n') (x : cohomology S.X₃ p)
    (y : cohomology B q) :
    δ hSB n n' hn (cup h x y) = cup h' (δ hS p p' hp x) y := by
  subst hp hn
  obtain ⟨x₃, rfl⟩ := cohomologyπ_surjective S.X₃ p x
  obtain ⟨y, rfl⟩ := cohomologyπ_surjective B q y
  have := hS.epi_g
  obtain ⟨x₂, hx₂⟩ := (ModuleCat.epi_iff_surjective ((coeffCochainsMap S.g).f p)).1 inferInstance
    (cocycleι S.X₃ p x₃)
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d hS (p + 1) x₃ x₂ hx₂
  have hx₂' : (fun σ => S.g.hom (cochainOf S.X₂ x₂ σ)) = cochainOf S.X₃ (cocycleι S.X₃ p x₃) :=
    congrArg (cochainOf S.X₃) hx₂
  have hx₁' : (fun σ => S.f.hom (cochainOf S.X₁ (cocycleι S.X₁ (p + 1) x₁) σ)) =
      (inhomogeneousCochains.d S.X₂ p).hom (cochainOf S.X₂ x₂) :=
    (congrArg (cochainOf S.X₂) hx₁).trans (cochainOf_d x₂)
  rw [δ_cohomologyπ_of_lift hS rfl x₃ x₂ hx₂ x₁ hx₁, cup_cohomologyπ, cup_cohomologyπ]
  refine δ_cohomologyπ_of_lift hSB rfl (cupCocycles h x₃ y)
    (cupLocallyConstant h x₂ (cocycleι B q y)) ?_ (cupCocycles h' x₁ y) ?_
  · change (coeffCochainsMap (S.g ▷ B)).f n (cupLocallyConstant h x₂ (cocycleι B q y)) =
      cocycleι (S.X₃ ⊗ B) n (cupCocycles h x₃ y)
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f, cocycleι_cupCocycles, cochainOf_cupLocallyConstant,
      cochainOf_cupLocallyConstant, ← hx₂']
    funext σ
    rw [← tensorHom_id, tensorHom_cupCochain]
    rfl
  · change (coeffCochainsMap (S.f ▷ B)).f (n + 1) (cocycleι (S.X₁ ⊗ B) (n + 1) (cupCocycles h' x₁ y)) =
      (cochains (S.X₂ ⊗ B)).d n (n + 1) (cupLocallyConstant h x₂ (cocycleι B q y))
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f, cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cochainOf_d,
      cochainOf_cupLocallyConstant, d_cupCochain, d_cocycleι, cupCochain_zero_right, smul_zero,
      add_zero, ← hx₁']
    funext σ
    rw [← tensorHom_id, tensorHom_cupCochain]
    rfl

end TensorRight

section TensorLeft

variable {S : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃] (B : Rep.{u} k G) [IsSmoothRep B]

instance isSmoothRep_map_tensorLeft_X₁ : IsSmoothRep (S.map (tensorLeft B)).X₁ :=
  isSmoothRep_tensor B S.X₁

instance isSmoothRep_map_tensorLeft_X₂ : IsSmoothRep (S.map (tensorLeft B)).X₂ :=
  isSmoothRep_tensor B S.X₂

instance isSmoothRep_map_tensorLeft_X₃ : IsSmoothRep (S.map (tensorLeft B)).X₃ :=
  isSmoothRep_tensor B S.X₃

variable {B}

theorem δ_cup_of_shortExact_tensorLeft (hS : S.ShortExact)
    (hSB : (S.map (tensorLeft B)).ShortExact) {p p' q n n' : ℕ} (hp : p + 1 = p')
    (hn : n + 1 = n') (h : q + p = n) (h' : q + p' = n') (y : cohomology B q)
    (x : cohomology S.X₃ p) :
    δ hSB n n' hn (cup h y x) = (-1 : k) ^ q • cup h' y (δ hS p p' hp x) := by
  subst hp hn
  obtain ⟨x₃, rfl⟩ := cohomologyπ_surjective S.X₃ p x
  obtain ⟨y, rfl⟩ := cohomologyπ_surjective B q y
  have := hS.epi_g
  obtain ⟨x₂, hx₂⟩ := (ModuleCat.epi_iff_surjective ((coeffCochainsMap S.g).f p)).1 inferInstance
    (cocycleι S.X₃ p x₃)
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d hS (p + 1) x₃ x₂ hx₂
  have hx₂' : (fun σ => S.g.hom (cochainOf S.X₂ x₂ σ)) = cochainOf S.X₃ (cocycleι S.X₃ p x₃) :=
    congrArg (cochainOf S.X₃) hx₂
  have hx₁' : (fun σ => S.f.hom (cochainOf S.X₁ (cocycleι S.X₁ (p + 1) x₁) σ)) =
      (inhomogeneousCochains.d S.X₂ p).hom (cochainOf S.X₂ x₂) :=
    (congrArg (cochainOf S.X₂) hx₁).trans (cochainOf_d x₂)
  rw [δ_cohomologyπ_of_lift hS rfl x₃ x₂ hx₂ x₁ hx₁, cup_cohomologyπ, cup_cohomologyπ,
    ← map_smul]
  refine δ_cohomologyπ_of_lift hSB rfl (cupCocycles h y x₃)
    (cupLocallyConstant h (cocycleι B q y) x₂) ?_ ((-1 : k) ^ q • cupCocycles h' y x₁) ?_
  · change (coeffCochainsMap (B ◁ S.g)).f n (cupLocallyConstant h (cocycleι B q y) x₂) =
      cocycleι (B ⊗ S.X₃) n (cupCocycles h y x₃)
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f, cocycleι_cupCocycles, cochainOf_cupLocallyConstant,
      cochainOf_cupLocallyConstant, ← hx₂']
    funext σ
    rw [← id_tensorHom, tensorHom_cupCochain]
    rfl
  · change (coeffCochainsMap (B ◁ S.f)).f (n + 1)
        (cocycleι (B ⊗ S.X₁) (n + 1) ((-1 : k) ^ q • cupCocycles h' y x₁)) =
      (cochains (B ⊗ S.X₂)).d n (n + 1) (cupLocallyConstant h (cocycleι B q y) x₂)
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f, map_smul, cochainOf_smul, cocycleι_cupCocycles,
      cochainOf_cupLocallyConstant, cochainOf_d, cochainOf_cupLocallyConstant, d_cupCochain,
      d_cocycleι, cupCochain_zero_left, zero_add, ← hx₁']
    funext σ
    rw [Pi.smul_apply, Pi.smul_apply, map_smul, ← id_tensorHom, tensorHom_cupCochain]
    rfl

end TensorLeft

end Langlands.ProfiniteCohomology
