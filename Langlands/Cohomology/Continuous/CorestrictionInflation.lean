import Langlands.Cohomology.Tate.CohomologyTransferZero
import Langlands.Cohomology.Tate.CohomologyTransfer
import Langlands.Cohomology.Tate.StandardChains

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R]

section Prism

variable {X : Type u}

/-- Prepend a fixed first coordinate to homogeneous chains. -/
def chainCone (x : X) (m : ℕ) :
    MonoidAlgebra R (Fin m → X) →ₗ[R] MonoidAlgebra R (Fin (m + 1) → X) :=
  MonoidAlgebra.mapDomainLinearMap R R (fun e : Fin m → X => (Fin.cons x e : Fin (m + 1) → X))

lemma chainCone_single (x : X) (m : ℕ) (e : Fin m → X) (r : R) :
    chainCone x m (MonoidAlgebra.single e r) = MonoidAlgebra.single (Fin.cons x e) r :=
  MonoidAlgebra.mapDomainLinearMap_single _ r e

lemma cons_comp_succ_succAbove (x : X) {m : ℕ} (e : Fin (m + 1) → X) (p : Fin (m + 1)) :
    (Fin.cons x e : Fin (m + 2) → X) ∘ p.succ.succAbove = Fin.cons x (e ∘ p.succAbove) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [Fin.succ_succAbove_succ]

lemma standard_d_single_one (m : ℕ) (c : Fin (m + 1) → X) :
    Rep.standardComplex.d R X m (MonoidAlgebra.single c 1) =
      ∑ p : Fin (m + 1), ((-1 : R) ^ (p : ℕ)) • MonoidAlgebra.single (c ∘ p.succAbove) 1 := by
  rw [Rep.standardComplex.d_of]
  apply Finset.sum_congr rfl
  intro p _
  rw [MonoidAlgebra.smul_single', mul_one]

/-- The cone identity for the standard homogeneous differential. -/
lemma standard_d_chainCone_single (x : X) (m : ℕ) (e : Fin (m + 1) → X) :
    Rep.standardComplex.d R X (m + 1) (chainCone x (m + 1) (MonoidAlgebra.single e 1)) =
      MonoidAlgebra.single e 1 -
        chainCone x m (Rep.standardComplex.d R X m (MonoidAlgebra.single e 1)) := by
  rw [chainCone_single, standard_d_single_one, standard_d_single_one, map_sum,
    Fin.sum_univ_succ]
  have h0 : (Fin.cons x e : Fin (m + 2) → X) ∘ (0 : Fin (m + 2)).succAbove = e := by
    funext j
    simp
  rw [h0]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Finset.sum_neg_distrib, cons_comp_succ_succAbove, map_smul, chainCone_single,
    sub_eq_add_neg]

lemma standard_d_chainCone (x : X) (m : ℕ) (y : MonoidAlgebra R (Fin (m + 1) → X)) :
    Rep.standardComplex.d R X (m + 1) (chainCone x (m + 1) y) =
      y - chainCone x m (Rep.standardComplex.d R X m y) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]; abel
  | single e r =>
    rw [← mul_one r, ← MonoidAlgebra.smul_single', map_smul, map_smul,
      standard_d_chainCone_single, map_smul, map_smul, smul_sub]

variable {Y : Type u}

/-- The homogeneous differential with its zeroth face separated. -/
lemma standard_d_single_succ (m : ℕ) (c : Fin (m + 2) → X) :
    Rep.standardComplex.d R X (m + 1) (MonoidAlgebra.single c 1) =
      MonoidAlgebra.single (Fin.tail c) 1 -
        ∑ i : Fin (m + 1), ((-1 : R) ^ (i : ℕ)) •
          MonoidAlgebra.single (c ∘ i.succ.succAbove) 1 := by
  rw [standard_d_single_one, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Finset.sum_neg_distrib, ← sub_eq_add_neg, Fin.succAbove_zero]
  rfl

/-- The prism operator between the coordinatewise maps induced by `α` and `β`. -/
def chainPrism (α β : X → Y) :
    (m : ℕ) → MonoidAlgebra R (Fin m → X) →ₗ[R] MonoidAlgebra R (Fin (m + 1) → Y)
  | 0 => 0
  | m + 1 => (MonoidAlgebra.basis (Fin (m + 1) → X) R).constr R fun d =>
      MonoidAlgebra.single (Fin.cons (β (d 0)) (α ∘ d) : Fin (m + 2) → Y) 1 -
        chainCone (β (d 0)) (m + 1) (chainPrism α β m (MonoidAlgebra.single (Fin.tail d) 1))

lemma chainPrism_zero (α β : X → Y) : chainPrism (R := R) α β 0 = 0 := rfl

lemma chainPrism_succ_single (α β : X → Y) (m : ℕ) (d : Fin (m + 1) → X) :
    chainPrism (R := R) α β (m + 1) (MonoidAlgebra.single d 1) =
      MonoidAlgebra.single (Fin.cons (β (d 0)) (α ∘ d) : Fin (m + 2) → Y) 1 -
        chainCone (β (d 0)) (m + 1) (chainPrism α β m (MonoidAlgebra.single (Fin.tail d) 1)) := by
  rw [chainPrism, ← MonoidAlgebra.basis_apply, Module.Basis.constr_basis]

lemma comp_succ_succAbove_zero {m : ℕ} (d : Fin (m + 2) → X) (i : Fin (m + 1)) :
    (d ∘ i.succ.succAbove) 0 = d 0 := by
  simp

lemma tail_comp_succ_succAbove {m : ℕ} (d : Fin (m + 2) → X) (i : Fin (m + 1)) :
    Fin.tail (d ∘ i.succ.succAbove) = Fin.tail d ∘ i.succAbove := by
  funext j
  simp [Fin.tail, Fin.succ_succAbove_succ]

/-- The prism identity `∂P + P∂ = α - β` on homogeneous generators. -/
lemma chainPrism_identity_single (α β : X → Y) (j : ℕ) (d : Fin (j + 1) → X) :
    Rep.standardComplex.d R Y (j + 1) (chainPrism α β (j + 1) (MonoidAlgebra.single d 1)) +
        chainPrism α β j (Rep.standardComplex.d R X j (MonoidAlgebra.single d 1)) =
      MonoidAlgebra.single (α ∘ d) 1 - MonoidAlgebra.single (β ∘ d) 1 := by
  induction j with
  | zero =>
    rw [chainPrism_succ_single, chainPrism_zero, LinearMap.zero_apply, LinearMap.zero_apply,
      map_zero, sub_zero, add_zero, ← chainCone_single, standard_d_chainCone,
      standard_d_single_one, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul,
      chainCone_single]
    congr 2
    funext i
    rw [Fin.eq_zero i]
    rfl
  | succ j ih =>
    have hP : ∀ i : Fin (j + 1),
        chainPrism (R := R) α β (j + 1) (MonoidAlgebra.single (d ∘ i.succ.succAbove) 1) =
          chainCone (β (d 0)) (j + 1) (MonoidAlgebra.single (α ∘ d ∘ i.succ.succAbove) 1) -
            chainCone (β (d 0)) (j + 1)
              (chainPrism α β j (MonoidAlgebra.single (Fin.tail d ∘ i.succAbove) 1)) := by
      intro i
      rw [chainPrism_succ_single, comp_succ_succAbove_zero, tail_comp_succ_succAbove,
        chainCone_single]
    have hα : Rep.standardComplex.d R Y (j + 1) (MonoidAlgebra.single (α ∘ d) 1) =
        MonoidAlgebra.single (α ∘ Fin.tail d) 1 -
          ∑ i : Fin (j + 1), ((-1 : R) ^ (i : ℕ)) •
            MonoidAlgebra.single (α ∘ d ∘ i.succ.succAbove) 1 :=
      standard_d_single_succ j (α ∘ d)
    have hβ : chainCone (β (d 0)) (j + 1) (MonoidAlgebra.single (β ∘ Fin.tail d) 1) =
        (MonoidAlgebra.single (β ∘ d) 1 : MonoidAlgebra R (Fin (j + 2) → Y)) := by
      rw [chainCone_single]
      congr 1
      funext i
      exact Fin.cases rfl (fun i => rfl) i
    have ih' := eq_sub_of_add_eq (ih (Fin.tail d))
    rw [chainPrism_succ_single, map_sub, ← chainCone_single, standard_d_chainCone,
      standard_d_chainCone, hα, standard_d_single_succ, map_sub, map_sum]
    rw [ih', standard_d_single_one j (Fin.tail d)]
    simp only [map_sub, map_sum, map_smul, hP, hβ, smul_sub, Finset.sum_sub_distrib]
    abel


lemma mapDomain_chainCone {X Y : Type u} (τ : X → Y) (x : X) (m : ℕ)
    (z : MonoidAlgebra R (Fin m → X)) :
    MonoidAlgebra.mapDomainLinearMap R R (fun e : Fin (m + 1) → X => τ ∘ e) (chainCone x m z) =
      chainCone (τ x) m (MonoidAlgebra.mapDomainLinearMap R R (fun e : Fin m → X => τ ∘ e) z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | single e r =>
    rw [chainCone_single, MonoidAlgebra.mapDomainLinearMap_single,
      MonoidAlgebra.mapDomainLinearMap_single, chainCone_single, Fin.comp_cons]

/-- The prism operator commutes with compatible coordinatewise maps. -/
lemma chainPrism_mapDomain {X Y : Type u} (α β : X → Y) (σ : X → X) (τ : Y → Y)
    (hα : ∀ x, α (σ x) = τ (α x)) (hβ : ∀ x, β (σ x) = τ (β x)) (m : ℕ)
    (z : MonoidAlgebra R (Fin m → X)) :
    chainPrism α β m (MonoidAlgebra.mapDomainLinearMap R R (fun e : Fin m → X => σ ∘ e) z) =
      MonoidAlgebra.mapDomainLinearMap R R (fun e : Fin (m + 1) → Y => τ ∘ e)
        (chainPrism α β m z) := by
  induction m with
  | zero => simp [chainPrism_zero]
  | succ m ih =>
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | single e r =>
      rw [← mul_one r, ← MonoidAlgebra.smul_single', map_smul, map_smul, map_smul, map_smul,
        MonoidAlgebra.mapDomainLinearMap_single, chainPrism_succ_single,
        chainPrism_succ_single, map_sub, MonoidAlgebra.mapDomainLinearMap_single,
        mapDomain_chainCone]
      have ht : (Fin.tail (σ ∘ e) : Fin m → X) = σ ∘ Fin.tail e := rfl
      have h0 : β ((σ ∘ e) 0) = τ (β (e 0)) := hβ (e 0)
      have he : α ∘ σ ∘ e = τ ∘ α ∘ e := funext fun i => hα (e i)
      rw [ht, h0, ← MonoidAlgebra.mapDomainLinearMap_single (R := R) (S := R)
        (fun e : Fin m → X => σ ∘ e) (1 : R) (Fin.tail e), ih, Fin.comp_cons, he]

end Prism

section Coordinates

variable {H G₁ G₂ : Type u} [Group H] [Group G₁] [Group G₂]

/-- The diagonal action on homogeneous chains is coordinatewise left multiplication. -/
lemma diagonal_ρ_eq {G : Type u} [Group G] (g : G) (m : ℕ) :
    (Rep.diagonal R G m).ρ g =
      MonoidAlgebra.mapDomainLinearMap R R (fun e : Fin m → G => (fun x => g * x) ∘ e) := by
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change Representation.ofMulAction R G (Fin m → G) g (MonoidAlgebra.single c 1) =
    MonoidAlgebra.mapDomainLinearMap R R (fun e : Fin m → G => (fun x => g * x) ∘ e)
      (MonoidAlgebra.single c 1)
  rw [Representation.ofMulAction_single, MonoidAlgebra.mapDomainLinearMap_single]
  rfl

/-- The coordinatewise map of diagonal representations induced by an equivariant map. -/
def coordinateHom (ι : H →* G₁) (ψ : H →* G₂) (θ : G₁ → G₂)
    (hθ : ∀ h g, θ (ι h * g) = ψ h * θ g) (m : ℕ) :
    Rep.res ι (Rep.diagonal R G₁ m) ⟶ Rep.res ψ (Rep.diagonal R G₂ m) :=
  Rep.ofHom ⟨MonoidAlgebra.mapDomainLinearMap R R (fun c : Fin m → G₁ => θ ∘ c), fun h => by
    apply MonoidAlgebra.lhom_ext'
    intro c
    apply LinearMap.ext_ring
    change MonoidAlgebra.mapDomainLinearMap R R (fun c : Fin m → G₁ => θ ∘ c)
        (Representation.ofMulAction R G₁ (Fin m → G₁) (ι h) (MonoidAlgebra.single c 1)) =
      Representation.ofMulAction R G₂ (Fin m → G₂) (ψ h)
        (MonoidAlgebra.mapDomainLinearMap R R (fun c : Fin m → G₁ => θ ∘ c)
          (MonoidAlgebra.single c 1))
    rw [Representation.ofMulAction_single, MonoidAlgebra.mapDomainLinearMap_single,
      MonoidAlgebra.mapDomainLinearMap_single, Representation.ofMulAction_single]
    congr 1
    funext i
    exact hθ h (c i)⟩

lemma coordinateHom_single (ι : H →* G₁) (ψ : H →* G₂) (θ : G₁ → G₂)
    (hθ : ∀ h g, θ (ι h * g) = ψ h * θ g) (m : ℕ) (c : Fin m → G₁) (r : R) :
    (coordinateHom ι ψ θ hθ m).hom (MonoidAlgebra.single c r) =
      MonoidAlgebra.single (θ ∘ c) r :=
  MonoidAlgebra.mapDomainLinearMap_single _ r c

/-- The prism operator as a morphism of restricted diagonal representations. -/
def prismHom (ι : H →* G₁) (ψ : H →* G₂) (α β : G₁ → G₂)
    (hα : ∀ h g, α (ι h * g) = ψ h * α g) (hβ : ∀ h g, β (ι h * g) = ψ h * β g) (m : ℕ) :
    Rep.res ι (Rep.diagonal R G₁ m) ⟶ Rep.res ψ (Rep.diagonal R G₂ (m + 1)) :=
  Rep.ofHom ⟨chainPrism α β m, fun h => by
    change chainPrism α β m ∘ₗ (Rep.diagonal R G₁ m).ρ (ι h) =
      (Rep.diagonal R G₂ (m + 1)).ρ (ψ h) ∘ₗ chainPrism α β m
    rw [diagonal_ρ_eq, diagonal_ρ_eq]
    exact LinearMap.ext (chainPrism_mapDomain α β (fun x => ι h * x) (fun y => ψ h * y)
      (hα h) (hβ h) m)⟩

variable (ι : H →* G₁) (ψ : H →* G₂) (α β : G₁ → G₂)
  (hα : ∀ h g, α (ι h * g) = ψ h * α g) (hβ : ∀ h g, β (ι h * g) = ψ h * β g)

/-- The prism identity in degree zero, for restricted standard resolutions. -/
lemma coordinateHom_sub_zero :
    coordinateHom (R := R) ι ψ α hα 1 - coordinateHom ι ψ β hβ 1 =
      prismHom ι ψ α β hα hβ 1 ≫
        (Rep.resFunctor ψ).map ((Rep.standardComplex R G₂).d 1 0) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change (coordinateHom ι ψ α hα 1).hom (MonoidAlgebra.single c 1) -
      (coordinateHom ι ψ β hβ 1).hom (MonoidAlgebra.single c 1) =
    ((Rep.standardComplex R G₂).d 1 0).hom (chainPrism α β 1 (MonoidAlgebra.single c 1))
  rw [coordinateHom_single, coordinateHom_single, Rep.standardComplex.d_apply,
    ← chainPrism_identity_single α β 0 c, chainPrism_zero, LinearMap.zero_apply, add_zero]

/-- The prism identity in positive degree, for restricted standard resolutions. -/
lemma coordinateHom_sub_succ (n : ℕ) :
    coordinateHom (R := R) ι ψ α hα (n + 1 + 1) - coordinateHom ι ψ β hβ (n + 1 + 1) =
      (prismHom ι ψ α β hα hβ (n + 1 + 1) ≫
          (Rep.resFunctor ψ).map ((Rep.standardComplex R G₂).d (n + 1 + 1) (n + 1)) :
          Rep.res ι (Rep.diagonal R G₁ (n + 1 + 1)) ⟶ Rep.res ψ (Rep.diagonal R G₂ (n + 1 + 1))) +
        ((Rep.resFunctor ι).map ((Rep.standardComplex R G₁).d (n + 1) n) ≫
          prismHom ι ψ α β hα hβ (n + 1) :
          Rep.res ι (Rep.diagonal R G₁ (n + 1 + 1)) ⟶
            Rep.res ψ (Rep.diagonal R G₂ (n + 1 + 1))) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change (coordinateHom ι ψ α hα (n + 1 + 1)).hom (MonoidAlgebra.single c 1) -
      (coordinateHom ι ψ β hβ (n + 1 + 1)).hom (MonoidAlgebra.single c 1) =
    ((Rep.standardComplex R G₂).d (n + 1 + 1) (n + 1)).hom
        (chainPrism α β (n + 1 + 1) (MonoidAlgebra.single c 1)) +
      chainPrism α β (n + 1) (((Rep.standardComplex R G₁).d (n + 1) n).hom
        (MonoidAlgebra.single c 1))
  rw [coordinateHom_single, coordinateHom_single, Rep.standardComplex.d_apply,
    Rep.standardComplex.d_apply]
  exact (chainPrism_identity_single α β (n + 1) c).symm

end Coordinates

section Transfer

variable {Γ Δ : Type u} [Group Γ] [Group Δ] {K : Subgroup Δ} {K' : Subgroup Γ} [Fintype (Γ ⧸ K')]
  {π' : K' →* K} {A : Rep.{u} R Δ} {B : Rep.{u} R Γ}
  (φ' : Rep.res π' (Rep.res K.subtype A) ⟶ Rep.res K'.subtype B)

/-- Relative trace along `K'` of a coefficient map pulled back through a comparison `Φ`. -/
def comparisonTransfer {P : Rep.{u} R Γ} {Q : Rep.{u} R K}
    (Φ : Rep.res K'.subtype P ⟶ Rep.res π' Q) :
    (Q ⟶ Rep.res K.subtype A) →ₗ[R] (P ⟶ B) where
  toFun F := Tate.homTransfer K' P B (Φ ≫ (Rep.resFunctor π').map F ≫ φ')
  map_add' F G := by
    rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, map_add]
  map_smul' r F := by
    rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul, map_smul, RingHom.id_apply]

lemma comparisonTransfer_apply {P : Rep.{u} R Γ} {Q : Rep.{u} R K}
    (Φ : Rep.res K'.subtype P ⟶ Rep.res π' Q) (F : Q ⟶ Rep.res K.subtype A) :
    comparisonTransfer φ' Φ F =
      Tate.homTransfer K' P B (Φ ≫ (Rep.resFunctor π').map F ≫ φ') :=
  rfl

lemma comparisonTransfer_sub {P : Rep.{u} R Γ} {Q : Rep.{u} R K}
    (Φ₁ Φ₂ : Rep.res K'.subtype P ⟶ Rep.res π' Q) (F : Q ⟶ Rep.res K.subtype A) :
    comparisonTransfer φ' (Φ₁ - Φ₂) F =
      comparisonTransfer φ' Φ₁ F - comparisonTransfer φ' Φ₂ F := by
  rw [comparisonTransfer_apply, comparisonTransfer_apply, comparisonTransfer_apply,
    Preadditive.sub_comp, map_sub]

lemma comparisonTransfer_add {P : Rep.{u} R Γ} {Q : Rep.{u} R K}
    (Φ₁ Φ₂ : Rep.res K'.subtype P ⟶ Rep.res π' Q) (F : Q ⟶ Rep.res K.subtype A) :
    comparisonTransfer φ' (Φ₁ + Φ₂) F =
      comparisonTransfer φ' Φ₁ F + comparisonTransfer φ' Φ₂ F := by
  rw [comparisonTransfer_apply, comparisonTransfer_apply, comparisonTransfer_apply,
    Preadditive.add_comp, map_add]

lemma comparisonTransfer_comp_map {P : Rep.{u} R Γ} {Q Q' : Rep.{u} R K}
    (Φ : Rep.res K'.subtype P ⟶ Rep.res π' Q) (d : Q ⟶ Q') (F : Q' ⟶ Rep.res K.subtype A) :
    comparisonTransfer φ' (Φ ≫ (Rep.resFunctor π').map d) F =
      comparisonTransfer φ' Φ (d ≫ F) := by
  rw [comparisonTransfer_apply, comparisonTransfer_apply, Functor.map_comp, Category.assoc,
    Category.assoc]

lemma comparisonTransfer_map_comp {P P' : Rep.{u} R Γ} {Q : Rep.{u} R K} (d : P' ⟶ P)
    (Φ : Rep.res K'.subtype P ⟶ Rep.res π' Q) (F : Q ⟶ Rep.res K.subtype A) :
    comparisonTransfer φ' ((Rep.resFunctor K'.subtype).map d ≫ Φ) F =
      d ≫ comparisonTransfer φ' Φ F := by
  rw [comparisonTransfer_apply, comparisonTransfer_apply, Category.assoc,
    Tate.homTransfer_precomp]

end Transfer

section CochainMaps

variable {G₁ G₂ : Type u} [Group G₁] [Group G₂]

/-- The coordinatewise map of homogeneous chains induced by a group homomorphism. -/
abbrev standardMap (f : G₂ →* G₁) (m : ℕ) :
    Rep.diagonal R G₂ m ⟶ Rep.res f (Rep.diagonal R G₁ m) :=
  coordinateHom (MonoidHom.id G₂) f f (fun h g => map_mul f h g) m

lemma diagonal_ρ_single {G : Type u} [Group G] (m : ℕ) (g : G) (c : Fin m → G) (r : R) :
    (Rep.diagonal R G m).ρ g (MonoidAlgebra.single c r) = MonoidAlgebra.single (g • c) r :=
  Representation.ofMulAction_single (k := R) (G := G) (H := Fin m → G) g c r

lemma standardComplex_ρ_single {G : Type u} [Group G] (n : ℕ) (g : G) (c : Fin (n + 1) → G)
    (r : R) :
    ((Rep.standardComplex R G).X n).ρ g (MonoidAlgebra.single c r) =
      MonoidAlgebra.single (g • c) r :=
  Representation.ofMulAction_single (k := R) (G := G) (H := Fin (n + 1) → G) g c r

/-- Mathlib's inhomogeneous cochain map, transported to the standard Hom complexes. -/
lemma cochainsIsoStandard_cochainsMap (X : Rep.{u} R G₁) (Y : Rep.{u} R G₂) (f : G₂ →* G₁)
    (ψ : Rep.res f X ⟶ Y) (n : ℕ) (F : (Rep.standardComplex R G₁).X n ⟶ X) :
    ((Tate.cochainsIsoStandard Y).hom.f n).hom
        (((groupCohomology.cochainsMap f ψ).f n).hom
          (((Tate.cochainsIsoStandard X).inv.f n).hom F)) =
      standardMap f (n + 1) ≫ (Rep.resFunctor f).map F ≫ ψ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change (((Tate.cochainsIsoStandard Y).hom.f n).hom
      (((groupCohomology.cochainsMap f ψ).f n).hom
        (((Tate.cochainsIsoStandard X).inv.f n).hom F))).hom (MonoidAlgebra.single c 1) =
    ψ.hom (F.hom ((standardMap f (n + 1)).hom (MonoidAlgebra.single c 1)))
  rw [Tate.cochainsIsoStandard_hom_single, one_smul, coordinateHom_single]
  change Y.ρ (c 0) (ψ.hom ((((Tate.cochainsIsoStandard X).inv.f n).hom F :
      (Fin n → G₁) → X) (f ∘ fun i => (c i.castSucc)⁻¹ * c i.succ))) = _
  rw [Tate.cochainsIsoStandard_inv_apply]
  have hc : Fin.partialProd (f ∘ fun i : Fin n => (c i.castSucc)⁻¹ * c i.succ) =
      (f (c 0))⁻¹ • (f ∘ c) := by
    have he : (f ∘ fun i : Fin n => (c i.castSucc)⁻¹ * c i.succ) =
        fun i => ((f ∘ c) i.castSucc)⁻¹ * (f ∘ c) i.succ := by
      funext i
      simp only [Function.comp_apply, map_mul, map_inv]
    rw [he, eq_inv_smul_iff]
    exact Fin.partialProd_left_inv (f ∘ c)
  have hs : (MonoidAlgebra.single ((f (c 0))⁻¹ • (f ∘ c)) (1 : R) :
      (Rep.standardComplex R G₁).X n) =
      ((Rep.standardComplex R G₁).X n).ρ (f (c 0))⁻¹ (MonoidAlgebra.single (f ∘ c) 1) :=
    (Representation.ofMulAction_single (k := R) (G := G₁) (H := Fin (n + 1) → G₁)
      (f (c 0))⁻¹ (f ∘ c) 1).symm
  rw [hc, hs, Rep.hom_comm_apply F, ← map_inv]
  change Y.ρ (c 0) (ψ.hom ((Rep.res f X).ρ (c 0)⁻¹ _)) = _
  rw [Rep.hom_comm_apply ψ, Representation.self_inv_apply]

end CochainMaps

section Choice

variable {Γ Δ : Type u} [Group Γ] [Group Δ] (π : Γ →* Δ) (hπ : Function.Surjective π)
  (K : Subgroup Δ) [Fintype (Δ ⧸ K)] (K' : Subgroup Γ) [Fintype (Γ ⧸ K')]
  (hK : ∀ g, g ∈ K' ↔ π g ∈ K)

include hπ hK in
/-- A right-`K`-invariant sum over coset representatives of `Δ ⧸ K` may be computed from
the images of the representatives of `Γ ⧸ K'`. -/
lemma sum_quotient_out_map {M : Type*} [AddCommMonoid M] (f : Δ → M)
    (hf : ∀ (δ : Δ) (k : K), f (δ * k) = f δ) :
    ∑ p : Γ ⧸ K', f (π p.out) = ∑ q : Δ ⧸ K, f q.out := by
  refine Fintype.sum_bijective (fun p : Γ ⧸ K' => (QuotientGroup.mk (π p.out) : Δ ⧸ K))
    ⟨fun p₁ p₂ h => ?_, fun q => ?_⟩ _ _ fun p => ?_
  · rw [← Quotient.out_eq' p₁, ← Quotient.out_eq' p₂]
    apply QuotientGroup.eq.mpr
    rw [hK, map_mul, map_inv]
    exact QuotientGroup.eq.mp h
  · obtain ⟨g, hg⟩ := hπ q.out
    refine ⟨QuotientGroup.mk g, ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K' g
    change (QuotientGroup.mk (π (QuotientGroup.mk g : Γ ⧸ K').out) : Δ ⧸ K) = q
    rw [hk, map_mul, hg, QuotientGroup.mk_mul_of_mem _ ((hK k).mp k.property)]
    exact Quotient.out_eq' q
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (π p.out)
    rw [hk, hf]

end Choice

section Comparison

variable {Γ Δ : Type u} [Group Γ] [Group Δ] (π : Γ →* Δ) (hπ : Function.Surjective π)
  (K : Subgroup Δ) (K' : Subgroup Γ) (hK : ∀ g, g ∈ K' ↔ π g ∈ K)
  (π' : K' →* K) (hπ' : ∀ g, (π' g : Δ) = π g)

include hπ' in
/-- The coset coordinate of the image in `Δ` is equivariant along `π'`. -/
lemma imageCoordinate_mul (h : K') (g : Γ) :
    Tate.cosetCoordinate K (π (K'.subtype h * g)) = π' h * Tate.cosetCoordinate K (π g) := by
  change Tate.cosetCoordinate K (π ((h : Γ) * g)) = _
  rw [map_mul, ← hπ', Tate.cosetCoordinate_subgroup_mul]

/-- The image of the coset coordinate in `Γ` is equivariant along `π'`. -/
lemma mapCoordinate_mul (h : K') (g : Γ) :
    π' (Tate.cosetCoordinate K' (K'.subtype h * g)) = π' h * π' (Tate.cosetCoordinate K' g) := by
  change π' (Tate.cosetCoordinate K' ((h : Γ) * g)) = _
  rw [Tate.cosetCoordinate_subgroup_mul, map_mul]

lemma standardCosetComparison_comp_standardMap (n : ℕ) :
    Tate.standardCosetComparisonComponent K' n ≫ standardMap (R := R) π' (n + 1) =
      coordinateHom K'.subtype π' (fun g => π' (Tate.cosetCoordinate K' g))
        (mapCoordinate_mul K K' π') (n + 1) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change (standardMap π' (n + 1)).hom
      ((Tate.standardCosetComparisonComponent K' n).hom (MonoidAlgebra.single c 1)) =
    (coordinateHom K'.subtype π' (fun g => π' (Tate.cosetCoordinate K' g))
      (mapCoordinate_mul K K' π') (n + 1)).hom (MonoidAlgebra.single c 1)
  rw [Tate.standardCosetComparisonComponent_single, coordinateHom_single, coordinateHom_single]
  rfl

variable [Fintype (Δ ⧸ K)] [Fintype (Γ ⧸ K')] (A : Rep.{u} R Δ) (B : Rep.{u} R Γ)
  (φ : Rep.res π A ⟶ B) (φ' : Rep.res π' (Rep.res K.subtype A) ⟶ Rep.res K'.subtype B)
  (hφ' : φ'.hom.toLinearMap = φ.hom.toLinearMap)

/-- Corestriction along `K` followed by the cochain map of `(π, φ)`, on standard Hom
complexes. -/
def leftComposite :
    (Rep.standardComplex R K).linearYonedaObj R (Rep.res K.subtype A) ⟶
      (Rep.standardComplex R Γ).linearYonedaObj R B :=
  Tate.homogeneousCochainTransfer K A ≫ (Tate.cochainsIsoStandard A).inv ≫
    groupCohomology.cochainsMap π φ ≫ (Tate.cochainsIsoStandard B).hom

/-- The cochain map of `(π', φ')` followed by corestriction along `K'`, on standard Hom
complexes. -/
def rightComposite :
    (Rep.standardComplex R K).linearYonedaObj R (Rep.res K.subtype A) ⟶
      (Rep.standardComplex R Γ).linearYonedaObj R B :=
  (Tate.cochainsIsoStandard (Rep.res K.subtype A)).inv ≫ groupCohomology.cochainsMap π' φ' ≫
    (Tate.cochainsIsoStandard (Rep.res K'.subtype B)).hom ≫ Tate.homogeneousCochainTransfer K' B

omit [Fintype (Δ ⧸ K)] in
lemma rightComposite_f_apply (n : ℕ)
    (F : (Rep.standardComplex R K).X n ⟶ Rep.res K.subtype A) :
    ((rightComposite K K' π' A B φ').f n).hom F =
      comparisonTransfer φ' (coordinateHom K'.subtype π'
        (fun g => π' (Tate.cosetCoordinate K' g)) (mapCoordinate_mul K K' π') (n + 1)) F := by
  change Tate.homTransfer K' ((Rep.standardComplex R Γ).X n) B
      (Tate.standardCosetComparisonComponent K' n ≫
        ((Tate.cochainsIsoStandard (Rep.res K'.subtype B)).hom.f n).hom
          (((groupCohomology.cochainsMap π' φ').f n).hom
            (((Tate.cochainsIsoStandard (Rep.res K.subtype A)).inv.f n).hom F))) = _
  rw [cochainsIsoStandard_cochainsMap, ← Category.assoc,
    standardCosetComparison_comp_standardMap]
  rfl

include hπ hK hφ' in
lemma leftComposite_f_apply (n : ℕ)
    (F : (Rep.standardComplex R K).X n ⟶ Rep.res K.subtype A) :
    ((leftComposite π K A B φ).f n).hom F =
      comparisonTransfer φ' (coordinateHom K'.subtype π'
        (fun g => Tate.cosetCoordinate K (π g)) (imageCoordinate_mul π K K' π' hπ') (n + 1)) F := by
  change ((Tate.cochainsIsoStandard B).hom.f n).hom (((groupCohomology.cochainsMap π φ).f n).hom
      (((Tate.cochainsIsoStandard A).inv.f n).hom
        (Tate.homTransfer K ((Rep.standardComplex R Δ).X n) A
          (Tate.standardCosetComparisonComponent K n ≫ F)))) = _
  rw [cochainsIsoStandard_cochainsMap]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change φ.hom ((Tate.homTransfer K ((Rep.standardComplex R Δ).X n) A
      (Tate.standardCosetComparisonComponent K n ≫ F)).hom
        ((standardMap π (n + 1)).hom (MonoidAlgebra.single c 1))) =
    (Tate.homTransfer K' (Rep.diagonal R Γ (n + 1)) B
      (coordinateHom K'.subtype π' (fun g => Tate.cosetCoordinate K (π g))
        (imageCoordinate_mul π K K' π' hπ') (n + 1) ≫ (Rep.resFunctor π').map F ≫ φ')).hom
        (MonoidAlgebra.single c 1)
  rw [coordinateHom_single, Tate.homTransfer_apply, Tate.homTransfer_apply, map_sum]
  obtain ⟨f, hfdef⟩ : ∃ f : Δ → B, ∀ δ, f δ = φ.hom (A.ρ δ (F.hom (MonoidAlgebra.single
      (Tate.cosetCoordinate K ∘ (δ⁻¹ • (π ∘ c))) 1))) := ⟨_, fun _ => rfl⟩
  have hf : ∀ (δ : Δ) (k : K), f (δ * k) = f δ := by
    intro δ k
    have hc : Tate.cosetCoordinate K ∘ ((δ * k)⁻¹ • (π ∘ c)) =
        k⁻¹ • (Tate.cosetCoordinate K ∘ (δ⁻¹ • (π ∘ c))) := by
      funext i
      change Tate.cosetCoordinate K ((δ * k)⁻¹ * π (c i)) =
        k⁻¹ * Tate.cosetCoordinate K (δ⁻¹ * π (c i))
      rw [← Tate.cosetCoordinate_subgroup_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc]
    rw [hfdef, hfdef, hc, ← standardComplex_ρ_single (R := R) n k⁻¹, Rep.hom_comm_apply F]
    change φ.hom (A.ρ (δ * k) (A.ρ ((k⁻¹ : K) : Δ) _)) = _
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel_right]
  trans ∑ q : Δ ⧸ K, f q.out
  · apply Finset.sum_congr rfl
    intro q _
    rw [hfdef, standardComplex_ρ_single]
    change φ.hom (A.ρ q.out (F.hom ((Tate.standardCosetComparisonComponent K n).hom
      (MonoidAlgebra.single (q.out⁻¹ • (π ∘ c)) 1)))) = _
    rw [Tate.standardCosetComparisonComponent_single]
  rw [← sum_quotient_out_map π hπ K K' hK f hf]
  apply Finset.sum_congr rfl
  intro p _
  rw [hfdef, diagonal_ρ_single]
  change φ.hom ((Rep.res π A).ρ p.out _) = _
  rw [Rep.hom_comm_apply φ]
  congr 1
  change _ = φ'.hom (F.hom ((coordinateHom K'.subtype π' (fun g => Tate.cosetCoordinate K (π g))
    (imageCoordinate_mul π K K' π' hπ') (n + 1)).hom (MonoidAlgebra.single (p.out⁻¹ • c) 1)))
  rw [coordinateHom_single]
  have hα : (fun g => Tate.cosetCoordinate K (π g)) ∘ (p.out⁻¹ • c) =
      Tate.cosetCoordinate K ∘ ((π p.out)⁻¹ • (π ∘ c)) := by
    funext i
    change Tate.cosetCoordinate K (π (p.out⁻¹ * c i)) =
      Tate.cosetCoordinate K ((π p.out)⁻¹ * π (c i))
    rw [map_mul, map_inv]
  rw [hα]
  exact (LinearMap.congr_fun hφ' _).symm

omit [Fintype (Δ ⧸ K)] in
/-- The cochain homotopy: relative trace along `K'` of the prism operator between the two
coset-coordinate comparisons. -/
def prismHomotopy (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel j i) :
    ((Rep.standardComplex R K).linearYonedaObj R (Rep.res K.subtype A)).X i ⟶
      ((Rep.standardComplex R Γ).linearYonedaObj R B).X j :=
  match i, hij with
  | _, rfl => ModuleCat.ofHom (comparisonTransfer (P := (Rep.standardComplex R Γ).X j)
      (Q := (Rep.standardComplex R K).X (j + 1)) φ'
      (prismHom K'.subtype π' (fun g => Tate.cosetCoordinate K (π g))
        (fun g => π' (Tate.cosetCoordinate K' g)) (imageCoordinate_mul π K K' π' hπ')
        (mapCoordinate_mul K K' π') (j + 1)))

include hπ hK hφ' in
/-- The two composites differ by the null-homotopic map of the traced prism operator. -/
lemma leftComposite_sub_rightComposite :
    leftComposite π K A B φ - rightComposite K K' π' A B φ' =
      Homotopy.nullHomotopicMap' (prismHomotopy π K K' π' hπ' A B φ') := by
  apply HomologicalComplex.hom_ext
  intro n
  rcases n with _ | n
  · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right
      (show (ComplexShape.up ℕ).Rel 0 1 from rfl) (fun l hl => Nat.succ_ne_zero l hl)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro F
    change ((leftComposite π K A B φ).f 0).hom F - ((rightComposite K K' π' A B φ').f 0).hom F =
      comparisonTransfer φ' (prismHom K'.subtype π' (fun g => Tate.cosetCoordinate K (π g))
        (fun g => π' (Tate.cosetCoordinate K' g)) (imageCoordinate_mul π K K' π' hπ')
        (mapCoordinate_mul K K' π') (0 + 1)) ((Rep.standardComplex R K).d 1 0 ≫ F)
    rw [leftComposite_f_apply π hπ K K' hK π' hπ' A B φ φ' hφ' 0 F, rightComposite_f_apply,
      ← comparisonTransfer_sub, coordinateHom_sub_zero, comparisonTransfer_comp_map]
  · rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro F
    change ((leftComposite π K A B φ).f (n + 1)).hom F -
        ((rightComposite K K' π' A B φ').f (n + 1)).hom F =
      comparisonTransfer φ' (prismHom K'.subtype π' (fun g => Tate.cosetCoordinate K (π g))
          (fun g => π' (Tate.cosetCoordinate K' g)) (imageCoordinate_mul π K K' π' hπ')
          (mapCoordinate_mul K K' π') (n + 1 + 1))
          ((Rep.standardComplex R K).d (n + 1 + 1) (n + 1) ≫ F) +
        ((Rep.standardComplex R Γ).d (n + 1) n ≫
          comparisonTransfer φ' (prismHom K'.subtype π' (fun g => Tate.cosetCoordinate K (π g))
            (fun g => π' (Tate.cosetCoordinate K' g)) (imageCoordinate_mul π K K' π' hπ')
            (mapCoordinate_mul K K' π') (n + 1)) F : Rep.diagonal R Γ (n + 1 + 1) ⟶ B)
    rw [leftComposite_f_apply π hπ K K' hK π' hπ' A B φ φ' hφ' (n + 1) F,
      rightComposite_f_apply, ← comparisonTransfer_sub, coordinateHom_sub_succ,
      comparisonTransfer_add, comparisonTransfer_comp_map, comparisonTransfer_map_comp]
    rfl

end Comparison

/-- Ordinary corestriction commutes with the cohomology maps induced by a surjection `π` whose
pullback of `K` is `K'`, for compatible coefficient maps `φ` and `φ'`. -/
theorem ordinaryCohomologyCorestriction_comp_map {R Γ Δ : Type u} [CommRing R] [Group Γ]
    [Group Δ] (π : Γ →* Δ) (hπ : Function.Surjective π) (K : Subgroup Δ) [Fintype (Δ ⧸ K)]
    (K' : Subgroup Γ) [Fintype (Γ ⧸ K')] (hK : ∀ g, g ∈ K' ↔ π g ∈ K) (π' : K' →* K)
    (hπ' : ∀ g, (π' g : Δ) = π g) (A : Rep.{u} R Δ) (B : Rep.{u} R Γ) (φ : Rep.res π A ⟶ B)
    (φ' : Rep.res π' (Rep.res K.subtype A) ⟶ Rep.res K'.subtype B)
    (hφ' : φ'.hom.toLinearMap = φ.hom.toLinearMap) (q : ℕ) :
    Tate.ordinaryCohomologyCorestriction K A q ≫ groupCohomology.map π φ q =
      groupCohomology.map π' φ' q ≫ Tate.ordinaryCohomologyCorestriction K' B q := by
  have hL : Tate.ordinaryCorestrictionCochainMap K A ≫ groupCohomology.cochainsMap π φ =
      (Tate.cochainsIsoStandard (Rep.res K.subtype A)).hom ≫ leftComposite π K A B φ ≫
        (Tate.cochainsIsoStandard B).inv := by
    simp only [Tate.ordinaryCorestrictionCochainMap, leftComposite, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hR : groupCohomology.cochainsMap π' φ' ≫ Tate.ordinaryCorestrictionCochainMap K' B =
      (Tate.cochainsIsoStandard (Rep.res K.subtype A)).hom ≫ rightComposite K K' π' A B φ' ≫
        (Tate.cochainsIsoStandard B).inv := by
    simp only [Tate.ordinaryCorestrictionCochainMap, rightComposite, Category.assoc,
      Iso.hom_inv_id_assoc]
  have hH : Homotopy (leftComposite π K A B φ) (rightComposite K K' π' A B φ') :=
    Homotopy.equivSubZero.symm ((Homotopy.ofEq
      (leftComposite_sub_rightComposite π hπ K K' hK π' hπ' A B φ φ' hφ')).trans
        (Homotopy.nullHomotopy' _))
  change HomologicalComplex.homologyMap _ q ≫ HomologicalComplex.homologyMap _ q =
    HomologicalComplex.homologyMap _ q ≫ HomologicalComplex.homologyMap _ q
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hL, hR]
  exact ((hH.compRight _).compLeft _).homologyMap_eq q

end Langlands.Continuous
