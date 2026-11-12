import Langlands.GroupScheme.IntegralCocycleVanishing
import Langlands.GroupScheme.AffinePointPiProducts
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Galois cocycles on finite free local Galois covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace GaloisRingCover

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {Γ : Type u} [Group Γ] (ρ : Γ →* (B ≃ₐ[R] B))

/-- The coordinate `x ⊗ y ↦ x * g(y)` of the double tensor product. -/
def component (g : Γ) : B ⊗[R] B →ₐ[B] B :=
  Algebra.TensorProduct.lift (Algebra.ofId B B) (ρ g).toAlgHom (fun _ _ => Commute.all _ _)

@[simp] theorem component_tmul (g : Γ) (x y : B) : component ρ g (x ⊗ₜ y) = x * ρ g y := rfl

/-- All coordinates together. -/
def tensorHom : B ⊗[R] B →ₐ[B] (Γ → B) := AlgHom.pi (component ρ)

@[simp] theorem tensorHom_apply (x : B ⊗[R] B) (g : Γ) :
    tensorHom ρ x g = component ρ g x := rfl

variable [IsLocalRing B] [Module.Free R B] [Module.Finite R B] [Finite Γ]

/-- **Galois decomposition of the double tensor product.** If `B` is local and finite free over
`R`, and `Γ` has order the rank of `B` and acts faithfully on the residue field, then
`x ⊗ y ↦ (g ↦ x * g(y))` is an isomorphism `B ⊗[R] B ≃ (Γ → B)`. The matrix of this map in an
`R`-basis has invertible reduction by Dedekind's independence of characters. -/
theorem tensorHom_bijective (hcard : Nat.card Γ = Module.finrank R B)
    (hfaithful : ∀ g : Γ, (∀ x : B, residue B (ρ g x) = residue B x) → g = 1) :
    Function.Bijective (tensorHom ρ) := by
  classical
  have : Nontrivial R := (algebraMap R B).domain_nontrivial
  let : Fintype Γ := Fintype.ofFinite Γ
  let J := Module.Free.ChooseBasisIndex R B
  let b : Module.Basis J R B := Module.Free.chooseBasis R B
  have hJ : Fintype.card J = Fintype.card Γ := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ← hcard, Nat.card_eq_fintype_card]
  let ε : J ≃ Γ := Fintype.equivOfCardEq hJ
  let v : Module.Basis J B (B ⊗[R] B) := Algebra.TensorProduct.basis B b
  let v' : Module.Basis J B (Γ → B) := (Pi.basisFun B Γ).reindex ε.symm
  let f : B ⊗[R] B →ₗ[B] (Γ → B) := (tensorHom ρ).toLinearMap
  let M := LinearMap.toMatrix v v' f
  have hM : ∀ i j, M i j = ρ (ε i) (b j) := by
    intro i j
    simp [M, LinearMap.toMatrix_apply, v, v', f]
  suffices h : IsUnit M.det from (LinearEquiv.ofIsUnitDet h).bijective
  rw [← residue_ne_zero_iff_isUnit, RingHom.map_det]
  intro h0
  obtain ⟨w, hw, hwM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  let χ : J → ResidueField B →* ResidueField B :=
    fun i => (ResidueField.mapAlgEquiv (ρ (ε i))).toAlgHom.toMonoidHom
  have hχ : ∀ i y, χ i (residue B y) = residue B (ρ (ε i) y) := fun _ _ => rfl
  have hχinj : Function.Injective χ := by
    intro i j hij
    apply ε.injective
    have hfix : ∀ y : B, residue B (ρ (ε i * (ε j)⁻¹) y) = residue B y := by
      intro y
      have := congrArg (fun φ : ResidueField B →* ResidueField B =>
        φ (residue B ((ρ (ε j)).symm y))) hij
      simp only [hχ] at this
      rw [map_mul, map_inv]
      change residue B (ρ (ε i) ((ρ (ε j)).symm y)) = residue B y
      rw [this, AlgEquiv.apply_symm_apply]
    exact mul_inv_eq_one.mp (hfaithful _ hfix)
  have hsum : ∀ y : B, ∑ i, w i * residue B (ρ (ε i) y) = 0 := by
    intro y
    have hy : y = ∑ j, b.repr y j • b j := (b.sum_repr y).symm
    have hcoord : ∀ j, ∑ i, w i * residue B (ρ (ε i) (b j)) = 0 := by
      intro j
      have := congrFun hwM j
      simpa [Matrix.vecMul, dotProduct, hM] using this
    calc ∑ i, w i * residue B (ρ (ε i) y)
        = ∑ i, w i * ∑ j, residue B (algebraMap R B (b.repr y j)) *
            residue B (ρ (ε i) (b j)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [hy]
          simp [map_sum, Algebra.smul_def]
      _ = ∑ j, residue B (algebraMap R B (b.repr y j)) *
            ∑ i, w i * residue B (ρ (ε i) (b j)) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = 0 := by simp [hcoord]
  have hli : LinearIndependent (ResidueField B) (fun i => (χ i : ResidueField B → ResidueField B)) :=
    (linearIndependent_monoidHom (ResidueField B) (ResidueField B)).comp χ hχinj
  apply hw
  funext i
  refine (Fintype.linearIndependent_iff.mp hli) w ?_ i
  funext x
  obtain ⟨y, rfl⟩ := residue_surjective x
  simpa [Finset.sum_apply, hχ] using hsum y

omit [IsLocalRing B] [Module.Free R B] [Module.Finite R B] in
/-- Coordinates of the triple tensor product are compositions of the double coordinates. -/
def tripleComponent (σ τ : Γ) : B ⊗[R] (B ⊗[R] B) →ₐ[R] B :=
  ((component ρ σ).restrictScalars R).comp
    (Algebra.TensorProduct.map (AlgHom.id R B) ((component ρ τ).restrictScalars R))

omit [IsLocalRing B] [Module.Free R B] [Module.Finite R B] [Finite Γ] in
@[simp] theorem tripleComponent_tmul (σ τ : Γ) (x y z : B) :
    tripleComponent ρ σ τ (x ⊗ₜ (y ⊗ₜ z)) = x * ρ σ (y * ρ τ z) := rfl

omit [IsLocalRing B] [Module.Free R B] [Module.Finite R B] in
/-- When the double coordinates form an isomorphism, the triple coordinates are jointly
injective. -/
theorem triple_ext (hbij : Function.Bijective (tensorHom ρ)) {u v : B ⊗[R] (B ⊗[R] B)}
    (h : ∀ σ τ, tripleComponent ρ σ τ u = tripleComponent ρ σ τ v) : u = v := by
  classical
  let : Fintype Γ := Fintype.ofFinite Γ
  let mid : Γ → (B ⊗[R] (B ⊗[R] B) →ₐ[R] B ⊗[R] B) := fun τ =>
    Algebra.TensorProduct.map (AlgHom.id R B) ((component ρ τ).restrictScalars R)
  have hmid : ∀ τ, mid τ u = mid τ v := by
    intro τ
    apply hbij.1
    funext σ
    exact h σ τ
  let e : B ⊗[R] B ≃ₐ[R] (Γ → B) :=
    AlgEquiv.ofBijective ((tensorHom ρ).restrictScalars R) hbij
  let L : B ⊗[R] (B ⊗[R] B) ≃ₐ[R] (Γ → B ⊗[R] B) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans
      (Algebra.TensorProduct.piRight R R B (fun _ : Γ => B))
  have hL : ∀ w τ, L w τ = mid τ w := by
    intro w τ
    induction w using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  apply L.injective
  funext τ
  rw [hL, hL, hmid]

end GaloisRingCover

namespace Cocycle

variable {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}

/-- A natural cocycle from one morphism on the universal overlap satisfying the cocycle
identity on the universal triple overlap. -/
def ofOverlap (δ : U ⊗ U ⟶ G.X)
    (h : CartesianMonoidalCategory.lift (fst U (U ⊗ U)) (snd U (U ⊗ U) ≫ snd U U) ≫ δ =
      (CartesianMonoidalCategory.lift (fst U (U ⊗ U)) (snd U (U ⊗ U) ≫ fst U U) ≫ δ) *
        (snd U (U ⊗ U) ≫ δ)) :
    Cocycle G U where
  toFun a b := CartesianMonoidalCategory.lift a b ≫ δ
  naturality t a b := by rw [comp_lift_assoc]
  cocycle a b c := by
    have := congrArg
      (fun φ => CartesianMonoidalCategory.lift a (CartesianMonoidalCategory.lift b c) ≫ φ) h
    simpa only [MonObj.comp_mul, comp_lift_assoc, lift_fst, lift_snd_assoc, lift_fst,
      lift_snd] using this

@[simp] theorem ofOverlap_toFun (δ : U ⊗ U ⟶ G.X) (h) {Z : Over S} (a b : Z ⟶ U) :
    (ofOverlap δ h).toFun a b = CartesianMonoidalCategory.lift a b ≫ δ := rfl

end Cocycle

namespace GaloisRingCover

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {Γ : Type u} [Group Γ] (ρ : Γ →* (B ≃ₐ[R] B))

variable (R B) in
/-- The actual spectrum of `B` over `Spec R`. -/
abbrev cover : Over (Spec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).obj (Opposite.op (CommAlgCat.of R B))

/-- An automorphism of `B` as an endomorphism of its spectrum. -/
def arrow (σ : B ≃ₐ[R] B) : cover R B ⟶ cover R B :=
  (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom σ.toAlgHom).op

variable (G : GroupScheme (Spec (CommRingCat.of R)))

/-- The action of an automorphism of `B` on points with coefficients in `B`. -/
def conjugate (σ : B ≃ₐ[R] B) :
    G.affinePoints (CommAlgCat.of R B) →* G.affinePoints (CommAlgCat.of R B) :=
  G.affinePointMap (CommAlgCat.ofHom σ.toAlgHom)

theorem conjugate_apply (σ : B ≃ₐ[R] B) (x : G.affinePoints (CommAlgCat.of R B)) :
    conjugate G σ x = arrow σ ≫ x := rfl

/-- The crossed homomorphism identity `c (σ τ) = c σ * σ (c τ)`. -/
def IsCrossed (c : Γ → G.affinePoints (CommAlgCat.of R B)) : Prop :=
  ∀ σ τ, c (σ * τ) = c σ * conjugate G (ρ σ) (c τ)

variable [IsAffine G.X.left] [Finite Γ] (hbij : Function.Bijective (tensorHom ρ))

/-- The point over `B ⊗[R] B` whose coordinates are the values of `c`. -/
def overlapPoint (c : Γ → G.affinePoints (CommAlgCat.of R B)) :
    G.affinePoints (CommAlgCat.of R B ⊗ CommAlgCat.of R B) :=
  G.affinePointMap
    (CommAlgCat.ofHom (AlgEquiv.ofBijective ((tensorHom ρ).restrictScalars R) hbij).symm.toAlgHom)
    (G.affinePointPi (fun _ : Γ => CommAlgCat.of R B) c)

omit [Finite Γ] in
theorem overlapPoint_component (c : Γ → G.affinePoints (CommAlgCat.of R B)) (g : Γ) :
    G.affinePointMap (CommAlgCat.ofHom ((component ρ g).restrictScalars R))
      (overlapPoint ρ G hbij c) = c g := by
  rw [overlapPoint, ← MonoidHom.comp_apply, ← G.affinePointMap_comp]
  have h : CommAlgCat.ofHom (AlgEquiv.ofBijective ((tensorHom ρ).restrictScalars R) hbij).symm.toAlgHom ≫
      CommAlgCat.ofHom ((component ρ g).restrictScalars R) =
      CommAlgCat.ofHom (Pi.evalAlgHom R (fun _ : Γ => B) g) := by
    apply CommAlgCat.hom_ext
    ext x
    change component ρ g ((AlgEquiv.ofBijective ((tensorHom ρ).restrictScalars R) hbij).symm x) = x g
    rw [← tensorHom_apply]
    exact congrFun ((AlgEquiv.ofBijective ((tensorHom ρ).restrictScalars R) hbij).apply_symm_apply x) g
  rw [h]
  exact G.affinePointsEval_pi (fun _ : Γ => CommAlgCat.of R B) c g

/-- The braided structure of `algSpec`, restated for a base given by a type; instance search
does not find `braidedAlgSpec` through `CommRingCat.of`. -/
@[instance_reducible]
local instance algSpecBraided : (algSpec (CommRingCat.of R)).Braided :=
  braidedAlgSpec (R := CommRingCat.of R)

variable (R B) in
/-- The coefficient algebra as an object of the opposite category. -/
abbrev coeff : (CommAlgCat.{u} R)ᵒᵖ := Opposite.op (CommAlgCat.of R B)

omit [IsAffine G.X.left] [Finite Γ] in
/-- The comparison map of `algSpec` on a pair of morphisms. -/
theorem map_comp_prodComparison {Y : (CommAlgCat.{u} R)ᵒᵖ} (a b : Y ⟶ coeff R B) :
    (algSpec (CommRingCat.of R)).map (CartesianMonoidalCategory.lift a b) ≫
        CartesianMonoidalCategory.prodComparison (algSpec (CommRingCat.of R)) (coeff R B)
          (coeff R B) =
      CartesianMonoidalCategory.lift ((algSpec (CommRingCat.of R)).map a)
        ((algSpec (CommRingCat.of R)).map b) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [← Functor.map_comp]

omit [IsAffine G.X.left] [Finite Γ] in
/-- The monoidal structure map `μ` of `algSpec` inverts the product comparison. -/
theorem prodComparison_comp_μ :
    CartesianMonoidalCategory.prodComparison (algSpec (CommRingCat.of R)) (coeff R B) (coeff R B) ≫
        Functor.LaxMonoidal.μ (algSpec (CommRingCat.of R)) (coeff R B) (coeff R B) = 𝟙 _ := by
  have h : CartesianMonoidalCategory.prodComparison (algSpec (CommRingCat.of R)) (coeff R B) (coeff R B) =
      Functor.OplaxMonoidal.δ (algSpec (CommRingCat.of R)) (coeff R B) (coeff R B) :=
    Over.OverMorphism.ext rfl
  rw [h, Functor.Monoidal.δ_μ]

omit [IsAffine G.X.left] [Finite Γ] in
theorem lift_comp_μ {Y : (CommAlgCat.{u} R)ᵒᵖ} (a b : Y ⟶ coeff R B) :
    CartesianMonoidalCategory.lift ((algSpec (CommRingCat.of R)).map a)
        ((algSpec (CommRingCat.of R)).map b) ≫
        Functor.LaxMonoidal.μ (algSpec (CommRingCat.of R)) (coeff R B) (coeff R B) =
      (algSpec (CommRingCat.of R)).map (CartesianMonoidalCategory.lift a b) := by
  rw [← map_comp_prodComparison, Category.assoc, prodComparison_comp_μ, Category.comp_id]

/-- The universal overlap morphism determined by the values of `c`. -/
def overlap (c : Γ → G.affinePoints (CommAlgCat.of R B)) : cover R B ⊗ cover R B ⟶ G.X :=
  Functor.LaxMonoidal.μ (algSpec (CommRingCat.of R)) (coeff R B) (coeff R B) ≫
    overlapPoint ρ G hbij c

omit [Finite Γ] in
/-- The overlap morphism on the pair of spectrum maps of `a` and `b`. -/
theorem lift_overlap {Y : (CommAlgCat.{u} R)ᵒᵖ} (a b : Y ⟶ coeff R B)
    (c : Γ → G.affinePoints (CommAlgCat.of R B)) :
    CartesianMonoidalCategory.lift ((algSpec (CommRingCat.of R)).map a)
        ((algSpec (CommRingCat.of R)).map b) ≫ overlap ρ G hbij c =
      G.affinePointMap (CartesianMonoidalCategory.lift a b).unop (overlapPoint ρ G hbij c) := by
  rw [overlap, ← Category.assoc, lift_comp_μ]
  rfl

omit [IsAffine G.X.left] [Finite Γ] in
theorem prodComparison_eq_δ (A A' : (CommAlgCat.{u} R)ᵒᵖ) :
    CartesianMonoidalCategory.prodComparison (algSpec (CommRingCat.of R)) A A' =
      Functor.OplaxMonoidal.δ (algSpec (CommRingCat.of R)) A A' :=
  Over.OverMorphism.ext rfl

omit [IsAffine G.X.left] [Finite Γ] in
@[reassoc]
theorem μ_map_fst (A A' : (CommAlgCat.{u} R)ᵒᵖ) :
    Functor.LaxMonoidal.μ (algSpec (CommRingCat.of R)) A A' ≫
      (algSpec (CommRingCat.of R)).map (fst A A') = fst _ _ := by
  rw [← CartesianMonoidalCategory.prodComparison_fst, ← Category.assoc, prodComparison_eq_δ,
    Functor.Monoidal.μ_δ, Category.id_comp]

omit [IsAffine G.X.left] [Finite Γ] in
@[reassoc]
theorem μ_map_snd (A A' : (CommAlgCat.{u} R)ᵒᵖ) :
    Functor.LaxMonoidal.μ (algSpec (CommRingCat.of R)) A A' ≫
      (algSpec (CommRingCat.of R)).map (snd A A') = snd _ _ := by
  rw [← CartesianMonoidalCategory.prodComparison_snd, ← Category.assoc, prodComparison_eq_δ,
    Functor.Monoidal.μ_δ, Category.id_comp]

variable (R B) in
/-- The comparison from the triple product of covers to the spectrum of the triple tensor
product. -/
def tripleMap : cover R B ⊗ (cover R B ⊗ cover R B) ⟶
    (algSpec (CommRingCat.of R)).obj (coeff R B ⊗ (coeff R B ⊗ coeff R B)) :=
  (cover R B ◁ Functor.LaxMonoidal.μ (algSpec (CommRingCat.of R)) (coeff R B) (coeff R B)) ≫
    Functor.LaxMonoidal.μ (algSpec (CommRingCat.of R)) (coeff R B) (coeff R B ⊗ coeff R B)

omit [IsAffine G.X.left] [Finite Γ] in
theorem tripleMap_fst :
    tripleMap R B ≫ (algSpec (CommRingCat.of R)).map (fst (coeff R B) (coeff R B ⊗ coeff R B)) =
      fst _ _ := by
  rw [tripleMap, Category.assoc, μ_map_fst, CartesianMonoidalCategory.whiskerLeft_fst]

omit [IsAffine G.X.left] [Finite Γ] in
theorem tripleMap_snd_fst :
    tripleMap R B ≫ (algSpec (CommRingCat.of R)).map
      (snd (coeff R B) (coeff R B ⊗ coeff R B) ≫ fst (coeff R B) (coeff R B)) =
      snd _ _ ≫ fst _ _ := by
  rw [tripleMap, Functor.map_comp, Category.assoc, μ_map_snd_assoc,
    CartesianMonoidalCategory.whiskerLeft_snd_assoc, μ_map_fst]

omit [IsAffine G.X.left] [Finite Γ] in
theorem tripleMap_snd_snd :
    tripleMap R B ≫ (algSpec (CommRingCat.of R)).map
      (snd (coeff R B) (coeff R B ⊗ coeff R B) ≫ snd (coeff R B) (coeff R B)) =
      snd _ _ ≫ snd _ _ := by
  rw [tripleMap, Functor.map_comp, Category.assoc, μ_map_snd_assoc,
    CartesianMonoidalCategory.whiskerLeft_snd_assoc, μ_map_snd]

omit [IsAffine G.X.left] [Finite Γ] in
theorem tripleMap_snd :
    tripleMap R B ≫ (algSpec (CommRingCat.of R)).map (snd (coeff R B) (coeff R B ⊗ coeff R B)) =
      snd _ _ ≫ Functor.LaxMonoidal.μ (algSpec (CommRingCat.of R)) (coeff R B) (coeff R B) := by
  rw [tripleMap, Category.assoc, μ_map_snd, CartesianMonoidalCategory.whiskerLeft_snd]

omit [Finite Γ] in
theorem lift_overlap_of_tripleMap
    {x y : cover R B ⊗ (cover R B ⊗ cover R B) ⟶ cover R B}
    (a b : coeff R B ⊗ (coeff R B ⊗ coeff R B) ⟶ coeff R B)
    (hx : tripleMap R B ≫ (algSpec (CommRingCat.of R)).map a = x)
    (hy : tripleMap R B ≫ (algSpec (CommRingCat.of R)).map b = y)
    (c : Γ → G.affinePoints (CommAlgCat.of R B)) :
    CartesianMonoidalCategory.lift x y ≫ overlap ρ G hbij c =
      tripleMap R B ≫
        G.affinePointMap (CartesianMonoidalCategory.lift a b).unop (overlapPoint ρ G hbij c) := by
  rw [← hx, ← hy, ← CartesianMonoidalCategory.comp_lift, Category.assoc, lift_overlap]

include hbij in
/-- Points over the triple tensor product are determined by their triple coordinates. -/
theorem triple_points_ext
    {p q : G.affinePoints (CommAlgCat.of R B ⊗ (CommAlgCat.of R B ⊗ CommAlgCat.of R B))}
    (h : ∀ σ τ, G.affinePointMap (CommAlgCat.ofHom (tripleComponent ρ σ τ)) p =
      G.affinePointMap (CommAlgCat.ofHom (tripleComponent ρ σ τ)) q) : p = q := by
  apply G.affinePointEvaluation_injective
  funext a
  apply triple_ext ρ hbij
  intro σ τ
  have := congrArg (fun x => G.affinePointEvaluation (CommAlgCat.of R B) x a) (h σ τ)
  rw [G.affinePointEvaluation_map, G.affinePointEvaluation_map] at this
  exact this

omit [IsAffine G.X.left] [Finite Γ] in
theorem face₁₂ (σ τ : Γ) :
    (CartesianMonoidalCategory.lift (fst (coeff R B) (coeff R B ⊗ coeff R B))
        (snd (coeff R B) (coeff R B ⊗ coeff R B) ≫ fst (coeff R B) (coeff R B))).unop ≫
      CommAlgCat.ofHom (tripleComponent ρ σ τ) =
      CommAlgCat.ofHom ((component ρ σ).restrictScalars R) := by
  apply CommAlgCat.hom_ext
  apply Algebra.TensorProduct.ext'
  intro x y
  simp [tripleComponent]

omit [IsAffine G.X.left] [Finite Γ] in
theorem face₂₃ (σ τ : Γ) :
    (snd (coeff R B) (coeff R B ⊗ coeff R B)).unop ≫ CommAlgCat.ofHom (tripleComponent ρ σ τ) =
      CommAlgCat.ofHom ((component ρ τ).restrictScalars R) ≫
        CommAlgCat.ofHom (ρ σ).toAlgHom := by
  apply CommAlgCat.hom_ext
  apply Algebra.TensorProduct.ext'
  intro x y
  simp [tripleComponent]

omit [IsAffine G.X.left] [Finite Γ] in
theorem face₁₃ (σ τ : Γ) :
    (CartesianMonoidalCategory.lift (fst (coeff R B) (coeff R B ⊗ coeff R B))
        (snd (coeff R B) (coeff R B ⊗ coeff R B) ≫ snd (coeff R B) (coeff R B))).unop ≫
      CommAlgCat.ofHom (tripleComponent ρ σ τ) =
      CommAlgCat.ofHom ((component ρ (σ * τ)).restrictScalars R) := by
  apply CommAlgCat.hom_ext
  apply Algebra.TensorProduct.ext'
  intro x y
  simp [tripleComponent]

omit [IsAffine G.X.left] [Finite Γ] in
theorem affinePointMap_affinePointMap {A A' A'' : CommAlgCat.{u} R} (f : A ⟶ A') (f' : A' ⟶ A'')
    (x : G.affinePoints A) :
    G.affinePointMap f' (G.affinePointMap f x) = G.affinePointMap (f ≫ f') x := by
  rw [G.affinePointMap_comp]
  rfl

/-- The universal overlap morphism of a crossed homomorphism satisfies the cocycle identity on
the universal triple overlap. -/
theorem overlap_triple (c : Γ → G.affinePoints (CommAlgCat.of R B)) (hc : IsCrossed ρ G c) :
    CartesianMonoidalCategory.lift (fst (cover R B) (cover R B ⊗ cover R B))
        (snd (cover R B) (cover R B ⊗ cover R B) ≫ snd (cover R B) (cover R B)) ≫
        overlap ρ G hbij c =
      (CartesianMonoidalCategory.lift (fst (cover R B) (cover R B ⊗ cover R B))
        (snd (cover R B) (cover R B ⊗ cover R B) ≫ fst (cover R B) (cover R B)) ≫
          overlap ρ G hbij c) *
        (snd (cover R B) (cover R B ⊗ cover R B) ≫ overlap ρ G hbij c) := by
  rw [lift_overlap_of_tripleMap ρ G hbij _ _ tripleMap_fst tripleMap_snd_snd,
    lift_overlap_of_tripleMap ρ G hbij _ _ tripleMap_fst tripleMap_snd_fst]
  have hsnd : snd (cover R B) (cover R B ⊗ cover R B) ≫ overlap ρ G hbij c =
      tripleMap R B ≫ G.affinePointMap (snd (coeff R B) (coeff R B ⊗ coeff R B)).unop
        (overlapPoint ρ G hbij c) := by
    rw [overlap, ← Category.assoc, ← tripleMap_snd, Category.assoc]
    rfl
  rw [hsnd, ← MonObj.comp_mul]
  congr 1
  apply triple_points_ext ρ G hbij
  intro σ τ
  rw [map_mul, affinePointMap_affinePointMap, affinePointMap_affinePointMap,
    affinePointMap_affinePointMap, face₁₃, face₁₂, face₂₃, ← affinePointMap_affinePointMap,
    overlapPoint_component, overlapPoint_component, overlapPoint_component]
  exact hc σ τ

/-- The natural cocycle on the spectrum of `B` defined by a crossed homomorphism. -/
def ofCrossed (c : Γ → G.affinePoints (CommAlgCat.of R B)) (hc : IsCrossed ρ G c) :
    Cocycle G (cover R B) :=
  Cocycle.ofOverlap (overlap ρ G hbij c) (overlap_triple ρ G hbij c hc)

/-- Its value on the identity and an automorphism is the value of the crossed homomorphism. -/
theorem ofCrossed_toFun_arrow (c : Γ → G.affinePoints (CommAlgCat.of R B))
    (hc : IsCrossed ρ G c) (g : Γ) :
    (ofCrossed ρ G hbij c hc).toFun (𝟙 _) (arrow (ρ g)) = c g := by
  rw [ofCrossed, Cocycle.ofOverlap_toFun]
  have h1 : 𝟙 (cover R B) = (algSpec (CommRingCat.of R)).map (𝟙 (coeff R B)) :=
    ((algSpec (CommRingCat.of R)).map_id _).symm
  rw [h1, arrow, lift_overlap]
  have h2 : (CartesianMonoidalCategory.lift (𝟙 (coeff R B))
      (CommAlgCat.ofHom (ρ g).toAlgHom).op).unop =
      CommAlgCat.ofHom ((component ρ g).restrictScalars R) := by
    apply CommAlgCat.hom_ext
    apply Algebra.TensorProduct.ext'
    intro x y
    simp
  rw [h2, overlapPoint_component]

/-- A trivialization of the scheme cocycle is a Galois coboundary for the crossed
homomorphism. -/
theorem exists_coboundary_of_isTrivial (c : Γ → G.affinePoints (CommAlgCat.of R B))
    (hc : IsCrossed ρ G c) (h : (ofCrossed ρ G hbij c hc).IsTrivial) :
    ∃ f : G.affinePoints (CommAlgCat.of R B), ∀ g : Γ, c g = f * (conjugate G (ρ g) f)⁻¹ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun g => ?_⟩
  rw [← ofCrossed_toFun_arrow ρ G hbij c hc g, hf, Category.id_comp]
  rfl

end GaloisRingCover

/-- **Unramified Galois cocycles over complete rings with finite residue field.** Let `R` be
complete for a maximal ideal `I` with finite residue ring, and let `H` be a smooth affine group
scheme over `Spec R` with connected special fibre. Let `B` be a local `R`-algebra, finite and free
over `R`, with a finite group `Γ` of `R`-algebra automorphisms whose order is the rank of `B` and
which acts faithfully on the residue field of `B`. Then every crossed homomorphism from `Γ` to
the points `H(B)` is a coboundary. -/
def IntegralGaloisCocycleVanishingStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) [I.IsMaximal] [Finite (R ⧸ I)] [IsAdicComplete I R]
    (H : GroupScheme (Spec (CommRingCat.of R))) [Smooth H.X.hom] [IsAffineHom H.X.hom],
    ConnectedSpace ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj H).X.left →
    ∀ (B : Type u) [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Free R B]
      [Module.Finite R B] (Γ : Type u) [Group Γ] [Finite Γ] (ρ : Γ →* (B ≃ₐ[R] B)),
      Nat.card Γ = Module.finrank R B →
      (∀ g : Γ, (∀ x : B, residue B (ρ g x) = residue B x) → g = 1) →
      ∀ c : Γ → H.affinePoints (CommAlgCat.of R B), GaloisRingCover.IsCrossed ρ H c →
        ∃ f : H.affinePoints (CommAlgCat.of R B),
          ∀ g : Γ, c g = f * (GaloisRingCover.conjugate H (ρ g) f)⁻¹

theorem integralGaloisCocycleVanishing : IntegralGaloisCocycleVanishingStatement.{u} := by
  intro R _ I _ _ _ H _ _ hconn B _ _ _ _ _ Γ _ _ ρ hcard hfaithful c hc
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have hbij := GaloisRingCover.tensorHom_bijective ρ hcard hfaithful
  have hff : (CommRingCat.ofHom (algebraMap R B)).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff _).mpr hff
  have : IsAffine (GaloisRingCover.cover R B).left := by
    change IsAffine (Spec _)
    infer_instance
  have : Flat (GaloisRingCover.cover R B).hom := hflat
  have : Surjective (GaloisRingCover.cover R B).hom := hsurj
  exact GaloisRingCover.exists_coboundary_of_isTrivial ρ H hbij c hc
    (integralCocycleVanishing R I H hconn _ _)

end Langlands.GroupScheme
