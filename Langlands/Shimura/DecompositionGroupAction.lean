import Langlands.Galois.ClosureRestriction
import Langlands.Galois.FrobeniusLift

/-! # Restriction of Galois actions to decomposition groups

Objects of a category with an action of the absolute Galois group of a field `K` are restricted
to the absolute Galois group of an extension `E` along a specified embedding of algebraic
closures. Two embeddings give restrictions that are naturally isomorphic through the action of
the element of `Gal(K̄/K)` relating them. At a finite place `v` of a number field this restricts
to the absolute Galois group of the actual completion; the triviality of the action of the
actual inertia subgroup does not depend on the embedding, and for such unramified actions every
geometric Frobenius lift acts by one endomorphism. See `DecompositionGroupAction.md`.
-/

noncomputable section

universe u v w uK uE uH uG

set_option autoImplicit false

namespace Langlands.Shimura.DecompositionGroupAction

open CategoryTheory Langlands.GaloisRepresentation

variable (V : Type u) [Category.{v} V]

/-! ## Restriction along conjugate homomorphisms -/

section Conjugation

variable {H : Type uH} {G : Type uG} [Monoid H] [Group G]

/-- If `c * f₂ h = f₁ h * c` for every `h`, the action of `c` is a natural isomorphism from the
restriction along `f₂` to the restriction along `f₁`. -/
def resConjugateIso (f₁ f₂ : H →* G) (c : G) (hc : ∀ h, c * f₂ h = f₁ h * c) :
    Action.res V f₂ ≅ Action.res V f₁ :=
  NatIso.ofComponents
    (fun M => Action.mkIso (M.ρAut c) (fun h => by
      change M.ρ (f₂ h) ≫ M.ρ c = M.ρ c ≫ M.ρ (f₁ h)
      simpa only [map_mul, End.mul_def] using congrArg M.ρ (hc h)))
    (fun p => Action.Hom.ext (p.comm c).symm)

@[simp] theorem resConjugateIso_hom_app_hom (f₁ f₂ : H →* G) (c : G)
    (hc : ∀ h, c * f₂ h = f₁ h * c) (M : Action V G) :
    ((resConjugateIso V f₁ f₂ c hc).hom.app M).hom = M.ρ c :=
  rfl

@[simp] theorem resConjugateIso_inv_app_hom (f₁ f₂ : H →* G) (c : G)
    (hc : ∀ h, c * f₂ h = f₁ h * c) (M : Action V G) :
    ((resConjugateIso V f₁ f₂ c hc).inv.app M).hom = M.ρ c⁻¹ :=
  rfl

variable {V} in
/-- Elements conjugate by `c` act trivially together. -/
theorem ρ_eq_id_iff_of_conj (M : Action V G) {a b c : G} (h : c * b = a * c) :
    M.ρ a = 𝟙 M.V ↔ M.ρ b = 𝟙 M.V := by
  have ha : a = c * b * c⁻¹ := eq_mul_inv_of_mul_eq h.symm
  change a ∈ M.ρ.ker ↔ b ∈ M.ρ.ker
  rw [ha]
  constructor
  · intro hx
    have := M.ρ.normal_ker.conj_mem _ hx c⁻¹
    rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
      mul_one] at this
  · intro hx
    exact M.ρ.normal_ker.conj_mem _ hx c

end Conjugation

/-- Mapping actions through a functor commutes with restriction along a monoid homomorphism. -/
def mapActionResIso {W : Type w} [Category.{v} W] (F : V ⥤ W) {H : Type uH} {G : Type uG}
    [Monoid H] [Monoid G] (f : H →* G) :
    F.mapAction G ⋙ Action.res W f ≅ Action.res V f ⋙ F.mapAction H :=
  NatIso.ofComponents
    (fun M => Action.mkIso (Iso.refl _) (fun h => by
      change F.map (M.ρ (f h)) ≫ 𝟙 (F.obj M.V) = 𝟙 (F.obj M.V) ≫ F.map (M.ρ (f h))
      rw [Category.comp_id, Category.id_comp]))
    (fun p => Action.Hom.ext (by
      change F.map p.hom ≫ 𝟙 _ = 𝟙 _ ≫ F.map p.hom
      rw [Category.comp_id, Category.id_comp]))

@[simp] theorem mapActionResIso_hom_app_hom {W : Type w} [Category.{v} W] (F : V ⥤ W)
    {H : Type uH} {G : Type uG} [Monoid H] [Monoid G] (f : H →* G) (M : Action V G) :
    ((mapActionResIso V F f).hom.app M).hom = 𝟙 (F.obj M.V) :=
  rfl

/-! ## Restriction along an embedding of algebraic closures -/

section Closure

variable {K : Type uK} {E : Type uE} [Field K] [Field E] [Algebra K E]

/-- Actions of `Gal(K̄/K)` restricted to `Gal(Ē/E)` along the continuous restriction homomorphism
of the specified closure embedding `ι`. -/
def alongClosure (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) :
    Action V (Field.absoluteGaloisGroup K) ⥤ Action V (Field.absoluteGaloisGroup E) :=
  Action.res V (restrictionAlongClosure ι).toMonoidHom

@[simp] theorem alongClosure_obj_V (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (M : Action V (Field.absoluteGaloisGroup K)) :
    ((alongClosure V ι).obj M).V = M.V :=
  rfl

@[simp] theorem alongClosure_obj_ρ (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (M : Action V (Field.absoluteGaloisGroup K)) (g : Field.absoluteGaloisGroup E) :
    ((alongClosure V ι).obj M).ρ g = M.ρ (restrictionAlongClosure ι g) :=
  rfl

@[simp] theorem alongClosure_map_hom (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    {M N : Action V (Field.absoluteGaloisGroup K)} (p : M ⟶ N) :
    ((alongClosure V ι).map p).hom = p.hom :=
  rfl

/-- Changing the closure embedding from `κ` to `ι` is the action of `closureChange ι κ`. -/
def alongClosureChangeIso (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) :
    alongClosure V κ ≅ alongClosure V ι :=
  resConjugateIso V _ _ (closureChange ι κ) (closureChange_intertwines ι κ)

@[simp] theorem alongClosureChangeIso_hom_app_hom
    (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (M : Action V (Field.absoluteGaloisGroup K)) :
    ((alongClosureChangeIso V ι κ).hom.app M).hom = M.ρ (closureChange ι κ) :=
  rfl

@[simp] theorem alongClosureChangeIso_inv_app_hom
    (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (M : Action V (Field.absoluteGaloisGroup K)) :
    ((alongClosureChangeIso V ι κ).inv.app M).hom = M.ρ (closureChange ι κ)⁻¹ :=
  rfl

end Closure

/-! ## Decomposition groups at finite places -/

section FinitePlace

variable {K : Type uK} [Field K] [NumberField K] (v : Global.FinitePlace K)

/-- The restriction homomorphism from the absolute Galois group of the actual completion at `v`
to that of `K`, along the specified closure embedding `ι`. -/
def localRestriction (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    LocalGroup v →* Field.absoluteGaloisGroup K := by
  letI : Algebra K (Global.FiniteCompletion K v) :=
    (NumberField.FinitePlace.embedding (K := K) v).toAlgebra
  exact (restrictionAlongClosure ι).toMonoidHom

/-- The restriction is the unique automorphism of `K̄` compatible with `ι`. -/
theorem localRestriction_commutes
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) (g : LocalGroup v)
    (x : AlgebraicClosure K) :
    letI : Algebra K (Global.FiniteCompletion K v) :=
      (NumberField.FinitePlace.embedding (K := K) v).toAlgebra
    ι (AlgEquiv.toRingEquiv (localRestriction v ι g) x) = AlgEquiv.toRingEquiv g (ι x) := by
  let : Algebra K (Global.FiniteCompletion K v) :=
    (NumberField.FinitePlace.embedding (K := K) v).toAlgebra
  exact restrictionAlongClosure_commutes ι g x

/-- For Mathlib's chosen closure embedding this is the published restriction map. -/
theorem localRestriction_chosen_apply (g : LocalGroup v) :
    localRestriction v (chosenClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) g =
      Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding (K := K) v) g :=
  rfl

/-- The element of `Gal(K̄/K)` relating two closure embeddings at `v`. -/
def localClosureChange
    (ι κ : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    Field.absoluteGaloisGroup K := by
  letI : Algebra K (Global.FiniteCompletion K v) :=
    (NumberField.FinitePlace.embedding (K := K) v).toAlgebra
  exact closureChange ι κ

theorem localClosureChange_intertwines
    (ι κ : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) (g : LocalGroup v) :
    localClosureChange v ι κ * localRestriction v κ g =
      localRestriction v ι g * localClosureChange v ι κ := by
  let : Algebra K (Global.FiniteCompletion K v) :=
    (NumberField.FinitePlace.embedding (K := K) v).toAlgebra
  exact closureChange_intertwines ι κ g

/-- Actions of `Gal(K̄/K)` restricted to the decomposition group at `v`, the absolute Galois group
of the actual completion, along the closure embedding `ι`. -/
def atFinitePlace (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    Action V (Field.absoluteGaloisGroup K) ⥤ Action V (LocalGroup v) :=
  Action.res V (localRestriction v ι)

@[simp] theorem atFinitePlace_obj_V
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    (M : Action V (Field.absoluteGaloisGroup K)) :
    ((atFinitePlace V v ι).obj M).V = M.V :=
  rfl

@[simp] theorem atFinitePlace_obj_ρ
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    (M : Action V (Field.absoluteGaloisGroup K)) (g : LocalGroup v) :
    ((atFinitePlace V v ι).obj M).ρ g = M.ρ (localRestriction v ι g) :=
  rfl

@[simp] theorem atFinitePlace_map_hom
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    {M N : Action V (Field.absoluteGaloisGroup K)} (p : M ⟶ N) :
    ((atFinitePlace V v ι).map p).hom = p.hom :=
  rfl

/-- This is the restriction along the closure embedding for the algebra structure of the
completion. -/
theorem atFinitePlace_eq_alongClosure
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    letI : Algebra K (Global.FiniteCompletion K v) :=
      (NumberField.FinitePlace.embedding (K := K) v).toAlgebra
    atFinitePlace V v ι = alongClosure V ι :=
  rfl

/-- Changing the closure embedding at `v` from `κ` to `ι` is the action of the element of
`Gal(K̄/K)` relating them. -/
def atFinitePlaceChangeIso
    (ι κ : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    atFinitePlace V v κ ≅ atFinitePlace V v ι :=
  resConjugateIso V _ _ (localClosureChange v ι κ) (localClosureChange_intertwines v ι κ)

@[simp] theorem atFinitePlaceChangeIso_hom_app_hom
    (ι κ : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    (M : Action V (Field.absoluteGaloisGroup K)) :
    ((atFinitePlaceChangeIso V v ι κ).hom.app M).hom = M.ρ (localClosureChange v ι κ) :=
  rfl

/-- An action is unramified at `v` along `ι` if the actual inertia subgroup of the completion,
the kernel of its residue action, acts trivially after restriction along `ι`. -/
def IsUnramifiedAlong (M : Action V (Field.absoluteGaloisGroup K))
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) : Prop :=
  ∀ i : localInertia v, ((atFinitePlace V v ι).obj M).ρ i.val = 𝟙 M.V

/-- An action is unramified at `v` if it is unramified along Mathlib's chosen closure
embedding. -/
def IsUnramifiedAt (M : Action V (Field.absoluteGaloisGroup K)) : Prop :=
  IsUnramifiedAlong V v M (chosenClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))

variable {V v}

/-- Unramifiedness does not depend on the closure embedding. -/
theorem isUnramifiedAlong_iff (M : Action V (Field.absoluteGaloisGroup K))
    (ι κ : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    IsUnramifiedAlong V v M ι ↔ IsUnramifiedAlong V v M κ :=
  forall_congr' fun i =>
    ρ_eq_id_iff_of_conj M (localClosureChange_intertwines v ι κ i.val)

theorem isUnramifiedAt_iff_along (M : Action V (Field.absoluteGaloisGroup K))
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    IsUnramifiedAt V v M ↔ IsUnramifiedAlong V v M ι :=
  isUnramifiedAlong_iff M _ ι

/-- Unramifiedness is invariant under isomorphism. -/
theorem IsUnramifiedAlong.of_iso {M N : Action V (Field.absoluteGaloisGroup K)} (e : M ≅ N)
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hM : IsUnramifiedAlong V v M ι) : IsUnramifiedAlong V v N ι := by
  intro i
  change N.ρ (localRestriction v ι i.val) = 𝟙 N.V
  have hc := e.inv.comm (localRestriction v ι i.val)
  rw [show M.ρ (localRestriction v ι i.val) = 𝟙 M.V from hM i, Category.comp_id] at hc
  calc
    N.ρ (localRestriction v ι i.val) =
        N.ρ (localRestriction v ι i.val) ≫ e.inv.hom ≫ e.hom.hom := by
      rw [← Action.comp_hom, e.inv_hom_id, Action.id_hom, Category.comp_id]
    _ = 𝟙 N.V := by
      rw [← Category.assoc, hc, ← Action.comp_hom, e.inv_hom_id, Action.id_hom]

/-- For an action unramified along `ι`, elements with the same residue action act by the same
endomorphism. -/
theorem IsUnramifiedAlong.ρ_eq_of_residueAction_eq {M : Action V (Field.absoluteGaloisGroup K)}
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hM : IsUnramifiedAlong V v M ι) {g h : LocalGroup v}
    (hres : localResidueAction v g = localResidueAction v h) :
    ((atFinitePlace V v ι).obj M).ρ g = ((atFinitePlace V v ι).obj M).ρ h := by
  have hker : g * h⁻¹ ∈ localInertia v := by
    change localResidueAction v (g * h⁻¹) = 1
    rw [map_mul, map_inv, hres, mul_inv_cancel]
  have hprod := hM ⟨g * h⁻¹, hker⟩
  let r := ((atFinitePlace V v ι).obj M).ρ
  change r (g * h⁻¹) = 1 at hprod
  change r g = r h
  calc
    r g = r g * (r (h⁻¹) * r h) := by
      rw [← map_mul, inv_mul_cancel, map_one, mul_one]
    _ = r (g * h⁻¹) * r h := by rw [map_mul, mul_assoc]
    _ = r h := by rw [hprod, one_mul]

variable (V v)

/-- The endomorphism by which the chosen geometric Frobenius lift at `v` acts after restriction
along `ι`. For unramified actions every geometric Frobenius lift acts by it. -/
def geometricFrobenius (M : Action V (Field.absoluteGaloisGroup K))
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) : M.V ⟶ M.V :=
  ((atFinitePlace V v ι).obj M).ρ (geometricFrobeniusLift v)

variable {V v}

theorem geometricFrobenius_eq_of_lift {M : Action V (Field.absoluteGaloisGroup K)}
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hM : IsUnramifiedAlong V v M ι) {g : LocalGroup v} (hg : IsGeometricFrobeniusLift v g) :
    ((atFinitePlace V v ι).obj M).ρ g = geometricFrobenius V v M ι :=
  hM.ρ_eq_of_residueAction_eq
    (residueAction_eq_of_geometricFrobenius hg (geometricFrobeniusLift_spec v))

/-- Morphisms of actions intertwine the Frobenius endomorphisms. -/
theorem geometricFrobenius_naturality {M N : Action V (Field.absoluteGaloisGroup K)} (p : M ⟶ N)
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    geometricFrobenius V v M ι ≫ p.hom = p.hom ≫ geometricFrobenius V v N ι :=
  ((atFinitePlace V v ι).map p).comm (geometricFrobeniusLift v)

/-- The Frobenius endomorphisms along two closure embeddings are conjugate by the action of the
element relating them. -/
theorem geometricFrobenius_conj (M : Action V (Field.absoluteGaloisGroup K))
    (ι κ : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    geometricFrobenius V v M κ ≫ M.ρ (localClosureChange v ι κ) =
      M.ρ (localClosureChange v ι κ) ≫ geometricFrobenius V v M ι :=
  ((atFinitePlaceChangeIso V v ι κ).hom.app M).comm (geometricFrobeniusLift v)

end FinitePlace

end Langlands.Shimura.DecompositionGroupAction
