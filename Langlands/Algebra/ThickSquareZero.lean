import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Maps

/-! # Commutative trivial square-zero extensions -/

universe u

namespace Langlands.Algebra

/-- The trivial square-zero extension `A ⊕ F` of a commutative ring `A` by an `A`-module `F`,
with multiplication `(a, f) * (a', f') = (a * a', a • f' + a' • f)`. It is Mathlib's
`TrivSqZeroExt A F` with the opposite action of `A` taken equal to the given action. -/
def Thick (A F : Type u) : Type u := TrivSqZeroExt A F

namespace Thick

section Basic

variable {A F : Type u}

/-- The element `(a, f)`. -/
def mk (a : A) (f : F) : Thick A F := (a, f)

/-- The first component. -/
def fst (x : Thick A F) : A := Prod.fst (show A × F from x)

/-- The second component. -/
def snd (x : Thick A F) : F := Prod.snd (show A × F from x)

@[simp] lemma fst_mk (a : A) (f : F) : fst (mk a f) = a := rfl

@[simp] lemma snd_mk (a : A) (f : F) : snd (mk a f) = f := rfl

@[ext] lemma ext {x y : Thick A F} (h₁ : fst x = fst y) (h₂ : snd x = snd y) : x = y :=
  Prod.ext h₁ h₂

@[simp] lemma mk_fst_snd (x : Thick A F) : mk (fst x) (snd x) = x := rfl

end Basic

variable {A F : Type u} [CommRing A] [AddCommGroup F] [Module A F]

instance instCommRing : CommRing (Thick A F) :=
  letI : Module Aᵐᵒᵖ F := Module.compHom F (RingEquiv.toOpposite A).symm.toRingHom
  haveI : IsCentralScalar A F := ⟨fun _ _ => rfl⟩
  TrivSqZeroExt.commRing

@[simp] lemma fst_add (x y : Thick A F) : fst (x + y) = fst x + fst y := rfl

@[simp] lemma snd_add (x y : Thick A F) : snd (x + y) = snd x + snd y := rfl

@[simp] lemma fst_neg (x : Thick A F) : fst (-x) = -fst x := rfl

@[simp] lemma snd_neg (x : Thick A F) : snd (-x) = -snd x := rfl

@[simp] lemma fst_sub (x y : Thick A F) : fst (x - y) = fst x - fst y := rfl

@[simp] lemma snd_sub (x y : Thick A F) : snd (x - y) = snd x - snd y := rfl

@[simp] lemma fst_zero : fst (0 : Thick A F) = 0 := rfl

@[simp] lemma snd_zero : snd (0 : Thick A F) = 0 := rfl

@[simp] lemma fst_one : fst (1 : Thick A F) = 1 := rfl

@[simp] lemma snd_one : snd (1 : Thick A F) = 0 := rfl

@[simp] lemma fst_mul (x y : Thick A F) : fst (x * y) = fst x * fst y := rfl

@[simp] lemma snd_mul (x y : Thick A F) : snd (x * y) = fst x • snd y + fst y • snd x := rfl

/-- The inclusion `a ↦ (a, 0)`. -/
def inl : A →+* Thick A F where
  toFun a := mk a 0
  map_one' := rfl
  map_mul' a b := by ext <;> simp
  map_zero' := rfl
  map_add' a b := by ext <;> simp

@[simp] lemma fst_inl (a : A) : fst (inl a : Thick A F) = a := rfl

@[simp] lemma snd_inl (a : A) : snd (inl a : Thick A F) = 0 := rfl

/-- The projection `(a, f) ↦ a`. -/
def fstHom : Thick A F →+* A where
  toFun := fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma fstHom_apply (x : Thick A F) : fstHom x = fst x := rfl

instance instAlgebra {S : Type*} [CommRing S] [Algebra S A] : Algebra S (Thick A F) :=
  (inl.comp (algebraMap S A)).toAlgebra

lemma algebraMap_apply {S : Type*} [CommRing S] [Algebra S A] (s : S) :
    algebraMap S (Thick A F) s = inl (algebraMap S A s) := rfl

@[simp] lemma fst_algebraMap {S : Type*} [CommRing S] [Algebra S A] (s : S) :
    fst (algebraMap S (Thick A F) s) = algebraMap S A s := rfl

@[simp] lemma snd_algebraMap {S : Type*} [CommRing S] [Algebra S A] (s : S) :
    snd (algebraMap S (Thick A F) s) = 0 := rfl

@[simp] lemma fst_smul {S : Type*} [CommRing S] [Algebra S A] (s : S) (x : Thick A F) :
    fst (s • x) = algebraMap S A s * fst x := rfl

@[simp] lemma snd_smul {S : Type*} [CommRing S] [Algebra S A] (s : S) (x : Thick A F) :
    snd (s • x) = algebraMap S A s • snd x := by
  change snd (algebraMap S (Thick A F) s * x) = _
  simp

instance instIsScalarTower {S T : Type*} [CommRing S] [CommRing T] [Algebra S T] [Algebra T A]
    [Algebra S A] [IsScalarTower S T A] : IsScalarTower S T (Thick A F) :=
  IsScalarTower.of_algebraMap_eq fun s => by
    ext
    · simp [IsScalarTower.algebraMap_apply S T A]
    · simp

/-- The inclusion `f ↦ (0, f)`. -/
def inr : F →ₗ[A] Thick A F where
  toFun f := mk 0 f
  map_add' f f' := by ext <;> simp
  map_smul' a f := by
    ext
    · simp
    · rw [snd_smul]
      simp

@[simp] lemma fst_inr (f : F) : fst (inr f : Thick A F) = 0 := rfl

@[simp] lemma snd_inr (f : F) : snd (inr f : Thick A F) = f := rfl

lemma inr_mul_inr (f f' : F) : (inr f : Thick A F) * inr f' = 0 := by
  ext <;> simp

lemma inl_mul_inr (a : A) (f : F) : (inl a : Thick A F) * inr f = inr (a • f) := by
  ext <;> simp

lemma eq_inl_add_inr (x : Thick A F) : x = inl (fst x) + inr (snd x) := by
  ext <;> simp

lemma mem_ker_fstHom_iff (x : Thick A F) : x ∈ RingHom.ker (fstHom : Thick A F →+* A) ↔
    ∃ f, inr f = x := by
  constructor
  · intro h
    refine ⟨snd x, ?_⟩
    ext
    · exact (RingHom.mem_ker.mp h).symm
    · rfl
  · rintro ⟨f, rfl⟩
    exact RingHom.mem_ker.mpr rfl

/-- The projection `(a, f) ↦ a` as an algebra map. -/
def fstAlgHom (S : Type*) [CommRing S] [Algebra S A] : Thick A F →ₐ[S] A :=
  { fstHom with commutes' := fun _ => rfl }

@[simp] lemma fstAlgHom_apply (S : Type*) [CommRing S] [Algebra S A] (x : Thick A F) :
    fstAlgHom S x = fst x := rfl

lemma fst_surjective : Function.Surjective (fst : Thick A F → A) := fun a => ⟨inl a, rfl⟩

lemma isNilpotent_of_fst_eq_zero (x : Thick A F) (hx : fst x = 0) : IsNilpotent x := by
  refine ⟨2, ?_⟩
  have : x = inr (snd x) := by ext <;> simp [hx]
  rw [this, pow_two, inr_mul_inr]

lemma inr_injective : Function.Injective (inr : F →ₗ[A] Thick A F) := fun f f' h => by
  simpa using congrArg snd h

section Lift

variable {B : Type*} [CommRing B]

/-- The ring map `(a, f) ↦ ρ a + D f`, for an additive `D` with `D (a • f) = ρ a * D f` and
square-zero image. -/
def lift (ρ : A →+* B) (D : F →+ B) (hD : ∀ a f, D (a • f) = ρ a * D f)
    (hDD : ∀ f f', D f * D f' = 0) : Thick A F →+* B where
  toFun x := ρ (fst x) + D (snd x)
  map_one' := by simp
  map_mul' x y := by
    simp only [fst_mul, snd_mul, map_mul, map_add, hD]
    rw [add_mul, mul_add, mul_add, hDD, add_zero]
    ring
  map_zero' := by simp
  map_add' x y := by
    simp only [fst_add, snd_add, map_add]
    ring

@[simp] lemma lift_apply (ρ : A →+* B) (D : F →+ B) (hD : ∀ a f, D (a • f) = ρ a * D f)
    (hDD : ∀ f f', D f * D f' = 0) (x : Thick A F) :
    lift ρ D hD hDD x = ρ (fst x) + D (snd x) := rfl

end Lift

section Derivation

variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P] [Module P F] [Module R F]
  [IsScalarTower R P F]

/-- The `R`-algebra map `p ↦ (p, D p)` of a derivation. -/
def ofDerivation (D : Derivation R P F) : P →ₐ[R] Thick P F where
  toFun p := mk p (D p)
  map_one' := by ext <;> simp
  map_mul' p q := by
    ext
    · simp
    · simp [Derivation.leibniz]
  map_zero' := by ext <;> simp
  map_add' p q := by ext <;> simp
  commutes' r := by ext <;> simp

omit [IsScalarTower R P F] in
@[simp] lemma fst_ofDerivation (D : Derivation R P F) (p : P) : fst (ofDerivation D p) = p := rfl

omit [IsScalarTower R P F] in
@[simp] lemma snd_ofDerivation (D : Derivation R P F) (p : P) :
    snd (ofDerivation D p) = D p := rfl

end Derivation

section Map

variable {A' : Type u} [CommRing A'] [Module A' F]

/-- The ring map `(a, f) ↦ (π a, f)`, when `A` acts on `F` through `π : A →+* A'`. -/
def map (π : A →+* A') (hπ : ∀ (a : A) (f : F), a • f = π a • f) : Thick A F →+* Thick A' F :=
  lift (inl.comp π) (inr : F →ₗ[A'] Thick A' F).toAddMonoidHom
    (fun a f => by
      change inr (a • f) = inl (π a) * inr f
      rw [inl_mul_inr, hπ])
    (fun f f' => inr_mul_inr f f')

@[simp] lemma fst_map (π : A →+* A') (hπ : ∀ (a : A) (f : F), a • f = π a • f) (x : Thick A F) :
    fst (map π hπ x) = π (fst x) := by
  change fst (inl (π (fst x)) + inr (snd x)) = _
  simp

@[simp] lemma snd_map (π : A →+* A') (hπ : ∀ (a : A) (f : F), a • f = π a • f) (x : Thick A F) :
    snd (map π hπ x) = snd x := by
  change snd (inl (π (fst x)) + inr (snd x)) = _
  simp

end Map

end Thick

end Langlands.Algebra
