import Mathlib.Algebra.Field.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# The symplectic Steinberg cocycle group

Matsumoto's algebraic Steinberg cocycle relations and the corresponding
abelian presentation of `S(F)` are given in Proposition 5.5 and Corollary 5.11.
See `matsumoto-1969-sous-groupes-arithmetiques`, §5, printed pp. 26, 28
and 30–31, SHA-256 `4ac51e1290e2ab3c633d5a55378eb078f88d824bb3d28aac3585fce0595db5ca`.
-/

namespace Langlands.Covering.BrylinskiDeligne

universe u v

variable {F : Type u} [Field F]

/-- The unit with value `1 - a` when `a` is a unit different from `1`. -/
def oneSubUnit (a : Fˣ) (ha : a ≠ 1) : Fˣ :=
  Units.mk0 (1 - (a : F)) (sub_ne_zero.mpr fun h => ha (Units.ext h.symm))

@[simp] theorem coe_oneSubUnit (a : Fˣ) (ha : a ≠ 1) :
    (oneSubUnit a ha : F) = 1 - (a : F) :=
  rfl

/-- A multiplicative Steinberg cocycle satisfying Matsumoto's (S1), (S2) and (S3). -/
structure SteinbergCocycle (F : Type u) [Field F] (A : Type v) [CommGroup A] where
  toFun : Fˣ → Fˣ → A
  cocycle (a b d : Fˣ) :
    toFun a b * toFun (a * b) d = toFun a (b * d) * toFun b d
  one_one : toFun 1 1 = 1
  inv_inv (a b : Fˣ) : toFun a b = toFun a⁻¹ b⁻¹
  one_sub_mul (a b : Fˣ) (ha : a ≠ 1) : toFun a b = toFun a (oneSubUnit a ha * b)

variable {A : Type v} [CommGroup A]

namespace SteinbergCocycle

instance : CoeFun (SteinbergCocycle F A) (fun _ => Fˣ → Fˣ → A) :=
  ⟨toFun⟩

@[simp] theorem one_left (c : SteinbergCocycle F A) (a : Fˣ) : c 1 a = 1 := by
  have h : c 1 a * 1 = c 1 a * c 1 a := by
    simpa only [c.one_one, one_mul, mul_one] using c.cocycle 1 1 a
  exact (mul_left_cancel h).symm

@[simp] theorem one_right (c : SteinbergCocycle F A) (a : Fˣ) : c a 1 = 1 := by
  have h : c a 1 * c a 1 = c a 1 * 1 := by
    simpa only [c.one_one, one_mul, mul_one] using c.cocycle a 1 1
  exact mul_left_cancel h

end SteinbergCocycle

private abbrev FreeSymbols (F : Type u) [Field F] :=
  Abelianization (FreeGroup (Fˣ × Fˣ))

private def freeSymbol (a b : Fˣ) : FreeSymbols F :=
  Abelianization.of (FreeGroup.of (a, b))

/-- The two sides of each defining relation, expressed in the free abelian group. -/
private inductive SymbolRelation (F : Type u) [Field F] : FreeSymbols F → FreeSymbols F → Prop
  | cocycle (a b d : Fˣ) :
      SymbolRelation F (freeSymbol a b * freeSymbol (a * b) d)
        (freeSymbol a (b * d) * freeSymbol b d)
  | one_one : SymbolRelation F (freeSymbol 1 1) 1
  | inv_inv (a b : Fˣ) : SymbolRelation F (freeSymbol a b) (freeSymbol a⁻¹ b⁻¹)
  | one_sub_mul (a b : Fˣ) (ha : a ≠ 1) :
      SymbolRelation F (freeSymbol a b) (freeSymbol a (oneSubUnit a ha * b))

private def relatorSubgroup (F : Type u) [Field F] : Subgroup (FreeSymbols F) :=
  Subgroup.closure {r | ∃ x y, SymbolRelation F x y ∧ r = x / y}

/-- The abelian group `S(F)` on unit pairs with the symplectic Steinberg relations. -/
def SymplecticSteinbergK2 (F : Type u) [Field F] : Type u :=
  FreeSymbols F ⧸ relatorSubgroup F

namespace SymplecticSteinbergK2

instance : CommGroup (SymplecticSteinbergK2 F) :=
  inferInstanceAs (CommGroup (FreeSymbols F ⧸ relatorSubgroup F))

/-- The class of the generator indexed by `(a, b)`. -/
def symbol (a b : Fˣ) : SymplecticSteinbergK2 F :=
  QuotientGroup.mk (freeSymbol a b)

private theorem quotient_eq {x y : FreeSymbols F} (h : SymbolRelation F x y) :
    (QuotientGroup.mk x : SymplecticSteinbergK2 F) = QuotientGroup.mk y :=
  QuotientGroup.eq_iff_div_mem.mpr (Subgroup.subset_closure ⟨x, y, h, rfl⟩)

/-- The canonical Steinberg cocycle with values in `S(F)`. -/
def universalCocycle (F : Type u) [Field F] :
    SteinbergCocycle F (SymplecticSteinbergK2 F) where
  toFun := symbol
  cocycle a b d := quotient_eq (.cocycle a b d)
  one_one := quotient_eq .one_one
  inv_inv a b := quotient_eq (.inv_inv a b)
  one_sub_mul a b ha := quotient_eq (.one_sub_mul a b ha)

@[simp] theorem universalCocycle_apply (a b : Fˣ) : universalCocycle F a b = symbol a b :=
  rfl

@[simp] theorem symbol_one_left (a : Fˣ) : symbol 1 a = 1 :=
  (universalCocycle F).one_left a

@[simp] theorem symbol_one_right (a : Fˣ) : symbol a 1 = 1 :=
  (universalCocycle F).one_right a

private def freeEval (c : SteinbergCocycle F A) : FreeSymbols F →* A :=
  Abelianization.lift (FreeGroup.lift fun p : Fˣ × Fˣ => c p.1 p.2)

private theorem freeEval_freeSymbol (c : SteinbergCocycle F A) (a b : Fˣ) :
    freeEval c (freeSymbol a b) = c a b := by
  simp only [freeEval, freeSymbol, Abelianization.lift_apply_of, FreeGroup.lift_apply_of]

private theorem relatorSubgroup_le_ker (c : SteinbergCocycle F A) :
    relatorSubgroup F ≤ (freeEval c).ker := by
  rw [relatorSubgroup, Subgroup.closure_le]
  rintro _ ⟨x, y, h, rfl⟩
  change freeEval c (x / y) = 1
  rw [map_div, div_eq_one]
  cases h with
  | cocycle a b d =>
    simpa only [map_mul, freeEval_freeSymbol] using c.cocycle a b d
  | one_one =>
    simpa only [map_one, freeEval_freeSymbol] using c.one_one
  | inv_inv a b =>
    simpa only [freeEval_freeSymbol] using c.inv_inv a b
  | one_sub_mul a b ha =>
    simpa only [freeEval_freeSymbol] using c.one_sub_mul a b ha

/-- Evaluate the presented symbols in a Steinberg cocycle with commutative coefficients. -/
def lift (c : SteinbergCocycle F A) : SymplecticSteinbergK2 F →* A :=
  QuotientGroup.lift (relatorSubgroup F) (freeEval c) (relatorSubgroup_le_ker c)

@[simp] theorem lift_symbol (c : SteinbergCocycle F A) (a b : Fˣ) :
    lift c (symbol a b) = c a b :=
  (QuotientGroup.lift_mk' _ (relatorSubgroup_le_ker c) _).trans (freeEval_freeSymbol c a b)

/-- Homomorphisms out of `S(F)` are determined by the symbols. -/
theorem hom_ext {f g : SymplecticSteinbergK2 F →* A}
    (h : ∀ a b : Fˣ, f (symbol a b) = g (symbol a b)) : f = g := by
  apply QuotientGroup.monoidHom_ext (N := relatorSubgroup F)
  apply Abelianization.hom_ext
  apply FreeGroup.ext_hom
  intro p
  exact h p.1 p.2

/-- A homomorphism evaluating every symbol by `c` is equal to `lift c`. -/
theorem lift_unique (c : SteinbergCocycle F A) (f : SymplecticSteinbergK2 F →* A)
    (h : ∀ a b : Fˣ, f (symbol a b) = c a b) : f = lift c :=
  hom_ext fun a b => (h a b).trans (lift_symbol c a b).symm

end SymplecticSteinbergK2

end Langlands.Covering.BrylinskiDeligne
