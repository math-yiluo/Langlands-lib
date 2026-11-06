import Langlands.Geometry.Building.RootVectorCoordinatesOfNoHigherRoots
import Langlands.Geometry.Building.IntegerValuation
import Langlands.FieldTheory.HenselianIntegerAddValuation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Card

/-! # Minimum valuations in actual finite root-vector coordinates -/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k] {J : Type w} [Fintype J]
  (omega : AddValuation k (WithTop ℝ))

/-- The finite minimum of the values of the vector coordinates. -/
def finiteVectorValue (x : J → k) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun j => omega (x j)

theorem finiteVectorValue_le (x : J → k) (j : J) :
    finiteVectorValue omega x ≤ omega (x j) := by
  classical
  exact Finset.inf_le (Finset.mem_univ j)

@[simp] theorem finiteVectorValue_zero : finiteVectorValue omega (0 : J → k) = ⊤ := by
  classical
  simp [finiteVectorValue]

@[simp] theorem finiteVectorValue_eq_top_iff (x : J → k) :
    finiteVectorValue omega x = ⊤ ↔ x = 0 := by
  constructor
  · intro h
    funext j
    apply omega.top_iff.mp
    exact top_le_iff.mp (h ▸ finiteVectorValue_le omega x j)
  · rintro rfl
    exact finiteVectorValue_zero omega

theorem finiteVectorValue_add_ge (x y : J → k) :
    min (finiteVectorValue omega x) (finiteVectorValue omega y) ≤
      finiteVectorValue omega (x + y) := by
  classical
  apply Finset.le_inf
  intro j _
  exact (min_le_min (finiteVectorValue_le omega x j)
    (finiteVectorValue_le omega y j)).trans (omega.map_add (x j) (y j))

@[simp] theorem finiteVectorValue_neg (x : J → k) :
    finiteVectorValue omega (-x) = finiteVectorValue omega x := by
  simp only [finiteVectorValue, Pi.neg_apply, omega.map_neg]

theorem finiteVectorValue_smul (c : k) (x : J → k) :
    finiteVectorValue omega (c • x) = omega c + finiteVectorValue omega x := by
  classical
  simp only [finiteVectorValue, Pi.smul_apply, smul_eq_mul, omega.map_mul]
  exact (Finset.apply_inf_eq_inf_comp_of_linearOrder
    (fun z : WithTop ℝ => omega c + z)
    (fun _ _ h => add_le_add le_rfl h) (by simp)).symm

@[simp] theorem finiteVectorValue_const [Nonempty J] (x : k) :
    finiteVectorValue omega (fun _ : J => x) = omega x := by
  classical
  exact Finset.inf_const Finset.univ_nonempty _

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {a : characterLattice S}
  (c : WeightedRootVectorCoordinates i a)

/-- The coordinate minimum on the actual root subgroup, infinite off it. -/
def weightedRootVectorValue (g : rationalPoints G) : WithTop ℝ := by
  classical
  exact if hg : g ∈ rootGroupPoints i a then
    finiteVectorValue omega (c.equiv.symm ⟨g, hg⟩).toAdd else ⊤

@[simp] theorem weightedRootVectorValue_of_mem (g : rootGroupPoints i a) :
    weightedRootVectorValue omega c g =
      finiteVectorValue omega (c.equiv.symm g).toAdd := by
  simp only [weightedRootVectorValue, dite_eq_left g.property]

theorem weightedRootVectorValue_of_not_mem {g : rationalPoints G}
    (hg : g ∉ rootGroupPoints i a) : weightedRootVectorValue omega c g = ⊤ := by
  simp only [weightedRootVectorValue, dite_eq_right hg]

@[simp] theorem weightedRootVectorValue_coordinate (x : Fin c.dimension → k) :
    weightedRootVectorValue omega c (c.equiv (Multiplicative.ofAdd x)) =
      finiteVectorValue omega x := by
  rw [weightedRootVectorValue_of_mem, c.equiv.symm_apply_apply]
  rfl

@[simp] theorem weightedRootVectorValue_one : weightedRootVectorValue omega c 1 = ⊤ := by
  simpa using weightedRootVectorValue_coordinate omega c 0

theorem weightedRootVectorValue_eq_top_iff {g : rationalPoints G}
    (hg : g ∈ rootGroupPoints i a) :
    weightedRootVectorValue omega c g = ⊤ ↔ g = 1 := by
  rw [weightedRootVectorValue_of_mem omega c ⟨g, hg⟩, finiteVectorValue_eq_top_iff]
  constructor
  · intro h
    have h' : c.equiv.symm ⟨g, hg⟩ = 1 := h
    have he := congrArg c.equiv h'
    exact congrArg Subtype.val (by simpa only [c.equiv.apply_symm_apply, map_one] using he)
  · rintro rfl
    simp

theorem weightedRootVectorValue_mul_ge {g h : rationalPoints G}
    (hg : g ∈ rootGroupPoints i a) (hh : h ∈ rootGroupPoints i a) :
    min (weightedRootVectorValue omega c g) (weightedRootVectorValue omega c h) ≤
      weightedRootVectorValue omega c (g * h) := by
  rw [weightedRootVectorValue_of_mem omega c ⟨g, hg⟩,
    weightedRootVectorValue_of_mem omega c ⟨h, hh⟩,
    weightedRootVectorValue_of_mem omega c ⟨g * h, (rootGroupPoints i a).mul_mem hg hh⟩]
  change _ ≤ finiteVectorValue omega (c.equiv.symm (⟨g, hg⟩ * ⟨h, hh⟩)).toAdd
  rw [map_mul, toAdd_mul]
  exact finiteVectorValue_add_ge omega _ _

theorem weightedRootVectorValue_inv {g : rationalPoints G}
    (hg : g ∈ rootGroupPoints i a) :
    weightedRootVectorValue omega c g⁻¹ = weightedRootVectorValue omega c g := by
  rw [weightedRootVectorValue_of_mem omega c ⟨g, hg⟩,
    weightedRootVectorValue_of_mem omega c ⟨g⁻¹, (rootGroupPoints i a).inv_mem hg⟩]
  change finiteVectorValue omega (c.equiv.symm (⟨g, hg⟩⁻¹)).toAdd = _
  rw [map_inv, toAdd_inv, finiteVectorValue_neg]

/-- All real thresholds are subgroups of the actual rational root group. -/
def weightedRootVectorFiltration (r : ℝ) : Subgroup (rationalPoints G) where
  carrier := {g | g ∈ rootGroupPoints i a ∧ (r : WithTop ℝ) ≤ weightedRootVectorValue omega c g}
  one_mem' := ⟨(rootGroupPoints i a).one_mem, by simp⟩
  mul_mem' hg hh := ⟨(rootGroupPoints i a).mul_mem hg.1 hh.1,
    (le_min hg.2 hh.2).trans (weightedRootVectorValue_mul_ge omega c hg.1 hh.1)⟩
  inv_mem' hg := ⟨(rootGroupPoints i a).inv_mem hg.1, by
    rw [weightedRootVectorValue_inv omega c hg.1]; exact hg.2⟩

@[simp] theorem mem_weightedRootVectorFiltration (r : ℝ) (g : rationalPoints G) :
    g ∈ weightedRootVectorFiltration omega c r ↔
      g ∈ rootGroupPoints i a ∧ (r : WithTop ℝ) ≤ weightedRootVectorValue omega c g := Iff.rfl

/-- The constructed root weight gives the exact torus conjugation shift. -/
theorem weightedRootVectorValue_conjugation (s : rationalPoints S.toGrp)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a) :
    weightedRootVectorValue omega c
        (rationalPoints.map i s * g * (rationalPoints.map i s)⁻¹) =
      weightedRootVectorValue omega c g +
        omega (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s : k) := by
  obtain ⟨x, hx⟩ := c.equiv.surjective ⟨g, hg⟩
  have h : (c.equiv x : rationalPoints G) = g := congrArg Subtype.val hx
  have hc := c.conjugation s x.toAdd
  simp only [ofAdd_toAdd] at hc
  have hxv : weightedRootVectorValue omega c (c.equiv x) =
      finiteVectorValue omega x.toAdd := by
    simpa only [ofAdd_toAdd] using weightedRootVectorValue_coordinate omega c x.toAdd
  rw [← h, hc, weightedRootVectorValue_coordinate, hxv, finiteVectorValue_smul, add_comm]

section Henselian

variable (v : Valuation k (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)

/-- Base integer-normalized values in the actual finite root-vector coordinates. -/
def henselianRootVectorValue : rationalPoints G → WithTop ℝ :=
  weightedRootVectorValue (FieldTheory.henselianIntegerAddValuation v hH k) c

theorem henselianRootVectorValue_constant (x : kˣ) :
    henselianRootVectorValue c v hH
      (c.equiv (Multiplicative.ofAdd (fun _ => (x : k)))) =
        ((IntegerValuation.order v x : ℝ) : WithTop ℝ) := by
  let : Nonempty (Fin c.dimension) := ⟨⟨0, c.dimension_pos⟩⟩
  rw [henselianRootVectorValue, weightedRootVectorValue_coordinate, finiteVectorValue_const,
    ← show algebraMap k k (x : k) = (x : k) from rfl,
    FieldTheory.henselianIntegerAddValuation_base v hH k (Units.ne_zero x),
    IntegerValuation.order, IntegerValuation.orderUnits_toAdd]

theorem henselianRootVectorValue_exists_integer (hv : Function.Surjective v) (n : ℤ) :
    ∃ g ∈ rootGroupPoints i a, henselianRootVectorValue c v hH g =
      ((n : ℝ) : WithTop ℝ) := by
  obtain ⟨x, hx⟩ := hv (WithZero.exp (-n))
  have hx0 : x ≠ 0 := by
    intro h
    have hz : (0 : WithZero (Multiplicative ℤ)) = WithZero.exp (-n) := by
      simpa only [h, map_zero] using hx
    exact WithZero.exp_ne_zero hz.symm
  refine ⟨c.equiv (Multiplicative.ofAdd (fun _ => x)),
    (c.equiv (Multiplicative.ofAdd (fun _ => x))).property, ?_⟩
  have he := henselianRootVectorValue_constant c v hH (Units.mk0 x hx0)
  simpa only [Units.val_mk0, IntegerValuation.order, IntegerValuation.orderUnits_toAdd,
    hx, WithZero.log_exp, neg_neg] using he

theorem henselianRootVectorValue_image_infinite (hv : Function.Surjective v) :
    (henselianRootVectorValue c v hH '' (rootGroupPoints i a : Set (rationalPoints G))).Infinite := by
  have hinj : Function.Injective (fun n : ℤ => ((n : ℝ) : WithTop ℝ)) := by
    intro m n h
    exact_mod_cast WithTop.coe_injective h
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  exact henselianRootVectorValue_exists_integer c v hH hv n

theorem henselianRootVectorValue_three_le_encard (hv : Function.Surjective v) :
    3 ≤ (henselianRootVectorValue c v hH ''
      (rootGroupPoints i a : Set (rationalPoints G))).encard := by
  rw [(henselianRootVectorValue_image_infinite c v hH hv).encard_eq]
  exact le_top

theorem henselianRootVectorValue_conjugation (s : rationalPoints S.toGrp)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a) :
    henselianRootVectorValue c v hH
        (rationalPoints.map i s * g * (rationalPoints.map i s)⁻¹) =
      henselianRootVectorValue c v hH g +
        ((IntegerValuation.order v
          (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s) : ℝ) :
            WithTop ℝ) := by
  rw [henselianRootVectorValue, weightedRootVectorValue_conjugation _ _ _ hg]
  congr 1
  simpa only [Algebra.algebraMap_self_apply, IntegerValuation.order,
    IntegerValuation.orderUnits_toAdd] using
    FieldTheory.henselianIntegerAddValuation_base v hH k (Units.ne_zero
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s))

end Henselian

/-- Local V0/V1 data and the exact split-torus shift on one actual root group.
No relation between different roots is included. -/
structure TorusCompatibleLocalRootValue
    (v : Valuation k (WithZero (Multiplicative ℤ))) (i : S.toGrp ⟶ G)
    (a : characterLattice S) where
  value : rationalPoints G → WithTop ℝ
  eq_top_of_not_mem : ∀ g ∉ rootGroupPoints i a, value g = ⊤
  exists_integer : ∀ n : ℤ, ∃ g ∈ rootGroupPoints i a, value g = ((n : ℝ) : WithTop ℝ)
  three_le_encard : 3 ≤ (value '' (rootGroupPoints i a : Set (rationalPoints G))).encard
  eq_top_iff : ∀ g ∈ rootGroupPoints i a, value g = ⊤ ↔ g = 1
  mul_ge : ∀ g ∈ rootGroupPoints i a, ∀ h ∈ rootGroupPoints i a,
    min (value g) (value h) ≤ value (g * h)
  inv : ∀ g ∈ rootGroupPoints i a, value g⁻¹ = value g
  conjugation : ∀ (s : rationalPoints S.toGrp) (g : rationalPoints G),
    g ∈ rootGroupPoints i a →
      value (rationalPoints.map i s * g * (rationalPoints.map i s)⁻¹) =
        value g + ((IntegerValuation.order v
          (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s) : ℝ) :
            WithTop ℝ)

/-- Construct actual local V0/V1 values and torus compatibility without a
coordinate premise, for every root with no higher positive integral multiple. -/
def henselianLocalRootValueOfNoHigherRoots
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (hH : HenselianLocalRing v.valuationSubring) (hv : Function.Surjective v)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (hhigh : RelativeRoot.HasNoHigherRoots i a) :
    TorusCompatibleLocalRootValue v i a := by
  let c := weightedRootVectorCoordinatesOfNoHigherRoots hS i ha hhigh
  exact {
    value := henselianRootVectorValue c v hH
    eq_top_of_not_mem := fun _ hg => weightedRootVectorValue_of_not_mem _ c hg
    exists_integer := henselianRootVectorValue_exists_integer c v hH hv
    three_le_encard := henselianRootVectorValue_three_le_encard c v hH hv
    eq_top_iff := fun _ hg => weightedRootVectorValue_eq_top_iff _ c hg
    mul_ge := fun _ hg _ hh => weightedRootVectorValue_mul_ge _ c hg hh
    inv := fun _ hg => weightedRootVectorValue_inv _ c hg
    conjugation := fun s _ hg => henselianRootVectorValue_conjugation c v hH s hg }

end Langlands.Geometry.Building
