import Mathlib.Data.PNat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact

/-!
# Residue inverse limits and the profinite-integer scalar ring
-/

noncomputable section

namespace Langlands.Global

namespace ResidueLimit

/-- Reduction between positive residue moduli. -/
def transition {n m : ℕ+} (h : (n : ℕ) ∣ (m : ℕ)) :
    ZMod (m : ℕ) →+* ZMod (n : ℕ) := ZMod.castHom h _

@[simp] theorem transition_intCast {n m : ℕ+} (h : (n : ℕ) ∣ (m : ℕ)) (z : ℤ) :
    transition h (z : ZMod (m : ℕ)) = (z : ZMod (n : ℕ)) := map_intCast _ _

@[simp] theorem transition_self (n : ℕ+) : transition (dvd_refl (n : ℕ)) = RingHom.id _ := by
  ext x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simp

theorem transition_comp {n m k : ℕ+} (h : (n : ℕ) ∣ (m : ℕ))
    (h' : (m : ℕ) ∣ (k : ℕ)) :
    (transition h).comp (transition h') = transition (dvd_trans h h') := by
  ext x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simp

variable {ι : Type*} (modulus : ι → ℕ+)

/-- The subring cut out by every divisibility compatibility equation. -/
def compatibleSubring : Subring (∀ i, ZMod (modulus i : ℕ)) where
  carrier := {x | ∀ i j (h : (modulus i : ℕ) ∣ (modulus j : ℕ)),
    transition h (x j) = x i}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy i j h
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) (hx i j h) (hy i j h))
  neg_mem' := by
    intro x hx i j h
    exact (map_neg _ _).trans (congrArg Neg.neg (hx i j h))
  mul_mem' := by
    intro x y hx hy i j h
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (hx i j h) (hy i j h))

end ResidueLimit

/-- The actual inverse limit of the residue rings selected by `modulus`. -/
abbrev ResidueLimit {ι : Type*} (modulus : ι → ℕ+) :=
  ↥(ResidueLimit.compatibleSubring modulus)

namespace ResidueLimit

variable {ι : Type*} {modulus : ι → ℕ+}

/-- The coordinate reduction homomorphism. -/
def reduction (i : ι) : ResidueLimit modulus →+* ZMod (modulus i : ℕ) :=
  (Pi.evalRingHom (fun i => ZMod (modulus i : ℕ)) i).comp
    (compatibleSubring modulus).subtype

@[simp] theorem reduction_apply (i : ι) (x : ResidueLimit modulus) :
    reduction i x = x.val i := rfl

theorem compatible (x : ResidueLimit modulus) (i j : ι)
    (h : (modulus i : ℕ) ∣ (modulus j : ℕ)) :
    transition h (reduction j x) = reduction i x := x.property i j h

theorem transition_comp_reduction (i j : ι)
    (h : (modulus i : ℕ) ∣ (modulus j : ℕ)) :
    (transition h).comp (reduction (modulus := modulus) j) = reduction i := by
  ext x
  exact compatible x i j h

@[ext] theorem ext {x y : ResidueLimit modulus}
    (h : ∀ i, reduction i x = reduction i y) : x = y :=
  Subtype.ext (funext h)

/-- Integers give their normalized family of residues. -/
def intCastHom : ℤ →+* ResidueLimit modulus := Int.castRingHom _

@[simp] theorem reduction_intCast (i : ι) (z : ℤ) :
    reduction i (intCastHom (modulus := modulus) z) = (z : ZMod (modulus i : ℕ)) :=
  map_intCast (reduction i) z

theorem reduction_surjective (i : ι) :
    Function.Surjective (reduction (modulus := modulus) i) := by
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨intCastHom z, reduction_intCast i z⟩

/-- The unique ring homomorphism induced by a compatible cone. -/
def lift {R : Type*} [NonAssocSemiring R]
    (f : ∀ i, R →+* ZMod (modulus i : ℕ))
    (hf : ∀ i j (h : (modulus i : ℕ) ∣ (modulus j : ℕ)),
      (transition h).comp (f j) = f i) : R →+* ResidueLimit modulus where
  toFun r := ⟨fun i => f i r, fun i j h => DFunLike.congr_fun (hf i j h) r⟩
  map_zero' := by apply Subtype.ext; funext i; exact map_zero (f i)
  map_one' := by apply Subtype.ext; funext i; exact map_one (f i)
  map_add' x y := by apply Subtype.ext; funext i; exact map_add (f i) x y
  map_mul' x y := by apply Subtype.ext; funext i; exact map_mul (f i) x y

@[simp] theorem reduction_lift {R : Type*} [NonAssocSemiring R]
    (f : ∀ i, R →+* ZMod (modulus i : ℕ)) (hf) (i : ι) :
    (reduction i).comp (lift f hf) = f i := rfl

theorem lift_unique {R : Type*} [NonAssocSemiring R]
    (f : ∀ i, R →+* ZMod (modulus i : ℕ)) (hf)
    (g : R →+* ResidueLimit modulus) (hg : ∀ i, (reduction i).comp g = f i) :
    g = lift f hf := by
  ext r i
  exact DFunLike.congr_fun (hg i) r

theorem isClosed_compatibleSubring :
    IsClosed (compatibleSubring modulus : Set (∀ i, ZMod (modulus i : ℕ))) := by
  change IsClosed {x : ∀ i, ZMod (modulus i : ℕ) | ∀ i j (h : (modulus i : ℕ) ∣ (modulus j : ℕ)),
    transition h (x j) = x i}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun h => ?_)))
  exact isClosed_eq ((continuous_of_discreteTopology : Continuous (transition h)).comp
    (continuous_apply j)) (continuous_apply i)

instance : CompactSpace (ResidueLimit modulus) :=
  isCompact_iff_compactSpace.mp (isClosed_compatibleSubring (modulus := modulus)).isCompact

instance : T2Space (ResidueLimit modulus) :=
  inferInstanceAs (T2Space ↥(compatibleSubring modulus))

instance : TotallyDisconnectedSpace (ResidueLimit modulus) :=
  inferInstanceAs (TotallyDisconnectedSpace ↥(compatibleSubring modulus))

instance : IsTopologicalRing (ResidueLimit modulus) :=
  inferInstanceAs (IsTopologicalRing ↥(compatibleSubring modulus))

/-- Each finite residue projection is continuous in the induced product topology. -/
theorem continuous_reduction (i : ι) : Continuous (reduction (modulus := modulus) i) :=
  (continuous_apply i).comp continuous_subtype_val

theorem continuous_iff {X : Type*} [TopologicalSpace X] (f : X → ResidueLimit modulus) :
    Continuous f ↔ ∀ i, Continuous (fun x => reduction i (f x)) := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

theorem continuous_lift {R : Type*} [NonAssocSemiring R] [TopologicalSpace R]
    (f : ∀ i, R →+* ZMod (modulus i : ℕ)) (hf)
    (hc : ∀ i, Continuous (f i)) : Continuous (lift f hf) :=
  (continuous_iff _).2 hc

/-- The universal property in topological rings, with continuity recorded explicitly. -/
theorem existsUnique_continuous_lift {R : Type*} [NonAssocSemiring R] [TopologicalSpace R]
    (f : ∀ i, R →+* ZMod (modulus i : ℕ))
    (hf : ∀ i j (h : (modulus i : ℕ) ∣ (modulus j : ℕ)),
      (transition h).comp (f j) = f i)
    (hc : ∀ i, Continuous (f i)) :
    ∃! g : R →+* ResidueLimit modulus, Continuous g ∧ ∀ i, (reduction i).comp g = f i := by
  refine ⟨lift f hf, ⟨continuous_lift f hf hc, fun i => reduction_lift f hf i⟩, ?_⟩
  intro g hg
  exact lift_unique f hf g hg.2

end ResidueLimit

/-- The profinite-integer scalar ring, indexed by all positive integers. -/
abbrev ProfiniteIntegerRing := ResidueLimit (fun n : ℕ+ => n)

namespace ProfiniteIntegerRing

abbrev reduction (n : ℕ+) : ProfiniteIntegerRing →+* ZMod (n : ℕ) :=
  ResidueLimit.reduction n

abbrev intCastHom : ℤ →+* ProfiniteIntegerRing := ResidueLimit.intCastHom

end ProfiniteIntegerRing

/-- Positive moduli coprime to `p`; for prime `p` this is the prime-to-`p` index set. -/
abbrev PrimeToModulus (p : ℕ) := {n : ℕ+ // Nat.Coprime (n : ℕ) p}

/-- The residue inverse limit away from `p`. -/
abbrev PrimeToProfiniteIntegerRing (p : ℕ) :=
  ResidueLimit (fun n : PrimeToModulus p => n.val)

namespace PrimeToProfiniteIntegerRing

abbrev reduction {p : ℕ} (n : PrimeToModulus p) :
    PrimeToProfiniteIntegerRing p →+* ZMod (n.val : ℕ) := ResidueLimit.reduction n

abbrev intCastHom (p : ℕ) : ℤ →+* PrimeToProfiniteIntegerRing p :=
  ResidueLimit.intCastHom

/-- Restrict a full compatible family to the prime-to-`p` coordinates. -/
def restrict (p : ℕ) : ProfiniteIntegerRing →+* PrimeToProfiniteIntegerRing p :=
  ResidueLimit.lift (fun n => ProfiniteIntegerRing.reduction n.val)
    (fun i j h => ResidueLimit.transition_comp_reduction i.val j.val h)

@[simp] theorem reduction_restrict (p : ℕ) (n : PrimeToModulus p)
    (x : ProfiniteIntegerRing) : reduction n (restrict p x) =
    ProfiniteIntegerRing.reduction n.val x := rfl

theorem continuous_restrict (p : ℕ) : Continuous (restrict p) :=
  ResidueLimit.continuous_lift _ _ (fun n => ResidueLimit.continuous_reduction n.val)

end PrimeToProfiniteIntegerRing

end Langlands.Global
