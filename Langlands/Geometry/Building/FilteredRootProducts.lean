import Langlands.Geometry.Building.KPApartment
import Mathlib.Data.List.OfFn

/-!
# Actual filtered root blocks and their ordered multiplication

The real-depth specialization of KP Definition 7.3.3(1) retains both
`U_{a,x,f(a)}` and `U_{2a,x,f(2a)}`. The second factor is trivial when
`2a` is not an actual relative root. The block is a set product; its
identification with a subgroup and its product decompositions are separate
structural assertions.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

open Classical in
/-- The actual `U_{2a,x,r}`, with the trivial-group convention when `2a`
is not a relative root (KP Definition 7.3.3(1) and the convention preceding
Definition 6.3.4). -/
def doubleFiltration (x : D.Apartment) (a : characterLattice S) (r : ℝ) :
    Subgroup (rationalPoints G) :=
  if 2 • a ∈ relativeRoots i then D.filtration x (2 • a) r else ⊥

theorem doubleFiltration_of_mem (x : D.Apartment) (a : characterLattice S) (r : ℝ)
    (ha : 2 • a ∈ relativeRoots i) :
    D.doubleFiltration x a r = D.filtration x (2 • a) r := by
  classical
  simp only [doubleFiltration, ite_eq_left ha]

theorem doubleFiltration_of_not_mem (x : D.Apartment) (a : characterLattice S) (r : ℝ)
    (ha : 2 • a ∉ relativeRoots i) :
    D.doubleFiltration x a r = ⊥ := by
  classical
  simp only [doubleFiltration, ite_eq_right ha]

theorem doubleFiltration_le_doubleRootGroupPoints (x : D.Apartment)
    (a : characterLattice S) (r : ℝ) :
    D.doubleFiltration x a r ≤ doubleRootGroupPoints i a := by
  classical
  by_cases ha : 2 • a ∈ relativeRoots i
  · simpa only [doubleFiltration, doubleRootGroupPoints, ite_eq_left ha] using
      D.filtration_le_rootGroupPoints x (2 • a) r
  · simp only [doubleFiltration, doubleRootGroupPoints, ite_eq_right ha, le_refl]

/-- The real-depth block `U_{a,x,f} = U_{a,x,f(a)} U_{2a,x,f(2a)}`
of KP Definition 7.3.3(1). No concavity or subgroup assertion is built into
this definition. In particular the doubled-root factor is not discarded. -/
def filtrationBlock (x : D.Apartment) (f : characterLattice S → ℝ)
    (a : characterLattice S) : Set (rationalPoints G) :=
  (D.filtration x a (f a) : Set (rationalPoints G)) *
    (D.doubleFiltration x a (f (2 • a)) : Set (rationalPoints G))

theorem mem_filtrationBlock {x : D.Apartment} {f : characterLattice S → ℝ}
    {a : characterLattice S} {g : rationalPoints G} :
    g ∈ D.filtrationBlock x f a ↔
      ∃ u ∈ D.filtration x a (f a),
        ∃ v ∈ D.doubleFiltration x a (f (2 • a)), u * v = g :=
  Iff.rfl

/-- Multiply one element of each actual block, in the specified order.
For fixed-sign decompositions the later statement restricts `a` to enumerate
each indivisible root of that sign once. This definition alone asserts
neither a sign restriction nor a bijection. -/
def orderedFiltrationBlockProduct (x : D.Apartment) (f : characterLattice S → ℝ)
    {n : ℕ} (a : Fin n → characterLattice S)
    (u : ∀ j : Fin n, D.filtrationBlock x f (a j)) : rationalPoints G :=
  (List.ofFn fun j => (u j : rationalPoints G)).prod

end Langlands.Geometry.Building.KPApartmentData
