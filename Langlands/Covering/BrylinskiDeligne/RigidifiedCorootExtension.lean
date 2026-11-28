import Langlands.Covering.BrylinskiDeligne.LatticeSignExtension
import Langlands.Covering.BrylinskiDeligne.TriangularBilinearForm
import Langlands.GroupScheme.Reductive.Pinning
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.SetTheory.Cardinal.Finite

/-! # The rigidified sign extension on the coroot lattice -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.GroupScheme
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.Covering.BrylinskiDeligne

variable {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- The integer span of the coroots inside the pinning torus's cocharacter lattice. -/
abbrev CorootLattice := p.rootDatum.corootSpan ℤ

/-- The inclusion of the coroot lattice into the cocharacter lattice of the pinned torus. -/
def corootLatticeInclusion : CorootLattice p →ₗ[ℤ] cocharacterLattice p.torus :=
  (p.rootDatum.corootSpan ℤ).subtype

/-- The pinned simple coroots form an integer basis of their span. -/
def simpleCorootBasis : Module.Basis p.base.support ℤ (CorootLattice p) :=
  p.base.flip.toWeightBasisInt

@[simp] theorem corootLatticeInclusion_simpleCorootBasis (i : p.base.support) :
    corootLatticeInclusion p (simpleCorootBasis p i) = p.rootDatum.coroot i := by
  exact p.base.flip.coe_toWeightBasisInt_apply ⟨i.val, i.property⟩

/-- A numbering of the simple coroots, with order inherited from the finite ordinal. -/
def simpleCorootOrder : p.base.support ≃ Fin (Nat.card p.base.support) :=
  Finite.equivFin _

/-- The simple-coroot basis indexed in the chosen order. -/
def orderedSimpleCorootBasis : Module.Basis (Fin (Nat.card p.base.support)) ℤ (CorootLattice p) :=
  (simpleCorootBasis p).reindex (simpleCorootOrder p)

@[simp] theorem orderedSimpleCorootBasis_apply (i : Fin (Nat.card p.base.support)) :
    orderedSimpleCorootBasis p i = simpleCorootBasis p ((simpleCorootOrder p).symm i) :=
  Module.Basis.reindex_apply _ _ _

variable (B : LinearMap.BilinForm ℤ (CorootLattice p))

/-- The cocycle exponent is the strictly lower triangular part of `B` in the chosen basis. -/
def rigidifiedCorootForm : LinearMap.BilinForm ℤ (CorootLattice p) :=
  strictLowerBilinearForm (orderedSimpleCorootBasis p) B

theorem rigidifiedCorootForm_apply_basis (i j : Fin (Nat.card p.base.support)) :
    rigidifiedCorootForm p B (orderedSimpleCorootBasis p i) (orderedSimpleCorootBasis p j) =
      if j < i then B (orderedSimpleCorootBasis p i) (orderedSimpleCorootBasis p j) else 0 :=
  strictLowerBilinearForm_apply_basis _ _ _ _

/-- The sign extension of the actual coroot lattice using the triangular exponent. -/
abbrev RigidifiedCorootExtension : Type u :=
  LatticeSignExtension F (rigidifiedCorootForm p B)

/-- The short exact sequence of the rigidified coroot extension. -/
def rigidifiedCorootGroupExtension :
    GroupExtension Fˣ (RigidifiedCorootExtension p B) (Multiplicative (CorootLattice p)) :=
  LatticeSignExtension.groupExtension F (rigidifiedCorootForm p B)

theorem rigidifiedCoroot_central :
    (rigidifiedCorootGroupExtension p B).inl.range ≤
      Subgroup.center (RigidifiedCorootExtension p B) :=
  LatticeSignExtension.central F (rigidifiedCorootForm p B)

/-- The unit coordinate of a point in the coroot extension. -/
def corootUnitCoordinate (x : RigidifiedCorootExtension p B) : Fˣ :=
  letI := signCoefficientAction F (Y := CorootLattice p)
  x.left

/-- The distinguished lift has simple-coroot coordinate `i` and unit coordinate `1`. -/
def simpleCorootLift (i : p.base.support) : RigidifiedCorootExtension p B :=
  LatticeSignExtension.mk F (rigidifiedCorootForm p B) (simpleCorootBasis p i) 1

@[simp] theorem simpleCorootLift_projection (i : p.base.support) :
    (rigidifiedCorootGroupExtension p B).rightHom (simpleCorootLift p B i) =
      Multiplicative.ofAdd (simpleCorootBasis p i) := rfl

/-- The commutator is the central sign of `B` on the two projected coroot-lattice points. -/
theorem rigidifiedCoroot_commutator (hSymm : B.IsSymm)
    (hEven : ∀ i, Even (B (simpleCorootBasis p i) (simpleCorootBasis p i)))
    (x y : RigidifiedCorootExtension p B) :
    ⁅x, y⁆ = (rigidifiedCorootGroupExtension p B).inl
      ((-1 : Fˣ) ^ B ((rigidifiedCorootGroupExtension p B).rightHom x).toAdd
        ((rigidifiedCorootGroupExtension p B).rightHom y).toAdd) := by
  let E := rigidifiedCorootGroupExtension p B
  let v := (E.rightHom x).toAdd
  let w := (E.rightHom y).toAdd
  let D := rigidifiedCorootForm p B
  let n := D v w + D w v
  have hParity : Even (B v w - n) :=
    even_sub_strictLowerBilinearForm (orderedSimpleCorootBasis p) B hSymm.eq
      (fun i => by
        rw [orderedSimpleCorootBasis_apply]
        exact hEven ((simpleCorootOrder p).symm i)) v w
  have hSign : (-1 : Fˣ) ^ n = (-1 : Fˣ) ^ B v w := by
    calc
      (-1 : Fˣ) ^ n = (-1 : Fˣ) ^ n * (-1 : Fˣ) ^ (B v w - n) := by
        rw [negOne_zpow_even F hParity, mul_one]
      _ = (-1 : Fˣ) ^ B v w := by rw [← zpow_add, add_sub_cancel]
  exact (LatticeSignExtension.commutator F D x y).trans (congrArg E.inl hSign)

theorem simpleCorootLift_commutator (hSymm : B.IsSymm)
    (hEven : ∀ i, Even (B (simpleCorootBasis p i) (simpleCorootBasis p i)))
    (i j : p.base.support) :
    ⁅simpleCorootLift p B i, simpleCorootLift p B j⁆ = (rigidifiedCorootGroupExtension p B).inl
      ((-1 : Fˣ) ^ B (simpleCorootBasis p i) (simpleCorootBasis p j)) := by
  simpa only [simpleCorootLift_projection, toAdd_ofAdd] using
    rigidifiedCoroot_commutator p B hSymm hEven (simpleCorootLift p B i) (simpleCorootLift p B j)

/-- Powers of a distinguished lift have unit coordinate `1` for all integer exponents. -/
theorem simpleCorootLift_zpow (i : p.base.support) (n : ℤ) :
    simpleCorootLift p B i ^ n =
      LatticeSignExtension.mk F (rigidifiedCorootForm p B) (n • simpleCorootBasis p i) 1 := by
  let e := simpleCorootBasis p i
  let D := rigidifiedCorootForm p B
  have hb : orderedSimpleCorootBasis p (simpleCorootOrder p i) = e := by simp [e]
  have hD : D e e = 0 := by
    change rigidifiedCorootForm p B e e = 0
    rw [← hb, rigidifiedCorootForm_apply_basis, ite_eq_right (lt_irrefl _)]
  let f : Multiplicative ℤ →* RigidifiedCorootExtension p B :=
    { toFun := fun m => LatticeSignExtension.mk F D (m.toAdd • e) 1
      map_one' := by
        change LatticeSignExtension.mk F D ((0 : ℤ) • e) 1 = 1
        simp
      map_mul' := by
        intro m k
        change LatticeSignExtension.mk F D ((m.toAdd + k.toAdd) • e) 1 =
          LatticeSignExtension.mk F D (m.toAdd • e) 1 *
            LatticeSignExtension.mk F D (k.toAdd • e) 1
        rw [LatticeSignExtension.mk_mul, add_zsmul]
        simp [hD] }
  have ht : ((Multiplicative.ofAdd (1 : ℤ)) ^ n).toAdd = n := by
    rw [toAdd_zpow, toAdd_ofAdd, Int.zsmul_eq_mul, mul_one]
  have h := f.map_zpow (Multiplicative.ofAdd (1 : ℤ)) n
  change LatticeSignExtension.mk F D (((Multiplicative.ofAdd (1 : ℤ)) ^ n).toAdd • e) 1 =
    (LatticeSignExtension.mk F D ((1 : ℤ) • e) 1) ^ n at h
  simpa [ht, simpleCorootLift, D, e] using h.symm

/-- The product of the indicated integer powers in increasing simple-coroot order. -/
def orderedSimpleCorootProduct (n : Fin (Nat.card p.base.support) → ℤ) :
    RigidifiedCorootExtension p B :=
  ((Finset.univ.sort (· ≤ ·)).map fun i =>
    simpleCorootLift p B ((simpleCorootOrder p).symm i) ^ n i).prod

private theorem orderedSimpleCorootProduct_aux (n : Fin (Nat.card p.base.support) → ℤ)
    (indices : List (Fin (Nat.card p.base.support))) (h : indices.Pairwise (· ≤ ·)) :
    (indices.map fun i => simpleCorootLift p B ((simpleCorootOrder p).symm i) ^ n i).prod =
      LatticeSignExtension.mk F (rigidifiedCorootForm p B)
        (indices.map fun i => n i • orderedSimpleCorootBasis p i).sum 1 := by
  induction indices with
  | nil => simp
  | cons i indices ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
    have hzero : rigidifiedCorootForm p B (n i • orderedSimpleCorootBasis p i)
        (indices.map fun j => n j • orderedSimpleCorootBasis p j).sum = 0 :=
      strictLowerBilinearForm_ordered_sum (orderedSimpleCorootBasis p) B i indices hhead n
    rw [List.map_cons, List.prod_cons, ih htail, List.map_cons, List.sum_cons,
      simpleCorootLift_zpow, ← orderedSimpleCorootBasis_apply, LatticeSignExtension.mk_mul, hzero]
    simp only [zpow_zero, mul_one]

/-- Using the basis coordinates of a point gives its lift with unit coordinate `1`. -/
theorem orderedSimpleCorootProduct_repr (y : CorootLattice p) :
    orderedSimpleCorootProduct p B ((orderedSimpleCorootBasis p).repr y) =
      LatticeSignExtension.mk F (rigidifiedCorootForm p B) y 1 := by
  unfold orderedSimpleCorootProduct
  rw [orderedSimpleCorootProduct_aux p B _ _ (Finset.pairwise_sort _ _), sorted_sum_basis_repr]

/-- An element equals its central coefficient times its ordered product of simple lifts. -/
theorem rigidifiedCoroot_ordered_coordinates (x : RigidifiedCorootExtension p B) :
    (rigidifiedCorootGroupExtension p B).inl (corootUnitCoordinate p B x) *
      orderedSimpleCorootProduct p B
        ((orderedSimpleCorootBasis p).repr ((rigidifiedCorootGroupExtension p B).rightHom x).toAdd)
      = x := by
  rw [orderedSimpleCorootProduct_repr]
  unfold rigidifiedCorootGroupExtension
  rw [LatticeSignExtension.inl_eq_mk, LatticeSignExtension.mk_mul]
  simp only [zero_add, mul_one, map_zero, LinearMap.zero_apply, zpow_zero]
  exact LatticeSignExtension.mk_right_left F (rigidifiedCorootForm p B) x

/-- The central coefficient group and the distinguished simple-coroot lifts generate. -/
theorem rigidifiedCoroot_generates :
    Subgroup.closure
      (Set.range (rigidifiedCorootGroupExtension p B).inl ∪ Set.range (simpleCorootLift p B)) = ⊤ := by
  let S := Subgroup.closure
    (Set.range (rigidifiedCorootGroupExtension p B).inl ∪ Set.range (simpleCorootLift p B))
  apply top_unique
  intro x _
  change x ∈ S
  rw [← rigidifiedCoroot_ordered_coordinates p B x]
  apply S.mul_mem
  · exact Subgroup.subset_closure (Or.inl ⟨corootUnitCoordinate p B x, rfl⟩)
  · unfold orderedSimpleCorootProduct
    apply S.list_prod_mem
    intro g hg
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact S.zpow_mem (Subgroup.subset_closure (Or.inr ⟨(simpleCorootOrder p).symm i, rfl⟩)) _

end Langlands.Covering.BrylinskiDeligne
