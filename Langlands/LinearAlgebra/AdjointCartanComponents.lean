import Langlands.LinearAlgebra.SimplyConnectedCartanComponents

/-! # Cartan components and simple-root support in adjoint root data -/

noncomputable section

universe u v w

open Set Module Submodule

namespace Langlands.LinearAlgebra.AdjointCartanComponents

open SimplyConnectedCartanComponents

variable {J : Type u} {X : Type v} {Y : Type w}
  [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y}

/-- The simple roots of a base form a `ℤ`-basis of the weight lattice when the roots
span it. -/
def simpleRootBasis (b : P.Base) (hspan : P.rootSpan ℤ = ⊤) : Basis b.support ℤ X :=
  Basis.mk b.linearIndepOn_root <| by
    change ⊤ ≤ span ℤ (range <| P.root ∘ ((↑) : b.support → J))
    rw [range_comp, Subtype.range_coe_subtype, Finset.setOfPred_mem, b.span_int_root_support]
    exact hspan.ge

@[simp] lemma simpleRootBasis_apply (b : P.Base) (hspan : P.rootSpan ℤ = ⊤)
    (i : b.support) : simpleRootBasis b hspan i = P.root i := by
  simp [simpleRootBasis]

/-- Simple-root coefficient coordinates of the weight lattice. -/
def simpleRootCoordinates (b : P.Base) (hspan : P.rootSpan ℤ = ⊤) :
    X ≃ₗ[ℤ] (b.support → ℤ) :=
  (simpleRootBasis b hspan).equivFun

@[simp] lemma simpleRootCoordinates_apply (b : P.Base) (hspan : P.rootSpan ℤ = ⊤)
    (x : X) (i : b.support) :
    simpleRootCoordinates b hspan x i = (simpleRootBasis b hspan).repr x i :=
  rfl

/-- A simple root has coordinate `1` at its own index. -/
lemma simpleRootCoordinates_root_self (b : P.Base) (hspan : P.rootSpan ℤ = ⊤)
    (i : b.support) : simpleRootCoordinates b hspan (P.root i) i = 1 := by
  rw [simpleRootCoordinates_apply, ← simpleRootBasis_apply b hspan i, Basis.repr_self,
    Finsupp.single_eq_same]

/-- A simple root has coordinate `0` at every other index. -/
lemma simpleRootCoordinates_root_of_ne (b : P.Base) (hspan : P.rootSpan ℤ = ⊤)
    {i j : b.support} (h : j ≠ i) : simpleRootCoordinates b hspan (P.root i) j = 0 := by
  rw [simpleRootCoordinates_apply, ← simpleRootBasis_apply b hspan i, Basis.repr_self,
    Finsupp.single_eq_of_ne h]

variable (b : P.Base) (hspan : P.rootSpan ℤ = ⊤)

/-- A weight is supported on a Cartan component if its simple-root coordinates vanish
outside that component. -/
def RootSupported (c : Component b) (x : X) : Prop :=
  ∀ i : b.support, component b i ≠ c → (simpleRootBasis b hspan).repr x i = 0

/-- A simple root is supported on its own Cartan component. -/
theorem rootSupported_simple (i : b.support) :
    RootSupported b hspan (component b i) (P.root i) := by
  intro j hj
  have hji : j ≠ i := fun h => hj (congrArg (component b) h)
  rw [← simpleRootBasis_apply b hspan i, Basis.repr_self]
  simp [hji]

namespace RootSupported

variable {b hspan} {c : Component b} {x z : X}

/-- A component support is closed under negation. -/
theorem neg (hx : RootSupported b hspan c x) : RootSupported b hspan c (-x) := by
  intro i hi
  simp only [map_neg, Finsupp.neg_apply, hx i hi, neg_zero]

/-- A component support is closed under subtraction. -/
theorem sub (hx : RootSupported b hspan c x) (hz : RootSupported b hspan c z) :
    RootSupported b hspan c (x - z) := by
  intro i hi
  simp only [map_sub, Finsupp.sub_apply, hx i hi, hz i hi, sub_self]

/-- A component support is closed under integral multiplication. -/
theorem smul (hx : RootSupported b hspan c x) (n : ℤ) :
    RootSupported b hspan c (n • x) := by
  intro i hi
  simp only [map_smul, Finsupp.smul_apply, hx i hi, smul_zero]

/-- A simple coroot in another component annihilates a supported weight. -/
theorem pairing_eq_zero (hx : RootSupported b hspan c x)
    (i : b.support) (hi : component b i ≠ c) :
    P.toLinearMap x (P.coroot i) = 0 := by
  classical
  let e := simpleRootBasis b hspan
  have he : x = ∑ j : b.support, e.repr x j • e j := (e.sum_repr x).symm
  rw [he, map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : component b j = c
  · have hji : component b j ≠ component b i := fun h => hi (h.symm.trans hj)
    rw [map_smul, LinearMap.smul_apply]
    rw [show e j = P.root j from simpleRootBasis_apply b hspan j]
    rw [P.root_coroot_eq_pairing, pairing_eq_zero_of_component_ne b j i hji, smul_zero]
  · rw [hx j hj, zero_smul, map_zero, LinearMap.zero_apply]

/-- A nonzero weight cannot be supported on two different components. -/
theorem component_eq {d : Component b} (hx : RootSupported b hspan c x)
    (hz : RootSupported b hspan d x) (hne : x ≠ 0) : c = d := by
  classical
  by_contra hcd
  apply hne
  let e := simpleRootBasis b hspan
  apply e.repr.injective
  change e.repr x = e.repr 0
  rw [map_zero]
  ext i
  by_cases hi : component b i = c
  · exact hz i (by rwa [hi])
  · exact hx i hi

end RootSupported

/-- Every root of a finite reduced root datum whose roots span the weight lattice is
supported on one Cartan component. Simple reflections preserve this property. -/
theorem exists_rootSupported [Finite J] [P.IsReduced] (r : J) :
    ∃ c : Component b, RootSupported b hspan c (P.root r) := by
  classical
  refine b.induction_reflect r
    (p := fun i => ∃ c : Component b, RootSupported b hspan c (P.root i)) ?_ ?_ ?_
  · rintro i ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [P.root_reflectionPerm, P.reflection_apply_self]
    exact hc.neg
  · intro i hi
    exact ⟨component b ⟨i, hi⟩, rootSupported_simple b hspan ⟨i, hi⟩⟩
  · rintro i j ⟨c, hc⟩ hj
    by_cases hjc : component b ⟨j, hj⟩ = c
    · refine ⟨c, ?_⟩
      rw [P.root_reflectionPerm, P.reflection_apply_root]
      exact hc.sub ((hjc ▸ rootSupported_simple b hspan ⟨j, hj⟩).smul _)
    · have hp : P.pairing i j = 0 := by
        rw [← P.root_coroot_eq_pairing]
        exact hc.pairing_eq_zero ⟨j, hj⟩ hjc
      refine ⟨c, ?_⟩
      rw [P.root_reflectionPerm, P.reflection_apply_root, hp, zero_smul, sub_zero]
      exact hc

/-- Every root has a unique Cartan component in its simple-root support. -/
theorem existsUnique_rootSupported [Finite J] [P.IsReduced] (r : J) :
    ∃! c : Component b, RootSupported b hspan c (P.root r) := by
  obtain ⟨c, hc⟩ := exists_rootSupported b hspan r
  exact ⟨c, hc, fun d hd => hd.component_eq hc (P.ne_zero r)⟩

/-- The component of an arbitrary root, determined by its simple-root coordinates. -/
def rootComponent [Finite J] [P.IsReduced] (r : J) : Component b :=
  Classical.choose (existsUnique_rootSupported b hspan r)

/-- The specified root component supports the whole root. -/
theorem rootSupported_rootComponent [Finite J] [P.IsReduced] (r : J) :
    RootSupported b hspan (rootComponent b hspan r) (P.root r) :=
  (Classical.choose_spec (existsUnique_rootSupported b hspan r)).1

/-- The simple-root coordinates of a root vanish outside its component. -/
theorem simpleRootCoordinates_root_eq_zero [Finite J] [P.IsReduced] (r : J)
    (i : b.support) (hi : component b i ≠ rootComponent b hspan r) :
    simpleRootCoordinates b hspan (P.root r) i = 0 :=
  rootSupported_rootComponent b hspan r i hi

/-- On simple roots, the root component agrees with the quotient map on the
Cartan diagram. -/
theorem rootComponent_simple [Finite J] [P.IsReduced] (i : b.support) :
    rootComponent b hspan i = component b i :=
  (rootSupported_rootComponent b hspan i).component_eq
    (rootSupported_simple b hspan i) (P.ne_zero i)

end Langlands.LinearAlgebra.AdjointCartanComponents
