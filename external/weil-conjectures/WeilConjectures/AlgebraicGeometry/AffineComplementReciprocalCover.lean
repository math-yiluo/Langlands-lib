/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjective
import WeilConjectures.RingTheory.JacobsonDenominatorFunctionField

/-! # Reciprocal functions on a two-open cover

Source: Stacks Project, Varieties Lemma 09NB, first paragraph and open-cover construction.
(blueprint: lem-sc-affine-complement-reciprocal-cover)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem complement_stalk_dimension
    (X : Scheme.{u}) [IsIntegral X] (hdim : topologicalKrullDim X = 1)
    (U : X.Opens) (hne : (U : Set X).Nonempty) (x : X) (hx : x ∉ U) :
    ringKrullDim (X.presheaf.stalk x) = 1 := by
  let : PartialOrder X := specializationOrder X
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have hlt : x < genericPoint X := by
    refine lt_of_le_of_ne (genericPoint_specializes x) ?_
    intro he
    exact hx (he ▸ hη)
  rw [ringKrullDim_stalk_eq_coheight]
  have htop : (Order.coheight x : WithBot ℕ∞) ≤ 1 := by
    have h := Order.coheight_le_krullDim x
    rwa [← Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints,
      ← topologicalKrullDim, hdim] at h
  have hpos : 0 < Order.coheight x := by
    rw [Order.coheight_pos]
    intro hm
    exact hlt.not_ge (hm hlt.le)
  exact le_antisymm htop (by exact_mod_cast Order.one_le_iff_ne_zero.mpr hpos.ne')

private theorem generic_mem_open (X : Scheme.{u}) [IsIntegral X]
    (W : X.Opens) [Nonempty W] : genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using ‹Nonempty W›)

private theorem functionField_res (X : Scheme.{u}) [IsIntegral X]
    {W Z : X.Opens} [Nonempty W] [Nonempty Z] (i : Z ⟶ W) (s : Γ(X, W)) :
    X.germToFunctionField Z (X.presheaf.map i.op s) =
      X.germToFunctionField W s :=
  X.presheaf.germ_res_apply i (genericPoint X) (generic_mem_open X Z) s

/-- An affine open with finite complement admits a reciprocal function on an open
neighbourhood of its complement.

Source: Stacks Project, Varieties Lemma 09NB (varieties-lemma-find-globally-generated),
proof through the open-cover construction.
(blueprint: lem-sc-affine-complement-reciprocal-cover).

Proof: Set A = O(U), K = k(X), and B_x = O_{X,x} for x outside U. The stalks are
Noetherian local domains. Their dimension is one: the generic point lies in U and
strictly specializes to x, while chains in a stalk have length at most dim X = 1.
Both A and B_x have fraction field K. Separatedness makes A tensor B_x -> K
surjective. The common-denominator lemma 09N5 supplies nonzero f in A with inverse
in the maximal ideal of every B_x. Represent these inverse germs on neighbourhoods
V_x of x. All representatives have the same image f^{-1} in K and so agree on
nonempty overlaps by injectivity of regular functions into K; on empty overlaps
agreement is automatic. The sheaf axiom glues them to g on V = union V_x. Thus
U union V = X. On U intersect V the product fg is 1, again by injectivity into K.
Consequently g is a unit at every point of U intersect V. At each point outside U
its germ is in the maximal ideal by construction. This gives D(g) = U intersect V.
If the complement is empty, V is empty and g is its unique section; the
restriction equation holds in the subsingleton ring of sections on the empty overlap.
-/
theorem exists_affine_complement_reciprocal_cover
    (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated] [IsLocallyNoetherian X]
    [CompactSpace X] (hdim : topologicalKrullDim X = 1) (U : X.Opens)
    (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty)
    (hfin : (Set.compl (U : Set X)).Finite) :
    ∃ (V : X.Opens) (f : Γ(X, U)) (g : Γ(X, V)),
      U ⊔ V = ⊤ ∧
      X.presheaf.map (homOfLE inf_le_left).op f *
        X.presheaf.map (homOfLE inf_le_right).op g = 1 ∧
      X.basicOpen g = U ⊓ V := by
  classical
  let : Nonempty U := hne.to_subtype
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let C := (U : Set X)ᶜ
  let : Finite C := hfin.to_subtype
  have hlocaldim (x : C) : ringKrullDim (X.presheaf.stalk x.1) = 1 :=
    complement_stalk_dimension X hdim U hne x.1 x.2
  have hsurj (x : C) : Function.Surjective
      (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom ℤ Γ(X, U) X.functionField)
        (IsScalarTower.toAlgHom ℤ (X.presheaf.stalk x.1) X.functionField)) := by
    convert X.separated_affine_functionField_surjective U hU x.1 x.2 (hlocaldim x)
      using 1
    congr 1
  obtain ⟨f, hf, hfb⟩ := RingTheory.exists_inv_mem_jacobson_of_tensor_surjective
    (fun x : C ↦ X.presheaf.stalk x.1) hlocaldim hsurj
  choose b hb hbe using hfb
  have hrep (x : C) := X.presheaf.exists_germ_eq (b x)
  choose W hxW s hs using hrep
  have (x : C) : Nonempty (W x) := ⟨⟨x.1, hxW x⟩⟩
  have hfield (x : C) : X.germToFunctionField (W x) (s x) =
      (algebraMap Γ(X, U) X.functionField f)⁻¹ := by
    rw [← X.algebraMap_germ_eq_germToFunctionField (hxW x), hs x]
    exact hbe x
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf W s := by
    intro x y
    let : Nonempty (W x ⊓ W y : X.Opens) :=
      ⟨⟨genericPoint X, generic_mem_open X (W x), generic_mem_open X (W y)⟩⟩
    apply X.germToFunctionField_injective (W x ⊓ W y)
    rw [functionField_res X ((W x).infLELeft (W y)),
      functionField_res X ((W x).infLERight (W y))]
    exact (hfield x).trans (hfield y).symm
  obtain ⟨g, hg, _⟩ := X.sheaf.existsUnique_gluing W s hcompat
  change Γ(X, ⨆ x : C, W x) at g
  change ∀ x : C, X.presheaf.map (TopologicalSpace.Opens.leSupr W x).op g = s x at hg
  let V : X.Opens := ⨆ x : C, W x
  have hcover : U ⊔ V = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x ∈ U
    · exact Or.inl hx
    · exact Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
  have hnonunit (x : C) (hxV : x.1 ∈ V) :
      ¬ IsUnit (X.presheaf.germ V x.1 hxV g) := by
    have heq : X.presheaf.germ V x.1 hxV g = b x := by
      rw [← X.presheaf.germ_res_apply (TopologicalSpace.Opens.leSupr W x)
        x.1 (hxW x) g, hg x, hs x]
    rw [heq]
    have hb' := hb x
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hb'
    change b x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x.1) at hb'
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb'
    exact hb'
  rcases isEmpty_or_nonempty C with hC | hC
  · let : IsEmpty C := hC
    have hV : V = ⊥ := iSup_of_empty W
    let : Subsingleton Γ(X, U ⊓ V) := by
      rw [hV, inf_bot_eq]
      infer_instance
    refine ⟨V, f, g, hcover, Subsingleton.elim _ _, ?_⟩
    have hle : X.basicOpen g ≤ V := X.basicOpen_le g
    rw [hV] at hle
    exact (le_bot_iff.mp hle).trans (by simp [hV])
  · let : Nonempty C := hC
    let x₀ : C := Classical.choice hC
    let : Nonempty V := ⟨⟨x₀.1,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨x₀, hxW x₀⟩⟩⟩
    let : Nonempty (U ⊓ V : X.Opens) :=
      ⟨⟨genericPoint X, generic_mem_open X U, generic_mem_open X V⟩⟩
    have hgf : X.germToFunctionField V g =
        (algebraMap Γ(X, U) X.functionField f)⁻¹ := by
      rw [← functionField_res X (TopologicalSpace.Opens.leSupr W x₀) g, hg x₀]
      exact hfield x₀
    have hfg : X.presheaf.map (homOfLE inf_le_left).op f *
        X.presheaf.map (homOfLE inf_le_right).op g = 1 := by
      apply X.germToFunctionField_injective (U ⊓ V)
      rw [map_mul, map_one, functionField_res X (homOfLE inf_le_left),
        functionField_res X (homOfLE inf_le_right), hgf]
      apply mul_inv_cancel₀
      intro hz
      apply hf
      apply X.germToFunctionField_injective U
      simpa only [map_zero] using hz
    refine ⟨V, f, g, hcover, hfg, ?_⟩
    apply le_antisymm
    · intro x hxg
      have hxV : x ∈ V := X.basicOpen_le g hxg
      refine ⟨?_, hxV⟩
      by_contra hxU
      exact hnonunit ⟨x, hxU⟩ hxV ((X.mem_basicOpen g x hxV).mp hxg)
    · have hgunit : IsUnit (X.presheaf.map (homOfLE inf_le_right).op g) :=
        isUnit_iff_exists_inv'.mpr ⟨_, hfg⟩
      have hbasic := X.basicOpen_of_isUnit hgunit
      rw [X.basicOpen_res g (homOfLE inf_le_right).op] at hbasic
      exact hbasic.ge.trans inf_le_right

end AlgebraicGeometry
