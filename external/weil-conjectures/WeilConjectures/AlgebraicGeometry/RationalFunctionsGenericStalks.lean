/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalFunctions
public import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Rational functions and generic stalks

For a scheme `X` with finitely many irreducible components, taking germs at their generic
points identifies the ring of rational functions on `X` with the product of the generic stalks.

Source: Stacks Project, Morphisms, Lemma 01RV, first and third assertions
(blueprint: def-sc-function-field).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

section GenericPoints

variable {X : Scheme.{u}} {n : ℕ}
  (components : Fin n ≃ {Z : Set X // Z ∈ irreducibleComponents X})

/-- The open complement of all irreducible components other than the `i`-th one. -/
def openAwayFromOtherComponents (i : Fin n) : X.Opens :=
  ⟨(⋃ j ∈ ({i}ᶜ : Set (Fin n)), (components j).val)ᶜ,
    (Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ =>
      isClosed_of_mem_irreducibleComponents _ (components j).2).isOpen_compl⟩

variable {components}

/-- A point away from the other components lies only in the `i`-th component. -/
lemma eq_of_mem_openAwayFromOtherComponents {i j : Fin n} {x : X}
    (hx : x ∈ openAwayFromOtherComponents components i) (hj : x ∈ (components j).val) :
    j = i := by
  by_contra h
  exact hx (Set.mem_biUnion (x := j) h hj)

/-- The irreducible components cover `X`. -/
lemma exists_mem_component (x : X) : ∃ j : Fin n, x ∈ (components j).val := by
  have hx : x ∈ ⋃₀ irreducibleComponents X := by
    rw [sUnion_irreducibleComponents]; trivial
  obtain ⟨Z, hZ, hxZ⟩ := hx
  exact ⟨components.symm ⟨Z, hZ⟩, by simpa using hxZ⟩

variable {η : Fin n → X} (hη : ∀ i : Fin n, IsGenericPoint (η i) (components i).val)
include hη

/-- The generic point of the `i`-th component lies in no other component. -/
lemma mem_openAwayFromOtherComponents (i : Fin n) :
    η i ∈ openAwayFromOtherComponents components i := by
  intro hmem
  obtain ⟨j, hj, hηj⟩ := Set.mem_iUnion₂.mp hmem
  apply hj
  have hle : (components i).val ⊆ (components j).val := by
    rw [← (hη i).def]
    exact (isClosed_of_mem_irreducibleComponents _ (components j).2).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hηj)
  have := (components i).2.eq_of_le (components j).2.1 hle
  exact components.injective (Subtype.ext this.symm)

/-- Every dense open contains the generic points of all irreducible components. -/
lemma mem_of_dense {U : X.Opens} (hU : Dense (U : Set X)) (i : Fin n) : η i ∈ U := by
  obtain ⟨x, hxV, hxU⟩ := hU.inter_open_nonempty _
    (openAwayFromOtherComponents components i).isOpen
    ⟨η i, mem_openAwayFromOtherComponents hη i⟩
  change η i ∈ (U : Set X)
  rw [(hη i).mem_open_set_iff U.isOpen]
  obtain ⟨j, hj⟩ := exists_mem_component (components := components) x
  obtain rfl := eq_of_mem_openAwayFromOtherComponents hxV hj
  exact ⟨x, hj, hxU⟩

/-- An open containing the generic points of all irreducible components is dense. -/
lemma dense_of_forall_mem {W : X.Opens} (hW : ∀ i, η i ∈ W) : Dense (W : Set X) := by
  intro x
  obtain ⟨j, hj⟩ := exists_mem_component (components := components) x
  rw [← (hη j).def] at hj
  exact closure_mono (Set.singleton_subset_iff.mpr (hW j)) hj

end GenericPoints

/-- For a scheme with finitely many irreducible components, every dense open contains their
 generic points, and taking germs identifies rational functions with the product of the generic
 stalks. For an integral scheme there is one component, the whole space, and both the rational
 function ring and the generic stalk are fields. Source: Stacks Project, Lemma 01RV, first and
 third assertions (blueprint: def-sc-function-field). -/
theorem exists_ringEquiv_rationalFunctionRing_pi_stalk (X : Scheme.{u}) (n : ℕ)
    (components : Fin n ≃ {Z : Set X // Z ∈ irreducibleComponents X})
    (η : Fin n → X) (hη : ∀ i : Fin n, IsGenericPoint (η i) (components i).val) :
    ∃ hDense : ∀ (U : DenseOpens X) (i : Fin n), η i ∈ U.val,
      ∃ e : (X.rationalFunctionRing : Type u) ≃+* ((i : Fin n) → X.presheaf.stalk (η i)),
        (∀ (U : DenseOpens X) (f : Γ(X, U.val)) (i : Fin n),
          e ((colimit.ι (denseOpenSections X) (op U)) f) i =
            X.presheaf.germ U.val (η i) (hDense U i) f) ∧
        (IsIntegral X → n = 1 ∧ (∀ i : Fin n, (components i).val = Set.univ) ∧
          IsField (X.rationalFunctionRing : Type u) ∧
          ∀ i : Fin n, IsField (X.presheaf.stalk (η i)) ∧
            ∃ ei : (X.rationalFunctionRing : Type u) ≃+* X.presheaf.stalk (η i),
              ∀ r : X.rationalFunctionRing, ei r = e r i) := by
  have hDense : ∀ (U : DenseOpens X) (i : Fin n), η i ∈ U.val :=
    fun U i => mem_of_dense hη U.2 i
  let c : Cocone (denseOpenSections X) :=
    { pt := CommRingCat.of ((i : Fin n) → X.presheaf.stalk (η i))
      ι :=
        { app := fun U => CommRingCat.ofHom
            (RingHom.pi fun i => (X.presheaf.germ U.unop.val (η i) (hDense U.unop i)).hom)
          naturality := by
            intro U V f
            ext s
            funext i
            exact X.presheaf.germ_res_apply _ _ _ s } }
  let φ : X.rationalFunctionRing ⟶ c.pt := colimit.desc _ c
  have hφ : ∀ (U : DenseOpens X) (f : Γ(X, U.val)) (i : Fin n),
      φ ((colimit.ι (denseOpenSections X) (op U)) f) i =
        X.presheaf.germ U.val (η i) (hDense U i) f := by
    intro U f i
    exact congrFun (ConcreteCategory.congr_hom (colimit.ι_desc c (op U)) f) i
  have hinj : Function.Injective φ := by
    have key : ∀ (U : DenseOpens X) (f : Γ(X, U.val)),
        φ (colimit.ι (denseOpenSections X) (op U) f) = 0 →
          colimit.ι (denseOpenSections X) (op U) f = 0 := by
      intro U f hr
      have hW : ∀ i, ∃ (W : X.Opens) (_ : η i ∈ W) (iW : W ⟶ U.val),
          X.presheaf.map iW.op f = 0 := by
        intro i
        have h0 : X.presheaf.germ U.val (η i) (hDense U i) f =
            X.presheaf.germ U.val (η i) (hDense U i) 0 := by
          rw [map_zero, ← hφ U f i]
          exact congrFun hr i
        obtain ⟨W, hW, iU, iV, h⟩ := X.presheaf.germ_eq _ _ _ f 0 h0
        exact ⟨W, hW, iU, by rw [h, map_zero]⟩
      choose W hW iW hf using hW
      let W' : DenseOpens X :=
        ⟨⨆ i, W i, dense_of_forall_mem hη fun i => Opens.mem_iSup.mpr ⟨i, hW i⟩⟩
      have hle : W'.val ≤ U.val := iSup_le fun i => (iW i).le
      have hres : X.presheaf.map (homOfLE hle).op f = 0 := by
        refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf W W'.val (fun i => Opens.leSupr W i)
          le_rfl _ _ fun i => ?_
        change X.presheaf.map (Opens.leSupr W i).op (X.presheaf.map (homOfLE hle).op f) =
          X.presheaf.map (Opens.leSupr W i).op 0
        rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact hf i
      have hUW : W' ⟶ U := homOfLE hle
      rw [← colimit.w_apply (denseOpenSections X) hUW.op f]
      change (colimit.ι (denseOpenSections X) (op W')) (X.presheaf.map (homOfLE hle).op f) = 0
      rw [hres]
      exact map_zero _
    rw [injective_iff_map_eq_zero φ.hom]
    intro r hr
    obtain ⟨⟨U⟩, f, rfl⟩ := Concrete.colimit_exists_rep (denseOpenSections X) r
    exact key U f hr
  have hsurj : Function.Surjective φ := by
    intro g
    choose W hW s hs using fun i => X.presheaf.exists_germ_eq (g i)
    let W' : Fin n → X.Opens := fun i => W i ⊓ openAwayFromOtherComponents components i
    have hW' : ∀ i, η i ∈ W' i := fun i => ⟨hW i, mem_openAwayFromOtherComponents hη i⟩
    let s' : ∀ i, Γ(X, W' i) := fun i => X.presheaf.map (homOfLE inf_le_left).op (s i)
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 W' s' := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rfl
      · have hbot : W' i ⊓ W' j = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          obtain ⟨k, hk⟩ := exists_mem_component (components := components) x
          exact absurd ((eq_of_mem_openAwayFromOtherComponents hx.1.2 hk).symm.trans
            (eq_of_mem_openAwayFromOtherComponents hx.2.2 hk)) hij
        have := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
        exact Subsingleton.elim _ _
    obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing W' s' hcompat
    let V : DenseOpens X :=
      ⟨⨆ i, W' i, dense_of_forall_mem hη fun i => Opens.mem_iSup.mpr ⟨i, hW' i⟩⟩
    refine ⟨colimit.ι (denseOpenSections X) (op V) t, funext fun i => ?_⟩
    refine (hφ V t i).trans ?_
    rw [← X.presheaf.germ_res_apply (Opens.leSupr W' i) (η i) (hW' i) t]
    rw [show X.presheaf.map (Opens.leSupr W' i).op t = s' i from ht i]
    rw [X.presheaf.germ_res_apply, hs]
  let e := RingEquiv.ofBijective φ.hom ⟨hinj, hsurj⟩
  refine ⟨hDense, e, fun U f i => hφ U f i, fun hX => ?_⟩
  have huniv : ∀ i, (components i).val = Set.univ := fun i =>
    (components i).2.eq_of_le (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _)
  have hn : n = 1 := by
    have hmem : (Set.univ : Set X) ∈ irreducibleComponents X :=
      ⟨IrreducibleSpace.isIrreducible_univ X, fun _ _ _ => Set.subset_univ _⟩
    have h0 : 0 < n := Fin.pos (components.symm ⟨_, hmem⟩)
    have h1 : n ≤ 1 := by
      by_contra h
      have := components.injective (a₁ := ⟨0, by omega⟩) (a₂ := ⟨1, by omega⟩)
        (Subtype.ext ((huniv _).trans (huniv _).symm))
      simp at this
    omega
  have hgen : ∀ i, η i = genericPoint X := fun i =>
    (hη i).eq (by simpa [huniv i] using genericPoint_spec X)
  have hstalk : ∀ i, IsField (X.presheaf.stalk (η i)) := fun i => by
    rw [hgen i]
    exact Field.toIsField X.functionField
  have hsub : ∀ j k : Fin n, j = k := by
    subst hn
    exact Subsingleton.elim
  have hpi : ∀ i : Fin n, ∃ ei : (X.rationalFunctionRing : Type u) ≃+* X.presheaf.stalk (η i),
      ∀ r : X.rationalFunctionRing, ei r = e r i := fun i =>
    let _ : Unique (Fin n) := ⟨⟨i⟩, fun j => hsub j i⟩
    ⟨e.trans (RingEquiv.piUnique _), fun _ => rfl⟩
  obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨ei, -⟩ := hpi i
  exact ⟨hn, huniv, MulEquiv.isField (hstalk i) ei.toMulEquiv, fun i => ⟨hstalk i, hpi i⟩⟩

end AlgebraicGeometry.Scheme
