/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Basic.UnivLE

/-! # A universe bound from a nonzero etale module-sheaf section

Source: the sheaf condition (Stacks Project, Sites, Definition 00VR), applied to
scheme disjoint unions (Schemes, Section 01JA). The size argument is written by S1.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A nonzero section forces the scheme universe to be small in the section universe.
Source: Stacks Project, Sites, Definition 00VR (sheaf condition), and Schemes,
Section 01JA (gluing schemes, including disjoint unions); size argument written by S1.
(blueprint: lem-weil-pbc-etale-module-sheaf-nonzero-section-universe).

Proof: For each type A in the scheme universe, form the disjoint union V of A copies
of U, with its etale structure map to X. The summand inclusions form an etale cover.
Put E = F(U). For each a in A, prescribe maps E -> E that are the identity on summand a
and zero on every other summand. On two distinct summands a common source is empty,
so its section module is terminal; on the same summand the two restriction arrows
are equal since the inclusion is a monomorphism. Thus the family is compatible.
The module-valued sheaf condition glues it to a map t(a) : E -> F(V). If t(a) = t(b)
with a != b, restriction to summand a gives id_E = 0. Applying this equality to s
contradicts s != 0. Hence A embeds in the type of module maps E -> F(V), which lies
in the section universe. This proves Small A for every A, namely UnivLE.
The empty indexing type causes no problem: the same argument supplies its unique
empty injection. Empty U and the zero coefficient ring cannot have the required
nonzero section. No products in the module category or bounds on A are assumed. -/
theorem etale_module_sheaf_section_univLE (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (U : X.Etale) (s : F.obj.obj (op U)) (hs : s ≠ 0) : UnivLE.{u, max v w} := by
  classical
  constructor
  intro A
  let T : A → Scheme.{u} := fun _ ↦ U.left
  let f : ∀ a : A, T a ⟶ X := fun _ ↦ U.hom
  let : Etale (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ ↦ U.prop)
  let V : X.Etale := Scheme.Etale.mk (Sigma.desc f)
  let q (a : A) : U ⟶ V := MorphismProperty.Over.homMk (Sigma.ι T a)
  have hq : Sieve.ofArrows (fun _ : A ↦ U) q ∈ X.smallEtaleTopology V := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff q).mpr
    exact (sigmaOpenCover T).iUnion_range
  let E := F.obj.obj (op U)
  let x (a b : A) : E ⟶ E := if b = a then 𝟙 E else 0
  have hx (a : A) {W : X.Etale} {b b' : A} (f : W ⟶ U) (g : W ⟶ U)
      (hfg : f ≫ q b = g ≫ q b') : x a b ≫ F.obj.map f.op = x a b' ≫ F.obj.map g.op := by
    by_cases hbb : b = b'
    · subst b'
      have he : f = g := by
        apply MorphismProperty.Over.Hom.ext
        apply (cancel_mono (Sigma.ι T b)).mp
        exact congrArg (fun t ↦ t.left) hfg
      rw [he]
    · have : IsEmpty W.left :=
        isEmpty_of_commSq_sigmaι_of_ne
          (g := T) ⟨congrArg (fun t ↦ t.left) hfg⟩ hbb
      exact (Scheme.Etale.isTerminalSectionsOfIsEmpty F W).hom_ext _ _
  let t (a : A) : E ⟶ F.obj.obj (op V) :=
    F.property.amalgamateOfArrows q hq (x a) (@hx a)
  apply small_of_injective.{max v w, max v w, u} (f := t)
  intro a b hab
  by_contra hne
  have h := congrArg (fun k ↦ k ≫ F.obj.map (q a).op) hab
  have ha : t a ≫ F.obj.map (q a).op = 𝟙 E := by
    simpa only [x, ite_eq_left rfl] using F.property.amalgamateOfArrows_map q hq (x a) (@hx a) a
  have hb : t b ≫ F.obj.map (q a).op = 0 := by
    simpa only [x, ite_eq_right hne] using F.property.amalgamateOfArrows_map q hq (x b) (@hx b) a
  rw [ha, hb] at h
  apply hs
  exact ConcreteCategory.congr_hom h s

end AlgebraicGeometry
