/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.HomologicalComplex
public import WeilConjectures.CategoryTheory.SiteCechComplex
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.AlgebraicGeometry.AlternatingCechRestrictionHomotopy

/-!
# The alternating Čech complex computes Čech cohomology

Source: Stacks Project, Cohomology of Sheaves, Section 20.23, Lemma 20.23.5
(Tags 01FJ, 01FK, 01FM) (blueprint: lem-pc-alternating-cech-computes).

The full Čech complex and the complex indexed by strictly increasing tuples are
related by restriction.  The signed extension from increasing tuples and the explicit
repeated-index homotopies of Tags 01FJ, 01FK, and 01FM show that this restriction
induces an isomorphism on every Čech cohomology group.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private def orderedCochains (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :=
  AddCommGrpCat.of
    (∀ t : {t : Fin (p + 1) → I // StrictMono t}, F.obj (op (S.W p t.1)))

private def orderedRestriction (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :
    S.cochains F p ⟶ orderedCochains X U F S p :=
  AddCommGrpCat.ofHom
    { toFun := fun s t ↦ s t.1
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

private noncomputable def orderedDifferential (X : Scheme.{u}) {I : Type v}
    [LinearOrder I] (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :
    orderedCochains X U F S p ⟶ orderedCochains X U F S (p + 1) :=
  AddCommGrpCat.ofHom
    { toFun := fun s t ↦ ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        F.map (S.indexMap t.1 j.succAbove).op
          (s ⟨t.1 ∘ j.succAbove, t.2.comp (Fin.strictMono_succAbove j)⟩)
      map_zero' := by ext t; simp
      map_add' := by intro a b; ext t; simp [map_add, smul_add, Finset.sum_add_distrib] }

private theorem orderedRestriction_comm (X : Scheme.{u}) {I : Type v}
    [LinearOrder I] (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :
    orderedRestriction X U F S p ≫ orderedDifferential X U F S p =
      S.differential F p ≫ orderedRestriction X U F S (p + 1) := by
  rfl

private theorem orderedRestriction_surjective (X : Scheme.{u}) {I : Type v}
    [LinearOrder I] (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :
    Function.Surjective (orderedRestriction X U F S p) := by
  classical
  intro s
  refine ⟨fun t ↦ if h : StrictMono t then s ⟨t, h⟩ else 0, ?_⟩
  funext t
  change (if h : StrictMono t.1 then s ⟨t.1, h⟩ else 0) = s t
  simp [t.2]

private theorem orderedDifferential_squared (X : Scheme.{u}) {I : Type v}
    [LinearOrder I] (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :
    orderedDifferential X U F S p ≫ orderedDifferential X U F S (p + 1) = 0 := by
  have he : Epi (orderedRestriction X U F S p) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (orderedRestriction_surjective X U F S p)
  apply (cancel_epi (orderedRestriction X U F S p)).mp
  rw [← Category.assoc, orderedRestriction_comm, Category.assoc,
    orderedRestriction_comm, ← Category.assoc, S.differential_squared]
  simp

/-- The alternating Čech comparison for a Zariski open covering.

`S` is any choice of the intersections and their restriction maps, as in
`def-weil-pbc-site-cech-complex`. Its product universal properties on the poset
of opens identify `S.W p t` with the intersection of the `U (t i)`.
The simultaneous degree identifications `e` identify `A` with the products
on strictly increasing tuples. The first clause specifies its differential,
the second specifies restriction, and the last says that this very map induces
isomorphisms on cohomology. Nonnegative indexing represents zero negative terms.
Source: Stacks Project, Cohomology of Sheaves, Section 20.23, Definitions
20.23.2 and 20.23.4 and Lemmas 20.23.3, 20.23.5, 20.23.6 (Tags 01FJ, 01FK, 01FM)
(blueprint: lem-pc-alternating-cech-computes).

Proof:
1. The Zariski site is a poset, so permuting intersections preserves their
   restriction maps. Restriction to increasing tuples commutes with the signed
   face sum (Tag 01FK; lemma-uniform-bounds-pro-etale-affines, def-weil-pbc-site-cech-complex).
2. Extend an increasing-tuple cochain by the sign of the sorting permutation
   on distinct tuples and by zero on repeated tuples. Deleting an entry gives
   the same face sign on both sides, so this is a cochain map (Tags 01FJ, 01FK).
   Restriction after extension is the identity.
3. Use the first homotopy of Tag 01FM: for a tuple let `σ` stably sort its
   indices, and let `σ_a` agree with `σ` before `a` and list the remaining
   positions increasingly. Sum over `a` with coefficient `(-1)^a sign(σ_a)`
   the component indexed by `σ(0), ..., σ(a), σ_a(a), ..., σ_a(p)`.
   Adjacent terms cancel, giving `dh + hd = id - κ`, where `κ` is stable
   sorting with its sign. This retracts onto the semi-alternating complex,
   identified by restriction with the nondecreasing-tuple complex.
   On this complex use the second homotopy of Tag 01FM: zero on increasing
   tuples, and otherwise insert a repeat at the first equality in position
   `a`, with sign `(-1)^a`. Adjacent terms cancel, giving zero on increasing
   tuples and the original component otherwise. Extension by zero followed
   by projection is therefore homotopic to the identity. Restriction is a
   homotopy equivalence and its induced homology maps are isomorphisms.
-/
theorem alternatingCechComputes
    (X : Scheme.{u}) {I : Type v} [LinearOrder I] (U : I → X.Opens)
    (hU : iSup U = ⊤)
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) :
    ∃ A : CochainComplex AddCommGrpCat.{max v w} ℕ,
      ∃ e : ∀ p : ℕ, A.X p ≅ AddCommGrpCat.of
        (∀ t : {t : Fin (p + 1) → I // StrictMono t}, F.obj (op (S.W p t.1))),
        ∃ r : S.complex F ⟶ A,
          (∀ (p : ℕ) (s : A.X p)
            (t : {t : Fin (p + 2) → I // StrictMono t}),
            (e (p + 1)).hom ((A.d p (p + 1)) s) t =
              ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
                F.map (S.indexMap t.1 j.succAbove).op
                  ((e p).hom s ⟨t.1 ∘ j.succAbove,
                    t.2.comp (Fin.strictMono_succAbove j)⟩)) ∧
          (∀ (p : ℕ) (s : S.cochains F p)
            (t : {t : Fin (p + 1) → I // StrictMono t}),
            (e p).hom ((r.f p) s) t = s t.1) ∧
          ∀ p : ℕ, IsIso (HomologicalComplex.homologyMap r p) := by
  have _hCover := hU
  let A := CochainComplex.of (orderedCochains X U F S)
    (orderedDifferential X U F S) (orderedDifferential_squared X U F S)
  let e : ∀ p : ℕ, A.X p ≅ orderedCochains X U F S p := fun p ↦ Iso.refl _
  let r : S.complex F ⟶ A := CochainComplex.ofHom
    (orderedRestriction X U F S) (by
      intro p
      simpa only [A, SiteCechComplex.complex, CochainComplex.of_d] using
        orderedRestriction_comm X U F S p)
  have hd : ∀ (p : ℕ) (s : A.X p)
      (t : {t : Fin (p + 2) → I // StrictMono t}),
      (e (p + 1)).hom ((A.d p (p + 1)) s) t =
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
          F.map (S.indexMap t.1 j.succAbove).op
            ((e p).hom s ⟨t.1 ∘ j.succAbove,
              t.2.comp (Fin.strictMono_succAbove j)⟩) := by
    intro p s t
    simp only [A, CochainComplex.of_d]
    rfl
  have hr : ∀ (p : ℕ) (s : S.cochains F p)
      (t : {t : Fin (p + 1) → I // StrictMono t}),
      (e p).hom ((r.f p) s) t = s t.1 := by
    intro p s t
    rfl
  refine ⟨A, e, r, hd, hr, ?_⟩
  obtain ⟨i, hri, hir⟩ := alternatingCechRestrictionHomotopy X U F S A e r hr
  let E : HomotopyEquiv (S.complex F) A := ⟨r, i, hri.some, hir.some⟩
  intro p
  exact (E.toHomologyIso p).isIso_hom

end AlgebraicGeometry.Scheme
