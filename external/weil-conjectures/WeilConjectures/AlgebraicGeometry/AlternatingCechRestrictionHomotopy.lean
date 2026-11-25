/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.AlternatingCechSection
import WeilConjectures.AlgebraicGeometry.AlternatingCechKernelNullHomotopic

/-!
# Homotopy inverse for ordered Čech restriction

Source: Stacks Project, Cohomology of Sheaves, Tags 01FJ, 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A complex whose terms are identified with sections on increasing tuples, and a
cochain map which is restriction in those identifications, has a homotopy inverse.
No covering hypothesis is needed: this is a comparison of complexes for any family
of opens and any presheaf of abelian groups.

Source: Stacks Project, Cohomology of Sheaves, Lemmas 20.23.3, 20.23.4 and 20.23.6,
Tags 01FJ, 01FK and 01FM (blueprint: lem-pc-alternating-cech-restriction-homotopy).

Proof: The chosen products in the poset of opens are canonically the intersections.
Consequently their maps are unchanged under permutations, after transport along the
unique intersection isomorphisms. Extend a section on a strictly increasing tuple to
any tuple with distinct entries by the sign of the sorting permutation, transporting
along that isomorphism, and extend by zero on repeated tuples. The face sign identity
shows this extension commutes with the differential. The differential of `A` has the
usual face formula: lift an arbitrary section through the degreewise-surjective
restriction map and apply its chain-map equation and the displayed restriction formula.
Use `e` to transport the extension into a cochain map `i : A ⟶ S.complex F`.
Restriction after extension is the identity, including in degree zero.

For the other composite use the two homotopies of Tag 01FM. First stably sort a tuple:
let σ be the stable sorting permutation and let σ_a agree with σ before a and list
remaining positions in their original order. Sum the sections on the tuples
σ(0), ..., σ(a), σ_a(a), ..., σ_a(p) with coefficient (-1)^a sign(σ_a), transporting
between equal intersections. The adjacent terms cancel in dh + hd and leave the
identity minus signed stable sorting. This retracts the full complex onto the
semi-alternating complex, which restriction identifies with nondecreasing tuples.
There the second homotopy is zero on increasing tuples; otherwise insert a duplicate
at the first equality in position a, with sign (-1)^a. Adjacent faces cancel and leave
the identity minus extension by zero from increasing tuples. Compose the retractions
and their homotopies: i followed by r is the identity, and r followed by i is homotopic
to the identity on the full complex. The zero homotopy supplies the identity
on the increasing complex. Empty index types give zero complexes, so require no
separate nonemptiness hypothesis. -/
theorem alternatingCechRestrictionHomotopy (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (A : CochainComplex AddCommGrpCat.{max v w} ℕ)
    (e : ∀ p : ℕ, A.X p ≅ AddCommGrpCat.of
      (∀ t : {t : Fin (p + 1) → I // StrictMono t}, F.obj (op (S.W p t.1))))
    (r : S.complex F ⟶ A)
    (hr : ∀ (p : ℕ) (s : S.cochains F p)
      (t : {t : Fin (p + 1) → I // StrictMono t}),
      (e p).hom ((r.f p) s) t = s t.1) :
    ∃ i : A ⟶ S.complex F,
      Nonempty (Homotopy (r ≫ i) (𝟙 (S.complex F))) ∧
      Nonempty (Homotopy (i ≫ r) (𝟙 A)) := by
  obtain ⟨i, hi⟩ := alternatingCechRestrictionHomotopy_map X U F S A e r hr
  have hz : ∀ (p : ℕ) (s : S.cochains F p)
      (t : {t : Fin (p + 1) → I // StrictMono t}),
      (((r ≫ i - 𝟙 (S.complex F)).f p) s) t.1 = 0 := by
    intro p s t
    have heq := congrArg (fun g : A ⟶ A ↦ (e p).hom (g.f p ((r.f p) s))) hi
    have ht := congrFun heq t
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply, hr] at ht
    change ((r ≫ i).f p s) t.1 - s t.1 = 0
    exact sub_eq_zero.mpr ht
  obtain ⟨h⟩ := alternatingCechKernelNullHomotopic X U F S (r ≫ i - 𝟙 _) hz
  exact ⟨i, ⟨⟨Homotopy.equivSubZero.symm h⟩, ⟨Homotopy.ofEq hi⟩⟩⟩

end AlgebraicGeometry.Scheme
