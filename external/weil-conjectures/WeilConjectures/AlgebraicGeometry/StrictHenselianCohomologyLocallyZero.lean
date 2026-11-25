/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.StrictHenselianStalkSectionsEpi
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Positive étale cohomology classes are Zariski locally zero

Source: Stacks Project, Étale Cohomology, Tag 09AX, proof, Tags 03Q6 and 03QO.
(blueprint: lem-weil-pbc-strict-henselian-cohomology-locally-zero)
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

private theorem forget_preserves_small_filtered_colimits
    {J : Type v} [SmallCategory J] [IsFiltered J] [UnivLE.{v, w}]
    (D : J ⥤ AddCommGrpCat.{w}) : PreservesColimit D (forget AddCommGrpCat.{w}) := by
  have : PreservesFilteredColimitsOfSize.{v, v} (forget AddCommGrpCat.{w}) :=
    preservesFilteredColimitsOfSize_of_univLE _
  infer_instance

/-- Every positive-degree class on an open becomes zero near each point when all
local rings are strictly henselian.

Source: literature/stacks-project/etale-cohomology.tex, Tag 09AX, proof,
third and fourth sentences; Tags 03Q6 and 03QO.
(blueprint: lem-weil-pbc-strict-henselian-cohomology-locally-zero)

Proof: Compare the filtered colimit of object cohomology over neighbourhoods
of x with homology of stalkwise sections of an injective resolution, using
etaleObjectCohomology_stalk_complex. This comparison holds for arbitrary i,
without any henselian hypothesis. Apply strictHenselian_stalkSections_preservesEpimorphisms
at x to see that the section functor preserves epimorphisms. It preserves
finite limits already, since sheaf inclusion, restriction of presheaves and
filtered colimits of abelian groups do so. It therefore preserves homology.
The resolution is exact in degree n+1, so
its image has zero homology there. The comparison makes the colimit a
subsingleton. The class xi and zero consequently have the same coprojection.
The forgetful functor preserves filtered colimits at the neighbourhood
universe; the elementwise equality criterion supplies a later neighbourhood
V with a transition map from U killing xi. That map is the opposite of the
inclusion V into U, so V is contained in U and contains x. Remove the universe
lift from the equality to obtain exactly the required restriction equality.
The empty open has no x, and q=0 is excluded. No data-valued definition chooses
an injective resolution or an equivalence: the existential comparison theorem
is eliminated only within this proof. -/
theorem strictHenselian_cohomology_locally_zero
    {X : Scheme.{u + 1}}
    (hX : ∀ x : X, IsStrictlyHenselianLocalRing (X.presheaf.stalk x))
    (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (hq : 0 < q) (U : X.Opens)
    (ξ : (i.op ⋙ Sheaf.cohomologyPresheaf F q).obj (op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      (i.op ⋙ Sheaf.cohomologyPresheaf F q).map (homOfLE hVU).op ξ = 0 := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  obtain ⟨I, ⟨e⟩⟩ := etaleObjectCohomology_stalk_complex i F (n + 1) x
  have : PreservesFiniteLimits (etaleObjectStalkSections X i x) := inferInstance
  let E := etaleObjectStalkSections X i x
  have : E.PreservesEpimorphisms :=
    strictHenselian_stalkSections_preservesEpimorphisms i hi_inclusion x (hX x)
  have : E.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels E
  have hz : IsZero (((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology
      (n + 1)) :=
    (E.map_isZero (I.cocomplex_exactAt_succ n).isZero_homology).of_iso
      ((I.cocomplex.sc (n + 1)).mapHomologyIso E)
  let D : (OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x)ᵒᵖ ⥤
      AddCommGrpCat :=
    ((OpenNhds.inclusion (X := X.toLocallyRingedSpace.toTopCat) x) ⋙ i).op ⋙
    Sheaf.cohomologyPresheaf F (n + 1) ⋙ AddCommGrpCat.uliftFunctor.{u + 2}
  let A : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x := ⟨U, hx⟩
  have hs := AddCommGrpCat.subsingleton_of_isZero hz
  have hzero : colimit.ι D (op A) (ULift.up ξ) = colimit.ι D (op A) 0 := by
    apply e.injective
    exact hs.allEq _ _
  have : PreservesColimit D (forget AddCommGrpCat) :=
    forget_preserves_small_filtered_colimits D
  obtain ⟨V, f, _, hf⟩ :=
    Concrete.isColimit_exists_of_rep_eq D (i := op A) (j := op A)
      (colimit.isColimit D) (ULift.up ξ) 0 hzero
  refine ⟨V.unop.1, f.unop.le, V.unop.2, ?_⟩
  rw [map_zero] at hf
  change ULift.up ((i.op ⋙ Sheaf.cohomologyPresheaf F (n + 1)).map
    ((OpenNhds.inclusion x).map f.unop).op ξ) = 0 at hf
  have hh := congrArg ULift.down hf
  exact hh
