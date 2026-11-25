/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Equalizers

/-!
# Local lifts in a short exact sequence of etale module sheaves

Source: the Weil conjectures blueprint, `sec-proper-base-change/sk-thm-properbasechange`,
`lemma-constructible-flc-serre`, extension paragraph, the assertion that a surjection of
sheaves is locally surjective on sections (blueprint: lem-constructible-shortexact-local-lift).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Every section of the quotient in a short exact sequence of etale sheaves of modules
lifts over an etale covering. The coefficients are the constant ring sheaf of the
commutative ring `Λ` ("ring" in the Stacks sense, as in `def-weil-pbc-etale-sheaves`);
`ULift` only places the ring in the universe of the sheaf values. A covering is encoded by
its generated sieve, equivalently a jointly surjective family by
`ofArrows_mem_smallEtaleTopology_iff`.

Source: blueprint `lemma-constructible-flc-serre`, extension paragraph
(blueprint: lem-constructible-shortexact-local-lift).

Proof: `def-weil-pbc-exact-sequence` makes the quotient map an epimorphism. By
`situation-conventions` (1), forgetting module structure preserves
cokernels, so this is also an epimorphism of abelian sheaves. Apply
`lem-weil-pbc-abelian-sheaf-epi-locally-surjective` to the given section to obtain a covering
and a lift on each member. This only lifts individual sections and requires no splitting
of the sequence. -/
theorem exists_etale_local_lift_of_shortExact (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (S : ShortComplex (SheafOfModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} Λ)))))
    (hS : S.ShortExact) (U : X.Etale) (t : S.X₃.val.obj (op U)) :
    ∃ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U)
      (s : ∀ i : I, S.X₂.val.obj (op (V i))),
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧
        ∀ i : I, S.g.val.app (op (V i)) (s i) = S.X₃.val.map (f i).op t := by
  classical
  let R := (constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
    (RingCat.of (ULift.{u + 1, u} Λ))
  let F := SheafOfModules.toSheaf.{u + 1} R
  have : CategoryTheory.Limits.PreservesFiniteColimits F :=
    SheafOfModules.preservesFiniteColimits_toSheaf R
  have : ∀ {A B : SheafOfModules.{u + 1} R} (f : A ⟶ B),
      CategoryTheory.Limits.PreservesColimit
        (CategoryTheory.Limits.parallelPair f 0) F := fun _ ↦ inferInstance
  have : F.PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels F
  have : Epi S.g := hS.epi_g
  have : Sheaf.IsLocallySurjective (F.map S.g) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} (F.map S.g)).2
      inferInstance
  let T := Presheaf.imageSieve (F.map S.g).hom t
  obtain ⟨I, V, f, hf⟩ := T.exists_eq_ofArrows
  have hmem : T ∈ X.smallEtaleTopology U :=
    Presheaf.imageSieve_mem X.smallEtaleTopology (F.map S.g).hom t
  have hlift (i : I) : ∃ s : S.X₂.val.obj (op (V i)),
      S.g.val.app (op (V i)) s = S.X₃.val.map (f i).op t := by
    exact (show T (f i) from hf.symm ▸ Sieve.ofArrows_mk V f i)
  choose s hs using hlift
  exact ⟨I, V, f, s, hf ▸ hmem, hs⟩

end AlgebraicGeometry.Scheme
