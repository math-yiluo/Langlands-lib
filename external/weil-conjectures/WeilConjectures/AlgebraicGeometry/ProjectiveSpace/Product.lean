/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Zero
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finite products of projective spaces over a base

A finite fibre product `ℙ(n 1; S) ×_S ⋯ ×_S ℙ(n k; S)` of projective spaces over a base scheme
`S` admits a closed immersion into a single projective space `ℙ(N; S)` over `S`. The fibre
product is taken as the categorical product `∏ᶜ fun i ↦ Over.mk (ℙ(n i; S) ↘ S)` in `Over S`,
which exists because `Scheme` has finite limits.

The proof is an induction on the (finite) index type via `Finite.induction_empty_option`: the
empty product is the terminal object `S` of `Over S`, which is `ℙ(PUnit; S)`, and the inductive
step splits off one factor with `CategoryTheory.Limits.piOptionIso` and applies the relative
Segre embedding `AlgebraicGeometry.ProjectiveSpace.segre`. Since the index type of the target
grows by a product at every step, the statement is existential in the target index type; this
is all that Chow's lemma consumes.

## Main declarations

* `AlgebraicGeometry.ProjectiveSpace.segreOver`: the relative Segre morphism read as a morphism
  `ℙ(n; S) ⨯ ℙ(m; S) ⟶ ℙ(n × m; S)` of the binary product in `Over S`.
* `AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_pi`: a finite product of
  projective spaces over `S` admits a closed immersion into some `ℙ(N; S)` over `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

section Binary

variable (n m : Type u) (S : Scheme.{u})

/-- The relative Segre morphism as a morphism in `Over S` out of the binary product of
`ℙ(n; S)` and `ℙ(m; S)` in `Over S`. -/
def segreOver :
    (Over.mk (ℙ(n; S) ↘ S) ⨯ Over.mk (ℙ(m; S) ↘ S) : Over S) ⟶ Over.mk (ℙ(n × m; S) ↘ S) :=
  Over.homMk ((Over.prodLeftIsoPullback _ _).hom ≫ segre n m S) (by
    simp only [Category.assoc, Over.mk_hom, segre_over]
    exact (Over.prodLeftIsoPullback_hom_fst_assoc _ _ _).trans (Over.w prod.fst))

@[simp]
lemma segreOver_left :
    (segreOver n m S).left = (Over.prodLeftIsoPullback _ _).hom ≫ segre n m S :=
  rfl

instance : IsClosedImmersion (segreOver n m S).left := by
  rw [segreOver_left]
  infer_instance

end Binary

variable {ι : Type u} [Finite ι] (n : ι → Type u) [∀ i, Finite (n i)] (S : Scheme.{u})

/-- **A finite fibre product of projective spaces over `S` embeds into a projective space
over `S`**: the product `∏ᶜ fun i ↦ ℙ(n i; S)` in `Over S` admits a closed immersion into
`ℙ(N; S)` for some finite index type `N`, namely the iterated Segre embedding. -/
theorem exists_isClosedImmersion_pi :
    ∃ (N : Type u) (_ : Finite N)
      (g : (∏ᶜ fun i ↦ Over.mk (ℙ(n i; S) ↘ S)) ⟶ Over.mk (ℙ(N; S) ↘ S)),
      IsClosedImmersion g.left := by
  have : IsIso (ℙ(PUnit.{u + 1}; S) ↘ S) := inferInstance
  have hT' : IsTerminal (Over.mk (ℙ(PUnit.{u + 1}; S) ↘ S)) :=
    Over.mkIdTerminal.ofIso (Over.isoMk (asIso (ℙ(PUnit.{u + 1}; S) ↘ S)) (by simp)).symm
  refine Finite.induction_empty_option
    (P := fun ι ↦ ∀ [Finite ι] (n : ι → Type u) [∀ i, Finite (n i)],
      ∃ (N : Type u) (_ : Finite N)
        (g : (∏ᶜ fun i ↦ Over.mk (ℙ(n i; S) ↘ S)) ⟶ Over.mk (ℙ(N; S) ↘ S)),
        IsClosedImmersion g.left)
    ?_ ?_ ?_ ι n
  · intro α β e hα _ n _
    have : Finite α := Finite.of_equiv _ e.symm
    obtain ⟨N, _, g, hg⟩ := hα fun j ↦ n (e j)
    have ee : (∏ᶜ fun j ↦ Over.mk (ℙ(n (e j); S) ↘ S)) ≅ ∏ᶜ fun i ↦ Over.mk (ℙ(n i; S) ↘ S) :=
      Pi.whiskerEquiv (f := fun j ↦ Over.mk (ℙ(n (e j); S) ↘ S))
        (g := fun i ↦ Over.mk (ℙ(n i; S) ↘ S)) e fun _ ↦ Iso.refl _
    refine ⟨N, ‹_›, ee.inv ≫ g, ?_⟩
    have : IsIso (ee.inv.left) := inferInstanceAs (IsIso ((Over.forget S).map _))
    rw [Over.comp_left]
    infer_instance
  · intro _ n _
    have hT : IsTerminal (∏ᶜ fun i ↦ Over.mk (ℙ(n i; S) ↘ S)) :=
      IsTerminal.ofUniqueHom (fun _ ↦ Pi.lift fun i ↦ i.elim)
        fun _ _ ↦ Pi.hom_ext _ _ fun i ↦ i.elim
    refine ⟨PUnit.{u + 1}, inferInstance, (hT.uniqueUpToIso hT').hom, ?_⟩
    have : IsIso ((hT.uniqueUpToIso hT').hom.left) :=
      inferInstanceAs (IsIso ((Over.forget S).map _))
    infer_instance
  · intro α _ hα _ n _
    obtain ⟨N, _, g, hg⟩ := hα fun i ↦ n (some i)
    refine ⟨n none × N, inferInstance,
      (piOptionIso fun i ↦ Over.mk (ℙ(n i; S) ↘ S)).hom ≫
        prod.map (𝟙 (Over.mk (ℙ(n none; S) ↘ S))) g ≫ segreOver (n none) N S, ?_⟩
    have : IsIso ((piOptionIso fun i ↦ Over.mk (ℙ(n i; S) ↘ S)).hom.left) :=
      inferInstanceAs (IsIso ((Over.forget S).map _))
    have : IsClosedImmersion (prod.map (𝟙 (Over.mk (ℙ(n none; S) ↘ S))) g).left :=
      MorphismProperty.left_prod_map_id _ g hg
    rw [Over.comp_left, Over.comp_left]
    infer_instance

/-- A finite fibre product of projective spaces over `S` is proper over `S`. -/
theorem isProper_pi_hom :
    IsProper (∏ᶜ fun i ↦ Over.mk (ℙ(n i; S) ↘ S) : Over S).hom :=
  have (i : ι) : IsProper (Over.mk (ℙ(n i; S) ↘ S)).hom :=
    inferInstanceAs (IsProper (ℙ(n i; S) ↘ S))
  AlgebraicGeometry.isProper_pi_hom _

end AlgebraicGeometry.ProjectiveSpace
