/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.RingTheory.StrictHenselizationDimension

/-!
# The strict localization of a smooth surface at a rational point

Let `S` be a smooth surface over an algebraically closed field `k` and `t` a `k`-point of `S`,
with strict localization `T = Spec R`, `R = 𝒪^{sh}_{S,t}`. Then `R` is a regular local ring of
dimension `2` with residue field `k`.

## Main definitions

- `AlgebraicGeometry.Scheme.strictHenselizationAlgebra`: the `k`-algebra structure on `R`.

## Main results

- `AlgebraicGeometry.Scheme.isRegularLocalRing_strictHenselization_of_smooth`: `R` is regular.
- `AlgebraicGeometry.Scheme.ringKrullDim_strictHenselization_of_smooth`: `R` has dimension `2`.
- `AlgebraicGeometry.Scheme.bijective_residue_algebraMap_strictHenselization`: `k ≅ R/𝔪`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Over (Spec (.of k)))
  (t : Spec (.of k) ⟶ S.left)

/-- The `k`-algebra structure of the strict henselization `R = 𝒪^{sh}_{S,t}` of a `k`-scheme `S`,
from the structure morphism `Spec R ⟶ S ⟶ Spec k`. -/
@[instance_reducible]
noncomputable def strictHenselizationAlgebra : Algebra k (strictHenselization t) :=
  (Spec.preimage (strictLocalizationToBase t ≫ S.hom)).hom.toAlgebra

/-- The residue field of the strict henselization of a `k`-scheme at a `k`-point is `k`: the
evaluation `R ⟶ k` at the geometric point retracts `k ⟶ R` (as `t` is a section of `S ⟶ Spec k`)
and factors through the residue field `R/𝔪`, which it embeds into `k`. -/
theorem bijective_residue_algebraMap_strictHenselization (ht : t ≫ S.hom = 𝟙 _) :
    letI := strictHenselizationAlgebra S t
    Function.Bijective (IsLocalRing.residue (strictHenselization t) ∘
      algebraMap k (strictHenselization t)) := by
  let := strictHenselizationAlgebra S t
  have hφ : Spec.preimage (strictLocalizationToBase t ≫ S.hom) ≫ strictHenselizationEval t =
      𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc,
      spec_map_strictHenselizationEval_comp_strictLocalizationToBase, ht, Spec.map_id]
  have heval (c : k) : strictHenselizationEval t (algebraMap k (strictHenselization t) c) = c :=
    congrArg (fun f ↦ f.hom c) hφ
  have hcomp (c : k) : strictHenselizationResidueFieldEmb t
      (IsLocalRing.residue _ (algebraMap k (strictHenselization t) c)) = c := by
    rw [strictHenselizationResidueFieldEmb_residue, heval]
  refine ⟨fun a b h ↦ ?_, fun y ↦ ⟨strictHenselizationResidueFieldEmb t y,
    (strictHenselizationResidueFieldEmb t).injective (hcomp _)⟩⟩
  simpa only [Function.comp_apply, hcomp] using
    congrArg (strictHenselizationResidueFieldEmb t) h

variable [SmoothOfRelativeDimension 2 S.hom]

/-- The strict henselization of a smooth surface at a `k`-point is a regular local ring of
dimension `2`. In an affine chart `Spec A` around the image `x` of `t`, it is an algebraic strict
henselization of `A_x ≅ 𝒪_{S,x}` (`strictHenselization_chart_isStrictHenselization`), which is a
regular local ring (`S` is smooth over `k`) of dimension `2` (`x` is a closed point of the
smooth surface `S`); both properties pass to strict henselizations. -/
theorem isRegularLocalRing_and_ringKrullDim_strictHenselization_of_smooth
    (ht : t ≫ S.hom = 𝟙 _) :
    IsRegularLocalRing (strictHenselization t) ∧ ringKrullDim (strictHenselization t) = 2 := by
  have : Smooth S.hom := SmoothOfRelativeDimension.smooth 2 S.hom
  have hrange : Set.range t = {t (closedPoint k)} := by
    ext z
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨p, hp⟩ ↦ hp ▸ congrArg _ (Subsingleton.elim p _), fun hz ↦ ⟨_, hz.symm⟩⟩
  have hx : IsClosed ({t (closedPoint k)} : Set S.left) := by
    have := isClosedImmersion_of_comp_eq_id S.hom t ht
    rw [← hrange]
    exact t.isClosedEmbedding.isClosed_range
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := t (closedPoint k)) trivial
  have hsub : Set.range t ⊆ Set.range hU.fromSpec := by
    rw [hrange, hU.range_fromSpec, Set.singleton_subset_iff]
    exact hxU
  obtain ⟨xR, rfl⟩ : ∃ xR, t = xR ≫ hU.fromSpec :=
    ⟨IsOpenImmersion.lift _ t hsub, (IsOpenImmersion.lift_fac _ _ _).symm⟩
  obtain ⟨q, _, K, _, _, _, _, _, _, b, rfl, -, -, hH⟩ :=
    strictHenselization_chart_isStrictHenselization Γ(S.left, U) hU.fromSpec xR
  set P := xR (closedPoint k)
  have hP : hU.fromSpec P ∈ U := hxU
  let := S.left.presheaf.algebra_section_stalk ⟨_, hP⟩
  have := hU.isLocalization_stalk' P hP
  let e := (IsLocalization.algEquiv P.asIdeal.primeCompl
    (S.left.presheaf.stalk (hU.fromSpec P)) (Localization.AtPrime P.asIdeal)).toRingEquiv
  have := Smooth.isRegularLocalRing_stalk S.hom (hU.fromSpec P)
  have hreg : IsRegularLocalRing (Localization.AtPrime P.asIdeal) := .of_ringEquiv e
  refine ⟨(Algebra.isRegularLocalRing_iff_strictHenselization _ K _ hH).mp hreg, ?_⟩
  rw [← Algebra.ringKrullDim_eq_of_isStrictHenselization _ K _ hH,
    ← ringKrullDim_eq_of_ringEquiv e, ringKrullDim_stalk_eq_coheight,
    coheight_eq_of_smoothOfRelativeDimension_of_isClosed S.hom 2 (x := hU.fromSpec P) hx]
  rfl

/-- The strict henselization of a smooth surface at a `k`-point is a regular local ring. -/
theorem isRegularLocalRing_strictHenselization_of_smooth (ht : t ≫ S.hom = 𝟙 _) :
    IsRegularLocalRing (strictHenselization t) :=
  (isRegularLocalRing_and_ringKrullDim_strictHenselization_of_smooth S t ht).1

/-- The strict henselization of a smooth surface at a `k`-point has dimension `2`. -/
theorem ringKrullDim_strictHenselization_of_smooth (ht : t ≫ S.hom = 𝟙 _) :
    ringKrullDim (strictHenselization t) = 2 :=
  (isRegularLocalRing_and_ringKrullDim_strictHenselization_of_smooth S t ht).2

end AlgebraicGeometry.Scheme
