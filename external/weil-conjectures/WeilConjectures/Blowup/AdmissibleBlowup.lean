/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Principalization
public import WeilConjectures.Blowup.Proper
public import WeilConjectures.Blowup.BlowupUniversal
public import WeilConjectures.Blowup.FiniteDegree
public import WeilConjectures.Compactification.FiniteTypeExtension
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!

# Admissible blow-ups and boundary separation

This file records the admissible blow-up vocabulary and the boundary-separation
interface of the proof of Nagata's compactification theorem, following the revised
blueprint (`blueprint/src/version/detailed/nagata/nagata_new.tex`). The two-open
compactification theorem reaches its target by the boundary-separation route rather
than by module flattening: it uses blow-ups of sums of ideals to separate boundary
pieces (Stacks Tag 0F3V), common modifications, and the dense-source valuative
criterion. Module flattening (Stacks Tags 0815/081R and 081P/081L) is not on the
formalized route at all: it is the Stacks Project's proof of Tag 081S, but that chain
bottoms out in the dévissage sections of Stacks §§38.4–38.10, which exist neither in
Mathlib nor in the blueprint. Tag 081S — which lives in
`WeilConjectures.Compactification.EliminationOfIndeterminacy` — is formalized instead via Conrad's
Theorem 2.4 and Zariski's Main Theorem (`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`,
together with Stacks Tag 04II, already available as
`exists_immersion_affineSpace_of_quasiAffine`). Hence no flattening statements appear
in this file.

## Definitions

- `AlgebraicGeometry.IsAdmissible`: a `U`-admissible blow-up center: a finite-type
  quasi-coherent ideal whose support is disjoint from `U`; the associated
  `U`-admissible blow-up is the blow-up of that ideal
  (blueprint: `def:nagata-admissible-blowup`);
- `AlgebraicGeometry.separationBlowup`: the boundary-separation blow-up of the sum of
  two center ideals (revised blueprint: `def:nagata-separate-closed-subschemes`).

The finite-typeness predicate `Scheme.IdealSheafData.ofFiniteType` is provided by
`WeilConjectures.Compactification.FiniteTypeExtension`, the invertibility predicate
`Scheme.IdealSheafData.IsInvertible` by
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`, and the
principalization theorem `Scheme.IdealSheafData.isInvertible_comap_blowupMap`
(blueprint: `thm:nagata-blowup-principalizes-center`) by
`WeilConjectures.Blowup.Principalization`.

## Proved results

- `AlgebraicGeometry.IsAdmissible.isIso_blowupMap_restrict`: a `U`-admissible blow-up
  is an isomorphism over `U` (blueprint: `lemma:nagata-admissible-blowup-over-open`);
- `AlgebraicGeometry.exists_admissibleBlowup_cartierBoundary` and its fully proved
  locally Noetherian instance
  `exists_admissibleBlowup_cartierBoundary_of_isLocallyNoetherian`: preparation of a
  Cartier boundary (`lemma:nagata-cartier-boundary-preparation`, Stacks Tag 080Y);
- `AlgebraicGeometry.separationBlowup` together with its `U`-admissibility
  (`Scheme.IdealSheafData.coe_support_sup` of
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic`);
- `Scheme.exists_finiteType_ideal_coe_support_eq_compl`: a quasi-compact open of a
  qcqs scheme is the complement of the support of a finite-type ideal
  (`def:nagata-qc-open-complement-ideal`, Stacks Tag 01PH), by applying the gluing
  induction `Scheme.IdealSheafData.exists_finiteType_le_comap_eq` of
  `WeilConjectures.Compactification.FiniteTypeExtension` (Stacks Tag 01PF) inside the
  vanishing ideal of the reduced boundary;
- `IsAdmissible.exists_comp`: a composite of admissible blow-ups is an admissible
  blow-up (`lemma:nagata-admissible-blowup-comp`, Stacks Tag 080L), derived — via the
  image/preimage disjointness of the composite center — from the composition theorem
  for arbitrary blow-ups `Scheme.IdealSheafData.exists_blowup_comp` below;
- `Scheme.IdealSheafData.exists_blowup_comp_base_change`: the composition theorem for
  arbitrary blow-ups (`thm:nagata-composition-of-blowups`, Stacks Tag 080B), in
  existential interface form and compatibly with an arbitrary base change `f : Y ⟶ X`.
  The composite center is `K = I * L` for the finite-degree descent `L` of the second
  center; finite-typeness, the support formula and the comparison of blow-ups (product
  comparison, then removal of the effective Cartier exceptional factor `(I.comap π)^d`
  of `L.comap π`) are assembled here from the finite-degree descent and the two
  universal-property comparisons below. Its base-change-free part is
  `Scheme.IdealSheafData.exists_blowup_comp`;
- `Scheme.IdealSheafData.exists_blowup_mul_iso`: the product-ideal comparison
  `Bl_{I·L}(X) ≅ Bl_{L·O}(Bl_I X)` over `X` (`thm:nagata-blowup-product-ideal`,
  Stacks Tag 080A), and
  `Scheme.IdealSheafData.exists_blowup_mul_isInvertible_iso`: multiplying a
  center by an invertible ideal does not change the blow-up
  (`lemma:nagata-blowup-invertible-factor`, Stacks Tag 0807); both are proved from
  the universal property of blowing up (Tag 0806) and the invertibility kit of
  `WeilConjectures.Blowup.BlowupUniversal`;
- `disjoint_range_strictTransformMap_sup`: disjointness of
  strict transforms after blowing up a sum of ideals
  (`lemma:nagata-separate-closed-subschemes`, Stacks Tag 0F3V), by the chart-level
  argument of the revised blueprint: the charts of `Bl_{I₁ ⊔ I₂}` at degree-one
  elements coming from local sections of `I₁` or `I₂` cover the blow-up
  (`Scheme.IdealSheafData.exists_mem_range_chart_sup`), and the strict transform of
  `V(Iᵢ)` misses every `Iᵢ`-chart because there the extended center is generated by a
  section of `Iᵢ` (`disjoint_range_strictTransformMap_of_probe`); the
  quasi-compactness inputs are `AffineBlowup.compactSpace_of_fg`,
  `Scheme.IdealSheafData.quasiCompact_blowupMap` and
  `Scheme.IdealSheafData.isCompact_coe_compl_support`.

## Further inputs (Stacks citations of the revised blueprint)

The finite-degree approximation on the blow-up itself
(`Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup`, Stacks Tag 0803,
`lemma:nagata-proj-closed-center-finite-degree-exists`) is proved in
`WeilConjectures.Blowup.FiniteDegree`; the support formula of the full finite-degree
statement (`coe_support_eq_of_comap_pow_mul`) is proved here.

The universal property of blowing up (Stacks Tag 0806) and the invertibility
kit (`exists_lift_blowup`, `hom_ext_of_isInvertible_comap`,
`IsInvertible.mul`/`of_mul_left`/`of_mul_right`/`comap_blowupMap`) are provided
by `WeilConjectures.Blowup.BlowupUniversal`.

The affine-chart algebra of module strict transforms (Stacks Tag 080W) is provided by
the power-torsion API of `WeilConjectures.Mathlib.Algebra.Module.Torsion`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (U : X.Opens)

/-- A `U`-admissible blow-up center on `X`; the associated `U`-admissible blow-up is the
blow-up `I.blowup` of the center, with structure morphism `I.blowupMap`.
(Blueprint: `def:nagata-admissible-blowup`.) -/
structure IsAdmissible where
  /-- The center ideal of the blow-up. -/
  I : X.IdealSheafData
  /-- The center is a finite-type ideal sheaf. -/
  finiteType : I.ofFiniteType
  /-- The center is disjoint from the preserved open `U`; equivalently `I` restricts to
  the unit ideal on `U`. -/
  disjoint_support : Disjoint (U : Set X) (I.support : Set X)

namespace IsAdmissible

variable {X U} (B : IsAdmissible X U)

/-- The complement of the center of an admissible blow-up, i.e. the open locus over
which the blow-up is tautologically an isomorphism. The preserved open `U` is contained
in it (`AdmissibleBlowup.le_preservedOpen`). -/
abbrev preservedOpen : X.Opens := B.I.support.compl

lemma le_preservedOpen : U ≤ B.preservedOpen := by
  intro x hx
  exact Set.disjoint_left.mp B.disjoint_support hx

/-- **A `U`-admissible blow-up is proper**: the properness of the blow-up of the
center (`Scheme.IdealSheafData.isProper_blowupMap`, blueprint
`thm:nagata-global-blowup-proper`), the finite-typeness input being supplied by
admissibility. -/
theorem isProper_blowupMap : IsProper B.I.blowupMap :=
  B.I.isProper_blowupMap fun U ↦ B.finiteType U le_top

/-- A `U`-admissible blow-up is an isomorphism over `U`: the blow-up complement
theorem (`thm:nagata-global-blowup-complement`) applied to the disjointness of the
center from `U`.
(Blueprint: `lemma:nagata-admissible-blowup-over-open`.) -/
theorem isIso_blowupMap_restrict : IsIso (B.I.blowupMap ∣_ U) :=
  B.I.isIso_blowupMap_restrict B.disjoint_support

/-- **The support of a finite-degree center** (the support computation in the proofs of
Stacks Project Tags 0803/080B): if `L ≤ I^d` (`d ≥ 1`) is an ideal sheaf whose inverse
image on the blow-up of `I` is `I_E^d · J`, then the support of `L` is
`supp I ∪ π(supp J)`. Indeed `L ≤ I^d` forces `supp I ⊆ supp L`; the support of the
inverse image ideal is `π⁻¹(supp I) ∪ supp J`, which gives `π(supp J) ⊆ supp L`; and
away from `supp I` the blow-up is an isomorphism, under which `L` cuts out exactly
`supp J`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.coe_support_eq_of_comap_pow_mul
    {X : Scheme.{u}} (I : X.IdealSheafData) (J : I.blowup.IdealSheafData) {d : ℕ}
    (hd : d ≠ 0) {L : X.IdealSheafData} (hle : L ≤ I ^ d)
    (hcomap : L.comap I.blowupMap = (I.comap I.blowupMap) ^ d * J) :
    (L.support : Set X) =
      (I.support : Set X) ∪ I.blowupMap '' (J.support : Set I.blowup) := by
  set U₀ : X.Opens := I.support.compl with hU₀def
  set π := I.blowupMap with hπdef
  -- the blow-up is an isomorphism over the complement of the support of `I`
  have hiso : IsIso (π ∣_ U₀) :=
    I.isIso_blowupMap_restrict (by rw [hU₀def]; simpa using disjoint_compl_left)
  -- the support identity upstairs
  have hsupp₁ : (π ⁻¹' (L.support : Set X) : Set I.blowup) =
      π ⁻¹' (I.support : Set X) ∪ (J.support : Set I.blowup) := by
    have h1 : ((L.comap π).support : Set I.blowup) = π ⁻¹' (L.support : Set X) := by
      rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    have h2 : ((((I.comap π) ^ d) * J).support : Set I.blowup) =
        π ⁻¹' (I.support : Set X) ∪ (J.support : Set I.blowup) := by
      rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup,
        Scheme.IdealSheafData.support_pow _ _ hd, Scheme.IdealSheafData.support_comap,
        TopologicalSpace.Closeds.coe_preimage]
    rw [← h1, hcomap, h2]
  refine subset_antisymm ?_ ?_
  · -- `supp L ⊆ supp I ∪ π(supp J)`
    intro z hz
    by_cases hzI : z ∈ (I.support : Set X)
    · exact Or.inl hzI
    refine Or.inr ?_
    -- lift `z` through the isomorphism over the complement of `supp I`
    obtain ⟨z', rfl⟩ : z ∈ Set.range U₀.ι := by
      rw [Scheme.Opens.range_ι, hU₀def]
      exact hzI
    have hstep : (π ∣_ U₀) (inv (π ∣_ U₀) z') = z' := by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    have hπx₁ : π ((π ⁻¹ᵁ U₀).ι (inv (π ∣_ U₀) z')) = U₀.ι z' := by
      calc π ((π ⁻¹ᵁ U₀).ι (inv (π ∣_ U₀) z'))
          = ((π ⁻¹ᵁ U₀).ι ≫ π) (inv (π ∣_ U₀) z') := (Scheme.Hom.comp_apply _ _ _).symm
        _ = ((π ∣_ U₀) ≫ U₀.ι) (inv (π ∣_ U₀) z') := by rw [morphismRestrict_ι]
        _ = U₀.ι ((π ∣_ U₀) (inv (π ∣_ U₀) z')) := Scheme.Hom.comp_apply _ _ _
        _ = U₀.ι z' := by rw [hstep]
    have hx₁L : (π ⁻¹ᵁ U₀).ι (inv (π ∣_ U₀) z') ∈ π ⁻¹' (L.support : Set X) := by
      rw [Set.mem_preimage, hπx₁]
      exact hz
    rw [hsupp₁] at hx₁L
    rcases hx₁L with hx₁I | hx₁J
    · exact absurd (by rw [← hπx₁]; exact hx₁I) hzI
    · exact ⟨(π ⁻¹ᵁ U₀).ι (inv (π ∣_ U₀) z'), hx₁J, hπx₁⟩
  · -- `supp I ∪ π(supp J) ⊆ supp L`
    rintro z (hzI | ⟨x₁, hx₁, rfl⟩)
    · have h1 : ((I ^ d).support : Set X) ⊆ (L.support : Set X) :=
        Scheme.IdealSheafData.support_antitone hle
      have h2 : (I ^ d).support = I.support := Scheme.IdealSheafData.support_pow I d hd
      exact h1 (h2 ▸ hzI)
    · have hmem : x₁ ∈ π ⁻¹' (L.support : Set X) := by
        rw [hsupp₁]
        exact Or.inr hx₁
      exact hmem

/-- **Finite-degree descent of a second blow-up center** (Stacks Project Tag 0803
together with the support computation of the proof of Tag 080B; blueprint
`lemma:nagata-proj-closed-center-finite-degree-exists`,
`lemma:nagata-composition-center-ideal`): given a finite-type center `I` on a qcqs
scheme `X` with blow-up `π = I.blowupMap` and a finite-type center `J` on `I.blowup`,
there are a positive degree `d` and a finite-type ideal `L ≤ I ^ d` on `X` such that
the support of `L` is `supp I ∪ π(supp J)` and the inverse image ideal of `L` on the
blow-up is `I_E^d · J`.

This combines the finite-degree approximation `exists_finiteDegree_center_le_blowup`
(Tag 0803) with the support computation `coe_support_eq_of_comap_pow_mul`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteDegree_center
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : I.ofFiniteType) (J : I.blowup.IdealSheafData)
    (hJ : J.ofFiniteType) :
    ∃ (d : ℕ) (L : X.IdealSheafData), 0 < d ∧ L.ofFiniteType ∧ L ≤ I ^ d ∧
      (L.support : Set X) =
        (I.support : Set X) ∪ I.blowupMap '' (J.support : Set I.blowup) ∧
      L.comap I.blowupMap = (I.comap I.blowupMap) ^ d * J := by
  obtain ⟨d, L, hd, hLft, hLle, hLcomap⟩ :=
    Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup I hI J hJ
  exact ⟨d, L, hd, hLft, hLle,
    Scheme.IdealSheafData.coe_support_eq_of_comap_pow_mul I J hd.ne' hLle hLcomap,
    hLcomap⟩

/-- **Blow-up of a product ideal** (Stacks Project Tag 080A; blueprint
`thm:nagata-blowup-product-ideal`, `cor:nagata-blowup-product-common-refinement`).

The proof follows the comparison strategy of `def:nagata-blowup-product-comparison`
and `thm:nagata-blowup-product-ideal` of the revised blueprint and runs entirely
through the universal property of blowing up
(`Scheme.IdealSheafData.exists_lift_blowup` and
`Scheme.IdealSheafData.hom_ext_of_isInvertible_comap`, Stacks Project Tag 0806): on the
iterated blow-up the pullback of `I * L` is invertible, giving `α`; on the blow-up of
`I * L` the pullbacks of `I` and of `L` are invertible by the factor lemma
(`IsInvertible.of_mul_left/right`), giving the lift `β` to `I.blowup` and then
`γ` to the iterated blow-up; the two composites are identities by the uniqueness of
lifts. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_mul_iso
    {X : Scheme.{u}} (I L : X.IdealSheafData) :
    ∃ e : (I * L).blowup ≅ (L.comap I.blowupMap).blowup,
      e.hom ≫ (L.comap I.blowupMap).blowupMap ≫ I.blowupMap = (I * L).blowupMap := by
  -- notation: the first blow-up `π`, the second blow-up `q` and the product blow-up `c`
  set π := I.blowupMap with hπ
  set q := (L.comap π).blowupMap with hq
  set c := (I * L).blowupMap with hc
  -- the pullback of `I` to the blow-up is invertible
  have hE1 : (I.comap π).IsInvertible := I.isInvertible_comap_blowupMap
  -- hence so is its further pullback along the second blow-up
  have hE3 : ((I.comap π).comap q).IsInvertible :=
    hE1.comap_blowupMap (L.comap π)
  -- the pullback of `L.comap π` to the second blow-up is invertible
  have hE2 : ((L.comap π).comap q).IsInvertible :=
    (L.comap π).isInvertible_comap_blowupMap
  -- Step 1: the pullback of `I * L` along `ρ = q ≫ π` is invertible
  have hE4 : ((I * L).comap (q ≫ π)).IsInvertible := by
    have h4 : (I * L).comap (q ≫ π) =
        ((I.comap π).comap q) * ((L.comap π).comap q) := by
      rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_mul,
        Scheme.IdealSheafData.comap_mul]
    rw [h4]
    exact hE3.mul hE2
  obtain ⟨α, hα⟩ := (I * L).exists_lift_blowup hE4
  -- Step 2: the pullbacks of `I` and `L` to the product blow-up are invertible
  have hECc : ((I * L).comap c).IsInvertible :=
    (I * L).isInvertible_comap_blowupMap
  have hprod : ((I.comap c) * (L.comap c)).IsInvertible := by
    rw [← Scheme.IdealSheafData.comap_mul]
    exact hECc
  have hIc : (I.comap c).IsInvertible :=
    Scheme.IdealSheafData.IsInvertible.of_mul_left hprod
  have hLc : (L.comap c).IsInvertible :=
    Scheme.IdealSheafData.IsInvertible.of_mul_right hprod
  -- the lift `β` of the product blow-up to the blow-up of `I`
  obtain ⟨β, hβ⟩ := I.exists_lift_blowup hIc
  -- Step 3: the pullback of `L.comap π` along `β` is invertible
  have hLβ : ((L.comap π).comap β).IsInvertible := by
    have h6 : (L.comap π).comap β = L.comap c := by
      rw [← Scheme.IdealSheafData.comap_comp, hβ]
    rw [h6]
    exact hLc
  obtain ⟨γ, hγ⟩ := (L.comap π).exists_lift_blowup hLβ
  -- Step 4: the two composites are identities, by uniqueness of lifts
  have hγα : γ ≫ α = 𝟙 (I * L).blowup := by
    refine (I * L).hom_ext_of_isInvertible_comap hECc ?_ (Category.id_comp c)
    rw [Category.assoc, hα, ← Category.assoc, hγ, hβ]
  have hαβ : α ≫ β = q := by
    have hEρ : (I.comap (q ≫ π)).IsInvertible := by
      rw [Scheme.IdealSheafData.comap_comp]
      exact hE3
    refine I.hom_ext_of_isInvertible_comap hEρ ?_ ?_
    · rw [Category.assoc, hβ, hα]
    · exact congrArg (CategoryStruct.comp q) hπ.symm
  have hαγ : α ≫ γ = 𝟙 (L.comap π).blowup := by
    refine (L.comap π).hom_ext_of_isInvertible_comap hE2 ?_ (Category.id_comp q)
    rw [Category.assoc, hγ, hαβ]
  refine ⟨⟨γ, α, hγα, hαγ⟩, ?_⟩
  change γ ≫ q ≫ π = c
  rw [← Category.assoc, hγ, hβ]

/-- **Multiplying a center by an invertible ideal does not change the blow-up**
(consequence of Stacks Project Tags 0807 and 080A; blueprint
`lemma:nagata-blowup-invertible-factor`).

The proof runs through the universal property of blowing up
(`Scheme.IdealSheafData.exists_lift_blowup` and
`Scheme.IdealSheafData.hom_ext_of_isInvertible_comap`, Stacks Project Tag 0806): the
pullback of `C * M` to the blow-up of `M` is a product of invertible ideals,
giving a lift `α : M.blowup ⟶ (C * M).blowup`; conversely the pullback of `M` to the
blow-up of `C * M` is invertible by the factor lemma
(`IsInvertible.of_mul_right`), giving `β` in the other direction; the two
composites are identities by the uniqueness of lifts. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_mul_isInvertible_iso
    {Y : Scheme.{u}} {C : Y.IdealSheafData} (hC : C.IsInvertible)
    (M : Y.IdealSheafData) :
    ∃ e : (C * M).blowup ≅ M.blowup, e.hom ≫ M.blowupMap = (C * M).blowupMap := by
  -- the pullback of `C * M` to the blow-up of `M` is invertible
  have hCM : ((C * M).comap M.blowupMap).IsInvertible := by
    rw [Scheme.IdealSheafData.comap_mul]
    exact (hC.comap_blowupMap M).mul M.isInvertible_comap_blowupMap
  obtain ⟨α, hα⟩ := (C * M).exists_lift_blowup hCM
  -- the pullback of `M` to the blow-up of `C * M` is invertible
  have hECcm : ((C * M).comap (C * M).blowupMap).IsInvertible :=
    (C * M).isInvertible_comap_blowupMap
  have hMcm : (M.comap (C * M).blowupMap).IsInvertible := by
    refine Scheme.IdealSheafData.IsInvertible.of_mul_right
      (K₁ := C.comap (C * M).blowupMap) ?_
    rw [← Scheme.IdealSheafData.comap_mul]
    exact hECcm
  obtain ⟨β, hβ⟩ := M.exists_lift_blowup hMcm
  -- the two composites are identities, by uniqueness of lifts
  have hβα : β ≫ α = 𝟙 (C * M).blowup := by
    refine (C * M).hom_ext_of_isInvertible_comap hECcm ?_ (Category.id_comp _)
    rw [Category.assoc, hα, hβ]
  have hαβ : α ≫ β = 𝟙 M.blowup := by
    refine M.hom_ext_of_isInvertible_comap M.isInvertible_comap_blowupMap ?_
      (Category.id_comp _)
    rw [Category.assoc, hβ, hα]
  exact ⟨⟨β, α, hβα, hαβ⟩, hβ⟩

/-- **The blow-up comparison behind the composition theorem** (the geometric half of
Stacks Project Tag 080B): if the inverse image ideal of `B` on the blow-up of `A` is
`(A · 𝒪)^d · C`, then the blow-up of the product center `A * B` is, over the base, the
blow-up of `C` on the blow-up of `A`.

This is the product comparison (`exists_blowup_mul_iso`, Tag 080A) followed by the
removal of the invertible exceptional factor `(A · 𝒪)^d`
(`exists_blowup_mul_isInvertible_iso`, Tag 0807), the exceptional ideal being invertible
by the principalization theorem. No finiteness hypotheses are needed: those enter Tag
080B only through the finite-degree descent producing `B`, `d` and `C`, so the same
comparison applies verbatim to base-changed centers. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_mul_iso_of_comap_eq
    {Z : Scheme.{u}} (A B : Z.IdealSheafData) {d : ℕ} {C : A.blowup.IdealSheafData}
    (h : B.comap A.blowupMap = (A.comap A.blowupMap) ^ d * C) :
    ∃ e : (A * B).blowup ≅ C.blowup,
      e.hom ≫ C.blowupMap ≫ A.blowupMap = (A * B).blowupMap := by
  obtain ⟨e₁, he₁⟩ := Scheme.IdealSheafData.exists_blowup_mul_iso A B
  -- the exceptional ideal is invertible, hence so is its `d`-th power
  have hEC : ((A.comap A.blowupMap) ^ d).IsInvertible :=
    A.isInvertible_comap_blowupMap.pow d
  obtain ⟨e₂, he₂⟩ := Scheme.IdealSheafData.exists_blowup_mul_isInvertible_iso hEC C
  refine ⟨e₁ ≪≫ eqToIso (congrArg Scheme.IdealSheafData.blowup h) ≪≫ e₂, ?_⟩
  calc (e₁ ≪≫ eqToIso (congrArg Scheme.IdealSheafData.blowup h) ≪≫ e₂).hom ≫
        C.blowupMap ≫ A.blowupMap
      = e₁.hom ≫ eqToHom (congrArg Scheme.IdealSheafData.blowup h) ≫
          (e₂.hom ≫ C.blowupMap) ≫ A.blowupMap := by
        simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
    _ = e₁.hom ≫ (eqToHom (congrArg Scheme.IdealSheafData.blowup h) ≫
          ((A.comap A.blowupMap) ^ d * C).blowupMap) ≫ A.blowupMap := by
        rw [he₂, Category.assoc]
    _ = e₁.hom ≫ (B.comap A.blowupMap).blowupMap ≫ A.blowupMap := by
        rw [Scheme.IdealSheafData.eqToHom_comp_blowupMap h]
    _ = (A * B).blowupMap := he₁

/-- **Existence of the canonical lift of a blow-up along a base change** (Stacks
Project Tag 0806, existence): for `f : Y ⟶ X` the composite
`Bl_{I·𝒪_Y}(Y) ⟶ Y ⟶ X` pulls `I` back to the invertible exceptional ideal, hence
lifts to `Bl_I(X)`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_blowup_comap
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    ∃ h : (I.comap f).blowup ⟶ I.blowup,
      h ≫ I.blowupMap = (I.comap f).blowupMap ≫ f :=
  I.exists_lift_blowup
    (by rw [Scheme.IdealSheafData.comap_comp]
        exact (I.comap f).isInvertible_comap_blowupMap)

/-- **Uniqueness of the canonical lift of a blow-up along a base change** (Stacks
Project Tag 0806, uniqueness): for `f : Y ⟶ X` there is at most one morphism
`Bl_{I·𝒪_Y}(Y) ⟶ Bl_I(X)` lying over `f`, since the inverse image of `I` on
`Bl_{I·𝒪_Y}(Y)` is invertible. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.hom_ext_comap_blowup
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)
    {h₁ h₂ : (I.comap f).blowup ⟶ I.blowup}
    (e₁ : h₁ ≫ I.blowupMap = (I.comap f).blowupMap ≫ f)
    (e₂ : h₂ ≫ I.blowupMap = (I.comap f).blowupMap ≫ f) :
    h₁ = h₂ :=
  I.hom_ext_of_isInvertible_comap
    (by rw [Scheme.IdealSheafData.comap_comp]
        exact (I.comap f).isInvertible_comap_blowupMap) e₁ e₂

/-- **Composition of blow-ups, compatibly with base change** (Stacks Project Tag 080B):
on a qcqs scheme `X`, a finite-type center `I` with blow-up `π = I.blowupMap` and a
finite-type center `J` on `I.blowup` are composed into a single finite-type center `K`
on `X`, with support `supp I ∪ π(supp J)` and with `K.blowup ≅ J.blowup` over `X`.
Moreover the same identification holds after an arbitrary base change `f : Y ⟶ X`:
if `ρ : Bl_{I·𝒪_Y}(Y) ⟶ Bl_I(X)` is the canonical lift, then the blow-up of `K·𝒪_Y`
is the blow-up of `J·𝒪` over `Bl_{I·𝒪_Y}(Y)`.

The final clause records the compatibility of the two comparisons that the
common-modification theorem (Stacks Tag 0F3W) needs: for any lift `μ` of `ρ` to the
second blow-ups and any lift `l` of `f` to the blow-ups of `K`, the two composites
`(K·𝒪_Y).blowup ⟶ J.blowup` agree, both being lifts of `(K.comap f).blowupMap ≫ f`
along `K.blowupMap`.

The composite center is `K = I * L` for the finite-degree descent `L` of `J`
(`Scheme.IdealSheafData.exists_finiteDegree_center`, Stacks Tag 0803), so that
`L.comap π = (I.comap π)^d * J`. Base changing, `K.comap f = (I.comap f) * (L.comap f)`
and, using `ρ ≫ π = (I.comap f).blowupMap ≫ f`,
`(L.comap f).comap (I.comap f).blowupMap = ((I.comap f) · 𝒪)^d * (J.comap ρ)`, so
`exists_blowup_mul_iso_of_comap_eq` applies verbatim over `Y`.
(Blueprint: `thm:nagata-composition-of-blowups`.) -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp_base_change
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : I.ofFiniteType) (J : I.blowup.IdealSheafData)
    (hJ : J.ofFiniteType) :
    ∃ K : X.IdealSheafData, K.ofFiniteType ∧
      (K.support : Set X) =
        (I.support : Set X) ∪ I.blowupMap '' (J.support : Set I.blowup) ∧
      ∃ e₀ : K.blowup ≅ J.blowup, e₀.hom ≫ J.blowupMap ≫ I.blowupMap = K.blowupMap ∧
        ∀ {Y : Scheme.{u}} (f : Y ⟶ X) (ρ : (I.comap f).blowup ⟶ I.blowup),
          ρ ≫ I.blowupMap = (I.comap f).blowupMap ≫ f →
          ∃ e : (K.comap f).blowup ≅ (J.comap ρ).blowup,
            e.hom ≫ (J.comap ρ).blowupMap ≫ (I.comap f).blowupMap =
              (K.comap f).blowupMap ∧
            ∀ μ : (J.comap ρ).blowup ⟶ J.blowup,
              μ ≫ J.blowupMap = (J.comap ρ).blowupMap ≫ ρ →
              ∀ l : (K.comap f).blowup ⟶ K.blowup,
                l ≫ K.blowupMap = (K.comap f).blowupMap ≫ f →
                e.hom ≫ μ = l ≫ e₀.hom := by
  obtain ⟨d, L, -, hLft, -, hLsupp, hLpull⟩ :=
    Scheme.IdealSheafData.exists_finiteDegree_center I hI J hJ
  obtain ⟨e₀, he₀⟩ := Scheme.IdealSheafData.exists_blowup_mul_iso_of_comap_eq I L hLpull
  refine ⟨I * L, hI.mul hLft, ?_, e₀, he₀, ?_⟩
  · -- support of the product center
    rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup, hLsupp,
      ← Set.union_assoc, Set.union_self]
  intro Y f ρ hρ
  -- the base-changed composite center is the product of the base-changed factors
  have hKf : (I * L).comap f = (I.comap f) * (L.comap f) :=
    Scheme.IdealSheafData.comap_mul f I L
  -- the finite-degree identity, transported to the base-changed first blow-up
  have hLf : (L.comap f).comap (I.comap f).blowupMap =
      ((I.comap f).comap (I.comap f).blowupMap) ^ d * (J.comap ρ) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hρ, Scheme.IdealSheafData.comap_comp,
      hLpull, Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
      ← Scheme.IdealSheafData.comap_comp, hρ, Scheme.IdealSheafData.comap_comp]
  obtain ⟨e', he'⟩ :=
    Scheme.IdealSheafData.exists_blowup_mul_iso_of_comap_eq (I.comap f) (L.comap f) hLf
  refine ⟨eqToIso (congrArg Scheme.IdealSheafData.blowup hKf) ≪≫ e', ?_, ?_⟩
  · -- the base-changed comparison lies over `Y`
    rw [Iso.trans_hom, eqToIso.hom, Category.assoc, he',
      Scheme.IdealSheafData.eqToHom_comp_blowupMap hKf]
  · -- compatibility with the comparison over `X`, by uniqueness of lifts
    intro μ hμ l hl
    have hinv : e₀.inv ≫ (I * L).blowupMap = J.blowupMap ≫ I.blowupMap := by
      rw [← he₀, Iso.inv_hom_id_assoc]
    rw [← Iso.comp_inv_eq]
    refine (I * L).hom_ext_comap_blowup f ?_ hl
    simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
    rw [hinv, ← Category.assoc μ, hμ, Category.assoc, hρ, reassoc_of% he',
      ← Category.assoc, Scheme.IdealSheafData.eqToHom_comp_blowupMap hKf]

/-- **Composition of blow-ups** (Stacks Project Tag 080B), interface form; blueprint
`thm:nagata-composition-of-blowups`.

This is the base-change-free part of
`Scheme.IdealSheafData.exists_blowup_comp_base_change`, obtained by discarding its
final clause rather than by instantiating `f`: the composite center is
`K = I * L` with `L` the finite-degree descent of `J`
(`Scheme.IdealSheafData.exists_finiteDegree_center`, Stacks Tag 0803). -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : I.ofFiniteType) (J : I.blowup.IdealSheafData)
    (hJ : J.ofFiniteType) :
    ∃ K : X.IdealSheafData, K.ofFiniteType ∧
      (K.support : Set X) =
        (I.support : Set X) ∪ I.blowupMap '' (J.support : Set I.blowup) ∧
      ∃ e : K.blowup ≅ J.blowup,
        e.hom ≫ J.blowupMap ≫ I.blowupMap = K.blowupMap := by
  obtain ⟨K, hKft, hKsupp, e, he, -⟩ :=
    Scheme.IdealSheafData.exists_blowup_comp_base_change I hI J hJ
  exact ⟨K, hKft, hKsupp, e, he⟩

/-- **Composition of admissible blow-ups** (Stacks Project Tag 080L; blueprint
`lemma:nagata-admissible-blowup-comp`).

Difference from the informal statement: Stacks Tag 080L assumes `U` quasi-compact; the
formal proof needs no such hypothesis.

The proof applies the composition theorem for arbitrary blow-ups
(`Scheme.IdealSheafData.exists_blowup_comp`, Stacks Tag 080B): the composite center
`K` has support `|Z| ∪ π₁(|Z'|)`; the first part misses `U` by admissibility of `B₁`,
and the second part misses `U` because a point of `π₁(|Z'|) ∩ U` would lift to a point
of `|Z'| ∩ π₁⁻¹(U)`, contradicting admissibility of `B₂`. -/
theorem exists_comp [CompactSpace X] [QuasiSeparatedSpace X]
    (B₁ : IsAdmissible X U) (B₂ : IsAdmissible B₁.I.blowup (B₁.I.blowupMap ⁻¹ᵁ U)) :
    ∃ K : X.IdealSheafData, K.ofFiniteType ∧ Disjoint (U : Set X) (K.support : Set X) ∧
      ∃ iso : B₂.I.blowup ≅ K.blowup,
        iso.hom ≫ K.blowupMap = B₂.I.blowupMap ≫ B₁.I.blowupMap := by
  obtain ⟨K, hKft, hKsupp, e', he'⟩ :=
    Scheme.IdealSheafData.exists_blowup_comp B₁.I B₁.finiteType B₂.I B₂.finiteType
  -- admissibility of the composite center: `(|Z| ∪ π₁(|Z'|)) ∩ U = ∅`
  have hdisj : Disjoint (U : Set X) (K.support : Set X) := by
    rw [Set.disjoint_left]
    intro x hxU hxK
    rw [hKsupp] at hxK
    rcases hxK with hxI | ⟨x', hx', rfl⟩
    · exact Set.disjoint_left.mp B₁.disjoint_support hxU hxI
    · exact Set.disjoint_left.mp B₂.disjoint_support
        (show x' ∈ ((B₁.I.blowupMap ⁻¹ᵁ U : B₁.I.blowup.Opens) :
          Set B₁.I.blowup) from hxU) hx'
  refine ⟨K, hKft, hdisj, e'.symm, ?_⟩
  rw [Iso.symm_hom, ← he', Iso.inv_hom_id_assoc]

end IsAdmissible

variable {X U}

/-- **A quasi-compact open is the complement of the support of a finite-type ideal**
(Stacks Project Tag 01PH; blueprint: `lemma:nagata-qc-open-complement-ideal-exists`).

The ideal is the finite-type approximation of the vanishing ideal of the reduced
boundary, obtained by extending finitely generated pieces over a finite affine cover. -/
theorem Scheme.exists_finiteType_ideal_coe_support_eq_compl
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    ∃ I : X.IdealSheafData, I.ofFiniteType ∧ (I.support : Set X) = (U : Set X)ᶜ := by
  set H₀ : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ with hH₀def
  -- the vanishing ideal of the boundary restricts to the unit ideal on `U`
  have hcomap : H₀.comap U.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    ext1
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      hH₀def, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    ext x
    simp
  -- the finite-type approximation of the vanishing ideal (Stacks Tag 01PF)
  obtain ⟨I, hle, hft, hIcomap⟩ := Scheme.IdealSheafData.exists_finiteType_le_comap_eq
    H₀ U hU (by
      rw [Scheme.IdealSheafData.ofFiniteTypeOn_iff_comap, hcomap]
      intro U' _
      exact ⟨{1}, by simp⟩)
  refine ⟨I, hft, subset_antisymm ?_ ?_⟩
  · -- `I` restricts to the unit ideal on `U`, so its support misses `U`
    have h1 : I.comap U.ι = ⊤ := by rw [hIcomap, hcomap]
    have h2 : U.ι ⁻¹' (I.support : Set X) = ∅ := by
      have h3 : ((I.comap U.ι).support : Set U.toScheme) = ∅ := by
        rw [h1]; simp
      rwa [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage] at h3
    rw [Set.subset_compl_iff_disjoint_right, Set.disjoint_iff_inter_eq_empty,
      ← Scheme.Opens.range_ι (U := U), ← Set.image_preimage_eq_inter_range, h2,
      Set.image_empty]
  · -- `I` is contained in the vanishing ideal of the boundary, so its support covers it
    have h4 : (H₀.support : Set X) = (U : Set X)ᶜ := by
      rw [hH₀def, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    rw [← h4]
    exact Scheme.IdealSheafData.support_antitone hle

/-- **A quasi-compact open is the complement of the support of a finite-type ideal**,
locally Noetherian case.

Difference from `Scheme.exists_finiteType_ideal_coe_support_eq_compl`: no
quasi-compactness of `U` is needed, every ideal sheaf being of finite type; the ideal is
the vanishing ideal of the reduced boundary itself. This is the instance used for the
Noetherian compactification theorem (`thm:nagata-noetherian`). -/
theorem Scheme.exists_finiteType_ideal_coe_support_eq_compl_of_isLocallyNoetherian
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens) :
    ∃ I : X.IdealSheafData, I.ofFiniteType ∧ (I.support : Set X) = (U : Set X)ᶜ :=
  ⟨Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩,
    Scheme.IdealSheafData.ofFiniteType_of_isLocallyNoetherian _,
    by simp [Scheme.IdealSheafData.coe_support_vanishingIdeal]⟩

/-- **Extension of a constructible closed subset to a finite-type center** (Stacks
Project Tags 01PH and 01PF): on a quasi-compact quasi-separated scheme `X`, every
closed subset of a quasi-compact open `U` with quasi-compact complement — i.e. every
constructible closed subset of `U` — is the trace on `U` of the support of a
finite-type quasi-coherent ideal on `X`. -/
theorem Scheme.IdealSheafData.exists_finiteType_preimage_coe_support_eq
    [CompactSpace X] [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X))
    {T : Set U.toScheme} (hT : IsClosed T) (hc : IsCompact Tᶜ) :
    ∃ I : X.IdealSheafData, I.ofFiniteType ∧ U.ι ⁻¹' (I.support : Set X) = T := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  -- the finite-type vanishing ideal of `T` on `U` (Stacks Tag 01PH)
  obtain ⟨J, hJft, hJsupp⟩ :=
    U.toScheme.exists_finiteType_ideal_coe_support_eq_compl ⟨Tᶜ, hT.isOpen_compl⟩ hc
  -- extend it to a finite-type ideal on `X` (Stacks Tag 01PF)
  obtain ⟨I, hIft, hIcomap⟩ := Scheme.IdealSheafData.exists_finiteType_comap_eq U hU J hJft
  refine ⟨I, hIft, ?_⟩
  rw [← Scheme.IdealSheafData.coe_support_comap, hIcomap, hJsupp]
  exact compl_compl T

/-- **Preparation of a Cartier boundary, from a boundary ideal**: the blow-up of a
finite-type ideal whose support is exactly the complement of `U` is a `U`-admissible
blow-up on which the inverse image of the center is an invertible ideal supported
exactly on the boundary — the complement of the preimage of `U`. -/
theorem exists_admissibleBlowup_cartierBoundary_of_coe_support_eq_compl
    (I : X.IdealSheafData) (hft : I.ofFiniteType)
    (hsupp : (I.support : Set X) = (U : Set X)ᶜ) :
    ∃ (B : IsAdmissible X U) (J : B.I.blowup.IdealSheafData), J.IsInvertible ∧
      (J.support : Set B.I.blowup) = ((B.I.blowupMap ⁻¹ᵁ U) : Set B.I.blowup)ᶜ := by
  have hdisj : Disjoint (U : Set X) (I.support : Set X) := by
    rw [hsupp]
    exact disjoint_compl_right
  refine ⟨⟨I, hft, hdisj⟩, I.comap I.blowupMap,
    I.isInvertible_comap_blowupMap, ?_⟩
  change ((I.comap I.blowupMap).support : Set I.blowup) =
    ((I.blowupMap ⁻¹ᵁ U : I.blowup.Opens) : Set I.blowup)ᶜ
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hsupp,
    Set.preimage_compl]
  rfl

/-- **Preparation of a Cartier boundary** (Stacks Project Tag 080Y; blueprint:
`lemma:nagata-cartier-boundary-preparation`; proof order item 24). -/
theorem exists_admissibleBlowup_cartierBoundary [CompactSpace X] [QuasiSeparatedSpace X]
    (hU : IsCompact (U : Set X)) :
    ∃ (B : IsAdmissible X U) (J : B.I.blowup.IdealSheafData), J.IsInvertible ∧
      (J.support : Set B.I.blowup) = ((B.I.blowupMap ⁻¹ᵁ U) : Set B.I.blowup)ᶜ := by
  obtain ⟨I, hft, hsupp⟩ := X.exists_finiteType_ideal_coe_support_eq_compl U hU
  exact exists_admissibleBlowup_cartierBoundary_of_coe_support_eq_compl I hft hsupp

/-- **Preparation of a Cartier boundary**, locally Noetherian case (blueprint:
`lemma:nagata-cartier-boundary-preparation`; proof order item 24).

Difference from `exists_admissibleBlowup_cartierBoundary`: no compactness of `U` is
needed, the finite-type boundary ideal being the vanishing ideal of the reduced boundary
itself. This is the instance needed for the Noetherian compactification theorem
(`thm:nagata-noetherian`). -/
theorem exists_admissibleBlowup_cartierBoundary_of_isLocallyNoetherian
    [IsLocallyNoetherian X] :
    ∃ (B : IsAdmissible X U) (J : B.I.blowup.IdealSheafData), J.IsInvertible ∧
      (J.support : Set B.I.blowup) = ((B.I.blowupMap ⁻¹ᵁ U) : Set B.I.blowup)ᶜ := by
  obtain ⟨I, hft, hsupp⟩ :=
    X.exists_finiteType_ideal_coe_support_eq_compl_of_isLocallyNoetherian U
  exact exists_admissibleBlowup_cartierBoundary_of_coe_support_eq_compl I hft hsupp

section BoundarySeparation

/-! ### Boundary separation

This is the route the two-open compactification theorem takes instead of module
flattening: two finite-presentation closed subschemes which are disjoint over `U`
acquire disjoint strict transforms after blowing up the sum of their ideals
(Stacks Project Tag 0F3V; revised blueprint `def:nagata-separate-closed-subschemes`,
`lemma:nagata-separate-closed-subschemes`). -/

/-- **The boundary-separation blow-up** (revised blueprint
`def:nagata-separate-closed-subschemes`): the `U`-admissible blow-up of the sum of the
ideals of two finite-type centers whose common support is disjoint from `U`. -/
def separationBlowup (I₁ I₂ : X.IdealSheafData) (h₁ : I₁.ofFiniteType) (h₂ : I₂.ofFiniteType)
    (hdisj : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X))) :
    IsAdmissible X U :=
  ⟨I₁ ⊔ I₂, h₁.sup h₂,
    hdisj.mono_right (Scheme.IdealSheafData.coe_support_sup I₁ I₂).subset⟩

/-- **Compactness of the complement of the support** of a finite-type ideal sheaf on a
quasi-compact scheme: on each member of a finite affine cover the complement is the
complement of the vanishing locus of a finitely generated ideal, which is a finite union
of basic opens. -/
lemma Scheme.IdealSheafData.isCompact_coe_compl_support {X : Scheme.{u}} [CompactSpace X]
    {K : X.IdealSheafData} (hK : K.ofFiniteType) :
    IsCompact ((K.support.compl : X.Opens) : Set X) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens ↦ (V.1 : Set X)) (fun V ↦ V.1.isOpen) (by
      intro x _
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X] at hx
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨V, hV⟩)
  have hpiece : ∀ V : X.affineOpens,
      (K.support : Set X)ᶜ ∩ (V.1 : Set X) =
        V.2.fromSpec '' (PrimeSpectrum.zeroLocus ((K.ideal V : Ideal _) : Set _))ᶜ := by
    intro V
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_image]
    constructor
    · rintro ⟨hxs, hxV⟩
      have hxr : x ∈ Set.range V.2.fromSpec := by rw [V.2.range_fromSpec]; exact hxV
      obtain ⟨p, rfl⟩ := hxr
      refine ⟨p, fun hp ↦ hxs ?_, rfl⟩
      have hmem : V.2.fromSpec p ∈ X.zeroLocus (U := V.1) (K.ideal V : Set _) ∩ V.1 := by
        rw [← V.2.fromSpec_image_zeroLocus]
        exact ⟨p, hp, rfl⟩
      exact ((K.coe_support_inter V).symm ▸ hmem).1
    · rintro ⟨p, hp, rfl⟩
      have hxV : V.2.fromSpec p ∈ (V.1 : Set X) := by
        rw [← V.2.range_fromSpec]; exact ⟨p, rfl⟩
      refine ⟨fun hsupp ↦ hp ?_, hxV⟩
      have hmem : V.2.fromSpec p ∈ X.zeroLocus (U := V.1) (K.ideal V : Set _) ∩ V.1 :=
        (K.coe_support_inter V) ▸ ⟨hsupp, hxV⟩
      have := V.2.fromSpec_preimage_zeroLocus (K.ideal V : Set _)
      exact this ▸ (Set.mem_preimage.mpr hmem.1)
  have hcover : ((K.support.compl : X.Opens) : Set X) =
      ⋃ V ∈ t, ((K.support : Set X)ᶜ ∩ (V.1 : Set X)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact Set.mem_iUnion₂.mpr ⟨V, hVt, hx, hxV⟩
    · rintro hx
      obtain ⟨V, -, hx, -⟩ := Set.mem_iUnion₂.mp hx
      exact hx
  rw [hcover]
  refine t.finite_toSet.isCompact_biUnion fun V _ ↦ ?_
  rw [hpiece V]
  exact ((PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr
    ⟨K.ideal V, hK V le_top, rfl⟩).1).image V.2.fromSpec.continuous

/-- **The charts at pure degree-one elements cover the blow-up of a sum**: every point
of `Bl_{I₁ ⊔ I₂}(X)` lies in a chart at a degree-one element coming from a local
section of `I₁` or of `I₂`, since `D₊(b₁ + b₂) ⊆ D₊(b₁) ∪ D₊(b₂)`. -/
lemma Scheme.IdealSheafData.exists_mem_range_chart_sup {X : Scheme.{u}}
    (I₁ I₂ : X.IdealSheafData) (x : (I₁ ⊔ I₂).blowup) :
    ∃ (U : X.affineOpens) (b : Γ(X, U.1)) (hb : b ∈ (I₁ ⊔ I₂).ideal U),
      (b ∈ I₁.ideal U ∨ b ∈ I₂.ideal U) ∧
      x ∈ Set.range ((I₁ ⊔ I₂).blowupChart U hb) := by
  have hx : (I₁ ⊔ I₂).blowupMap x ∈ (⊤ : X.Opens) := trivial
  rw [← iSup_affineOpens_eq_top X] at hx
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hx2 : x ∈ (I₁ ⊔ I₂).blowupMap ⁻¹ᵁ U.1 := hU
  rw [(I₁ ⊔ I₂).blowupMap_preimage U] at hx2
  obtain ⟨y, rfl⟩ := hx2
  have hy : y ∈ (⊤ : (AffineBlowup ((I₁ ⊔ I₂).ideal U)).Opens) := trivial
  rw [← AffineBlowup.iSup_basicOpen_reesX_eq_top ((I₁ ⊔ I₂).ideal U)] at hy
  obtain ⟨a, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  obtain ⟨av, hav⟩ := a
  have hsup : (I₁ ⊔ I₂).ideal U = I₁.ideal U ⊔ I₂.ideal U := by
    rw [congrFun (Scheme.IdealSheafData.ideal_sup (I := I₁) (J := I₂)) U, Pi.sup_apply]
  have hav' : av ∈ I₁.ideal U ⊔ I₂.ideal U := hsup ▸ hav
  obtain ⟨b₁, hb₁, b₂, hb₂, hsum⟩ := Submodule.mem_sup.mp hav'
  subst hsum
  have hb₁K : b₁ ∈ (I₁ ⊔ I₂).ideal U := by
    rw [hsup]
    exact Submodule.mem_sup_left hb₁
  have hb₂K : b₂ ∈ (I₁ ⊔ I₂).ideal U := by
    rw [hsup]
    exact Submodule.mem_sup_right hb₂
  rw [show reesX ((I₁ ⊔ I₂).ideal U) (b₁ + b₂) hav =
    reesX ((I₁ ⊔ I₂).ideal U) b₁ hb₁K + reesX ((I₁ ⊔ I₂).ideal U) b₂ hb₂K from
    reesX_add _ hb₁K hb₂K] at hy
  have hy' := TopologicalSpace.Opens.mem_sup.mp (Proj.basicOpen_add_le _ _ _ hy)
  rcases hy' with h | h
  · rw [← AffineBlowup.opensRange_chart ((I₁ ⊔ I₂).ideal U)
      (reesX ((I₁ ⊔ I₂).ideal U) b₁ hb₁K) (reesX_mem _ b₁ hb₁K)] at h
    obtain ⟨z, rfl⟩ := h
    exact ⟨U, b₁, hb₁K, Or.inl hb₁, ⟨z, (I₁ ⊔ I₂).blowupChart_apply U hb₁K z⟩⟩
  · rw [← AffineBlowup.opensRange_chart ((I₁ ⊔ I₂).ideal U)
      (reesX ((I₁ ⊔ I₂).ideal U) b₂ hb₂K) (reesX_mem _ b₂ hb₂K)] at h
    obtain ⟨z, rfl⟩ := h
    exact ⟨U, b₂, hb₂K, Or.inr hb₂, ⟨z, (I₁ ⊔ I₂).blowupChart_apply U hb₂K z⟩⟩

/-- **The strict transform of a center misses the affine probes at its own sections**:
let `K` and `J` be ideal sheaves and let `c : Spec S ⟶ Bl_K(X)` be a morphism lying
over an affine probe `Spec.map φ ≫ fromSpec : Spec S ⟶ X` on which the extension of
`K` is generated by the image of a section `b` of `J` (so that, on the probe, the
extension of `K` is contained in the extension of `J`). Then the strict transform of
`V(J)` along the blow-up of `K` is disjoint from the image of `c`: at a point of
`V(J) ×_X Bl_K(X)` over the complement of the support of `K`, the extension of `K` is
the unit ideal while `b` vanishes, so the open locus misses the probe; the strict
transform is the closure of the open locus and the probe is open. In the application
`c` is a blow-up chart at the degree-one element attached to `b` and `S` is the chart
ring. -/
lemma disjoint_range_strictTransformMap_of_probe
    {X : Scheme.{u}} (K J : X.IdealSheafData) (U : X.affineOpens)
    (b : Γ(X, U.1)) (hbJ : b ∈ J.ideal U) {S : CommRingCat.{u}} (φ : Γ(X, U.1) ⟶ S)
    (hspan : (K.ideal U).map φ.hom = Ideal.span {φ.hom b})
    (c : Spec S ⟶ K.blowup) [IsOpenImmersion c]
    (hcomp : c ≫ K.blowupMap = Spec.map φ ≫ U.2.fromSpec)
    [QuasiCompact (strictTransformOpen J.subschemeι K.blowupMap K.support.compl).ι] :
    Disjoint
      (Set.range (strictTransformMap J.subschemeι K.blowupMap K.support.compl))
      (Set.range c) := by
  rw [Set.disjoint_left]
  rintro x ⟨t, rfl⟩ hxc
  -- the image point in the fibre product lies in the closure of the open locus
  have hwcl : strictTransformι J.subschemeι K.blowupMap
      K.support.compl t ∈ closure ((strictTransformOpen J.subschemeι K.blowupMap
        K.support.compl : Set _)) := by
    have hmem : strictTransformι J.subschemeι K.blowupMap
        K.support.compl t ∈ Set.range (strictTransformι
          J.subschemeι K.blowupMap K.support.compl) := ⟨t, rfl⟩
    have hrange : Set.range (strictTransformι J.subschemeι
        K.blowupMap K.support.compl) =
        ((((strictTransformOpen J.subschemeι K.blowupMap
          K.support.compl).ι).ker.support : Set _)) :=
      Scheme.IdealSheafData.range_subschemeι _
    rw [hrange, Scheme.Hom.support_ker, Scheme.Opens.range_ι] at hmem
    exact hmem
  -- pick a point of the open locus mapping into the probe
  have hopen : IsOpen (pullback.snd J.subschemeι K.blowupMap ⁻¹' (Set.range c)) := by
    have hoc : IsOpen (Set.range c) := by
      rw [← Scheme.Hom.coe_opensRange]
      exact c.opensRange.isOpen
    exact hoc.preimage (pullback.snd J.subschemeι K.blowupMap).continuous
  have hwmem : strictTransformι J.subschemeι K.blowupMap
      K.support.compl t ∈ pullback.snd J.subschemeι K.blowupMap ⁻¹' (Set.range c) := by
    rw [Set.mem_preimage]
    have heq : pullback.snd J.subschemeι K.blowupMap
        (strictTransformι J.subschemeι K.blowupMap
          K.support.compl t) =
        strictTransformMap J.subschemeι K.blowupMap K.support.compl t :=
      (Scheme.Hom.comp_apply _ _ _).symm
    rw [heq]
    exact hxc
  obtain ⟨w', hw'⟩ := mem_closure_iff.mp hwcl _ hopen hwmem
  obtain ⟨hw'o, hw'W⟩ := hw'
  obtain ⟨y', hy'⟩ := Set.mem_preimage.mp hw'o
  -- the base point of `w'` lies in the support of `J` but not in the support of `K`
  have hz1 : K.blowupMap (pullback.snd J.subschemeι K.blowupMap w') =
      (Spec.map φ ≫ U.2.fromSpec) y' := by
    rw [← hy', ← Scheme.Hom.comp_apply, hcomp]
  have hz2 : J.subschemeι (pullback.fst J.subschemeι K.blowupMap w') =
      K.blowupMap (pullback.snd J.subschemeι K.blowupMap w') := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hzJ : K.blowupMap (pullback.snd J.subschemeι K.blowupMap w') ∈
      (J.support : Set X) := by
    rw [← hz2, ← Scheme.IdealSheafData.range_subschemeι J]
    exact ⟨_, rfl⟩
  have hzK : K.blowupMap (pullback.snd J.subschemeι K.blowupMap w') ∉
      (K.support : Set X) := hw'W
  -- transfer both statements to the affine probe
  have hy'J : y' ∈ ((J.comap (Spec.map φ ≫ U.2.fromSpec)).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    exact Set.mem_preimage.mpr (hz1 ▸ hzJ)
  have hy'K : y' ∉ ((K.comap (Spec.map φ ≫ U.2.fromSpec)).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    exact fun hmem ↦ hzK (hz1 ▸ Set.mem_preimage.mp hmem)
  -- the pulled-back center is contained in the pulled-back ideal of `J`
  have hle : K.comap (Spec.map φ ≫ U.2.fromSpec) ≤ J.comap (Spec.map φ ≫ U.2.fromSpec) :=
    Scheme.IdealSheafData.comap_le_comap_of_ideal_map_eq_span K J U hbJ φ hspan
  exact hy'K (Scheme.IdealSheafData.support_antitone hle hy'J)

/-- **Quasi-compactness of the inclusion of the open locus of a strict transform** over
the complement of the support of a finite-type center on a qcqs scheme: the fibre
product is quasi-separated over `X`, and the open locus is the preimage of the
quasi-compact open `X ∖ supp K` under a quasi-compact morphism. -/
lemma quasiCompact_strictTransformOpen_ι {X : Scheme.{u}}
    [QuasiSeparatedSpace X] {K : X.IdealSheafData} (hK : K.ofFiniteType)
    (hU₀ : IsCompact ((K.support.compl : X.Opens) : Set X)) (J : X.IdealSheafData) :
    QuasiCompact (strictTransformOpen J.subschemeι K.blowupMap K.support.compl).ι := by
  have hπqc : QuasiCompact K.blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap hK
  have hproper : IsProper K.blowupMap := K.isProper_blowupMap fun U ↦ hK U le_top
  have hfstQS : QuasiSeparated (pullback.fst J.subschemeι K.blowupMap) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hPqs : QuasiSeparatedSpace ↥(Limits.pullback J.subschemeι K.blowupMap) :=
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst J.subschemeι K.blowupMap ≫ J.subschemeι)
  have hfstQC : QuasiCompact (pullback.fst J.subschemeι K.blowupMap) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hcpt : IsCompact
      ((strictTransformOpen J.subschemeι K.blowupMap K.support.compl :
        Set ↥(Limits.pullback J.subschemeι K.blowupMap))) := by
    rw [strictTransformOpen_eq_preimage]
    exact QuasiCompact.isCompact_preimage
      (f := pullback.fst J.subschemeι K.blowupMap ≫ J.subschemeι) _
      (K.support.compl).isOpen hU₀
  have : CompactSpace
      (strictTransformOpen J.subschemeι K.blowupMap K.support.compl).toScheme :=
    isCompact_iff_compactSpace.mp hcpt
  infer_instance

/-- **Boundary separation** (Stacks Project Tag 0F3V; revised blueprint
`lemma:nagata-separate-closed-subschemes`).

The proof is the chart argument of the revised blueprint: the charts of
`Bl_{I₁ ⊔ I₂}(X)` at degree-one elements coming from local sections of `I₁` or of `I₂`
cover the blow-up (`exists_mem_range_chart_sup`), and the strict transform of `V(Iᵢ)`
misses every `Iᵢ`-chart, because on such a chart the extension of the center is
generated by a section of `Iᵢ` (`disjoint_range_strictTransformMap_of_probe`); so the
two strict transforms have no common point. -/
theorem disjoint_range_strictTransformMap_sup [CompactSpace X]
    [QuasiSeparatedSpace X] (I₁ I₂ : X.IdealSheafData)
    (h₁ : I₁.ofFiniteType) (h₂ : I₂.ofFiniteType) :
    Disjoint
      (Set.range (strictTransformMap I₁.subschemeι (I₁ ⊔ I₂).blowupMap
        (I₁ ⊔ I₂).support.compl))
      (Set.range (strictTransformMap I₂.subschemeι (I₁ ⊔ I₂).blowupMap
        (I₁ ⊔ I₂).support.compl)) := by
  have hKft : (I₁ ⊔ I₂).ofFiniteType := h₁.sup h₂
  have hU₀ : IsCompact (((I₁ ⊔ I₂).support.compl : X.Opens) : Set X) :=
    Scheme.IdealSheafData.isCompact_coe_compl_support hKft
  have := quasiCompact_strictTransformOpen_ι hKft hU₀ I₁
  have := quasiCompact_strictTransformOpen_ι hKft hU₀ I₂
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  obtain ⟨U', b, hbK, hb12, hxc⟩ :=
    Scheme.IdealSheafData.exists_mem_range_chart_sup I₁ I₂ x
  have hspan : ((I₁ ⊔ I₂).ideal U').map (CommRingCat.ofHom
      (AffineBlowup.awayAlgebraMap ((I₁ ⊔ I₂).ideal U')
        (reesX ((I₁ ⊔ I₂).ideal U') b hbK))).hom =
      Ideal.span {(CommRingCat.ofHom (AffineBlowup.awayAlgebraMap ((I₁ ⊔ I₂).ideal U')
        (reesX ((I₁ ⊔ I₂).ideal U') b hbK))).hom b} := by
    rw [CommRingCat.hom_ofHom]
    exact AffineBlowup.map_awayAlgebraMap_reesX_eq_span_singleton ((I₁ ⊔ I₂).ideal U') b hbK
  have hcomp := (I₁ ⊔ I₂).blowupChart_comp_blowupMap U' hbK
  rcases hb12 with hb | hb
  · exact Set.disjoint_left.mp
      (disjoint_range_strictTransformMap_of_probe
        (I₁ ⊔ I₂) I₁ U' b hb _ hspan _ hcomp) hx₁ hxc
  · exact Set.disjoint_left.mp
      (disjoint_range_strictTransformMap_of_probe
        (I₁ ⊔ I₂) I₂ U' b hb _ hspan _ hcomp) hx₂ hxc

end BoundarySeparation

end AlgebraicGeometry
