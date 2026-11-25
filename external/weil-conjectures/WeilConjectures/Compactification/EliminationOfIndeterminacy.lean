/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Blowup.Density
public import WeilConjectures.Blowup.PartialSectionExtension
public import WeilConjectures.Compactification.BoundaryPreparation
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!

# Elimination of indeterminacy

This file proves **elimination of indeterminacy** (Stacks Project Tag 081S; blueprint
chapter "Elimination of indeterminacy after Deligne and Conrad", `thm:081S`; proof order
item 30):

- `AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap`: if
  `q : Z ⟶ X` is separated, of finite type and an isomorphism over a quasi-compact open
  `U` of the qcqs scheme `X`, then after a `U`-admissible blow-up the strict transform of
  `q` is an open immersion.
- `AlgebraicGeometry.eliminationBlowup`: the blow-up `X^el(q, U) ⟶ X` of blueprint
  `theorem-elimination-indeterminacy--1`, assembled from its three steps
  (`eliminationBoundaryIdeal`, `eliminationExtensionCentre`, `eliminationCentre`), and
  `AlgebraicGeometry.isOpenImmersion_strictTransformMap_eliminationBlowup`: the strict
  transform along it is an open immersion.

This is the root of the modification layer: the transport of scheme-theoretic images
(`WeilConjectures.Compactification.ImageTransport`), common modifications
(`WeilConjectures.Compactification.CommonModification`), graph extensions
(`WeilConjectures.Compactification.GraphExtension`) and isomorphism near a boundary
closure (`WeilConjectures.Compactification.IsomorphismNearClosure`) are all consumers of
it, and the two-open compactification theorem (proof order items 43–48) consumes those.

## The route taken

The Stacks Project proves Tag 081S by Raynaud–Gruson flattening (Stacks Tags 0815 and
081R, together with 081P and 081L), but that chain — proof order items 25–29 — is *not*
the route taken here: it bottoms out in the dévissage sections of Stacks §§38.4–38.10,
which exist neither in Mathlib nor in the blueprint.

Tag 081S is formalized instead via **Conrad's Theorem 2.4 and Zariski's Main Theorem**,
written up in the blueprint chapter "Elimination of indeterminacy after Deligne and
Conrad" (proof order items 61–75). The statement of Conrad's Theorem 2.4 that this file
consumes is `AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection` of
`WeilConjectures.Blowup.PartialSectionExtension`, used here through its `U = V` corollary
`AlgebraicGeometry.exists_admissibleBlowup_extend_section` (Conrad's Remark 2.5). Both are
formalized: `exists_admissibleBlowup_extend_partialSection` is proved in
`WeilConjectures/Blowup/PartialSectionExtension.lean`, with the `U = V` corollary
`exists_admissibleBlowup_extend_section` in the same file. The external inputs of that
proof are ZMT, which is Mathlib's `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`,
and Stacks Tag 04II, formalized here as `exists_immersion_affineSpace_of_quasiAffine`
(`WeilConjectures/Mathlib/AlgebraicGeometry/AffineSpace.lean`); see the route revision
note in `blueprint/src/version/detailed/nagata/nagata_new_proof_order.md`.

The deduction of Tag 081S carried out here is: prepare a Cartier boundary
(`exists_admissibleBlowup_cartierBoundary`, Tag 080Y), so that `U` becomes
scheme-theoretically dense; extend the inverse of `q` over `U` to a section over an open
`W` of a second admissible blow-up, by Conrad's Remark 2.5; compose the two blow-ups
(`Scheme.IdealSheafData.exists_blowup_comp`, Tag 080B); and observe that the graph of the
extension, being closed and containing the scheme-theoretically dense `U`-graph, cuts out
the strict transform, which is therefore isomorphic to the open `W`.

Note that the two-open compactification theorem itself does not go through flattening
either way — it uses the boundary-separation route of
`WeilConjectures.Blowup.AdmissibleBlowup`.

The finite-type helper lemmas of the blueprint are already in Mathlib and are not
restated in this development: `lemma:nagata-proper-to-separated-target` is Mathlib's
`AlgebraicGeometry.IsProper.of_comp`, and the two halves of
`lemma:nagata-finite-type-to-separated-target` (hence also
`lemma:nagata-open-immersion-qc-over-separated-target`) are Mathlib's
`AlgebraicGeometry.locallyOfFiniteType_of_comp` and
`AlgebraicGeometry.QuasiCompact.of_comp` (the latter only needs the second leg
quasi-separated, which separatedness supplies).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ### The elimination-of-indeterminacy construction

The three steps of blueprint `theorem-elimination-indeterminacy--1`, each step selecting its
output from the corresponding step lemma. -/

section EliminationConstruction

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
  (hU : IsCompact (U : Set X))

/-- **Step 1 of the elimination construction: the boundary ideal** `𝓘₀`: a selected
finite-type ideal sheaf on `X` whose support is exactly the complement of the quasi-compact
open `U` (`Scheme.exists_finiteType_ideal_coe_support_eq_compl`, Stacks Project Tag 01PH).
Its blow-up `X₁ = Bl_{𝓘₀}(X)` is a `U`-admissible blow-up in which `U` is
scheme-theoretically dense. (blueprint: `theorem-elimination-indeterminacy--1`, step 1) -/
noncomputable def eliminationBoundaryIdeal : X.IdealSheafData :=
  (X.exists_finiteType_ideal_coe_support_eq_compl U hU).choose

lemma eliminationBoundaryIdeal_ofFiniteType : (eliminationBoundaryIdeal hU).ofFiniteType :=
  (X.exists_finiteType_ideal_coe_support_eq_compl U hU).choose_spec.1

lemma coe_support_eliminationBoundaryIdeal :
    ((eliminationBoundaryIdeal hU).support : Set X) = (U : Set X)ᶜ :=
  (X.exists_finiteType_ideal_coe_support_eq_compl U hU).choose_spec.2

lemma support_compl_eliminationBoundaryIdeal : (eliminationBoundaryIdeal hU).support.compl = U := by
  apply TopologicalSpace.Opens.ext
  change ((eliminationBoundaryIdeal hU).support : Set X)ᶜ = (U : Set X)
  rw [coe_support_eliminationBoundaryIdeal, compl_compl]

lemma disjoint_support_eliminationBoundaryIdeal :
    Disjoint (U : Set X) ((eliminationBoundaryIdeal hU).support : Set X) := by
  rw [coe_support_eliminationBoundaryIdeal]; exact disjoint_compl_right

lemma isProper_eliminationBoundaryIdeal_blowupMap :
    IsProper (eliminationBoundaryIdeal hU).blowupMap :=
  IsAdmissible.isProper_blowupMap
    ⟨_, eliminationBoundaryIdeal_ofFiniteType hU, disjoint_support_eliminationBoundaryIdeal hU⟩

lemma compactSpace_eliminationBoundaryIdeal_blowup :
    CompactSpace (eliminationBoundaryIdeal hU).blowup :=
  have := isProper_eliminationBoundaryIdeal_blowupMap hU
  QuasiCompact.compactSpace_of_compactSpace (eliminationBoundaryIdeal hU).blowupMap

lemma quasiSeparatedSpace_eliminationBoundaryIdeal_blowup :
    QuasiSeparatedSpace (eliminationBoundaryIdeal hU).blowup :=
  have := isProper_eliminationBoundaryIdeal_blowupMap hU
  quasiSeparatedSpace_of_quasiSeparated (eliminationBoundaryIdeal hU).blowupMap

lemma isCompact_preimage_eliminationBoundaryIdeal :
    IsCompact (((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U :
      (eliminationBoundaryIdeal hU).blowup.Opens) : Set (eliminationBoundaryIdeal hU).blowup) :=
  have := isProper_eliminationBoundaryIdeal_blowupMap hU
  QuasiCompact.isCompact_preimage (f := (eliminationBoundaryIdeal hU).blowupMap) _ U.isOpen hU

/-- In `X₁ = Bl_{𝓘₀}(X)` the open `U` is scheme-theoretically dense. -/
lemma isSchemeTheoreticallyDominant_eliminationBoundaryIdeal :
    IsSchemeTheoreticallyDominant ((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U :
      (eliminationBoundaryIdeal hU).blowup.Opens).ι := by
  have h := (eliminationBoundaryIdeal
    hU).isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support
  rwa [support_compl_eliminationBoundaryIdeal] at h

lemma dense_preimage_eliminationBoundaryIdeal :
    Dense (((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U :
      (eliminationBoundaryIdeal hU).blowup.Opens) : Set (eliminationBoundaryIdeal hU).blowup) := by
  have := isSchemeTheoreticallyDominant_eliminationBoundaryIdeal hU
  have := compactSpace_eliminationBoundaryIdeal_blowup hU
  have := quasiSeparatedSpace_eliminationBoundaryIdeal_blowup hU
  have : CompactSpace ((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U :
      (eliminationBoundaryIdeal hU).blowup.Opens).toScheme :=
    isCompact_iff_compactSpace.mp (isCompact_preimage_eliminationBoundaryIdeal hU)
  have : QuasiCompact ((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U :
      (eliminationBoundaryIdeal hU).blowup.Opens).ι := inferInstance
  have h := Scheme.Hom.denseRange ((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U :
    (eliminationBoundaryIdeal hU).blowup.Opens).ι
  rwa [DenseRange, Scheme.Opens.range_ι] at h

variable {Z : Scheme.{u}} (q : Z ⟶ X) (hq : IsIso (q ∣_ U))

/-- **Step 2 of the elimination construction, the quasi-domination**: over the preimage of `U`
in `X₁ = Bl_{𝓘₀}(X)`, the section of the base change `Z ×_X X₁ ⟶ X₁` induced by the inverse of
the isomorphism `q⁻¹(U) ≅ U`. (blueprint: `theorem-elimination-indeterminacy--1`, step 2) -/
noncomputable def eliminationGraphSection :
    ((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U :
      (eliminationBoundaryIdeal hU).blowup.Opens).toScheme ⟶
      pullback q (eliminationBoundaryIdeal hU).blowupMap :=
  pullback.lift (((eliminationBoundaryIdeal hU).blowupMap ∣_ U) ≫ inv (q ∣_ U) ≫ (q ⁻¹ᵁ U).ι)
    ((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U).ι (by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι q U, IsIso.inv_hom_id_assoc,
        morphismRestrict_ι])

lemma eliminationGraphSection_snd :
    eliminationGraphSection hU q hq ≫ pullback.snd q (eliminationBoundaryIdeal hU).blowupMap =
      ((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U).ι :=
  pullback.lift_snd _ _ _

lemma eliminationGraphSection_fst :
    eliminationGraphSection hU q hq ≫ pullback.fst q (eliminationBoundaryIdeal hU).blowupMap =
      ((eliminationBoundaryIdeal hU).blowupMap ∣_ U) ≫ inv (q ∣_ U) ≫ (q ⁻¹ᵁ U).ι :=
  pullback.lift_fst _ _ _

variable [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]

/-- **Conrad's extension step of the elimination construction** (Conrad's Remark 2.5,
`exists_admissibleBlowup_extend_section`, applied over `X₁ = Bl_{𝓘₀}(X)` to the graph section
`eliminationGraphSection`): an admissible blow-up of `X₁` together with an extension of the
graph section over an open `W` containing the preimage of `U`, whose graph is closed. -/
theorem exists_eliminationExtension :
    ∃ (B : IsAdmissible (eliminationBoundaryIdeal hU).blowup
        ((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U))
      (W : B.I.blowup.Opens)
      (hUW : B.I.blowupMap ⁻¹ᵁ ((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U) ≤ W)
      (g : W.toScheme ⟶ pullback q (eliminationBoundaryIdeal hU).blowupMap)
      (hg : g ≫ pullback.snd q (eliminationBoundaryIdeal hU).blowupMap = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ _) ≫ eliminationGraphSection hU q hq ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  have := compactSpace_eliminationBoundaryIdeal_blowup hU
  have := quasiSeparatedSpace_eliminationBoundaryIdeal_blowup hU
  set p := pullback.snd q (eliminationBoundaryIdeal hU).blowupMap
  have : IsSeparated p := MorphismProperty.pullback_snd _ _ ‹_›
  have : LocallyOfFiniteType p := MorphismProperty.pullback_snd _ _ ‹_›
  have : QuasiCompact p := MorphismProperty.pullback_snd _ _ ‹_›
  have : CompactSpace ↥(pullback q (eliminationBoundaryIdeal hU).blowupMap) :=
    QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace ↥(pullback q (eliminationBoundaryIdeal hU).blowupMap) :=
    quasiSeparatedSpace_of_quasiSeparated p
  exact exists_admissibleBlowup_extend_section (isCompact_preimage_eliminationBoundaryIdeal hU)
    (dense_preimage_eliminationBoundaryIdeal hU) (eliminationGraphSection hU q hq)
    (eliminationGraphSection_snd hU q hq)

/-- **Step 2 of the elimination construction: the Conrad extension centre** on
`X₁ = Bl_{𝓘₀}(X)`, the admissible blow-up centre selected from `exists_eliminationExtension`
(Conrad's elimination theorem over the base `X₁`, applied to the quasi-domination
`eliminationGraphSection`). (blueprint: `theorem-elimination-indeterminacy--1`, step 2) -/
noncomputable def eliminationExtensionCentre :
    IsAdmissible (eliminationBoundaryIdeal hU).blowup
      ((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U) :=
  (exists_eliminationExtension hU q hq).choose

/-- The selected Conrad extension centre extends the graph section over an open `W`, with
closed graph. -/
theorem eliminationExtensionCentre_spec :
    ∃ (W : (eliminationExtensionCentre hU q hq).I.blowup.Opens)
      (hUW : (eliminationExtensionCentre hU q hq).I.blowupMap ⁻¹ᵁ
        ((eliminationBoundaryIdeal hU).blowupMap ⁻¹ᵁ U) ≤ W)
      (g : W.toScheme ⟶ pullback q (eliminationBoundaryIdeal hU).blowupMap)
      (hg : g ≫ pullback.snd q (eliminationBoundaryIdeal hU).blowupMap =
        W.ι ≫ (eliminationExtensionCentre hU q hq).I.blowupMap),
      (eliminationExtensionCentre hU q hq).I.blowup.homOfLE hUW ≫ g =
          ((eliminationExtensionCentre hU q hq).I.blowupMap ∣_ _) ≫
            eliminationGraphSection hU q hq ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) :=
  (exists_eliminationExtension hU q hq).choose_spec

/-- **Step 3 of the elimination construction: the composite centre** `K` on `X`, selected from
the composition theorem for blow-ups (`Scheme.IdealSheafData.exists_blowup_comp`, Stacks
Project Tag 080B) applied to the boundary ideal `𝓘₀` and the Conrad extension centre on
`X₁ = Bl_{𝓘₀}(X)`; thus `Bl_K(X)` is identified over `X` with the composite of the two
blow-ups. (blueprint: `theorem-elimination-indeterminacy--1`, step 3) -/
noncomputable def eliminationCentre : X.IdealSheafData :=
  (Scheme.IdealSheafData.exists_blowup_comp (eliminationBoundaryIdeal hU)
    (eliminationBoundaryIdeal_ofFiniteType hU) (eliminationExtensionCentre hU q hq).I
    (eliminationExtensionCentre hU q hq).finiteType).choose

theorem eliminationCentre_spec :
    (eliminationCentre hU q hq).ofFiniteType ∧
      ((eliminationCentre hU q hq).support : Set X) =
        ((eliminationBoundaryIdeal hU).support : Set X) ∪ (eliminationBoundaryIdeal hU).blowupMap ''
          ((eliminationExtensionCentre hU q hq).I.support :
            Set (eliminationBoundaryIdeal hU).blowup) ∧
      ∃ e : (eliminationCentre hU q hq).blowup ≅ (eliminationExtensionCentre hU q hq).I.blowup,
        e.hom ≫ (eliminationExtensionCentre hU q hq).I.blowupMap ≫
          (eliminationBoundaryIdeal hU).blowupMap = (eliminationCentre hU q hq).blowupMap :=
  (Scheme.IdealSheafData.exists_blowup_comp (eliminationBoundaryIdeal hU)
    (eliminationBoundaryIdeal_ofFiniteType hU) (eliminationExtensionCentre hU q hq).I
    (eliminationExtensionCentre hU q hq).finiteType).choose_spec

/-- The support of the composite centre is exactly the complement of `U`: by the support
formula of Tag 080B it is `Uᶜ ∪ π₁(supp 𝓘) = Uᶜ`, since `𝓘` is `U`-admissible on `X₁`. -/
theorem coe_support_eliminationCentre :
    ((eliminationCentre hU q hq).support : Set X) = (U : Set X)ᶜ := by
  have hKsupp := (eliminationCentre_spec hU q hq).2.1
  have hdisj₁ := disjoint_support_eliminationBoundaryIdeal hU
  have hdisjK : Disjoint (U : Set X) ((eliminationCentre hU q hq).support : Set X) := by
    rw [Set.disjoint_left]
    intro x hxU hxK
    rw [hKsupp] at hxK
    rcases hxK with hxI | ⟨x', hx', hx'eq⟩
    · exact Set.disjoint_left.mp hdisj₁ hxU hxI
    · refine Set.disjoint_left.mp (eliminationExtensionCentre hU q hq).disjoint_support ?_ hx'
      have hx'U : (eliminationBoundaryIdeal hU).blowupMap x' ∈ U := by rw [hx'eq]; exact hxU
      exact hx'U
  have hsub : (U : Set X)ᶜ ⊆ ((eliminationCentre hU q hq).support : Set X) := by
    rw [hKsupp, ← coe_support_eliminationBoundaryIdeal hU]; exact Set.subset_union_left
  exact subset_antisymm (Set.disjoint_left.mp hdisjK.symm) hsub

/-- **The elimination-of-indeterminacy blow-up** `X^el(q, U) ⟶ X`: for a separated morphism
`q : Z ⟶ X` of finite type over a qcqs scheme `X` which is an isomorphism over a quasi-compact
open `U`, the `U`-admissible blow-up of `X` assembled from the blueprint's three steps:

1. the boundary ideal `𝓘₀` with support `Uᶜ` (`eliminationBoundaryIdeal`), whose blow-up
   `X₁ = Bl_{𝓘₀}(X)` makes `U` scheme-theoretically dense;
2. the Conrad extension centre `𝓘` on `X₁` (`eliminationExtensionCentre`), along which the
   quasi-domination `eliminationGraphSection` induced by `q⁻¹(U) ≅ U` extends;
3. the composite centre `K` on `X` (`eliminationCentre`) with `Bl_K(X) ≅ Bl_𝓘(X₁)` over `X`,
   whose support is exactly `Uᶜ` (`coe_support_eliminationCentre`).

Difference from the blueprint: in step 3 the blueprint blows up `𝓘 · 𝓘₀𝒪_{X₁}` on `X₁`
(which dominates `Bl_𝓘(X₁)`) and then composes with `X₁ ⟶ X`. The formalization composes
`𝓘` itself with `𝓘₀`, so that `Bl_K(X) ≅ Bl_𝓘(X₁)` and the extension of the quasi-domination
lives directly on it; the support formula of Tag 080B already gives the support `Uᶜ`, and
the scheme-theoretic density of `U` in `Bl_K(X)` follows from that alone
(`isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support`).
(blueprint: `theorem-elimination-indeterminacy--1`) -/
noncomputable def eliminationBlowup : IsAdmissible X U where
  I := eliminationCentre hU q hq
  finiteType := (eliminationCentre_spec hU q hq).1
  disjoint_support := by rw [coe_support_eliminationCentre]; exact disjoint_compl_right

lemma eliminationBlowup_I : (eliminationBlowup hU q hq).I = eliminationCentre hU q hq := rfl


end EliminationConstruction

/-- The final step of elimination of indeterminacy, for arbitrary data of the shape produced
by the three steps of the construction: a modification `π₁ : Y₁ ⟶ X` with a section `f₁` of the
base change of `q` over the preimage of `U`, a second modification `π₂ : Y₂ ⟶ Y₁` with an
extension `g` of `f₁` over an open `W ⊇ π₂⁻¹(π₁⁻¹(U))` with closed graph, and a finite-type
ideal `K` with support `Uᶜ` whose blow-up is identified with `Y₂` over `X`. Then the strict
transform of `q` along `Bl_K(X) ⟶ X` is an open immersion: the graph of the extension is
closed and contains the scheme-theoretically dense `U`-graph, so it cuts out the strict
transform, which is therefore isomorphic to the open `W`. -/
theorem isOpenImmersion_strictTransformMap_of_extension {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {U : X.Opens} (hU : IsCompact (U : Set X)) {Z : Scheme.{u}}
    (q : Z ⟶ X) [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q] (hq : IsIso (q ∣_ U))
    {Y₁ Y₂ : Scheme.{u}} (π₁ : Y₁ ⟶ X) (π₂ : Y₂ ⟶ Y₁)
    (f₁ : (π₁ ⁻¹ᵁ U : Y₁.Opens).toScheme ⟶ pullback q π₁)
    (hf₁fst : f₁ ≫ pullback.fst q π₁ = (π₁ ∣_ U) ≫ inv (q ∣_ U) ≫ (q ⁻¹ᵁ U).ι)
    (W : Y₂.Opens) (hUW : π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) ≤ W) (g : W.toScheme ⟶ pullback q π₁)
    (hg : g ≫ pullback.snd q π₁ = W.ι ≫ π₂) (hext : Y₂.homOfLE hUW ≫ g = (π₂ ∣_ _) ≫ f₁)
    (hclosed : IsClosed (Set.range (pullback.lift g W.ι hg)))
    (K : X.IdealSheafData) (hKft : K.ofFiniteType) (hKsupp : (K.support : Set X) = (U : Set X)ᶜ)
    (e : K.blowup ≅ Y₂) (he : e.hom ≫ π₂ ≫ π₁ = K.blowupMap) :
    IsOpenImmersion (strictTransformMap q K.blowupMap U) := by
  set s : U.toScheme ⟶ Z := inv (q ∣_ U) ≫ (q ⁻¹ᵁ U).ι with hsdef
  set p : pullback q π₁ ⟶ Y₁ := pullback.snd q π₁ with hpdef
  have hdisjK : Disjoint (U : Set X) (K.support : Set X) := by
    rw [hKsupp]; exact disjoint_compl_right
  have hKcompl : K.support.compl = U := by
    apply TopologicalSpace.Opens.ext
    change (K.support : Set X)ᶜ = (U : Set X)
    rw [hKsupp, compl_compl]
  set π : K.blowup ⟶ X := K.blowupMap with hπdef
  have hproperK : IsProper π := IsAdmissible.isProper_blowupMap ⟨K, hKft, hdisjK⟩
  have : QuasiCompact π := inferInstance
  have : IsSeparated π := inferInstance
  have : CompactSpace K.blowup := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace K.blowup := quasiSeparatedSpace_of_quasiSeparated π
  have hisoπ : IsIso (π ∣_ U) := IsAdmissible.isIso_blowupMap_restrict ⟨K, hKft, hdisjK⟩
  -- `U` is scheme-theoretically dense in the composite blow-up
  have hstdK : IsSchemeTheoreticallyDominant (π ⁻¹ᵁ U : K.blowup.Opens).ι := by
    have h := K.isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support
    rwa [hKcompl] at h
  have hcptV : IsCompact ((π ⁻¹ᵁ U : K.blowup.Opens) : Set K.blowup) :=
    QuasiCompact.isCompact_preimage (f := π) _ U.isOpen hU
  have : CompactSpace (π ⁻¹ᵁ U : K.blowup.Opens).toScheme := isCompact_iff_compactSpace.mp hcptV
  have : QuasiCompact (π ⁻¹ᵁ U : K.blowup.Opens).ι := inferInstance
  -- the preimage of `U` in the composite blow-up lands in the transported open `W`
  have hmem : ∀ y : K.blowup, y ∈ (π ⁻¹ᵁ U : K.blowup.Opens) →
      e.hom y ∈ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : Y₂.Opens) := by
    intro y hy
    change π₁ (π₂ (e.hom y)) ∈ U
    have h1 : π y = π₁ (π₂ (e.hom y)) := by
      conv_lhs => rw [← he]
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact h1 ▸ hy
  have hV₀ : (π ⁻¹ᵁ U : K.blowup.Opens) ≤ e.hom ⁻¹ᵁ W := fun y hy => hUW (hmem y hy)
  -- the open locus over `U` is the preimage of `U`, since `q` and `π` are isomorphisms there
  set ρ : (strictTransformOpen q π U).toScheme ⟶ (π ⁻¹ᵁ U : K.blowup.Opens).toScheme :=
    pullback.snd q π ∣_ (π ⁻¹ᵁ U) with hρdef
  have hρι : ρ ≫ (π ⁻¹ᵁ U : K.blowup.Opens).ι =
      (strictTransformOpen q π U).ι ≫ pullback.snd q π := morphismRestrict_ι _ _
  set ω : (strictTransformOpen q π U).toScheme ≅ (q ⁻¹ᵁ U).toScheme :=
    (isPullback_strictTransformOpen q π U).isoIsPullback _ _
      (isPullback_morphismRestrict q U).flip with hωdef
  have hωfst : ω.hom ≫ (q ⁻¹ᵁ U).ι = (strictTransformOpen q π U).ι ≫ pullback.fst q π := by
    rw [hωdef]; exact IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hωsnd : ω.hom ≫ (q ∣_ U) = ρ ≫ (π ∣_ U) := by
    rw [hωdef]; exact IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hρiso : IsIso ρ := by
    have h1 : ρ = ω.hom ≫ (q ∣_ U) ≫ inv (π ∣_ U) := by
      rw [← Category.assoc, hωsnd, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [h1]; infer_instance
  -- the preimage of `U`, transported into the blow-up of the second centre
  have hrangeν : Set.range ((π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom) ⊆
      Set.range (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : Y₂.Opens).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    refine hmem _ ?_
    have h := Set.mem_range_self (f := ⇑(π ⁻¹ᵁ U : K.blowup.Opens).ι) y
    rwa [Scheme.Opens.range_ι] at h
  set ν : (π ⁻¹ᵁ U : K.blowup.Opens).toScheme ⟶ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : Y₂.Opens).toScheme :=
    IsOpenImmersion.lift (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : Y₂.Opens).ι
      ((π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom) hrangeν with hνdef
  have hνι : ν ≫ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : Y₂.Opens).ι =
      (π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom := IsOpenImmersion.lift_fac _ _ _
  have hνπ : ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ∣_ U) = π ∣_ U := by
    rw [← cancel_mono U.ι]
    calc (ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ∣_ U)) ≫ U.ι
        = ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ∣_ U) ≫ U.ι := by simp only [Category.assoc]
      _ = ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ⁻¹ᵁ U : Y₁.Opens).ι ≫ π₁ := by
          rw [morphismRestrict_ι]
      _ = (ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ⁻¹ᵁ U : Y₁.Opens).ι) ≫ π₁ := by
          simp only [Category.assoc]
      _ = (ν ≫ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : Y₂.Opens).ι ≫ π₂) ≫ π₁ := by
          rw [morphismRestrict_ι]
      _ = ((ν ≫ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : Y₂.Opens).ι) ≫ π₂) ≫ π₁ := by
          simp only [Category.assoc]
      _ = (((π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom) ≫ π₂) ≫ π₁ := by rw [hνι]
      _ = (π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom ≫ π₂ ≫ π₁ := by simp only [Category.assoc]
      _ = (π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ π := by rw [he]
      _ = (π ∣_ U) ≫ U.ι := by rw [morphismRestrict_ι]
  have hνW : K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W) = ν ≫ Y₂.homOfLE hUW := by
    rw [← cancel_mono W.ι]
    calc (K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W)) ≫ W.ι
        = K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W) ≫ W.ι := by simp only [Category.assoc]
      _ = K.blowup.homOfLE hV₀ ≫ (e.hom ⁻¹ᵁ W).ι ≫ e.hom := by rw [morphismRestrict_ι]
      _ = (K.blowup.homOfLE hV₀ ≫ (e.hom ⁻¹ᵁ W).ι) ≫ e.hom := by simp only [Category.assoc]
      _ = (π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom := by rw [Scheme.homOfLE_ι]
      _ = ν ≫ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : Y₂.Opens).ι := by rw [hνι]
      _ = ν ≫ Y₂.homOfLE hUW ≫ W.ι := by rw [Scheme.homOfLE_ι]
      _ = (ν ≫ Y₂.homOfLE hUW) ≫ W.ι := by simp only [Category.assoc]
  have hgU : K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁ = (π ∣_ U) ≫ s := by
    calc K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁
        = (K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W)) ≫ g ≫ pullback.fst q π₁ := by
          simp only [Category.assoc]
      _ = (ν ≫ Y₂.homOfLE hUW) ≫ g ≫ pullback.fst q π₁ := by rw [hνW]
      _ = ν ≫ (Y₂.homOfLE hUW ≫ g) ≫ pullback.fst q π₁ := by
          simp only [Category.assoc]
      _ = ν ≫ ((π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ f₁) ≫ pullback.fst q π₁ := by rw [hext]
      _ = (ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U))) ≫ f₁ ≫ pullback.fst q π₁ := by simp only [Category.assoc]
      _ = (ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U))) ≫ (π₁ ∣_ U) ≫ s := by rw [hf₁fst]
      _ = (ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ∣_ U)) ≫ s := by simp only [Category.assoc]
      _ = (π ∣_ U) ≫ s := by rw [hνπ]
  -- the comparison of the two fibre products
  have hbig : IsPullback (pullback.fst p π₂ ≫ pullback.fst q π₁)
      (pullback.snd p π₂ ≫ e.inv) q π := by
    have h0 : IsPullback (𝟙 (pullback p π₂)) (pullback.snd p π₂ ≫ e.inv)
        (pullback.snd p π₂) e.hom := IsPullback.of_horiz_isIso ⟨by simp⟩
    have h12 := (IsPullback.of_hasPullback p π₂).paste_horiz (IsPullback.of_hasPullback q π₁)
    have h := h0.paste_horiz h12
    rwa [Category.id_comp, he] at h
  set E : pullback p π₂ ≅ pullback q π :=
    hbig.isoIsPullback _ _ (IsPullback.of_hasPullback q π) with hEdef
  have hEfst : E.hom ≫ pullback.fst q π = pullback.fst p π₂ ≫ pullback.fst q π₁ := by
    rw [hEdef]; exact IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hEsnd : E.hom ≫ pullback.snd q π = pullback.snd p π₂ ≫ e.inv := by
    rw [hEdef]; exact IsPullback.isoIsPullback_hom_snd _ _ _ _
  -- the graph of the extension is a closed immersion
  set Γ : W.toScheme ⟶ pullback p π₂ := pullback.lift g W.ι hg with hΓdef
  have hΓsnd : Γ ≫ pullback.snd p π₂ = W.ι := pullback.lift_snd _ _ _
  have hΓfst : Γ ≫ pullback.fst p π₂ = g := pullback.lift_fst _ _ _
  have hΓimm : IsImmersion (Γ ≫ pullback.snd p π₂) := by rw [hΓsnd]; infer_instance
  have : IsImmersion Γ := IsImmersion.of_comp Γ (pullback.snd p π₂)
  have hΓci : IsClosedImmersion Γ := IsClosedImmersion.of_isPreimmersion Γ hclosed
  set ψ : (e.hom ⁻¹ᵁ W).toScheme ⟶ pullback q π := (e.hom ∣_ W) ≫ Γ ≫ E.hom with hψdef
  have hψci : IsClosedImmersion ψ := by rw [hψdef]; infer_instance
  have hψsnd : ψ ≫ pullback.snd q π = (e.hom ⁻¹ᵁ W).ι := by
    calc ψ ≫ pullback.snd q π
        = (e.hom ∣_ W) ≫ Γ ≫ E.hom ≫ pullback.snd q π := by
          rw [hψdef]; simp only [Category.assoc]
      _ = (e.hom ∣_ W) ≫ Γ ≫ pullback.snd p π₂ ≫ e.inv := by rw [hEsnd]
      _ = (e.hom ∣_ W) ≫ (Γ ≫ pullback.snd p π₂) ≫ e.inv := by simp only [Category.assoc]
      _ = (e.hom ∣_ W) ≫ W.ι ≫ e.inv := by rw [hΓsnd]
      _ = ((e.hom ∣_ W) ≫ W.ι) ≫ e.inv := by simp only [Category.assoc]
      _ = ((e.hom ⁻¹ᵁ W).ι ≫ e.hom) ≫ e.inv := by rw [morphismRestrict_ι]
      _ = (e.hom ⁻¹ᵁ W).ι := by simp
  have hψfst : ψ ≫ pullback.fst q π = (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁ := by
    calc ψ ≫ pullback.fst q π
        = (e.hom ∣_ W) ≫ Γ ≫ E.hom ≫ pullback.fst q π := by
          rw [hψdef]; simp only [Category.assoc]
      _ = (e.hom ∣_ W) ≫ Γ ≫ pullback.fst p π₂ ≫ pullback.fst q π₁ := by rw [hEfst]
      _ = (e.hom ∣_ W) ≫ (Γ ≫ pullback.fst p π₂) ≫ pullback.fst q π₁ := by
          simp only [Category.assoc]
      _ = (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁ := by rw [hΓfst]
  -- the open locus over `U` sits scheme-theoretically densely inside the graph
  set θ : (strictTransformOpen q π U).toScheme ⟶ (e.hom ⁻¹ᵁ W).toScheme :=
    ρ ≫ K.blowup.homOfLE hV₀ with hθdef
  have hstdLE : IsSchemeTheoreticallyDominant (K.blowup.homOfLE hV₀) :=
    IsSchemeTheoreticallyDominant.homOfLE hV₀
  have hθstd : IsSchemeTheoreticallyDominant θ := by rw [hθdef]; infer_instance
  have hθW : θ ≫ (e.hom ⁻¹ᵁ W).ι = (strictTransformOpen q π U).ι ≫ pullback.snd q π := by
    calc θ ≫ (e.hom ⁻¹ᵁ W).ι
        = ρ ≫ K.blowup.homOfLE hV₀ ≫ (e.hom ⁻¹ᵁ W).ι := by
          rw [hθdef]; simp only [Category.assoc]
      _ = ρ ≫ (π ⁻¹ᵁ U : K.blowup.Opens).ι := by rw [Scheme.homOfLE_ι]
      _ = (strictTransformOpen q π U).ι ≫ pullback.snd q π := hρι
  have hθfst : θ ≫ (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁ =
      (strictTransformOpen q π U).ι ≫ pullback.fst q π := by
    calc θ ≫ (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁
        = ρ ≫ K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁ := by
          rw [hθdef]; simp only [Category.assoc]
      _ = ρ ≫ (π ∣_ U) ≫ s := by rw [hgU]
      _ = (ρ ≫ (π ∣_ U)) ≫ s := by simp only [Category.assoc]
      _ = (ω.hom ≫ (q ∣_ U)) ≫ s := by rw [← hωsnd]
      _ = ω.hom ≫ (q ∣_ U) ≫ inv (q ∣_ U) ≫ (q ⁻¹ᵁ U).ι := by
          rw [hsdef]; simp only [Category.assoc]
      _ = ω.hom ≫ (q ⁻¹ᵁ U).ι := by rw [IsIso.hom_inv_id_assoc]
      _ = (strictTransformOpen q π U).ι ≫ pullback.fst q π := hωfst
  have hθψ : θ ≫ ψ = (strictTransformOpen q π U).ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hψfst]; exact hθfst
    · rw [Category.assoc, hψsnd]; exact hθW
  -- the strict transform is cut out by the graph, hence isomorphic to the open `W`
  have hker : (strictTransformι q π U).ker = ψ.ker := by
    rw [ker_strictTransformι, ← hθψ]
    exact Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant θ ψ
  set α := IsClosedImmersion.lift (strictTransformι q π U) ψ hker.le with hαdef
  have hαiso : IsIso α := IsClosedImmersion.isIso_lift (strictTransformι q π U) ψ hker
  have hα : α ≫ strictTransformι q π U = ψ := IsClosedImmersion.lift_fac _ _ _
  have hfinal : α ≫ strictTransformMap q π U = (e.hom ⁻¹ᵁ W).ι := by
    rw [strictTransformMap, ← Category.assoc, hα, hψsnd]
  have hrw : strictTransformMap q π U = inv α ≫ (e.hom ⁻¹ᵁ W).ι := by
    rw [← hfinal, IsIso.inv_hom_id_assoc]
  rw [hrw]
  infer_instance

/-- **Elimination of indeterminacy for the constructed blow-up** (Stacks Project Tag 081S;
blueprint: `theorem-elimination-indeterminacy`; proof order item 30): the strict transform
of `q` along `AlgebraicGeometry.eliminationBlowup` is an open immersion.

The proof follows the Conrad/Zariski's-Main-Theorem route along the three steps of the
construction: in `X₁ = Bl_{𝓘₀}(X)` the open `U` is scheme-theoretically dense; the graph
section extends over an open `W` of the Conrad blow-up `Bl_𝓘(X₁)`; and, transporting along
`Bl_K(X) ≅ Bl_𝓘(X₁)`, the graph of the extension cuts out the strict transform
(`isOpenImmersion_strictTransformMap_of_extension`). -/
theorem isOpenImmersion_strictTransformMap_eliminationBlowup {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {U : X.Opens} (hU : IsCompact (U : Set X)) {Z : Scheme.{u}}
    (q : Z ⟶ X) [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q] (hq : IsIso (q ∣_ U)) :
    IsOpenImmersion (strictTransformMap q (eliminationBlowup hU q hq).I.blowupMap
      (eliminationBlowup hU q hq).preservedOpen) := by
  obtain ⟨W, hUW, g, hg, hext, hclosed⟩ := eliminationExtensionCentre_spec hU q hq
  obtain ⟨hKft, -, e, he⟩ := eliminationCentre_spec hU q hq
  have hKsupp := coe_support_eliminationCentre hU q hq
  have hKcompl : (eliminationCentre hU q hq).support.compl = U := by
    apply TopologicalSpace.Opens.ext
    change ((eliminationCentre hU q hq).support : Set X)ᶜ = (U : Set X)
    rw [hKsupp, compl_compl]
  change IsOpenImmersion (strictTransformMap q (eliminationCentre hU q hq).blowupMap
    (eliminationCentre hU q hq).support.compl)
  rw [hKcompl]
  exact isOpenImmersion_strictTransformMap_of_extension hU q hq _ _ _
    (eliminationGraphSection_fst hU q hq) W hUW g hg hext hclosed _ hKft hKsupp e he

/-- **Elimination of indeterminacy** (Stacks Project Tag 081S; blueprint:
`lemma:nagata-elimination-indeterminacy`; proof order item 30): if `q : Z ⟶ X` is separated,
of finite type and an isomorphism over a quasi-compact open `U` of the qcqs scheme `X`, then
after a `U`-admissible blow-up the strict transform of `q` is an open immersion. A witness is
the constructed blow-up `AlgebraicGeometry.eliminationBlowup`
(`isOpenImmersion_strictTransformMap_eliminationBlowup`). -/
theorem exists_admissibleBlowup_isOpenImmersion_strictTransformMap
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) {Z : Scheme.{u}} (q : Z ⟶ X)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    (hq : IsIso (q ∣_ U)) :
    ∃ B : IsAdmissible X U,
      IsOpenImmersion (strictTransformMap q B.I.blowupMap B.preservedOpen) :=
  ⟨eliminationBlowup hU q hq, isOpenImmersion_strictTransformMap_eliminationBlowup hU q hq⟩

end AlgebraicGeometry
