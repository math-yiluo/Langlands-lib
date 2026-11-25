/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.NormalizationCover
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.IntegralEtaleNormalizationOpen

/-!
# An étale component is open in the normalization

Let `X` be a nonempty connected normal scheme of finite type over a field, and let
`Y₁ ⟶ X` be a separated étale morphism from a nonempty connected scheme.
The generic fibre of `Y₁ ⟶ X` is a single finite separable field extension of the
function field of `X`; the resulting normalization is finite over `X`, and `Y₁`
embeds in it as an open subscheme.

Source: blueprint lemma `lemma-geometric-coverings-normal-scheme--1`
(literature/blueprint/latest/blueprint/part-six-operations/
sec-reduction-finite-coefficients/sec-lattices/sk-lem-wrp-normal-geometric-cover/
det-wrp-cover-open-immersion.md and its `.proof.md`), with Stacks Project Tags
035B, 0AVK, 05K0 and 0AB1 (blueprint: lemma-geometric-coverings-normal-scheme--1).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

open Scheme

/-- An étale connected component over a connected normal finite-type scheme is open in its
finite generic normalization.

Source: blueprint lemma `lemma-geometric-coverings-normal-scheme--1`
(literature/blueprint/latest/blueprint/part-six-operations/
sec-reduction-finite-coefficients/sec-lattices/sk-lem-wrp-normal-geometric-cover/
det-wrp-cover-open-immersion.proof.md, both paragraphs, and
sk-lem-wrp-normal-geometric-cover.proof.md, second and third paragraphs);
Stacks Project Tags 035B, 0AVK, 05K0 and 0AB1
(blueprint: lemma-geometric-coverings-normal-scheme--1).

Proof (the six steps of the node):
1. `X` is finite type over a field, hence Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`); by `rem-pc-regular-normal` (2) the
   Noetherian normal `X` is a finite disjoint union of normal integral clopen pieces, and
   nonempty connectedness leaves one, so `X` is integral.
2. Affine étale charts `Spec B ⟶ Spec A ⊆ X` of `Y₁` are Noetherian
   (`pqf-lem-affine-open-locnoeth`, `lem-weil-pbc-finite-type-algebra-noetherian`,
   `lem-weil-pbc-finite-type-over-noetherian`);
   `proposition-proper-direct-image-finite-coefficients` gives every point of `Y₁` a normal integral
   open neighbourhood (no quasi-compactness of `Y₁`).
3. Hence `Y₁` is normal and reduced, its irreducible components are disjoint and open,
   and connectedness leaves one: `Y₁` is integral.
4. The image of `p` is nonempty open (`lem-weil-pbc-etale-morphism-open-map`), so the
   generic point of `Y₁` lies over that of `X`; the generic fibre has charts
   `(A ∖ 0)⁻¹ B`, nonzero domains with one common generic point
   (`lem-sc-integral-function-field-affine-fraction`,
   `lem-weil-pbc-fibre-product-affine-spectra`), and is a disjoint union of spectra of
   finite separable extensions (`lem-weil-pbc-etale-fibre-discrete-separable-points`);
   irreducibility leaves one, `Spec L`.
5. `lem-fin-normalization-extension-finite` makes `X.normalizationIn L ⟶ X` finite.
6. `lem-sf-integral-etale-normalization-open` (`integral_etale_normalization_open`)
   applied to `p`, the generic-fibre isomorphism of step 4 and the finite normalization
   of step 5 gives the open immersion `f : Y₁ ⟶ X.normalizationIn L` over `X`. -/
theorem det_wrp_cover_open_immersion
    {k : Type u} [Field k] {X Y₁ : Scheme.{u}}
    [ConnectedSpace X]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    [ConnectedSpace Y₁] (p : Y₁ ⟶ X) [IsSeparated p] [Etale p] :
    ∃ hXI : IsIntegral X,
      letI : IsIntegral X := hXI
      IsIntegral Y₁ ∧
      (∀ y : Y₁, IsDomain (Y₁.presheaf.stalk y) ∧
        IsIntegrallyClosed (Y₁.presheaf.stalk y)) ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra X.functionField L),
        FiniteDimensional X.functionField L ∧ Algebra.IsSeparable X.functionField L ∧
        ∃ (e : pullback p X.fromSpecFunctionField ≅ Spec (.of L)),
          e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) =
            pullback.snd p X.fromSpecFunctionField ∧
          IsFinite (X.fromNormalizationIn L) ∧
          ∃ (f : Y₁ ⟶ X.normalizationIn L),
            f ≫ X.fromNormalizationIn L = p ∧ IsOpenImmersion f := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType aX
  have hdomX (x : X) : IsDomain (X.presheaf.stalk x) := (hX x).1
  let : IrreducibleSpace X := irreducibleSpace_of_isDomain_stalk X hdomX
  let : IsReduced X := isReduced_of_isReduced_stalk X
  let hXI : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  refine ⟨hXI, ?_⟩
  let : IsIntegral X := hXI
  let : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨hY, hYstalk⟩ :=
    Scheme.isIntegral_and_isIntegrallyClosed_stalk_of_etale p (fun x ↦ (hX x).2)
  have hYnormal := Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale p
    (fun x ↦ (hX x).2)
  refine ⟨hY, hYnormal, ?_⟩
  let : IsIntegral Y₁ := hY
  let : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsDominant p :=
    ⟨p.isOpenMap.isOpen_range.dense (Set.range_nonempty p)⟩
  have hgen : p (genericPoint Y₁) = genericPoint X := by
    apply ((genericPoint_spec X).eq _).symm
    have h := (genericPoint_spec Y₁).image p.continuous
    rwa [Set.image_univ, p.denseRange.closure_range] at h
  let φ : X.functionField ⟶ Y₁.functionField :=
    X.presheaf.stalkSpecializes (Inseparable.of_eq hgen).specializes ≫
      p.stalkMap (genericPoint Y₁)
  have hw : Y₁.fromSpecFunctionField ≫ p = Spec.map φ ≫ X.fromSpecFunctionField := by
    dsimp [φ, Scheme.fromSpecFunctionField]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  let G := pullback p X.fromSpecFunctionField
  let π : G ⟶ Spec X.functionField := pullback.snd p X.fromSpecFunctionField
  let g : Spec Y₁.functionField ⟶ G :=
    pullback.lift Y₁.fromSpecFunctionField (Spec.map φ) hw
  have : IsLocallyArtinian G := IsLocallyArtinian.of_locallyQuasiFinite π
  let z : G := g (IsLocalRing.closedPoint Y₁.functionField)
  have hz : pullback.fst p X.fromSpecFunctionField z = genericPoint Y₁ := by
    change (g ≫ pullback.fst p X.fromSpecFunctionField) _ = _
    rw [pullback.lift_fst]
    exact Y₁.fromSpecStalk_closedPoint
  have hzall (y : G) : z = y := by
    apply specializes_iff_eq.mp
    apply (pullback.fst p X.fromSpecFunctionField).isEmbedding.toIsInducing.specializes_iff.mp
    rw [hz]
    exact genericPoint_specializes _
  have : Subsingleton G := ⟨fun a b ↦ (hzall a).symm.trans (hzall b)⟩
  have : Nonempty G := ⟨z⟩
  have : IsReduced G := isReduced_of_etale π
  have : IrreducibleSpace G := ⟨inferInstance⟩
  have : IsIntegral G := isIntegral_of_irreducibleSpace_of_isReduced _
  let L := Γ(G, ⊤)
  let : Field L := (isField_of_isIntegral_of_subsingleton G).toField
  let d : X.functionField ⟶ .of L := (Scheme.ΓSpecIso X.functionField).inv ≫ π.appTop
  let : Algebra X.functionField L := d.hom.toAlgebra
  have hd : RingHom.Etale d.hom :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso X.functionField).inv))
      ((HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := π)).mp inferInstance)
  have : Algebra.Etale X.functionField L := RingHom.etale_algebraMap.mp hd
  have : Module.Finite X.functionField L :=
    Algebra.FormallyUnramified.finite_of_free _ _
  have : Algebra.IsSeparable X.functionField L :=
    (Algebra.FormallyEtale.iff_isSeparable _ _).mp inferInstance
  let e : G ≅ Spec (.of L) := G.isoSpec
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) = π := by
    change G.isoSpec.hom ≫ Spec.map d = π
    dsimp only [d]
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  have : IsFinite (X.fromNormalizationIn L) := X.isFinite_fromNormalizationIn L aX
  obtain ⟨j, hj, hjopen, -⟩ := integral_etale_normalization_open hX p
    hYnormal L e he
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨e, he, inferInstance, ?_⟩
  exact ⟨j, hj, hjopen⟩


end AlgebraicGeometry
