/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportAmplitude
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import WeilConjectures.AlgebraicGeometry.Proper.ProperBoundedConstructible
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Finiteness of finite-type direct images of constructible etale sheaves

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`sbc-thm-finiteness-finite-type.md` (blueprint: theorem-results-from-etale-theory).

The ordinary direct image requires no separatedness. For the compact-support clauses,
use the Nagata compactification already supplied by `compactSupportAmplitudeCompactification`.
On the degree-zero input this candidate agrees with compactification-independent compact
support by `proposition-construction-independence-rf-shriek--7`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem isBoundedConstructible_single
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    DerivedCategory.isBoundedConstructible Λ X
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
  have : Scheme.IsConstructibleSheaf F :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
  refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 ?_,
    0, 0, le_rfl, fun q hq ↦ ?_⟩
  · by_cases hq : q = 0
    · subst q
      have : Scheme.IsConstructibleSheaf ((𝟭 _).obj F) := ‹Scheme.IsConstructibleSheaf F›
      exact Scheme.IsConstructibleSheaf.of_iso
        ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm
    · exact Scheme.IsConstructibleSheaf.of_isZero (by
        rcases lt_or_gt_of_ne hq with hq | hq
        · exact _root_.DerivedCategory.isZero_of_isGE _ 0 q hq
        · exact _root_.DerivedCategory.isZero_of_isLE _ 0 q hq)
  · rcases hq with hq | hq
    · exact _root_.DerivedCategory.isZero_of_isGE _ 0 q hq
    · exact _root_.DerivedCategory.isZero_of_isLE _ 0 q hq

private theorem isBoundedConstructible_of_iso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    {K L : DerivedCategoryModule Λ X} (e : K ≅ L)
    (hL : DerivedCategory.isBoundedConstructible Λ X L) :
    DerivedCategory.isBoundedConstructible Λ X K := by
  obtain ⟨hc, a, b, hab, hv⟩ := hL
  refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 ?_,
    a, b, hab, fun q hq ↦ (hv q hq).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e)⟩
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
  exact Scheme.IsConstructibleSheaf.of_iso
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e).symm

/-- Direct image of a finite constructible etale module sheaf along a finite-type map of
finite-type schemes over a field is bounded constructible. For a separated map the compact
support direct image is also bounded constructible, and its cohomology vanishes above twice
a bound on the dimensions of the original geometric fibres.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/sbc-thm-finiteness-finite-type.md`
(blueprint: theorem-results-from-etale-theory).

Proof, following the node's five steps:
1. The coefficient convention gives a finite commutative ring killed by positive N invertible
in k, hence on every k-scheme. Place F in degree zero; it is bounded constructible by
`def-weil-pbc-constructible-complexes`. Apply `proposition-six-operations-dctf--2` to obtain
the ordinary direct-image assertion, including nonseparated maps.
2. For separated f, finite type over the Noetherian field makes X and Y Noetherian
(`lem-weil-pbc-finite-type-over-noetherian`); local Noetherianity makes Y quasi-separated
(`lem-weil-pbc-locally-noetherian-quasi-separated`). Use
`theorem-nagata-s-compactification-theorem--1` and `definition-compactification-refinement--1` to
factor f as an open immersion j followed by a proper r. Properness includes finite type
(`def-weil-proper-morphism`). Finite affine covers and the union of algebra generators show the
compactification is finite type over k, hence Noetherian. All three schemes admit finite Noetherian
affine covers. No bound on the compactified fibres is required.
3. By `proposition-six-operations-dctf--6`, j_!F is constructible. Place it in degree zero and apply
`theorem-results-from-etale-theory--3` to r to obtain bounded constructibility of Rr_*(j_!F).
4. By `proposition-construction-independence-rf-shriek`, the chosen candidate is Rr_* Dj_!. Its
localization normalization identifies Dj_!(F[0]) with (j_!F)[0]. The bounded-below comparison of
`proposition-construction-independence-rf-shriek--7` identifies this with
compactification-independent Rf_!F. Isomorphisms preserve cohomology, constructibility, and
vanishing, giving the second clause.
5. The additive order m of 1 in the finite ring is positive, divides N, and is its additive
exponent: multiplication by m kills each ring element, and any annihilator kills 1. This
also holds for the zero ring with m = 1. Since N is invertible, so is m on Y. Apply
`theorem-results-from-etale-theory--5` to F and the original geometric-fibre bound to obtain
R^q f_! F = 0 for q > 2d. -/
theorem finiteType_directImages_finiteConstructible
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (N : ℕ) (hΛ : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [LocallyOfFiniteType f] [QuasiCompact f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    DerivedCategory.isBoundedConstructible Λ Y
      ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((_root_.DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F)) ∧
    ∀ [IsSeparated f],
      DerivedCategory.isBoundedConstructible Λ Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
          (compactSupportAmplitudeCompactification k Y f)).obj
          ((_root_.DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F)) ∧
      ∀ (d : ℕ),
        (∀ y : Y, topologicalKrullDim
          (↑(pullback f (Spec.map (CommRingCat.ofHom
            (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
              Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞)) →
        ∀ (q : ℤ), 2 * (d : ℤ) < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor
            (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
              ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
                (compactSupportAmplitudeCompactification k Y f)).obj
                ((_root_.DerivedCategory.singleFunctor
                  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F))) := by
  have hsingle := isBoundedConstructible_single Λ X F hF
  refine ⟨?_, ?_⟩
  · exact isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
      k Λ N hΛ (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) f
      (inferInstance : f.IsOver (Spec (.of k))).1 _ hsingle
  · intro hf
    let c := compactSupportAmplitudeCompactification k Y f
    have : HasInvertibleExponent Λ (Spec (.of k)) :=
      ⟨N, hΛ.1, hΛ.2.2.1, hΛ.2.2.2⟩
    have : HasInvertibleExponent Λ Y := HasInvertibleExponent.of_hom
      (Y ↘ Spec (.of k))
    refine ⟨?_, fun d hd q hq ↦
      isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE
        k Λ X Y f d hd F q hq⟩
    have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
    have : Scheme.IsConstructibleSheaf F :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
    have hjF : Scheme.IsConstructibleEtaleModuleSheaf
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).obj F) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
        (Scheme.IsConstructibleSheaf.openImmersionLowerShriek c.i c.i.closedComplement
          c.i.range_closedComplement F)
    have hcoeff (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) :
        IsSmoothBaseChangeCoefficients N Λ T :=
      ⟨hΛ.1, hΛ.2.1, hΛ.2.2.1, by
        simpa only [map_natCast] using hΛ.2.2.2.map aT.appTop.hom⟩
    have hproper := isBoundedConstructible_rightDerivedLowerStar_of_proper Λ N
      (c.g ≫ (Y ↘ Spec (.of k))) (Y ↘ Spec (.of k)) c.g rfl
      (hcoeff _ (c.g ≫ (Y ↘ Spec (.of k)))) (hcoeff _ (Y ↘ Spec (.of k)))
      _ (isBoundedConstructible_single Λ c.Z _ hjF)
    let J := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i
    exact isBoundedConstructible_of_iso Λ Y
      ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) c.g).mapIso
        ((J.mapDerivedCategorySingleFunctor 0).app F)) hproper

end AlgebraicGeometry.Etale
