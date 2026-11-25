/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedFiberComparison
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Lifting geometric specializations to strict local schemes

Source: Stacks Project, Tag 0GJ5, remark-can-lift
(blueprint: lem-weil-pbc-geometric-specialization-strict-local-lift).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A prescribed geometric generization lifts through the structural map of the strict
henselization at the specialized geometric point.
Source: Stacks Project, Tag 0GJ5, remark-can-lift
(blueprint: lem-weil-pbc-geometric-specialization-strict-local-lift).

Proof:
1. The strict henselization is local and its closed point maps to s, by
`strictHenselizationResidue`. Choose an affine open chart containing s. Every point
of a local spectrum generalizes its closed point, so the structural morphism factors
through this chart.
2. `smallStrictHenselization_indEtale_of_affine_chart` makes the resulting chart ring map
ind-etale, hence weakly etale. Composing with the open immersion shows that the
structural morphism is weakly etale and in particular flat.
3. Flat morphisms lift generalizations. Lift t along the structural morphism starting
at its closed point, obtaining an ordinary point x above t.
4. The fibre product with barT has a point above x and the unique point of Spec Ωt.
Its projection to Spec Ωt is weakly etale by base change, hence has a section by
`exists_comp_eq_id_of_weaklyEtale`. Compose this section with the other projection.
The pullback identity and section equation give exactly the prescribed barT. -/
theorem exists_geometricPoint_strictHenselization_lift
    {S : Scheme.{u}} (t s : S) (hts : t ⤳ s)
    {Ωt Ωs : Type u} [Field Ωt] [IsAlgClosed Ωt] [Field Ωs] [IsAlgClosed Ωs]
    (barT : Spec (.of Ωt) ⟶ S) (barS : Spec (.of Ωs) ⟶ S)
    (hbarT : barT (IsLocalRing.closedPoint Ωt) = t)
    (hbarS : barS (IsLocalRing.closedPoint Ωs) = s) :
    ∃ a : Spec (.of Ωt) ⟶ strictHenselizationScheme barS,
      a ≫ strictHenselizationStructuralMap barS = barT := by
  classical
  let : Algebra (S.residueField (barS (IsLocalRing.closedPoint Ωs))) Ωs :=
    (descResidueField (stalkClosedPointTo barS)).hom.toAlgebra
  obtain ⟨hlocal', -, hclosed', -⟩ := strictHenselizationResidue barS rfl
  obtain ⟨hlocal, -⟩ := strictHenselizationLocalStructure barS
  let := hlocal
  let := hlocal'
  let H := strictHenselizationRing barS
  let p := strictHenselizationStructuralMap barS
  have hclosed : p (IsLocalRing.closedPoint H) = barS (IsLocalRing.closedPoint Ωs) := by
    have h2 : (Spec.map (smallStrictHenselizationColimitIso barS).inv ≫
        strictLocalizationToBase barS) (IsLocalRing.closedPoint H) =
          barS (IsLocalRing.closedPoint Ωs) := by
      rw [Scheme.Hom.comp_apply]
      erw [@Spec_closedPoint _ _ hlocal' hlocal (smallStrictHenselizationColimitIso barS).inv
        inferInstance]
      exact hclosed'
    rwa [smallStrictHenselizationColimitIso_toBase barS] at h2
  have hpclosed : p (IsLocalRing.closedPoint H) = s := hclosed.trans hbarS
  obtain ⟨R, i, hi, hs, -⟩ :=
    exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) (by trivial)
  let := hi
  have hp : Set.range p ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map p.continuous).mem_open
      i.opensRange.isOpen (by
        change p (IsLocalRing.closedPoint H) ∈ Set.range i
        rw [hpclosed]
        exact hs)
  let g : strictHenselizationScheme barS ⟶ Spec R := IsOpenImmersion.lift i p hp
  have hg : g ≫ i = p := IsOpenImmersion.lift_fac i p hp
  let b : R →+* H := (Spec.preimage g).hom
  have hb : Spec.map (CommRingCat.ofHom b) = g := Spec.map_preimage g
  let : Algebra R H := b.toAlgebra
  have : Algebra.IndEtale R H :=
    smallStrictHenselization_indEtale_of_affine_chart barS R i
      (by simpa only [hbarS] using hs) (Iso.refl _) b
      (by simpa only [hb, Iso.refl_hom, Category.id_comp] using hg)
  have : Algebra.WeaklyEtale R H := inferInstance
  have hw : WeaklyEtale g := by
    rw [← hb]
    exact weaklyEtale_SpecMap_algebraMap
  have : WeaklyEtale p := by
    rw [← hg]
    infer_instance
  have hspec : t ⤳ p (IsLocalRing.closedPoint H) := hpclosed.symm ▸ hts
  obtain ⟨x, -, hpt⟩ := Flat.generalizingMap p hspec
  obtain ⟨v, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := barT) x
    (IsLocalRing.closedPoint Ωt) (hpt.trans hbarT.symm)
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale
    (Limits.pullback.snd p barT) v
  refine ⟨σ ≫ Limits.pullback.fst p barT, ?_⟩
  rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hσ, Category.id_comp]

end AlgebraicGeometry.Scheme
