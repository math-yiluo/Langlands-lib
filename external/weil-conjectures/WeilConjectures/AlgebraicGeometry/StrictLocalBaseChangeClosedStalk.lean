/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Square

/-! # The strict-local base-change mate on the closed stalk

Source: Stacks Project, Tags 03Q9 and 03QO.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme

/-- An invertible map on sections induces an invertible closed geometric stalk map.
This is the naturality argument of Stacks Project, Tag 03QO, followed by the
field-extension comparison of Tags 03PN and 03Q1. -/
private theorem closedStalk_isIso_of_sections
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    {k : Type u} [Field k] [IsSepClosed k]
    (a : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    {F H : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ H) [IsIso ((Sheaf.Γ _ AddCommGrpCat.{u + 1}).map φ)] :
    IsIso ((pointSmallEtale
      (a ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).sheafFiber.map φ) := by
  let t := a ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let c := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have ht : (c ≫ t) default = IsLocalRing.closedPoint A := by
    change (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
      ((c ≫ a) default) = _
    exact IsLocalRing.PrimeSpectrum.comap_residue A _
  have hA : IsStrictlyHenselianLocalRing A := ⟨inferInstance⟩
  obtain ⟨hgerm, hnat⟩ := strictlyHenselianSections_geometricStalk_isIso.{u, u}
    hA (c ≫ t) ht
  let T := Scheme.Etale.mk (𝟙 (Spec (.of A)))
  have hsections : IsIso (φ.hom.app (Opposite.op T)) := by
    exact (NatIso.isIso_map_iff
      (Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{u + 1}
        (MorphismProperty.Over.mkIdTerminal _ _)) φ).mp inferInstance
  have hF := hgerm F
  have hH := hgerm H
  have hstalk : IsIso ((pointSmallEtale (c ≫ t)).sheafFiber.map φ) := by
    rw [← isIso_comp_left_iff
      ((pointSmallEtale (c ≫ t)).toPresheafFiber T
        (Over.homMk (c ≫ t) (Category.comp_id _)) F.obj), hnat F H φ]
    infer_instance
  have hcompF := isIso_pointSmallEtalePrecomp_sheafFiber t c F
  have hcompH := isIso_pointSmallEtalePrecomp_sheafFiber t c H
  have hn := (pointSmallEtalePrecomp t c).sheafFiber.naturality φ
  rw [← isIso_comp_right_iff _
    ((pointSmallEtalePrecomp t c).sheafFiber.app H), hn]
  infer_instance

/-- On the closed stalk of any chosen strict-henselization model, homology of the
base-change mate is invertible. This concerns only the single lower cartesian square;
it does not involve a cube or any further inverse image.
Source: Stacks Project, Tag 03Q9 (theorem-higher-direct-images), restriction of injective
section complexes, and Tag 03QO (lemma-cohomology-strictly-henselian).
(blueprint: lem-weil-pbc-strict-local-base-change-closed-stalk).

Proof:
1. Apply `isIso_strictHenselization_baseChange_globalHomology` to f, s, G[0], and q.
The canonical derived mate there equals `derivedBaseChangeMapPlus`: compare their
components on bounded-below complexes using `Adjunction.derivedPlus_mateEquiv_app_fac`
and `pullbackSquareComparison_hom_app_factorsh`, then use
`derivedBaseChangeMapPlus_ext`. Thus global sections of homology of the canonical
strict-local base-change map are invertible, without a torsion assumption.
2. Put j = strictLocalizationToBase s, P = pullback f j, p = pullback.fst f j,
and v = pullback.snd f j. The map b : X₀ → P is the pullback lift of p₀ and f₀ ≫ eA.hom.
It satisfies b ≫ p = p₀ and b ≫ v = f₀ ≫ eA.hom. Pullback cancellation gives the
cartesian square (b, f₀, v, eA.hom); because eA.hom is invertible, b is invertible too.
Its derived base-change map is invertible: inverse image along an isomorphism is an
exact equivalence preserving injectives, so `derivedBaseChangeMapPlus_fac_app` on an
injective representative expresses this map as a composite of isomorphisms.
3. The horizontal pasting formula writes the outer mate at K = G[0] as
C(eA.hom,j).hom followed by D(eA.hom) of the canonical mate, the mate of the square
in step 2 at D(p)K, and R(f₀) of C(b,p).inv. Here C is `upperStarCompDerivedPlus`;
the equation b ≫ p = p₀ identifies the outer square with sq₀. Global sections after
inverse image along eA.hom are naturally isomorphic to global sections before it:
whisker the invertible adjunction unit with global sections, and apply
`lowerStarCompGlobalSectionsIso`. Homology commutes with exact inverse image by
`mapDerivedCategoryPlusHomologyFunctorIso`. Consequently the middle factor remains
invertible after global sections of homology, by step 1. All other factors are images
of isomorphisms under functors. Thus global sections of homology of the sq₀ mate are
invertible.
4. The point t = a followed by the residue closed-point map lies over the closed point
of Spec A (`IsLocalRing.PrimeSpectrum.comap_residue`). Enlarge k to AlgebraicClosure k.
`isIso_pointSmallEtalePrecomp_sheafFiber` and its naturality identify stalk maps before
and after this enlargement. Apply `strictlyHenselianSections_geometricStalk_isIso` to
the enlarged point and both homology sheaves. Its naturality states that the source
global germ followed by the stalk map is the section map followed by the target global
germ. The section map is invertible by step 3, using `ΓNatIsoSheafSections`. Both germs
are invertible by 03QO. Cancel the source germ, then the field-extension comparison,
to obtain invertibility of the displayed stalk map.
The argument applies to q = 0, zero sheaves, and empty total spaces; no relation of the
chosen point field k to Ω is required. -/
theorem isIso_strictHenselization_baseChange_closedStalk
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (eA : Spec (.of A) ≅ strictLocalization s)
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictLocalizationToBase s))
    {k : Type u} [Field k] [IsSepClosed k]
    (a : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIso ((pointSmallEtale
      (a ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) := by
  have := isIso_strictHenselization_baseChange_modelGlobalHomology
    f s eA p₀ f₀ sq₀ ((DerivedCategory.Plus.singleFunctor _ 0).obj G) (q : ℤ)
  exact closedStalk_isIso_of_sections a _

end AlgebraicGeometry.Etale
