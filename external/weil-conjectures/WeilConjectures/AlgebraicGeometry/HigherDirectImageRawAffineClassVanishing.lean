/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawComplexPresentation
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Eventual zero of raw affine cohomology classes

Source: Stacks Project, Tags 09Z1, 0EZM and 03FD.
(blueprint: sbc-lem-higher-image-raw-affine-class-vanishing).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- A raw cohomology class which is zero after pullback to the limit becomes
zero as a raw class at a later stage. The hypothesis is zero in cohomology,
not zero in the associated higher-image sheaf; no sheafification occurs here.
Source: Stacks Project, Tag 09Z1 (cohomology continuity in the proof), Tag 0EZM
(complex continuity), and Tag 03FD (module cohomology after forgetting scalars).
(blueprint: sbc-lem-higher-image-raw-affine-class-vanishing).

Proof: Base change the inverse system and its limiting scheme cone along U -> S.
The stages are qcqs, since their structure maps to affine U are qcqs; transitions
remain affine. Identify the raw derived Hom groups with cohomology of these
pullbacks using the free module sheaf of the terminal object. The coefficient
sheaves are pullbacks of G; inverse-image composition identifies the coefficient
diagram on the limit with the constant diagram of the limit pullback of G.
Its colimit is this sheaf since I opposite is nonempty and connected. Put the
sheaves in degree-zero complexes with uniform lower bound zero. Injective module
resolutions compute the underlying abelian cohomology by 03FD. Apply complex
continuity 0EZM to the base-changed diagram. Under the derived-adjunction
identifications, its maps are precisely the explicitly constructed raw pullbacks.
The equality criterion for filtered colimits of abelian groups, applied to z and
zero, gives a later stage and two arrows to it. Cofilteredness equalizes the arrows
if necessary, so one arrow kills z. In negative degrees the cohomology groups
are zero, and the identity arrow suffices. No finite covers or separatedness of
higher-image sheaves are used in this argument. -/
theorem exists_higher_image_raw_affine_class_eq_zero
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left] (i : I)
    (z : (higherDirectImageRawOverPresheaf Λ k G q (D.obj i)).obj (op U))
    (hz : higherDirectImageRawOverPullback Λ k G q (c.π.app i) U z = 0) :
    ∃ (j : I) (f : j ⟶ i),
      higherDirectImageRawOverPullback Λ k G q (D.map f) U z = 0 := by
  have s := nonempty_higherDirectImageRaw_complex_presentation Λ k G q D c hc U
  obtain ⟨hB⟩ := s.isColimit
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (forget AddCommGrpCat.{u + 1})
  have hzero :
      (higherDirectImageRawCocone Λ k G q D c U).ι.app (op i) z =
        (higherDirectImageRawCocone Λ k G q D c U).ι.app (op i) 0 := by
    change higherDirectImageRawOverPullback Λ k G q (c.π.app i) U z = _
    rw [hz, map_zero]
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (forget AddCommGrpCat.{u + 1}) hB) z 0).mp hzero
  refine ⟨j.unop, f.unop, ?_⟩
  change (higherDirectImageRawDiagram Λ k G q D U).map f z = 0
  change (higherDirectImageRawDiagram Λ k G q D U).map f z =
    (higherDirectImageRawDiagram Λ k G q D U).map f 0 at hf
  simpa only [map_zero] using hf

end AlgebraicGeometry.Etale
