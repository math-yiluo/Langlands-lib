/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictionMap
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenTransportSquare

/-! # Pinned restriction comparisons
Source: Stacks Tags 079W, 08FE and 09RE.
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section

private theorem restriction_transport
    {S Y : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens)
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    {T T' : Over S} (g : T' ⟶ T) (M Q : schemeDerivedCategory Y)
    (f : (derivedPullback (pullback.fst s T.hom)).obj M ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    perfectHomOpenRestrictionMap s B T'.hom a (perfectHomMap s g f) =
      perfectHomMap (B.ι ≫ s) g (perfectHomOpenRestrictionMap s B T.hom a f) := by
  exact perfect_hom_open_transport_square s B a g M Q f
    (fun r ↦ perfectHomOpenPullbackComparison s B r.hom a) (fun _ ↦ rfl)

/-- Restricting a pullback Hom commutes with stage and apex base-change transport.

Source: Stacks Project, perfect.tex Tag 09RE; Cohomology Tag 0D5S.
Proof: in each square let b be the base-change map of the open inclusion and g
be the base-change map of the later ring stage (or of the cocone apex).
The two composites of b and g agree by pullback.hom_ext: their first projections
are the same open inclusion followed by the original projection, and their second
projections are the same ring-scheme map followed by the second projection.
Expand the conjugation formulas in perfectHomOpenRestrictionMap and perfectHomMap.
Functor.map_comp combines the two pullbacks. The associativity equation of the
fixed counit-pinned perfectHomComposition compares both pasted composites with
the derived pullback of this common map. Naturality moves the common mate between
open restriction and derivedPullback(B.ι) past the pullback Hom. The comparison
components and their inverses cancel. The resulting composites are identical.
Specialize the cartesian map to R.map(j≤k) and to c.ι.app j. No representing
equivalences, quasi-coherence, or existence of restricted cocone data are used.
Empty opens, identities, zero objects, and a one-stage diagram obey the same
composition and inverse cancellation identities.
(blueprint: new-perfect-hom-open-restriction-transport). -/
theorem perfect_hom_open_restriction_transport
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι) :
    (∀ (j k : Set.Ici i) (hjk : j ≤ k) (M Q : schemeDerivedCategory Y)
      (f : (derivedPullback (pullback.fst s
          (Spec.map (R.map (homOfLE j.property))))).obj M ⟶
        (derivedPullback (pullback.fst s
          (Spec.map (R.map (homOfLE j.property))))).obj Q),
      perfectHomOpenRestrictionMap s B (Spec.map (R.map (homOfLE k.property))) a
          (perfectStageMap R s j.property hjk f) =
        perfectStageMap R (B.ι ≫ s) j.property hjk
          (perfectHomOpenRestrictionMap s B
            (Spec.map (R.map (homOfLE j.property))) a f)) ∧
    (∀ (j : Set.Ici i) (M Q : schemeDerivedCategory Y)
      (f : (derivedPullback (pullback.fst s
          (Spec.map (R.map (homOfLE j.property))))).obj M ⟶
        (derivedPullback (pullback.fst s
          (Spec.map (R.map (homOfLE j.property))))).obj Q),
      perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
          (perfectLimitMap R c s j.property f) =
        perfectLimitMap R c (B.ι ≫ s) j.property
          (perfectHomOpenRestrictionMap s B
            (Spec.map (R.map (homOfLE j.property))) a f)) := by
  constructor
  · intro j k hjk M Q f
    exact restriction_transport s B a
      (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
      (T' := Over.mk (Spec.map (R.map (homOfLE k.property))))
      (Over.homMk (Spec.map (R.map (homOfLE hjk)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) M Q f
  · intro j M Q f
    exact restriction_transport s B a
      (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.property)])) M Q f

end
end AlgebraicGeometry
