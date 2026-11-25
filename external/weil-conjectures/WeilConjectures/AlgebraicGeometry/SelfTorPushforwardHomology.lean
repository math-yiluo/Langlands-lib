/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.SelfTorProjectionHomology

/-! # Closed-immersion self-Tor on fixed resolution representatives

Source: Stacks Project, Tags 08EU, 068G, 06YS and 08KS.
(blueprint: lem-pc-self-tor-pushforward-homology). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- The homology of the derived tensor square of the pushed-forward structure sheaf
is the pushforward of the homology of its termwise pulled-back K-flat resolution.

Source: Stacks Project, Derived Categories of Schemes, Tag 08EU;
More on Algebra, Tag 068G;
modules.tex, Tag 08KS; Tag 06YS for K-flat representatives.
(blueprint: lem-pc-self-tor-pushforward-homology).

Proof: In standard derived localizations put E=O_Z[0] and K=B[0]. A closed immersion
is affine and hence quasi-compact and quasi-separated. Both E and K have
quasi-coherent cohomology: O_Z is quasi-coherent and affine pushforward preserves
quasi-coherence. Exactness of closed-immersion pushforward identifies Ri*E with K.
The qcqs derived projection formula gives K tensor^L K isomorphic to
Ri*(E tensor^L Li*K). The structure-sheaf single complex is the derived tensor unit,
so the right side is Ri*(Li*K). The augmentation a and K-flat representative
comparison identify Li*K with Q(T), for the actual termwise pullback T of P.
Closed-immersion pushforward is exact (after forgetting scalars, use the closed-image
homeomorphism and closed-subset exactness, and reflect exactness back to modules).
Thus its derived homology is ordinary pushforward of homology. Apply degree-k
homology to the preceding isomorphisms. Transport from standard localizations to the
supplied category on Y using the localization equivalences and the comparisons for
tensor and homology. This keeps the displayed fixed tensor structure. The argument
needs neither flatness of the immersion nor any boundedness of P. For the identity
immersion it reduces to the derived unit law. Empty schemes, the zero quotient and
all integer degrees are included by the same unit and representative comparisons. -/
theorem nonempty_selfTor_pushforward_homology
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hP : CochainComplex.IsKFlatTensorResolution (R := Y.sheaf) a) (k : ℤ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    Nonempty (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj (S.obj B ⊗ S.obj B)) ≅
      (Scheme.Modules.pushforward i).obj (T.homology k)) := by
  dsimp
  exact nonempty_selfTor_projection_homology i P a hP k _ (Iso.refl _)

end AlgebraicGeometry
