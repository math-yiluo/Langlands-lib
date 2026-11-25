/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechAlphaQuasiIso
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechAugmentationBoundarySquares

/-! # Boundary compatibility of the augmentation quotient

Source: Stacks Project, Tag 01EQ, augmented injective Čech double complex;
Homology, the horseshoe lemma and naturality of the homology connecting map.
(blueprint: lem-pc-abelian-cech-comparison-boundary)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The cocycle characterization implies the quotient equation on homology. -/
private theorem comparison_quotient
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (q : ℕ)
    (e : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F ≅
      (abelianCechSections I).homology q)
    (he : ∀ (t : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F),
      ∃ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I.cocomplex.X q)
        (ha : a ≫ I.cocomplex.d q (q + 1) = 0)
        (z : (abelianCechSections I).cycles q),
        I.extMk a (q + 1) rfl ha = t ∧
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I).iCycles q z ∧
        e.hom t = (abelianCechSections I).homologyπ q z)
    (c : (TopCat.Sheaf.cechCohomologyFunctor U q).obj F ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F)
    (hc : IsAbelianCechComparison U F q c) :
    c ≫ e.hom ≫ HomologicalComplex.homologyMap (abelianCechAlpha U I) q =
      HomologicalComplex.homologyMap (abelianCechBeta U I) q := by
  ext x
  obtain ⟨a, ha, z, ht, hz, hez⟩ := he (c x)
  change HomologicalComplex.homologyMap (abelianCechAlpha U I) q (e.hom (c x)) = _
  rw [hez]
  exact (hc I x a ha z hz ht.symm).symm

/-- The augmentation quotient commutes with connecting maps for sequences
surjective on every tuple intersection. Canonicity is an essential hypothesis.

Source: Stacks Project, Tag 01EQ, injective double-complex construction;
Tags 013T (horseshoe resolutions) and 0117 (connecting-map naturality).
(blueprint: lem-pc-abelian-cech-comparison-boundary)

Proof: Take horseshoe injective resolutions of the three terms of T. Their
sequence is split exact in each resolution degree. Applying sections on any
tuple intersection preserves those splittings, as do products and the finite
direct sums on total diagonals. This gives short exact sequences of section
complexes and total complexes. The tuple-surjectivity hypothesis gives the
short exact sequence of coefficient Čech complexes. The three alpha maps and
the three beta maps form morphisms of these short exact sequences; each square
is restriction naturality or the horseshoe augmentation equation. Naturality
of homology connecting maps yields delta-Cech followed by H(beta on T.X1)
equals H(beta on T.X3) followed by delta-total, and delta-sections followed by
H(alpha on T.X1) equals H(alpha on T.X3) followed by delta-total. The
constant-sheaf Hom adjunction identifies the section-complex boundary with
the Ext boundary: both are represented by lifting a cocycle to the middle
resolution, taking its differential, and lifting the result through the first
inclusion. This is Sheaf.functorHdelta with the same sign convention. Replace
the two beta maps by the assumed canonical comparison equations on these
horseshoe resolutions. Cancel the invertible alpha map and the canonical
Ext/section identification in degree q+1. The resulting identity is the one
asserted below. No hypothesis of canonicity on the middle sheaf is needed.
Degree zero uses the same boundary construction; the empty-cover case is zero.
Finite total diagonals give the argument for arbitrary covering index sets. -/
theorem abelianCechComparison_boundary
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))) (q : ℕ)
    (c : (TopCat.Sheaf.cechCohomologyFunctor U (q + 1)).obj T.X₁ ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).obj T.X₁)
    (d : (TopCat.Sheaf.cechCohomologyFunctor U q).obj T.X₃ ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj T.X₃)
    (hc : IsAbelianCechComparison U T.X₁ (q + 1) c)
    (hd : IsAbelianCechComparison U T.X₃ q d) :
    TopCat.Sheaf.cechδ U hT hg q ≫ c = d ≫ Sheaf.functorHδ hT q := by
  let I₁ := injectiveResolution T.X₁
  let I₃ := injectiveResolution T.X₃
  obtain ⟨e₁, he₁⟩ := abelianCechExtSectionIso_exists I₁ (q + 1)
  obtain ⟨e₃, he₃⟩ := abelianCechExtSectionIso_exists I₃ q
  obtain ⟨δ, hβ, hα⟩ :=
    abelianCechAugmentation_boundary_squares U T hT hg q I₁ I₃ e₁ e₃ he₁ he₃
  have hc' := comparison_quotient U I₁ (q + 1) e₁ he₁ c hc
  have hd' := comparison_quotient U I₃ q e₃ he₃ d hd
  have : QuasiIso (abelianCechAlpha U I₁) := abelianCechAlpha_quasiIso U hcover I₁
  apply (cancel_mono (e₁.hom ≫
    HomologicalComplex.homologyMap (abelianCechAlpha U I₁) (q + 1))).1
  simp only [Category.assoc]
  rw [hc', hα, hβ, ← hd']
  simp only [Category.assoc]
end AlgebraicGeometry.Scheme.Modules
