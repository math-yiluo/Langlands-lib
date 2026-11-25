/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.InvertSCOhomology
import WeilConjectures.AlgebraicGeometry.CohomologyFractionEventuallyZero
import WeilConjectures.AlgebraicGeometry.ResolutionUnitTwistComparison

/-! # Kernel torsion for raw section cohomology

Source: Stacks Project, Tags 09MR and 01E4.
(blueprint: lem-pc-section-cohomology-principal-torsion).
-/

@[expose] public section

universe u
set_option autoImplicit false

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A raw resolution cohomology class vanishing on a principal open is killed by
some power of its defining function. This is only the kernel assertion and makes
no claim that classes on the principal open lift.

Source: Stacks Project, Tag 09MR, Lemma 30.17.3, injectivity of the canonical map
and the zero criterion for fractions; Tag 01E4, Lemma 20.7.3.
(blueprint: lem-pc-section-cohomology-principal-torsion).

Proof: Put Y = f⁻¹W and let b be the pullback of a. The affineness of W and
qcqs hypotheses on f make Y qcqs. Restrict F and I to Y; open restriction
preserves quasi-coherence and injectives. Taking sections of I on Y and D(b)
identifies their cohomology with P(W) and P(D(a)), since f⁻¹D(a)=D(b).
The identifications come from the degreewise section identities for pushforward,
so they commute with restriction and multiplication by the pulled-back function.
Apply invertS_cohomology on Y to the tensor unit and its section b. Under the
unit tensor identifications, the fraction [0,x] maps to the restriction of x:
the canonical equation at exponent zero is precisely that equality. Thus the
hypothesis makes its image zero. Injectivity of the comparison makes [0,x]
zero in the fraction presentation. Apply cohomologyFraction_eventually_zero
at index zero to obtain an exponent n for which multiplication by b^n kills
x. Under the unit identifications its tensor transition is multiplication by
b^n, and under the section-complex identification this is the scalar action
of a^n on P(W). This gives the required equation. For a=0 choose n=1; for
unit a the restriction is an isomorphism, so x=0 and n=0 works. The same
argument includes q=0, the zero coefficient module, and empty W. -/
theorem sectionCohomologyPresheaf_pow_annihilates {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (hW : IsAffineOpen W) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    ∀ x : P.obj (op W), (P.map (homOfLE (T.basicOpen_le a)).op).hom x = 0 →
      ∃ n : ℕ, a ^ n • x = 0 := by
  dsimp only
  let Y := (f ⁻¹ᵁ W).toScheme
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
  let L := MonoidalCategory.tensorUnit Y.Modules
  have : CompactSpace Y := isCompact_iff_compactSpace.mp (f.isCompact_preimage hW.isCompact)
  have : QuasiSeparatedSpace Y :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ W).isOpen).mp
      (f.isQuasiSeparated_preimage hW.isQuasiSeparated)
  have : G.IsQuasicoherent := isQuasicoherent_restrictFunctor _ F
  obtain ⟨s, e, hres, hmul⟩ := resolution_unitTwist_comparison f F I q W a
  obtain ⟨U, hU, c, hc⟩ := invertS_cohomology Y L G s q
  obtain ⟨d, hd⟩ := hres U hU
  intro x hx
  have hrestrict := (hd x).trans (by rw [hx, map_zero])
  have hcanonical := hc 0 (e 0 x)
  have hz : c (cohomologyFraction L G s q ⊤ 0 (e 0 x)) = 0 := by
    have heq : (RingedSpace.openModuleCohomology Y.toRingedSpace q U).map
        (MonoidalCategory.rightUnitor G).inv
          (c (cohomologyFraction L G s q ⊤ 0 (e 0 x))) = 0 := by
      simpa only [tensorPowSection_zero, tensorPow_zero, MonoidalCategory.whiskerLeft_id,
        Category.comp_id] using hcanonical.trans hrestrict
    exact (ConcreteCategory.bijective_of_isIso
      ((RingedSpace.openModuleCohomology Y.toRingedSpace q U).map
        (MonoidalCategory.rightUnitor G).inv)).1
        (heq.trans (map_zero _).symm)
  have hfrac : cohomologyFraction L G s q ⊤ 0 (e 0 x) = 0 :=
    c.injective (hz.trans c.map_zero.symm)
  obtain ⟨n, hn⟩ := cohomologyFraction_eventually_zero L G s q ⊤ 0 (e 0 x) hfrac
  refine ⟨n, (e (0 + n)).injective ?_⟩
  rw [map_zero, ← hmul n x]
  exact hn

end AlgebraicGeometry.Scheme.Modules
