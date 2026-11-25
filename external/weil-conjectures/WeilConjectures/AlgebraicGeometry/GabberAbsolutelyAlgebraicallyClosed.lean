/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.GabberQuotientLocalizations
import WeilConjectures.AlgebraicGeometry.GabberQuotientPrincipalH1
import WeilConjectures.AlgebraicGeometry.ConstantEtaleCohomologyIsoComparison
import WeilConjectures.AlgebraicGeometry.GabberCriterion

/-! # Gabber vanishing for absolutely algebraically closed normal domains

Source: literature/stacks-project/etale-cohomology.tex, Lemma 09ZC
(label lemma-gabber-for-absolutely-algebraically-closed) (blueprint:
lem-weil-pbc-gabber-absolutely-algebraically-closed).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Let `R` be a normal domain with separably closed fraction field.  For every closed
subscheme `Z` of `Spec R`, the positive-degree étale cohomology of every finite constant
abelian sheaf vanishes.

Source: Stacks Project, `etale-cohomology.tex`, Lemma 09ZC
(label lemma-gabber-for-absolutely-algebraically-closed).

Proof (the five steps of the node):
1. By `def-weil-closed-immersion` and `def-weil-affine-spectrum`, write `Z` as
   `Spec (R/I)` over `Spec R`. The induced isomorphism of small étale sites preserves
   coverings, the terminal object, constant sheaves, and global sections. It therefore
   transports their derived cohomology (`def-weil-pbc-etale-cohomology`).
2. The stalks and function field of `Spec R` are the prime localizations and fraction
   field (`lem-weil-pbc-spec-domain-stalks-function-field`). Those localizations are
   normal domains (`lem-weil-pbc-localization-normal-domain`). Thus Stacks 09Z9,
   `proposition-base-change-larger-algebraically-closed` (2), makes every local ring strictly
   henselian.
3. At a prime of `R/I` with preimage `p`, the local ring is `R_p / I R_p`.
   By `lem-weil-pbc-strictly-henselian-quotient` (05WS), it is strictly henselian too.
4. For `h` in `R/I`, lift it to `f` in `R`. If `f = 0`, `D(h)` is empty and all
   abelian sheaves and their cohomology are zero. Otherwise `R_f` is a normal domain
   with the same separably closed fraction field. Localization commutes with quotient
   (`lem-weil-pbc-localization-quotient-commute`), so `Spec ((R/I)_h)` is a closed
   subscheme of `Spec R_f` (`lem-weil-pbc-spec-quotient-closed-immersion`). Stacks 09ZB,
   `lem-weil-pbc-gabber-h1-absolutely-algebraically-closed`, gives zero `H¹` there.
   Identify this spectrum with `D(h)` using
   `lem-weil-pbc-principal-localization-open-immersion` and transport as in step 1.
   Pullback preserves the constant sheaf (`lemma-constructible-pullback-constant`).
5. Apply `lem-weil-pbc-gabber-criterion` (0GY0) to `R/I` and the constant sheaf.
   Its local rings are strictly henselian by step 3. The required restriction map
   from `H¹(D(f+g))` has zero kernel because its source is zero by step 4.
   All positive cohomology vanishes; step 1 transports this vanishing back to `Z`.
(blueprint: lem-weil-pbc-gabber-absolutely-algebraically-closed)
-/
theorem gabber_absolutely_algebraically_closed
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hsep : IsSepClosed (FractionRing R))
    (Z : Scheme.{u}) (i : Z ⟶ Spec (CommRingCat.of R))
    [IsClosedImmersion i]
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] (q : ℤ) (hq : 1 ≤ q) :
    IsZero ((Etale.cohomology (AddCommGrpCat.{u + 1}) Z q).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)))) := by
  obtain ⟨I, e, _⟩ := IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion i)
  let F := (constantSheaf (Spec (CommRingCat.of (R ⧸ I))).smallEtaleTopology
    AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)
  have hR := gabber_quotient_localizations R hsep I
  have hfg : ∀ (f g : R ⧸ I) (x : Sheaf.H
      ((Etale.upperStar AddCommGrpCat.{u + 1}
        (Scheme.Opens.ι (X := Spec (CommRingCat.of (R ⧸ I)))
          (PrimeSpectrum.basicOpen (f + g)))).obj F) 1),
      x = 0 := by
    intro f g x
    have := Etale.gabber_quotient_principal_h1 R hsep I M (f + g)
    exact Subsingleton.elim _ _
  have hvan := Etale.gabberCriterion_degree (R ⧸ I) hR F
    (fun f g x _ _ ↦ hfg f g x)
  have hqnonneg : 0 ≤ q := by omega
  have hqnat : 0 < q.toNat := by omega
  have hz := (Etale.isZero_constant_cohomology_iff_subsingleton_H_of_iso
    Z (Spec (CommRingCat.of (R ⧸ I))) e M q.toNat).mpr (hvan q.toNat hqnat)
  simpa only [Int.toNat_of_nonneg hqnonneg] using hz

end AlgebraicGeometry
