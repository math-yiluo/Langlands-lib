/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import WeilConjectures.AlgebraicGeometry.LisseLatticeClassSheaf
import WeilConjectures.AlgebraicGeometry.LisseLatticeSliceTransport

/-!
# Etale-local integral lattices in lisse coefficient sheaves

Source: Bhatt--Scholze, Proposition 6.8.4(6) and Definition 6.8.3
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- A lisse coefficient sheaf admits lisse integral lattices after an etale cover.
The right-hand presheaf is the sectionwise slice-site presentation of `f⁻¹ L`, with
its coefficient action identified by the identity on continuous functions. An isomorphism
of these module presheaves is an isomorphism of module sheaves, since the forgetful
functor from module sheaves is fully faithful. Finite local freeness allows variable
ranks and rank zero. The empty scheme permits the empty etale covering.

Source: Bhatt--Scholze, Proposition 6.8.4(6), Definition 6.8.3
(auxiliary; not a blueprint node).

Proof plan:
1. Apply `lemma-lattices-lisse-e-sheaves--2` to the isomorphism classes of
   integral lattices with scalar-extension isomorphism. On each trivializing pro-etale
   member of rank n this is the constant sheaf GL_n(E)/GL_n(A). The identity coset gives
   a local section, also for n = 0.
2. Apply `lemma-lattices-lisse-e-sheaves--2` to descend inhabitedness
   to an etale covering. No compatibility among its sections is required.
3. Choose lattice representatives on the members. Their defining isomorphisms are the
   required scalar-extension isomorphisms. Slice-site restriction is inverse image with
   the displayed coefficient identification. For the empty scheme use the empty family. -/
theorem exists_lisse_lattice_etale_local (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)))
    (hL : L.IsFiniteLocallyFree) :
    ∃ (I : Type (u + 1)) (Y : I → X.Etale),
      (X.smallEtaleTopology).CoversTop Y ∧
      ∀ i : I, ∃ M : ringedSiteModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology (Y i).left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (lisseIntegerSheaf l E (Y i).left)),
        M.IsFiniteLocallyFree ∧
        Nonempty ((SheafOfModules.changeOfRings
          (lisseIntegerToField l E (Y i).left) M).val ≅
          (PresheafOfModules.pushforward
            (lisseEtaleCoefficientIdentification l E (Y i).hom)).obj L.val) := by
  obtain ⟨F, hconst, hlocal, hrepresent⟩ := exists_lisse_lattice_class_sheaf l E X L hL
  have hclass := ((Scheme.proEtale_locallyClassical_etaleCover X F).2.1 hconst).1
  obtain ⟨I, Y, hcover, hsections⟩ :=
    (Scheme.proEtale_locallyClassical_etaleCover X F).2.2 hclass hlocal
  refine ⟨I, Y, hcover, fun i ↦ ?_⟩
  obtain ⟨P⟩ := hrepresent ((Scheme.toProEt X).obj (Y i)) (hsections i)
  exact lisse_lattice_of_slice l E X L (Y i) P

end AlgebraicGeometry.ProEtale
