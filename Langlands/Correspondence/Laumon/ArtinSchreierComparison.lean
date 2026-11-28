import Langlands.MathlibBase
import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTransport
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The degree-one Artin–Schreier comparison

Katz (1986), (1.4.5), p. 80: for an `𝔽_p`-algebra `A`, the Artin–Schreier sequence
`0 → 𝔽_p → 𝔾_a → 𝔾_a → 0` of étale sheaves on `Spec A` and the vanishing of the étale cohomology
of `𝔾_a` in positive degrees on affine schemes give `H⁰(Spec A, 𝔽_p) ≅ Ker(1 - F)`,
`H¹(Spec A, 𝔽_p) ≅ A/(1 - F)A` (the Artin–Schreier quotient) and `Hᵠ(Spec A, 𝔽_p) = 0` for
`q ≥ 2`; and the inclusion `R[T] ⊆ R((T⁻¹))` induces a bijection of Artin–Schreier quotients.
This module defines the Artin–Schreier quotient, the map it induces for a ring map, the
connecting map `A → H¹(Spec A, ℤ/p)` of the Artin–Schreier sequence, the pullback on `ℤ/p`
cohomology and the ring map `R[T] → R((T⁻¹))`, and states the two comparisons.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace Langlands.Henniart.Laumon

section Quotient

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
/-- In the target of a ring map from a ring in which `p` vanishes, `p` vanishes. -/
theorem natCast_eq_zero_of_ringHom {B C : Type*} [CommRing B] [CommRing C] (φ : B →+* C)
    (hB : (p : B) = 0) : (p : C) = 0 := by
  rw [← map_natCast φ, hB, map_zero]

variable (B : Type*) [CommRing B]

/-- The image of the Artin–Schreier map `x ↦ x ^ p - x` (weil-conjectures's
`artinSchreierAddHom`) of a ring in which `p` vanishes: the subgroup `(F - 1)B = (1 - F)B`. -/
abbrev artinSchreierRange (hB : (p : B) = 0) : AddSubgroup B :=
  (artinSchreierAddHom p hB).range

/-- The Artin–Schreier quotient `B/(F - 1)B` of a ring in which `p` vanishes (Katz (1.4.5)). -/
abbrev artinSchreierQuotient (hB : (p : B) = 0) : Type _ :=
  B ⧸ artinSchreierRange p B hB

variable {B}

/-- The map of Artin–Schreier quotients induced by a ring map. -/
def artinSchreierQuotientMap {C : Type*} [CommRing C] (φ : B →+* C) (hB : (p : B) = 0) :
    artinSchreierQuotient p B hB →+
      artinSchreierQuotient p C (natCast_eq_zero_of_ringHom p φ hB) :=
  QuotientAddGroup.map _ _ φ.toAddMonoidHom (by
    rintro _ ⟨x, rfl⟩
    refine ⟨φ x, ?_⟩
    simp [artinSchreierAddHom_apply, map_sub, map_pow])

end Quotient

/-- The ring map `R[T] → R((T⁻¹))`: the ring of formal Laurent series `R((u))` in `u = T⁻¹` is
Mathlib's `LaurentSeries R` in the variable `u`, and `T` is sent to `u⁻¹`, the series
`single (-1) 1`. For a general ring `R` this is a ring, not a field.
It identifies `R[T]` with the Laurent polynomials in `u` with no positive power of `u`. -/
def artinSchreierLaurentHom (R : Type*) [CommRing R] : Polynomial R →+* LaurentSeries R :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (-1 : ℤ) (1 : R))

section Cohomology

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
/-- `p` vanishes in the global sections of `Spec B` when it vanishes in `B`. -/
theorem natCast_eq_zero_Γ_Spec (B : Type u) [CommRing B] (hB : (p : B) = 0) :
    (p : Γ(Spec (.of B), ⊤)) = 0 :=
  natCast_eq_zero_of_ringHom p (Scheme.ΓSpecIso (.of B)).inv.hom hB

/-- The pullback `Hᵠ(Y_ét, ℤ/p) → Hᵠ(X_ét, ℤ/p)` along a morphism `f : X ⟶ Y`: weil-conjectures's
`AlgebraicGeometry.Etale.cohomologyMap` followed by the identification
`f^* (ℤ/p)_Y ≅ (ℤ/p)_X` of constant sheaves. -/
def constantZModPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ) :
    Sheaf.H (Y.constantZMod p) q →+ Sheaf.H (X.constantZMod p) q :=
  (Sheaf.H.map (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))).hom) q).comp
    (Etale.cohomologyMap f (Y.constantZMod p) q)

variable (B : Type u) [CommRing B]

/-- The Artin–Schreier class map `B → H¹(Spec B, ℤ/p)`: an element `b`, as a global section of
`𝔾_a` (`Sheaf.H.equiv₀` at the terminal étale object), is sent by the connecting map of the
short exact Artin–Schreier sequence `0 → Ker ℘ → 𝔾_a → 𝔾_a → 0` (weil-conjectures's
`artinSchreierSequence_shortExact`) to `H¹(Ker ℘)`, identified with `H¹(ℤ/p)` by
`constantZModIsoKernelGaArtinSchreier`. It is the class of the Artin–Schreier torsor
`yᵖ - y = b`. -/
def artinSchreierCohomologyClass (hB : (p : B) = 0) :
    B →+ Sheaf.H ((Spec (.of B)).constantZMod p) 1 :=
  (Sheaf.H.map ((Spec (.of B)).constantZModIsoKernelGaArtinSchreier p
      (natCast_eq_zero_Γ_Spec p B hB)).inv 1).comp
    ((Sheaf.H.δ ((Spec (.of B)).artinSchreierSequence_shortExact p
        (natCast_eq_zero_Γ_Spec p B hB)) 0 1 rfl).comp
      ((Sheaf.H.equiv₀ (Spec (.of B)).gaSheaf
          (Scheme.isTerminalEtale (Spec (.of B)))).symm.toAddMonoidHom.comp
        (AddEquiv.ulift.symm.toAddMonoidHom.comp
          (Scheme.ΓSpecIso (.of B)).inv.hom.toAddMonoidHom)))

/-- The map `H⁰(Spec B, ℤ/p) → B` induced by the inclusion `ℤ/p → 𝔾_a`
(weil-conjectures's `constantZModToGaSheaf`) and `Sheaf.H.equiv₀` at the terminal étale
object. -/
def artinSchreierInvariantsMap (hB : (p : B) = 0) :
    Sheaf.H ((Spec (.of B)).constantZMod p) 0 →+ B :=
  (Scheme.ΓSpecIso (.of B)).hom.hom.toAddMonoidHom.comp
    (AddEquiv.ulift.toAddMonoidHom.comp
      ((Sheaf.H.equiv₀ (Spec (.of B)).gaSheaf
          (Scheme.isTerminalEtale (Spec (.of B)))).toAddMonoidHom.comp
        (Sheaf.H.map ((Spec (.of B)).constantZModToGaSheaf p (natCast_eq_zero_Γ_Spec p B hB)) 0)))

end Cohomology

/-- **Artin–Schreier cohomology of affine schemes** (Katz 1986, (1.4.5), p. 80, citing SGA 4,
IX 3.5 and VII 4.3). Let `p` be a prime and `B` a ring in which `p` vanishes. On `Spec B`:

1. `H⁰(Spec B, ℤ/p) → B` is injective with image the kernel of `x ↦ x ^ p - x`;
2. the Artin–Schreier class map `B → H¹(Spec B, ℤ/p)` is surjective with kernel `(F - 1)B`, so it
   induces an isomorphism from the Artin–Schreier quotient `B/(F - 1)B` onto `H¹(Spec B, ℤ/p)`;
3. `Hᵠ(Spec B, ℤ/p) = 0` for `q ≥ 2`;
4. the class map is natural: for a ring map `φ : B → C`, pullback along `Spec φ` sends the class
   of `b` to the class of `φ b`. -/
def AffineArtinSchreierCohomologyStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (B : Type u) [CommRing B] (hB : (p : B) = 0),
    Function.Injective (artinSchreierInvariantsMap p B hB) ∧
    (artinSchreierInvariantsMap p B hB).range = (artinSchreierAddHom p hB).ker ∧
    Function.Surjective (artinSchreierCohomologyClass p B hB) ∧
    (artinSchreierCohomologyClass p B hB).ker = artinSchreierRange p B hB ∧
    (∀ q : ℕ, 2 ≤ q → Subsingleton (Sheaf.H ((Spec (.of B)).constantZMod p) q)) ∧
    ∀ (C : Type u) [CommRing C] (φ : B →+* C) (b : B),
      constantZModPullback p (Spec.map (CommRingCat.ofHom φ)) 1
          (artinSchreierCohomologyClass p B hB b) =
        artinSchreierCohomologyClass p C (natCast_eq_zero_of_ringHom p φ hB) (φ b)

/-- **Artin–Schreier quotients of `R[T]` and `R((T⁻¹))`** (Katz 1986, (1.4.5), p. 80). For a
prime `p` and a ring `R` in which `p` vanishes, the ring map `R[T] → R((T⁻¹))` induces a
bijection of Artin–Schreier quotients. -/
def ArtinSchreierLaurentPolynomialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : (p : R) = 0),
    Function.Bijective (artinSchreierQuotientMap p (artinSchreierLaurentHom R)
      (natCast_eq_zero_of_ringHom p Polynomial.C hR))

end Langlands.Henniart.Laumon
