/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPolynomial.Basic
import WeilConjectures.AlgebraicGeometry.AffinePolynomialLocalizedFiniteProjectiveDimension
import WeilConjectures.RingTheory.ProjectiveDimensionLocusOpen
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension

/-! # A bounded polynomial resolution from finite stalk Tor dimension

Source: Stacks Project, Tag 069C, proof of (3) implies (1), and Tags 068X and 068W.
(blueprint: lem-pc-affine-polynomial-resolution-of-stalkwise).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

private theorem finite_projectiveDimension_of_localized
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : ∀ p : PrimeSpectrum R, ∃ n : ℕ,
      HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) n) :
    ∃ n : ℕ, HasProjectiveDimensionLE M n := by
  classical
  let O (n : ℕ) : Set (PrimeSpectrum R) :=
    {p | HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) n}
  have hcover : Set.univ ⊆ ⋃ n, O n := by
    intro p _
    obtain ⟨n, hn⟩ := h p
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O
    (fun n ↦ ModuleCat.isOpen_hasProjectiveDimensionLE_locus M n) hcover
  refine ⟨s.sup id, (M.hasProjectiveDimensionLE_iff_forall_primeSpectrum _).mpr ?_⟩
  intro p
  obtain ⟨n, hn, hpn⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ p))
  have : HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) n := hpn
  exact hasProjectiveDimensionLT_of_ge _ (n + 1) (s.sup id + 1)
    (Nat.add_le_add_right (Finset.le_sup (f := id) hn) 1)

namespace AlgebraicGeometry

/-- A finite polynomial presentation of an affine chart admits a bounded projective
resolution of its coordinate algebra over the polynomial ring.
Source: Stacks Project, Tag 069C, proof of (3) implies (1), using Tags 068X and 068W.

Proof: A = Γ(Y,U) is Noetherian. The polynomial ring P = A[x_1,...,x_n] is
Noetherian and the surjective presentation makes B = Γ(X,V) a finite P-module.
Thus B[0] is pseudo-coherent. For each prime q of P not containing the kernel,
B_q = 0. For a prime containing the kernel, its quotient corresponds to a point
of V. The affine stalk identifications and the compatibility of the presentation
with f identify B_q with that source stalk and the A-localization with the image
stalk. The assumption supplies a finite Tor bound there. The map A_p -> P_q is
flat, with fibres localizations of polynomial algebras over fields, of global
dimension at most n. Tag 068X makes B_q perfect over P_q. Tag 068W applies to the
bounded-below pseudo-coherent complex B[0], making B perfect over P. A finite
module concentrated in degree zero which is perfect has a finite projective
resolution: truncate a bounded projective representative above degree zero and
use exactness and projective splitting successively there. Reverse cochain degrees
to obtain a nonnegative projective resolution, with a natural bound d. For B = 0
use the zero projective resolution. No finite-dimensional hypothesis on A is used.
(blueprint: lem-pc-affine-polynomial-resolution-of-stalkwise). -/
theorem affinePolynomial_boundedResolution_of_stalkwise
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (n : ℕ) (g : MvPolynomial (Fin n) Γ(Y, U) →+* Γ(X, V))
    (hg : Function.Surjective g)
    (hcomp : g.comp (MvPolynomial.C) = (f.appLE U V e).hom) :
    ∃ (d : ℕ) (P : ProjectiveResolution
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of Γ(X, V) Γ(X, V)))),
      ∀ i : ℕ, d < i → IsZero (P.complex.X i) := by
  let R := MvPolynomial (Fin n) Γ(Y, U)
  let M := (ModuleCat.restrictScalars g).obj (ModuleCat.of Γ(X, V) Γ(X, V))
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsNoetherianRing R := inferInstance
  let φ : ModuleCat.of R R ⟶ M :=
    ModuleCat.semilinearMapAddEquiv g _ _ g.toSemilinearMap
  have hφ : Function.Surjective φ.hom := hg
  have : Module.Finite R M := Module.Finite.of_surjective φ.hom hφ
  obtain ⟨d, hd⟩ := finite_projectiveDimension_of_localized (R := R) M
    (affinePolynomial_localized_finiteProjectiveDimension_of_stalkwise
      f hperfect U hU V hV e n g hg hcomp)
  have : HasProjectiveDimensionLE M d := hd
  let := HasExt.standard (ModuleCat.{u} R)
  obtain ⟨P, hP⟩ := (ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE M d).mpr
    hd
  exact ⟨d, P, hP⟩

end AlgebraicGeometry
