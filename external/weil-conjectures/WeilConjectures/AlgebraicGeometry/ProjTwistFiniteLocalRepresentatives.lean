/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.AlgebraicGeometry.ProjTwistFiniteCanonicalEval
import WeilConjectures.AlgebraicGeometry.ProjTwistFiniteValues

/-!
# Finite localization data of twist sections

Source: Stacks Project, Tags 01MN and 01M7.
-/

@[expose] public section

universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj

/-- A finite principal cover carries fractions representing the section on every chart.
Source: Stacks Project, Tag 01M7, construction preceding Definition 27.8.3 (Tag 01M6).
(blueprint: lem-sc-proj-twist-finite-local-representatives)

Proof: around each point take a local homogeneous fraction for the section. Refine its
neighborhood by a homogeneous basic open contained in D₊(f), multiplying numerator and
denominator by its defining element and f. The new denominator h has positive degree c.
The affine chart sends this open to the principal open of h^b/f^c in A_(f).
Quasi-compactness extracts finitely many such opens; since they cover Spec(A_(f)), their
chart elements span the unit ideal. In A_f localized at h^b/f^c, h is invertible, so the
chosen fraction defines t. At every point where the chart element is invertible, the
ordinary map A_f → A_p extends by the module localization universal property. This
extension is linear for the A_(f)-action through A_p and sends t to the section value.
The chart cover supplies an invertible chart element at each point. For an empty chart,
use the empty family: A_(f) is the zero ring and there are no evaluation conditions. -/
theorem twist_finiteLocal_representatives
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (_ : Ideal.span (Set.range g) = ⊤)
      (t : ∀ i : Fin n, LocalizedModule.Away (g i) M),
      (∀ (i : Fin n) (p : basicOpen 𝒜 f),
      let F := IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2)
      IsUnit (F (algebraMap B (Localization.Away f) (g i))) →
      ∃ e : LocalizedModule.Away (g i) M →+
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal,
        (∀ z : M, e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) = F z) ∧
        (∀ (a : B) (x : LocalizedModule.Away (g i) M),
          e (a • x) = F (algebraMap B (Localization.Away f) a) * e x) ∧
        e (t i) = (s.1 p).1) := by
  dsimp
  obtain ⟨n, g, hspan, t, hv⟩ := twist_finiteLocal_values 𝒜 k f b hb hf s
  refine ⟨n, g, hspan, t, ?_⟩
  intro i p hi
  obtain ⟨e, he, hlin⟩ := twist_finiteLocal_canonical_eval 𝒜 f (g i) p hi
  refine ⟨e, he, hlin, ?_⟩
  exact hv i p e he hlin

end AlgebraicGeometry.Proj
