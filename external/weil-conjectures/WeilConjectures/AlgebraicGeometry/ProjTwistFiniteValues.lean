/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.AlgebraicGeometry.ProjTwistLocalClearing
import Mathlib.Data.Fintype.EquivFin

/-! # Finite local representatives of twist sections

A section of a twist `𝒪(k)` on a standard open `D₊(f)` of `Proj A` is represented by
finitely many fractions on a principal cover of the affine chart, and these fractions recover
the section values under every canonical evaluation (Stacks Project, Tag 01M7). -/

@[expose] public section
universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj
/-- Finite representatives satisfy the section values for every canonical evaluation.
Source: Stacks Project, Section 27.8, Lemma 27.8.1 (finite standard-open refinements)
and the construction preceding Lemma 27.8.4, Tag 01M7, applied to A(k).
(blueprint: new-finite-values)

Proof: write the section near each point as a homogeneous fraction a/d. Choose a
homogeneous u whose basic open contains that point and is inside
this neighborhood and D₊(f). Replace the fraction by N/h, where N=a*u*f and h=d*u*f.
Then c=deg(h)>0, D₊(h) is inside that neighborhood, and the section there is N/h.
The chart D₊(f) ≅ Spec(B) carries D₊(h) to D(g), with g=h^b/f^c in B.
Quasi-compactness selects finitely many such opens covering D₊(f); their g's span
one, since their principal opens cover Spec(B). Enumerate them by Fin n. Define
z=h^(b-1)*N/f^c in M=A_f, and t=z/g in M localized at g. The identity
h^b/f^c=g shows this is N/h wherever h is invertible.

For any p and additive e with the two displayed identities, let x be 1/g in M_g.
Since g*x=1, scalar compatibility and e(1)=1 imply F(g)*e(x)=1. Thus F(g) is a
unit even though this is not a separate hypothesis. Since F(g)=h^b/f^c and f is
invertible at p, h is invertible there too, so p lies in D₊(h). Similarly g*t=z
implies F(g)*e(t)=F(z). Cancel this unit to obtain e(t)=N/h=s(p). This works for
every e, without assuming it is a ring map. If the chart is empty, B is the zero
ring: use n=0 and the empty family (its span is both bottom and top). The
construction allows zero sections, nilpotent f, degree-zero d, and negative k. -/
theorem twist_finiteLocal_values
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (_ : Ideal.span (Set.range g) = ⊤)
      (t : ∀ i : Fin n, LocalizedModule.Away (g i) M),
      ∀ (i : Fin n) (p : basicOpen 𝒜 f)
        (e : LocalizedModule.Away (g i) M →+
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal),
        (∀ z : M, e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) =
          IsLocalization.map (M := Submonoid.powers f)
            (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
            (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
            (Submonoid.powers_le.mpr p.2) z) →
        (∀ (a : B) (x : LocalizedModule.Away (g i) M),
          e (a • x) =
            IsLocalization.map (M := Submonoid.powers f)
              (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
              (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
              (Submonoid.powers_le.mpr p.2)
              (algebraMap B (Localization.Away f) a) * e x) →
        e (t i) = (s.1 p).1 := by
  classical
  dsimp
  let B := HomogeneousLocalization.Away 𝒜 f
  let M := LocalizedModule.Away f A
  let : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
  have hlocal := twist_local_clearing 𝒜 k f b hb hf s
  choose g z hg hz using hlocal
  obtain ⟨a, ha⟩ := isCompact_univ.elim_finite_subcover
    (fun x : PrimeSpectrum B => (PrimeSpectrum.basicOpen (g x) : Set (PrimeSpectrum B)))
    (fun x => (PrimeSpectrum.basicOpen (g x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hg x⟩)
  let ix : Fin a.card → a := a.equivFin.symm
  let g' : Fin a.card → B := fun i => g (ix i).1
  have hspan : Ideal.span (Set.range g') = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply top_unique
    intro x _
    obtain ⟨y, hxy⟩ := Set.mem_iUnion.mp (ha (Set.mem_univ x))
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hxy
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨a.equivFin ⟨y, hy⟩, ?_⟩
    change x ∈ PrimeSpectrum.basicOpen (g ((a.equivFin.symm (a.equivFin ⟨y, hy⟩)).1))
    rw [Equiv.symm_apply_apply]
    exact hxy
  let den (i : Fin a.card) : Submonoid.powers (g' i) :=
    ⟨g' i, Submonoid.mem_powers (g' i)⟩
  let t (i : Fin a.card) : LocalizedModule.Away (g' i) M :=
    LocalizedModule.mk (z (ix i).1) (den i)
  refine ⟨a.card, g', hspan, t, ?_⟩
  intro i p e he hlin
  let F : Localization.Away f →+* Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal :=
    IsLocalization.map (M := Submonoid.powers f)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
      (Submonoid.powers_le.mpr p.2)
  have hcancel (w : M) :
      g' i • LocalizedModule.mk w (den i) =
        LocalizedModule.mkLinearMap (Submonoid.powers (g' i)) M w := by
    rw [LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply]
    exact LocalizedModule.mk_cancel (den i) w
  have hunit : IsUnit (F (algebraMap B (Localization.Away f) (g' i))) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨e (LocalizedModule.mk (1 : M) (den i)), ?_⟩
    calc
      F (algebraMap B (Localization.Away f) (g' i)) *
          e (LocalizedModule.mk (1 : M) (den i)) =
          e (g' i • LocalizedModule.mk (1 : M) (den i)) := (hlin _ _).symm
      _ = F 1 := by rw [hcancel, he]
      _ = 1 := F.map_one
  apply hunit.mul_left_cancel
  calc
    F (algebraMap B (Localization.Away f) (g' i)) * e (t i) =
        e (g' i • t i) := (hlin _ _).symm
    _ = F (z (ix i).1) := by rw [hcancel, he]
    _ = F (algebraMap B (Localization.Away f) (g' i)) * (s.1 p).1 :=
      (hz (ix i).1 p hunit).symm
end AlgebraicGeometry.Proj

