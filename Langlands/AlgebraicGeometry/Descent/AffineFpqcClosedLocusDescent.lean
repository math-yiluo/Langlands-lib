import Langlands.AlgebraicGeometry.Descent.FppfClosedLocusDescentProof

/-! # Descent of closed loci along affine fpqc covers -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineFpqcClosedLocusDescent

open FppfClosedLocusDescent

/-- The ideal descended from the ideals of a finite affine family. -/
def descendedIdeal {Y : Scheme.{u}} {κ : Type*} {W : κ → Scheme.{u}}
    (f : ∀ l, W l ⟶ Y) (I : ∀ l, Ideal Γ(W l, ⊤)) : Ideal Γ(Y, ⊤) :=
  ⨅ l, (I l).comap (f l).appTop.hom

/-- A finite flat affine family descends closed loci for any subcanonical topology
in which it is a covering family. No finite-presentation hypothesis is used. -/
theorem finiteCover (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    {Y : Scheme.{u}} [IsAffine Y] (E : Sieve Y) (hE : J.IsClosed E)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (W : κ → Scheme.{u}) [∀ l, IsAffine (W l)] (f : ∀ l, W l ⟶ Y)
    (hflat : ∀ l, Flat (f l))
    (hS : Sieve.generate (Presieve.ofArrows W f) ∈ J Y)
    (h : ∀ l, ∃ (Z : Scheme.{u}) (ι : Z ⟶ W l), IsClosedImmersion ι ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ W l), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E (g ≫ f l)) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y), IsClosedImmersion ι ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E g := by
  choose Z ιZ hιZ hfac using h
  let _ : ∀ l, Algebra Γ(Y, ⊤) Γ(W l, ⊤) := fun l ↦ (f l).appTop.hom.toAlgebra
  have hflat' (l : κ) : Module.Flat Γ(Y, ⊤) Γ(W l, ⊤) := by
    have := hflat l
    exact (f l).flat_appTop
  let I : ∀ l, Ideal Γ(W l, ⊤) := fun l ↦ RingHom.ker (ιZ l).appTop.hom
  obtain ⟨Z₀, ι₀, hι₀, hker⟩ :=
    exists_isClosedImmersion_ker_appTop (descendedIdeal f I)
  refine ⟨Z₀, ι₀, hι₀, fun T g ↦ ⟨fun hk ↦ ?_, fun hg ↦ ?_⟩⟩
  · have hg := (factors_iff_ker_appTop_le ι₀ g).mp hk
    rw [hker] at hg
    refine hE g (J.superset_covering ?_ (J.pullback_stable g hS))
    intro T' u hu
    obtain ⟨l, m, hm⟩ := exists_of_pullback_generate_ofArrows g u hu
    change E (u ≫ g)
    rw [← hm]
    refine (hfac l m).mp ((factors_iff_ker_appTop_le (ιZ l) m).mpr ?_)
    refine (le_map_iInf_comap Γ(Y, ⊤) (fun l ↦ Γ(W l, ⊤)) I l fun l' b hb ↦
      tmul_one_eq_zero_of_mem_ker E (f l) (f l') (ιZ l) (ιZ l') (hfac l) (hfac l')
        rfl rfl b hb).trans ?_
    rw [Ideal.map_le_iff_le_comap]
    have h1 := hg.trans (ker_appTop_le_ker_comp_appTop u g)
    rw [← hm, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, ← RingHom.comap_ker] at h1
    exact h1
  · have := hι₀
    refine exists_lift_of_covering J ι₀ g _ (J.pullback_stable g hS) ?_
    intro T' u hu
    obtain ⟨l, m, hm⟩ := exists_of_pullback_generate_ofArrows g u hu
    have hEm : E (m ≫ f l) := hm ▸ E.downward_closed hg u
    have hk := (factors_iff_ker_appTop_le (ιZ l) m).mp ((hfac l m).mpr hEm)
    rw [factors_iff_ker_appTop_le, hker, ← hm, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      ← RingHom.comap_ker]
    exact (iInf_le _ l).trans (Ideal.comap_mono hk)

/-- A closed locus descends along a single flat surjective affine morphism of
an affine base. Tests may be arbitrary schemes. -/
theorem affine {Y W : Scheme.{u}} [IsAffine Y] [IsAffine W]
    (E : Sieve Y) (hE : Scheme.fpqcTopology.IsClosed E)
    (f : W ⟶ Y) [Flat f] [Surjective f]
    (h : ∃ (Z : Scheme.{u}) (ι : Z ⟶ W), IsClosedImmersion ι ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ W), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E (g ≫ f)) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y), IsClosedImmersion ι ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E g := by
  apply finiteCover Scheme.fpqcTopology E hE (fun _ : PUnit.{1} ↦ W) (fun _ ↦ f)
    (fun _ ↦ inferInstance) _ (fun _ ↦ h)
  rw [Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck f.singleton_mem_fpqcPrecoverage

end Langlands.AlgebraicGeometry.AffineFpqcClosedLocusDescent
