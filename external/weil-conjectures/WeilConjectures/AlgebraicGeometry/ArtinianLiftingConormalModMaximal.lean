/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Filtration
import WeilConjectures.AlgebraicGeometry.ArtinianLiftingTruncatedSection
import WeilConjectures.AlgebraicGeometry.TruncatedSectionConormalResidueKernel

/-!
# Artinian lifting splits the conormal map modulo the maximal ideal

Source: Stacks Project, Algebra, Lemma 02HT, proof of (4) implies (1),
third through last paragraphs.
-/

@[expose] public section

universe u v

namespace Algebra

private theorem residue_retraction_of_kernel
    {S M T : Type u} [CommRing S] [IsLocalRing S]
    [AddCommGroup M] [Module S M] [AddCommGroup T] [Module S T]
    (f : M →ₗ[S] T)
    (hf : ∀ x, f x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S T) →
      x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S M)) :
    ∃ g : (T ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S T))) →ₗ[S]
        (M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M))),
      g.comp (((IsLocalRing.maximalIdeal S • (⊤ : Submodule S T)).mkQ).comp f) =
        (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M)).mkQ := by
  let m := IsLocalRing.maximalIdeal S
  let p : Submodule S M := m • ⊤
  let t : Submodule S T := m • ⊤
  have hmap : p ≤ Submodule.comap f t :=
    Submodule.smul_top_le_comap_smul_top m f
  let fbar : (M ⧸ p) →ₗ[S] (T ⧸ t) := p.mapQ t f hmap
  have hinj : Function.Injective fbar := by
    rw [← LinearMap.ker_eq_bot]
    apply bot_unique
    intro x hx
    obtain ⟨x, rfl⟩ := p.mkQ_surjective x
    have hfx : f x ∈ t := by
      exact (Submodule.Quotient.mk_eq_zero t).mp hx
    exact (Submodule.Quotient.mk_eq_zero p).mpr (hf x hfx)
  -- A linear injection over the residue field extends the identity on its source.
  let k := S ⧸ m
  let : Field k := Ideal.Quotient.field m
  let fk : (M ⧸ p) →ₗ[k] (T ⧸ t) :=
    fbar.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := m))
  obtain ⟨g, hg⟩ := IsSemisimpleModule.extension_property fk hinj
    (LinearMap.id : (M ⧸ p) →ₗ[k] (M ⧸ p))
  refine ⟨g.restrictScalars S, ?_⟩
  ext x
  exact LinearMap.congr_fun hg (p.mkQ x)

/-- Source: Stacks Project, Algebra, Lemma 02HT, proof of (4) implies (1),
third through last paragraphs (https://stacks.math.columbia.edu/tag/02HT).
(blueprint: lem-weil-pbc-artinian-lifting-conormal-mod-maximal).

Proof in words:
Let S = A_q, C = P.Ring, J = ker(C -> S), and m = maximalIdeal C. Surjectivity
between local rings identifies the preimage of the maximal ideal of S with m,
so J is contained in m. For each N >= 1, form C/(J^2 + m^N) -> C/(J + m^N).
These are nonzero Artinian local rings: both defining ideals contain m^N and lie
in m, and C is Noetherian. Their kernel has square zero. The natural map from A
into the second quotient has preimage maximal ideal q. Filter the kernel by
ideals with length-one factors. The intervening quotients are Artinian local.
Use the lifting hypothesis successively from the last quotient to the first;
the preimage maximal ideal remains q since a surjection of local rings pulls
back the maximal ideal. This gives an R-compatible lift from A to the first quotient.

Every element outside q maps to a unit, so the lift extends to S. The maximal
ideal of S maps into the maximal ideal of the first quotient, whose N-th power
vanishes. Hence the lift factors through S/(maximalIdeal S)^N, identified with
the second quotient. The resulting map is a section, by localization and quotient
uniqueness. Square-zero section conormal retraction gives a left inverse to the
conormal map for this pair of Artinian quotients.

Artin-Rees for J inside C gives c >= 1 such that m^N intersect J is contained
in m^(N-c) J for N >= c. Choose N = c+1.
Tensor the preceding left inverse with the residue field S/maximalIdeal S. The modular law
identifies the source with J/(J^2 + m J). Differential reduction modulo the maximal ideal,
first for J with exponent 1 and then for m in C/J^2 with exponent N-1,
identifies the target with the reduction of S tensor_C Omega(C/R). On generators,
the resulting map is the reduction of P.cotangentComplex, since both send x to dx.
Write its left inverse as vk and compose with the quotient projection to obtain
the displayed equation. Transport test rings to Type (max u v) using ULift when
necessary; lengths and both lifting equations are preserved. This argument also
covers J = 0 (the conormal module is zero) and zero-variable presentations.
-/
theorem artinian_lifting_conormal_split_mod_maximal
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (q : Ideal A) [q.IsPrime]
    (P : Extension.{u} R (Localization.AtPrime q))
    [IsLocalRing P.Ring] [IsNoetherianRing P.Ring]
    (hlift : ∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp (algebraMap R A) = φ.comp ρ →
          Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp (algebraMap R A) = ρ) :
    ∃ vk : (P.CotangentSpace ⧸
          ((IsLocalRing.maximalIdeal (Localization.AtPrime q)) •
            (⊤ : Submodule (Localization.AtPrime q) P.CotangentSpace))) →ₗ[Localization.AtPrime q]
        (P.Cotangent ⧸
          ((IsLocalRing.maximalIdeal (Localization.AtPrime q)) •
            (⊤ : Submodule (Localization.AtPrime q) P.Cotangent))),
        vk.comp ((((IsLocalRing.maximalIdeal (Localization.AtPrime q)) •
            (⊤ : Submodule (Localization.AtPrime q) P.CotangentSpace)).mkQ).comp
              P.cotangentComplex) =
          ((IsLocalRing.maximalIdeal (Localization.AtPrime q)) •
            (⊤ : Submodule (Localization.AtPrime q) P.Cotangent)).mkQ := by
  let m := IsLocalRing.maximalIdeal P.Ring
  obtain ⟨c, hc⟩ := m.exists_pow_inf_eq_pow_smul
    (P.ker : Submodule P.Ring P.Ring)
  -- Two extra powers ensure N >= 2 even when the Artin--Rees index is zero.
  have hAR : (m ^ (c + 2) • (⊤ : Submodule P.Ring P.Ring) ⊓ P.ker) ≤
      m • P.ker := by
    rw [hc (c + 2) (by omega)]
    apply le_trans (smul_mono_right _ inf_le_right)
    apply Submodule.smul_mono_left
    simpa using (Ideal.pow_le_self (I := m) (n := 2) (by decide))
  obtain ⟨σ, hσ⟩ := artinian_lifting_truncated_section.{u, v} q P hlift (c + 2) (by omega)
  apply residue_retraction_of_kernel P.cotangentComplex
  exact truncated_section_conormal_residue_kernel P (c + 2) (by omega) hAR σ hσ

end Algebra
