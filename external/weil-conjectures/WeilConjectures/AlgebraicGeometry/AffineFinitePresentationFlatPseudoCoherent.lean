/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A bounded-above finite-presentation flat quasi-coherent complex on an affine
scheme has pseudo-coherent global sections.
Source: Stacks Project, Tag 064U, implication (3) to (1), and the affine
quasi-coherent equivalence used in Tag 08EB.
(blueprint: lem-pc-affine-finite-presentation-flat-pseudo-coherent).

Proof: Identify S with Spec A for A = Γ(S, ⊤). The affine quasi-coherent
equivalence identifies each section module of D with a finitely presented flat
A-module, hence a finite projective module. Evaluation preserves zero objects,
so the section complex P is zero above b. For its top term choose a finite
projective complement C^b such that P^b ⊕ C^b is finite free. Descending in n,
choose a finite projective complement C^(n-1) so that
P^(n-1) ⊕ C^n ⊕ C^(n-1) is finite free. This yields a bounded-above complex F:
its differential agrees with that of P on the P summands, is the identity on
C^n between degrees n-1 and n, and zero on the remaining complement. Thus F
is the direct sum of P and contractible identity pairs. Projection F → P is a
homotopy equivalence, hence a quasi-isomorphism and gives Q(F) ≅ Q(P). All
terms of F are finite free, and F is zero above b. These data witness the
ring definition of pseudo-coherence. The complements may continue indefinitely
below; no lower bound on F is asserted or required. The zero ring and the zero
complex also satisfy this construction. -/
theorem affine_finitePresentation_flat_pseudoCoherent (S : Scheme.{u})
    (hS : IsAffine S) (D : CochainComplex S.Modules ℤ) (b : ℕ)
    (hDle : D.IsStrictlyLE b)
    (hDflat : ∀ n : ℤ, (D.X n).IsFlatOver (𝟙 S))
    (hDqc : ∀ n : ℤ, (D.X n).IsQuasicoherent)
    (hDfp : ∀ n : ℤ, (D.X n).IsFinitePresentation) :
      (letI : CommRing (S.ringCatSheaf.obj.obj (.op ⊤)) :=
        inferInstanceAs (CommRing Γ(S, ⊤));
        letI := HasDerivedCategory.standard (ModuleCat.{u} (S.ringCatSheaf.obj.obj (.op ⊤)));
        DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
          (((SheafOfModules.evaluation.{u} S.ringCatSheaf (.op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D))) := by
  have := hS
  let A := S.ringCatSheaf.obj.obj (.op ⊤)
  let : CommRing A := inferInstanceAs (CommRing Γ(S, ⊤))
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let P : CochainComplex (ModuleCat.{u} A) ℤ :=
    ((SheafOfModules.evaluation.{u} S.ringCatSheaf (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj D
  have hPbound : P.IsStrictlyLE (b : ℤ) := by
    have := hDle
    exact inferInstance
  have hterms : ∀ n : ℤ, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n) := by
    intro n
    change Module.Finite Γ(S, ⊤) Γ(D.X n, ⊤) ∧
      Module.Projective Γ(S, ⊤) Γ(D.X n, ⊤)
    have := hDqc n
    have := hDfp n
    have hfp : Module.FinitePresentation Γ(S, ⊤) Γ(D.X n, ⊤) :=
      finitePresentation_sections_of_isFinitePresentation (D.X n) (isAffineOpen_top S)
    have hflat := hDflat n ⟨⊤, isAffineOpen_top S⟩ ⟨⊤, isAffineOpen_top S⟩ (by simp)
    have he : Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ (by simp) = 𝟙 Γ(S, ⊤) := by
      simp [Scheme.Hom.appLE]
    dsimp only at hflat
    rw [he] at hflat
    change Module.Flat Γ(S, ⊤) Γ(D.X n, ⊤) at hflat
    have : Module.Flat Γ(S, ⊤) Γ(D.X n, ⊤) := hflat
    exact ⟨inferInstanceAs (Module.Finite Γ(S, ⊤) Γ(D.X n, ⊤)),
      Module.Flat.projective_of_finitePresentation⟩
  obtain ⟨F, hFbound, hFfree, f, hf⟩ :=
    CochainComplex.exists_finiteFree_model_of_finite_projective A P (b : ℤ) hPbound
      (fun n ↦ (hterms n).1) (fun n ↦ (hterms n).2)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) f).mpr hf
  exact ⟨F, (b : ℤ), hFbound, hFfree, ⟨asIso (DerivedCategory.Q.map f)⟩⟩

end AlgebraicGeometry.Scheme.Modules
