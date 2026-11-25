/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.AffineFinitePresentationFlatShorteningConstruction
import WeilConjectures.AlgebraicGeometry.AffineFinitePresentationFlatPseudoCoherent

/-! # Shortening a finite-presentation flat complex on an affine scheme -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Residue-field vanishing shortens a bounded finite-presentation flat complex on
an affine scheme without shrinking that scheme. This is an algebraic statement;
there is no proper morphism, coefficient sheaf, or competing cohomology model.
Source: Stacks Project, https://stacks.math.columbia.edu/tag/068V (residue criterion),
Tags 0653 and 064U (Tor-amplitude and finite-projective representatives), and 08EB.
(blueprint: lem-pc-affine-finite-presentation-flat-shortening).

Proof:
1. Identify S with Spec A. The affine quasi-coherent equivalence identifies the
   global-section terms of B with finitely presented flat A-modules, hence finite
   projectives. The complex P of sections is concentrated in [0,b], and associated
   sheaves recover B, including its differentials. Residue pullback is ordinary
   tensor of P with the corresponding residue field.
2. If the top degree m is greater than d, its fibre homology is the cokernel of
   the preceding differential. This cokernel is finite and has zero fibre at every
   prime by hvan. Local Nakayama makes its localization zero at every prime;
   hence it is zero. The differential onto P^m is therefore surjective and splits
   because P^m is projective. Decompose P^(m-1) as its finite-projective kernel
   plus P^m. The complex relation makes the preceding differential land in that
   kernel, so the P^m summands in degrees m-1,m form a contractible subcomplex.
   Remove it. This is a chain homotopy equivalence, preserved by every tensor.
3. Repeat at the next top degree until the complex is concentrated in [0,d].
   All replacements are finite projective. No negative term is introduced:
   each removed pair has m > d >= 0, hence m-1 >= 0. If b <= d no cancellation
   is needed. Associate sheaves to the resulting complex and transport to S.
   Its terms are flat and quasi-coherent. Its section complex is bounded finite
   projective, hence pseudo-coherent: successively add finite-projective
   complements as contractible pairs, descending from the top degree, to form
   a bounded-above finite free complex with the same derived image (Tag 064U).
   That free complex may be unbounded below, as the definition permits.
4. Pullback preserves the chain homotopy equivalences from step 2. Taking homology
   gives the isomorphisms for every scheme over S, including nonaffine ones.
   This keeps S fixed and claims no global freeness. For the zero ring use the
   zero complex; d = 0 yields a finite-projective module in degree zero. -/
theorem exists_affine_finitePresentation_flat_shortening (S : Scheme.{u})
    (hS : IsAffine S) (B : CochainComplex S.Modules ℤ) (b d : ℕ)
    (hBge : B.IsStrictlyGE 0) (hBle : B.IsStrictlyLE b)
    (hBflat : ∀ n : ℤ, (B.X n).IsFlatOver (𝟙 S))
    (hBqc : ∀ n : ℤ, (B.X n).IsQuasicoherent)
    (hBfp : ∀ n : ℤ, (B.X n).IsFinitePresentation)
    (hvan : ∀ (s : S) (q : ℕ), d < q →
      IsZero ((((Modules.pullback (S.fromSpecResidueField s)).mapHomologicalComplex _).obj
        B).homology q)) :
    ∃ D : CochainComplex S.Modules ℤ,
      D.IsStrictlyGE 0 ∧ D.IsStrictlyLE d ∧
      (∀ n : ℤ, (D.X n).IsFlatOver (𝟙 S)) ∧
      (∀ n : ℤ, (D.X n).IsQuasicoherent) ∧
      (letI : CommRing (S.ringCatSheaf.obj.obj (.op ⊤)) :=
        inferInstanceAs (CommRing Γ(S, ⊤));
        letI := HasDerivedCategory.standard (ModuleCat.{u} (S.ringCatSheaf.obj.obj (.op ⊤)));
        DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
          (((SheafOfModules.evaluation.{u} S.ringCatSheaf (.op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D))) ∧
      ∀ {T' : Scheme.{u}} (g : T' ⟶ S) (q : ℕ),
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj D).homology q ≅
          (((Modules.pullback g).mapHomologicalComplex _).obj B).homology q) := by
  obtain ⟨D, hDge, hDle, hDflat, hDqc, hDfp, ⟨e⟩⟩ :=
    affine_finitePresentation_flat_shortening_construction S hS B b d hBge hBle
      hBflat hBqc hBfp hvan
  refine ⟨D, hDge, hDle, hDflat, hDqc,
    affine_finitePresentation_flat_pseudoCoherent S hS D d hDle hDflat hDqc hDfp, ?_⟩
  intro T' g q
  exact ⟨((Modules.pullback g).mapHomotopyEquiv e).toHomologyIso (q : ℤ)⟩

end AlgebraicGeometry.Scheme.Modules
