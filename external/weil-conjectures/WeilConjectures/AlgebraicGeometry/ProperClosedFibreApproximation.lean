/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.ProperLimitNoetherian
import WeilConjectures.AlgebraicGeometry.AffineApproximationRingPresentation
import WeilConjectures.AlgebraicGeometry.QuotientFibreLimitTransfer

/-!
# Closed fibres of proper Noetherian approximations

Source: Stacks Project, Tag 0GS2, proof, General case, and Tag 0A0P.
(blueprint: lem-weil-pbc-proper-closed-fibre-approximation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The closed fibre of a proper scheme is a directed limit of the closed fibres
of proper models over finite-type integer rings, with affine transitions.
This construction depends only on the proper morphism and its base ideal; no cover
or descent of a cover is part of its conclusion.

Source: Stacks Project, Tag 0GS2, proof, General case, first approximation paragraph;
Tag 0A0P, proper Noetherian approximation.
(blueprint: lem-weil-pbc-proper-closed-fibre-approximation).

Proof:
1. Apply proper Noetherian approximation with its affine clause to f. Choose the
   proper stages X_i over Spec R_i, where R_i is finite type over the integers,
   and the compatible projections p_i and ring maps alpha_i : R_i -> A. Their
   rings have colimit A, and the schemes X_i have limit Y.
2. Put K_i = alpha_i^{-1}(I). The transition maps preserve these ideals. The
   quotient cocone has colimit A/I: represent any element by an element of a
   stage ring; if its image is zero modulo I, that representative already lies
   in K_i. Equivalently, compatible maps from all R_i/K_i induce a map from A
   that kills I, and therefore a unique map from A/I.
3. Apply Spec to this quotient colimit. Pullbacks commute with limits, so the
   closed fibres X_i,0 have limit Y_0. The projections are induced by p_i and
   the quotient ring maps; the pullback projection equations give exactly the
   two compatibilities below. Isomorphisms e allow arbitrary choices of objects
   for the resulting diagram without imposing definitional equalities.
4. A transition X_j,0 -> X_i,0 factors through the base change of X_i,0 to X_j:
   the first map is a closed immersion, because the extended K_i is contained
   in K_j, and the second is a base change of the affine transition X_j -> X_i.
   Thus transitions are affine. Each closed fibre is proper over an affine
   scheme, hence quasi-compact and quasi-separated. This also covers I = top,
   when every closed fibre is empty, and the zero base ring. -/
theorem exists_proper_closedFibre_approximation
    {A : Type u} [CommRing A] (I : Ideal A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λᵒᵖ ⥤ Scheme.{u})
      (π : (Functor.const Λᵒᵖ).obj
        (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⟶ D),
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      (∀ {i j : Λᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)) ∧
      (∀ i, CompactSpace (D.obj i)) ∧ (∀ i, QuasiSeparatedSpace (D.obj i)) ∧
      ∀ i : Λᵒᵖ,
        ∃ (R : Type u) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R)
          (α : R →+* A) (X : Scheme.{u}) (h : X ⟶ Spec (.of R)) (_ : IsProper h)
          (p : Y ⟶ X)
          (e : D.obj i ≅ pullback h (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I.comap α))))),
          p ≫ h = f ≫ Spec.map (CommRingCat.ofHom α) ∧
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ p =
            (π.app i ≫ e.hom) ≫ pullback.fst h (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I.comap α)))) ∧
          (π.app i ≫ e.hom) ≫ pullback.snd h (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I.comap α)))) =
            pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
              Spec.map (CommRingCat.ofHom (Ideal.quotientMap I α le_rfl)) := by
  obtain ⟨Λ, hpre, hne, hdir, Xs, Ss, fs, p, s, hl, hs, ht, hp, hft, hw, ha⟩ :=
    AlgebraicGeometry.exists_proper_limit_noetherian f
  let _ : Preorder Λ := hpre
  let _ : Nonempty Λ := hne
  let _ : IsDirected Λ (· ≤ ·) := hdir
  obtain ⟨has, hcs⟩ := ha inferInstance
  obtain ⟨B, g, α, hc, hB, hg, hpg⟩ := affine_approximation_ring_presentation
    f Xs Ss fs p s (fun i ↦ (has i).1) (fun i ↦ (has i).2) hcs hp hw
  obtain ⟨D, π, hlim, haff, he⟩ := quotient_fibre_limit_transfer I f B Xs g α p hc hl
    (fun {i j} a ↦ (ht i j a).1) hpg
  have hstage (i : Λᵒᵖ) : CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i) := by
    obtain ⟨e, _⟩ := he i
    let _ : IsProper (g.app i) := hg i
    let q := pullback.snd (g.app i) (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I.comap (α.app i.unop).hom))))
    exact ⟨QuasiCompact.compactSpace_of_compactSpace (e.hom ≫ q),
      quasiSeparatedSpace_of_quasiSeparated (e.hom ≫ q)⟩
  refine ⟨Λ, hpre, hne, hdir, D, π, hlim, haff,
    (fun i ↦ (hstage i).1), (fun i ↦ (hstage i).2), ?_⟩
  intro i
  obtain ⟨e, he₁, he₂⟩ := he i
  exact ⟨B.obj i.unop, inferInstance, hB i.unop, (α.app i.unop).hom,
    Xs.obj i, g.app i, hg i, p.app i, e, hpg i, he₁, he₂⟩

end AlgebraicGeometry.Scheme
