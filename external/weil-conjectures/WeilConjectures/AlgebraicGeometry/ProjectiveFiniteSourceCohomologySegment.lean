/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.ProjectiveFiniteCohomologyPresentation
import WeilConjectures.AlgebraicGeometry.PQFCohomology

/-! # A finite-source cohomology segment for a projective embedding

Source: Stacks Project, Tags 01YS (Lemma 30.14.1 (3)) and 01Y6 (Lemma 30.9.9).
(blueprint: lem-pc-p2-projective-finite-source-cohomology-segment)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

-- Comparing the underlying Ext cohomology with pushforward unfolds several functors.
private theorem pushforward_cohomology_linearEquiv
    {X P T : Scheme.{u}} (j : X ⟶ P) [IsAffineHom j] (g : P ⟶ T)
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) :
    letI : Module Γ(T, ⊤) (F.H q) := Module.compHom _ (j ≫ g).appTop.hom
    letI : Module Γ(T, ⊤) (((pushforward j).obj F).H q) :=
      Module.compHom _ g.appTop.hom
    Nonempty (F.H q ≃ₗ[Γ(T, ⊤)] ((pushforward j).obj F).H q) := by
  let : Module Γ(T, ⊤) (F.H q) := Module.compHom _ (j ≫ g).appTop.hom
  let : Module Γ(T, ⊤) (((pushforward j).obj F).H q) :=
    Module.compHom _ g.appTop.hom
  obtain ⟨e⟩ := nonempty_functorH_iso_pushforwardAb_of_isAffineHom j q
  let A := (cechAcyclicOnAffines X).FullSubcategory
  let M : A := ⟨(SheafOfModules.toSheaf X.ringCatSheaf).obj F,
    cechAcyclicOnAffines_of_isQuasicoherent F⟩
  let E : F.H q ≃+ ((pushforward j).obj F).H q :=
    (e.app M).addCommGroupIsoToAddEquiv
  refine ⟨{ E with map_smul' := fun c x ↦ ?_ }⟩
  change E (H.map (F.smulHom ((j ≫ g).appTop c)) q x) =
    H.map (((pushforward j).obj F).smulHom (g.appTop c)) q (E x)
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← pushforward_map_smulHom]
  have h := NatTrans.naturality_apply e.hom
    (ObjectProperty.homMk ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (F.smulHom (j.appTop (g.appTop c)))) : M ⟶ M) x
  exact h

/-- The descending-induction segment, without assuming finiteness of its last term.

Source: Stacks Project, Tags 01YS (Lemma 30.14.1 (3)) and 01Y6 (Lemma 30.9.9).
(blueprint: lem-pc-p2-projective-finite-source-cohomology-segment)

Proof: identify the affine base T with Spec Gamma(T,O), and transport the specified
closed embedding to projective space over that ring. Push F forward along the embedding;
closed pushforward is quasi-coherent and finitely presented on the Noetherian projective
space and preserves cohomology. Choose an epimorphism E -> j_* F from a finite sum of
negative twists by clearing denominators of finitely many generators on the standard
charts. Its kernel K is quasi-coherent and finitely presented. The long exact sequence
contains H^q(E) -> H^q(j_* F) -> H^(q+1)(K). Set V = H^q(E), which is finite: cohomology
commutes with finite sums, and the standard-cover monomial calculation gives finite free
cohomology for each twist over the base ring. Transport the middle term to H^q(F).
All maps, including the closed-pushforward comparison and the affine-base identification,
commute with multiplication by base sections, so this is an exact segment of modules
with precisely the displayed restriction-of-scalars actions. No finiteness of H^(q+1)(K)
is asserted. If the coordinate type is empty, projective space and Y are empty; take
K and V zero, and the segment is exact. -/
theorem exists_projective_finite_source_cohomology_segment
    {Y T : Scheme.{u}} [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (F : Y.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (q : ℕ) :
    letI : Module Γ(T, ⊤) (F.H q) :=
      Module.compHom _ (j ≫ (ℙ(N; T) ↘ T)).appTop.hom
    ∃ (K : (ℙ(N; T)).Modules) (_ : K.IsQuasicoherent) (_ : K.IsFinitePresentation),
      letI : Module Γ(T, ⊤) (K.H (q + 1)) :=
        Module.compHom _ (ℙ(N; T) ↘ T).appTop.hom
      ∃ (V : ModuleCat.{u} Γ(T, ⊤)) (_ : Module.Finite Γ(T, ⊤) V)
        (a : V →ₗ[Γ(T, ⊤)] F.H q) (b : F.H q →ₗ[Γ(T, ⊤)] K.H (q + 1)),
        Function.Exact a b := by
  let P := ℙ(N; T)
  let g : P ⟶ T := P ↘ T
  obtain ⟨E, φ, hφ, hKqc, hKfp, hE⟩ :=
    exists_projective_finite_cohomology_presentation N j F q
  have : Epi φ := hφ
  let K := Limits.kernel φ
  let S : ShortComplex P.Modules :=
    ShortComplex.mk (Limits.kernel.ι φ) φ (Limits.kernel.condition φ)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel φ }
  let : Module Γ(T, ⊤) (E.H q) := Module.compHom _ g.appTop.hom
  let : Module Γ(T, ⊤) (F.H q) := Module.compHom _ (j ≫ g).appTop.hom
  let : Module Γ(T, ⊤) (((pushforward j).obj F).H q) :=
    Module.compHom _ g.appTop.hom
  let : Module Γ(T, ⊤) (K.H (q + 1)) := Module.compHom _ g.appTop.hom
  obtain ⟨e⟩ := pushforward_cohomology_linearEquiv j g F q
  let a₀ : E.H q →ₗ[Γ(T, ⊤)] ((pushforward j).obj F).H q :=
    { toFun := H.map φ q
      map_add' := map_add _
      map_smul' := fun c x ↦ H.map_smul φ q (g.appTop c) x }
  let b₀ : ((pushforward j).obj F).H q →ₗ[Γ(T, ⊤)] K.H (q + 1) :=
    { toFun := H.δ hS q
      map_add' := map_add _
      map_smul' := fun c x ↦ H.δ_smul hS q (g.appTop c) x }
  have hex : Function.Exact a₀ b₀ :=
    AddMonoidHom.exact_iff.mpr (H.ker_δ_eq_range_map_g hS q)
  refine ⟨K, hKqc, hKfp, ModuleCat.of Γ(T, ⊤) (E.H q), hE,
    e.symm.toLinearMap.comp a₀, b₀.comp e.toLinearMap, ?_⟩
  intro x
  change b₀ (e x) = 0 ↔ ∃ y, e.symm (a₀ y) = x
  rw [hex (e x)]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [hy, e.symm_apply_apply]⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [← hy, e.apply_symm_apply]⟩

end AlgebraicGeometry.Scheme.Modules
