/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.EssSurj

/-!
# Essential surjectivity of base change along a universal homeomorphism

Let `f : X ⟶ Y` be a universal homeomorphism. We show that every étale `X`-scheme is the base
change of an étale `Y`-scheme, i.e. that `f.Etale : Y.Etale ⥤ X.Etale` is essentially
surjective.

By `AlgebraicGeometry.Scheme.Hom.etale_essImage_of_forall_exists_mem` it suffices to show that
every point `u` of an étale `X`-scheme `U` has an open neighbourhood in the essential image.
Choosing affine opens `Y₀ ⊆ Y`, `U₀ ⊆ U` over `f ⁻¹ᵁ Y₀`, and shrinking `U₀` to a basic open on
which `U₀ ⟶ f ⁻¹ᵁ Y₀` is standard étale, the fibre degrees become bounded, and the affine
case `AlgebraicGeometry.Scheme.Hom.descendsWithBound` applies.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

section Bound

variable {U X : Scheme.{u}} (g : U ⟶ X) [AlgebraicGeometry.Etale g]

/-- Every point of an étale scheme over `X` has an affine open neighbourhood, contained in a
given affine open `U₀` lying over an affine open `X₀ ⊆ X`, on which the fibre degrees over
`X₀` are bounded. -/
lemma exists_isAffineOpen_le_forall_fiberDegree_le {X₀ : X.Opens} (hX₀ : IsAffineOpen X₀)
    {U₀ : U.Opens} (hU₀ : IsAffineOpen U₀) (e : U₀ ≤ g ⁻¹ᵁ X₀) {u : U} (hu : u ∈ U₀) :
    ∃ (W : U.Opens) (hW : W ≤ U₀) (hWa : IsAffineOpen W) (n : ℕ), u ∈ W ∧
      haveI : IsAffine W.toScheme := hWa
      haveI : IsAffine X₀.toScheme := hX₀
      ∀ x, (g.resLE X₀ W (hW.trans e)).fiberDegree x ≤ n := by
  have hφ : (g.appLE X₀ U₀ e).hom.Etale := g.etale_appLE hX₀ hU₀ e
  algebraize [(g.appLE X₀ U₀ e).hom]
  have : Algebra.Etale Γ(X, X₀) Γ(U, U₀) := RingHom.etale_algebraMap.mp hφ
  let q := hU₀.primeIdealOf ⟨u, hu⟩
  obtain ⟨c, hcq, hc⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := Γ(X, X₀)) q.asIdeal
  have hW : U.basicOpen c ≤ U₀ := U.basicOpen_le c
  have hWa : IsAffineOpen (U.basicOpen c) := hU₀.basicOpen c
  have hu' : u ∈ U.basicOpen c := by
    have hmem : (⟨u, hu⟩ : U₀) ∈ U₀.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen c := hcq
    rwa [Opens.toSpecΓ_preimage_basicOpen] at hmem
  -- the algebra structure on `Γ(U, U.basicOpen c)` over `Γ(X, X₀)`
  have hφ' : g.appLE X₀ (U.basicOpen c) (hW.trans e) =
      g.appLE X₀ U₀ e ≫ U.presheaf.map (homOfLE hW).op := (g.appLE_map e _).symm
  let _ : Algebra Γ(X, X₀) Γ(U, U.basicOpen c) :=
    (g.appLE X₀ (U.basicOpen c) (hW.trans e)).hom.toAlgebra
  have : IsScalarTower Γ(X, X₀) Γ(U, U₀) Γ(U, U.basicOpen c) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change (g.appLE X₀ (U.basicOpen c) (hW.trans e)).hom x = _
      rw [hφ']
      rfl
  have hst : Algebra.IsStandardEtale Γ(X, X₀) Γ(U, U.basicOpen c) :=
    have := hU₀.isLocalization_basicOpen c
    Algebra.IsStandardEtale.of_equiv ((IsLocalization.algEquiv (Submonoid.powers c)
      (Localization.Away c) Γ(U, U.basicOpen c)).restrictScalars Γ(X, X₀))
  have : IsAffine (U.basicOpen c).toScheme := hWa
  have : IsAffine X₀.toScheme := hX₀
  have hiso₁ : IsIso (U.basicOpen c).toSpecΓ := inferInstanceAs (IsIso hWa.isoSpec.hom)
  have hiso₂ : IsIso X₀.toSpecΓ := inferInstanceAs (IsIso hX₀.isoSpec.hom)
  have hsq : IsPullback (U.basicOpen c).toSpecΓ (g.resLE X₀ (U.basicOpen c) (hW.trans e))
      (Spec.map (g.appLE X₀ (U.basicOpen c) (hW.trans e))) X₀.toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨Scheme.Opens.toSpecΓ_SpecMap_appLE g X₀ _ _⟩
  obtain ⟨n, hn⟩ := Scheme.Hom.exists_forall_fiberDegree_SpecMap_le Γ(X, X₀) Γ(U, U.basicOpen c)
  refine ⟨U.basicOpen c, hW, hWa, n, hu', fun x ↦ ?_⟩
  rw [(Spec.map (g.appLE X₀ (U.basicOpen c) (hW.trans e))).fiberDegree_of_isPullback hsq x]
  exact hn _

end Bound

section EssSurj

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

/-- **Essential surjectivity of base change along a universal homeomorphism**: every étale
`X`-scheme is in the essential image of `f.Etale : Y.Etale ⥤ X.Etale`, [Stacks 04DZ]. -/
theorem etale_essImage (U : X.Etale) : f.Etale.essImage U := by
  refine etale_essImage_of_forall_exists_mem f U fun u ↦ ?_
  -- affine opens `Y₀ ∋ f (U.hom u)`, `X₀ = f ⁻¹ᵁ Y₀` and `U₀ ∋ u` over `X₀`.
  obtain ⟨_, ⟨Y₀, hY₀, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (U.hom u))) isOpen_univ
  have hX₀ : IsAffineOpen (f ⁻¹ᵁ Y₀) := hY₀.preimage f
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hu, hU₀X₀⟩ :=
    U.left.isBasis_affineOpens.exists_subset_of_mem_open (show u ∈ U.hom ⁻¹ᵁ (f ⁻¹ᵁ Y₀) from hy)
      (U.hom ⁻¹ᵁ (f ⁻¹ᵁ Y₀)).isOpen
  obtain ⟨W, hW, hWa, n, huW, hn⟩ := exists_isAffineOpen_le_forall_fiberDegree_le U.hom hX₀ hU₀
    hU₀X₀ hu
  have : IsAffine W.toScheme := hWa
  have : IsAffine (f ⁻¹ᵁ Y₀).toScheme := hX₀
  have : IsAffine (Scheme.Opens.toScheme Y₀) := hY₀
  -- the affine case
  let U' : (f ⁻¹ᵁ Y₀).toScheme.Etale := Etale.mk (U.hom.resLE (f ⁻¹ᵁ Y₀) W (hW.trans hU₀X₀))
  have : IsAffineHom U'.hom := inferInstanceAs (IsAffineHom (U.hom.resLE (f ⁻¹ᵁ Y₀) W _))
  obtain ⟨V₀, -, ⟨e⟩⟩ := descendsWithBound n (f ∣_ Y₀) U' hn
  refine ⟨W, huW, ?_⟩
  have h := etale_essImage_etaleOfRestrict f Y₀ ⟨V₀, ⟨e⟩⟩
  refine Functor.essImage.ofIso ?_ h
  exact MorphismProperty.Over.isoMk (Iso.refl _) (by simp [U'])

/-- Base change along a universal homeomorphism is essentially surjective on étale schemes. -/
instance etale_essSurj : f.Etale.EssSurj where
  mem_essImage U := etale_essImage f U

end EssSurj

end AlgebraicGeometry.Scheme.Hom
