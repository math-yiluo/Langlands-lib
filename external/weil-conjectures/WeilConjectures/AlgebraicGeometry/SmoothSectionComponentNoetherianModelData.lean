/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.NoetherianApproximationSmoothStage

/-!
# Local noetherian approximation of a smooth morphism and its section

Source: Stacks Project, Tags 055Q, 01ZM and 0C0C.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- Descend the smooth morphism first, then lift its descended section into a
later pullback. The section argument follows the already proved
`exists_noetherian_model_with_section` (Stacks Tags 01ZM and 055P). -/
private theorem exists_smooth_noetherian_model_with_section {X S : Scheme.{u}}
    [IsAffine S] (f : X ⟶ S) [Smooth f] [QuasiCompact f] [QuasiSeparated f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    ∃ (X₀ S₀ : Scheme.{u}) (f₀ : X₀ ⟶ S₀) (σ₀ : S₀ ⟶ X₀)
      (a : X ⟶ X₀) (b : S ⟶ S₀),
      IsNoetherian S₀ ∧ Smooth f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
      σ₀ ≫ f₀ = 𝟙 S₀ ∧ IsPullback a f f₀ b ∧ σ ≫ a = b ≫ σ₀ := by
  classical
  let N := Scheme.NoetherianApproximation.ofIsAffine S
  obtain ⟨i₁, Y₁, q₁, hqfp, hqqc, hqqs, a₁, H₁⟩ :=
    Scheme.exists_isPullback_of_finitePresentation (D := N.D) N.isLimit f
  let : LocallyOfFinitePresentation q₁ := hqfp
  let : QuasiCompact q₁ := hqqc
  let : QuasiSeparated q₁ := hqqs
  obtain ⟨j₁, hj₁⟩ := N.exists_smooth_affine_model q₁ f a₁ H₁
  let i := j₁.left
  let Y := Limits.pullback q₁ (N.D.map j₁.hom)
  let q : Y ⟶ N.D.obj i := Limits.pullback.snd _ _
  let : Smooth q := hj₁
  let a : X ⟶ Y := Limits.pullback.lift a₁ (f ≫ N.π.app i) (by
    rw [H₁.w, Category.assoc, (Limits.Cone.mk S N.π).w j₁.hom])
  have H : IsPullback a f q (N.π.app i) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback q₁ (N.D.map j₁.hom))
    · simpa only [a, Limits.pullback.lift_fst, i, (Limits.Cone.mk S N.π).w j₁.hom] using H₁
    · simp [a]
  let D := Over.forget i ⋙ N.D
  have : ∀ {j k : Over i} (v : j ⟶ k), IsAffineHom (D.map v) := fun v ↦
    inferInstanceAs (IsAffineHom (N.D.map v.left))
  have : ∀ j : Over i, CompactSpace (D.obj j) := fun j ↦
    inferInstanceAs (CompactSpace (N.D.obj j.left))
  have : ∀ j : Over i, QuasiSeparatedSpace (D.obj j) := fun j ↦
    inferInstanceAs (QuasiSeparatedSpace (N.D.obj j.left))
  let c := (Limits.Cone.mk S N.π).whisker (Over.forget i)
  let t : D ⟶ (Functor.const (Over i)).obj (N.D.obj i) :=
    { app := fun j ↦ N.D.map j.hom
      naturality := fun j k v ↦ by
        change N.D.map v.left ≫ N.D.map k.hom = N.D.map j.hom ≫ 𝟙 _
        rw [← N.D.map_comp, Over.w v, Category.comp_id] }
  obtain ⟨j, τ, hτ, hτq⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t q c
      ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) (Limits.Cone.mk S N.π)).symm
        N.isLimit) (σ ≫ a) (by
        ext j
        change N.π.app j.left ≫ N.D.map j.hom = (σ ≫ a) ≫ q
        rw [Category.assoc, H.w, ← Category.assoc, hσ, Category.id_comp]
        exact (Limits.Cone.mk S N.π).w j.hom)
  change N.π.app j.left ≫ τ = σ ≫ a at hτ
  change τ ≫ q = N.D.map j.hom at hτq
  let X₀ := Limits.pullback q (N.D.map j.hom)
  let f₀ : X₀ ⟶ N.D.obj j.left := Limits.pullback.snd _ _
  let σ₀ : N.D.obj j.left ⟶ X₀ := Limits.pullback.lift τ (𝟙 _) (by simp [hτq])
  let a₀ : X ⟶ X₀ := Limits.pullback.lift a (f ≫ N.π.app j.left) (by
    rw [H.w, Category.assoc, (Limits.Cone.mk S N.π).w j.hom])
  have Ha : IsPullback a₀ f f₀ (N.π.app j.left) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback q (N.D.map j.hom))
    · simpa [a₀, (Limits.Cone.mk S N.π).w j.hom] using H
    · simp [a₀]
  have hsection : σ ≫ a₀ = N.π.app j.left ≫ σ₀ := by
    apply Limits.pullback.hom_ext
    · simpa [a₀, σ₀, Category.assoc] using hτ.symm
    · simp only [a₀, σ₀, Category.assoc, Limits.pullback.lift_snd, Category.comp_id]
      rw [← Category.assoc, hσ, Category.id_comp]
  have : Smooth f₀ := inferInstanceAs
    (Smooth (Limits.pullback.snd q (N.D.map j.hom)))
  have : LocallyOfFinitePresentation f₀ := inferInstanceAs
    (LocallyOfFinitePresentation (Limits.pullback.snd q (N.D.map j.hom)))
  have : QuasiCompact f₀ := inferInstanceAs (QuasiCompact (Limits.pullback.snd q (N.D.map j.hom)))
  have : QuasiSeparated f₀ := inferInstanceAs
    (QuasiSeparated (Limits.pullback.snd q (N.D.map j.hom)))
  exact ⟨X₀, N.D.obj j.left, f₀, σ₀, a₀, N.π.app j.left,
    inferInstance, inferInstance, inferInstance, inferInstance, by simp [σ₀, f₀], Ha,
    hsection⟩

/-- A smooth quasi-compact quasi-separated morphism with a section admits, near any
source point, a noetherian model together with cartesian comparison squares and a
compatible restricted section. No assertion about connected components is made here.

Source: Stacks Project, Tag 055Q, first two paragraphs; Tag 01ZM, clauses (1)-(3);
and Tag 0C0C (descent of smoothness).
Proof: choose an affine open V containing g(x), and set W = g⁻¹(V). The restriction
q : W → V is smooth and finitely presented: smoothness gives local finite presentation,
and quasi-compactness and quasi-separatedness give finite presentation. Its section τ
is the restriction of σ, so τ≫W.ι = V.ι≫σ. Express the coordinate ring of V as the
filtered union of its finite-type ℤ-subalgebras. Tag 01ZM(1) descends q to a finitely
presented stage model. The eventual-smoothness theorem (Tag 0C0C) permits an increase
so that this model is smooth. Tag 01ZM(2) then descends the section composed with
the source comparison to a later base stage, over the smooth model's base. Lift
this map and the identity into the pullback of the model to that stage. The second
projection gives the section identity directly; the first projection and uniqueness
of pullback lifts give compatibility with τ. The affine base T₀ is noetherian
because its ring is finite type over ℤ. Finite presentation of g₀ supplies quasi-compactness and
quasi-separatedness. The base-change isomorphism supplies a and b and the second
cartesian square, with τ≫a = b≫σ₀. The first square is cartesian by the construction
W = g⁻¹(V). Every later increase of the index preserves these identities.

(blueprint: lem-sbc-smooth-section-component-noetherian-model-data) -/
theorem Smooth.exists_section_component_noetherian_model_data {P T : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (x : P) :
    ∃ (W : P.Opens) (_ : x ∈ W) (V : T.Opens) (P₀ T₀ : Scheme.{u})
      (g₀ : P₀ ⟶ T₀) (σ₀ : T₀ ⟶ P₀) (a : W.toScheme ⟶ P₀)
      (q : W.toScheme ⟶ V.toScheme) (τ : V.toScheme ⟶ W.toScheme)
      (b : V.toScheme ⟶ T₀),
      IsNoetherian T₀ ∧ Smooth g₀ ∧ QuasiCompact g₀ ∧ QuasiSeparated g₀ ∧
      σ₀ ≫ g₀ = 𝟙 T₀ ∧ τ ≫ q = 𝟙 V.toScheme ∧
      IsPullback W.ι q g V.ι ∧ IsPullback a q g₀ b ∧
      τ ≫ W.ι = V.ι ≫ σ ∧ τ ≫ a = b ≫ σ₀ := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x)) isOpen_univ
  let V : T.Opens := V
  let : IsAffine V.toScheme := hV
  let W := g ⁻¹ᵁ V
  let q := g ∣_ V
  have H : IsPullback W.ι q g V.ι := (isPullback_morphismRestrict g V).flip
  let τ : V.toScheme ⟶ W.toScheme := H.lift (V.ι ≫ σ) (𝟙 V.toScheme) (by
    simp [hσ])
  have hτ : τ ≫ q = 𝟙 V.toScheme := H.lift_snd _ _ _
  have hcompat : τ ≫ W.ι = V.ι ≫ σ := H.lift_fst _ _ _
  obtain ⟨P₀, T₀, g₀, σ₀, a, b, hT₀, hg₀, hqc₀, hqs₀, hσ₀, H₀, hcompat₀⟩ :=
    exists_smooth_noetherian_model_with_section q τ hτ
  exact ⟨W, hxV, V, P₀, T₀, g₀, σ₀, a, q, τ, b,
    hT₀, hg₀, hqc₀, hqs₀, hσ₀, hτ, H, H₀, hcompat, hcompat₀⟩

end AlgebraicGeometry
