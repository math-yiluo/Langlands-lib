/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.AffineSpaceRigidity

/-!
# Rigidity of invertible modules over a basic open of affine space

Let `k` be an algebraically closed field, `X` an integral `k`-scheme whose local rings are unique
factorization domains, and `U = D(r) = Spec k[x₁, …, x_d]_r` a basic open of affine `d`-space
with `k`-points `p` and `q`. For every invertible module `ℒ` on `X ×_k U` the restrictions
`ℒ|_{X × p}` and `ℒ|_{X × q}` are isomorphic (Stacks 0BEH).

## Strategy

The line through `p = (a_i)` and `q = (b_i)` is the `k`-algebra map
`ℓ : k[x₁, …, x_d] ⟶ k[t]`, `x_i ↦ a_i + t (b_i - a_i)`. With `f = ℓ r` it induces
`Ψ : k[x]_r ⟶ k[t]_f`, and `p`, `q` factor through `Spec Ψ` via the points `t = 0` and `t = 1`
of `D(f)` (`MvPolynomial.exists_algHom_localizationAway_polynomial`). The statement then follows
from the case of the affine line (`AlgebraicGeometry.nonempty_iso_pullback_lift_of_isAlgClosed`)
applied to the pullback of `ℒ` to `X ×_k D(f)`.

## Main results

- `AlgebraicGeometry.nonempty_iso_pullback_lift_of_isAlgClosed_mvPolynomial`: Stacks 0BEH for a
  basic open of affine `d`-space.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

/-- Two `k`-points of a basic open `D(r)` of affine space lie on a line: there is `f : k[t]`
and a `k`-algebra map `k[x]_r ⟶ k[t]_f` through which both points factor via evaluation at
`0` and `1`. -/
theorem MvPolynomial.exists_algHom_localizationAway_polynomial {k σ : Type*} [CommRing k]
    (r : MvPolynomial σ k) (φp φq : Localization.Away r →ₐ[k] k) :
    ∃ (f : k[X]) (Ψ : Localization.Away r →ₐ[k] Localization.Away f)
      (e₀ e₁ : Localization.Away f →ₐ[k] k), e₀.comp Ψ = φp ∧ e₁.comp Ψ = φq := by
  let a (i : σ) := φp (algebraMap (MvPolynomial σ k) (Localization.Away r) (MvPolynomial.X i))
  let b (i : σ) := φq (algebraMap (MvPolynomial σ k) (Localization.Away r) (MvPolynomial.X i))
  let ℓ : MvPolynomial σ k →ₐ[k] k[X] := aeval fun i ↦ Polynomial.C (a i) +
    Polynomial.X * Polynomial.C (b i - a i)
  have h₀ : (Polynomial.aeval 0).comp ℓ =
      φp.comp (IsScalarTower.toAlgHom k _ (Localization.Away r)) := by
    ext i
    simp [ℓ, a]
  have h₁ : (Polynomial.aeval 1).comp ℓ =
      φq.comp (IsScalarTower.toAlgHom k _ (Localization.Away r)) := by
    ext i
    simp [ℓ, b]
  have hu (φ : Localization.Away r →ₐ[k] k) (c : k)
      (h : (Polynomial.aeval c).comp ℓ = φ.comp (IsScalarTower.toAlgHom k _ _)) :
      ∀ y : Submonoid.powers (ℓ r), IsUnit (Polynomial.aeval c (y : k[X])) := by
    rintro ⟨_, n, rfl⟩
    have := congr($h r)
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [map_pow, this]
    exact ((IsLocalization.Away.algebraMap_isUnit r).map φ).pow n
  refine ⟨ℓ r, IsLocalization.Away.mapₐ _ _ ℓ r, IsLocalization.liftAlgHom (hu φp 0 h₀),
    IsLocalization.liftAlgHom (hu φq 1 h₁), ?_, ?_⟩
  · refine IsLocalization.algHom_ext (Submonoid.powers r) ?_
    ext i
    simpa [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq,
      Algebra.algHom, IsLocalization.lift_eq] using congr($h₀ (MvPolynomial.X i))
  · refine IsLocalization.algHom_ext (Submonoid.powers r) ?_
    ext i
    simpa [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq,
      Algebra.algHom, IsLocalization.lift_eq] using congr($h₁ (MvPolynomial.X i))

namespace AlgebraicGeometry
/-- Let `ψ : T' ⟶ T` be a morphism of `S`-schemes and `M` a module on `X ×_S T`. If the pullbacks
of `(𝟙 × ψ)^* M` along the sections `X ⟶ X ×_S T'` given by `p'` and `q'` are isomorphic, then
so are the pullbacks of `M` along the sections `X ⟶ X ×_S T` given by `p' ≫ ψ` and `q' ≫ ψ`. -/
lemma nonempty_iso_pullback_lift_of_comp {X S T T' : Scheme.{u}} {sX : X ⟶ S} {sT : T ⟶ S}
    {sT' : T' ⟶ S} (ψ : T' ⟶ T) (hψ : ψ ≫ sT = sT') {p' q' : X ⟶ T'}
    (hp' : 𝟙 X ≫ sX = p' ≫ sT') (hq' : 𝟙 X ≫ sX = q' ≫ sT') {gp gq : X ⟶ T}
    (hgp : 𝟙 X ≫ sX = gp ≫ sT) (hgq : 𝟙 X ≫ sX = gq ≫ sT) (hp : p' ≫ ψ = gp)
    (hq : q' ≫ ψ = gq) (M : (pullback sX sT).Modules)
    (H : Nonempty ((Scheme.Modules.pullback (pullback.lift (𝟙 X) p' hp')).obj
        ((Scheme.Modules.pullback (pullback.map sX sT' sX sT (𝟙 X) ψ (𝟙 S) (by simp)
          (by simp [hψ]))).obj M) ≅
      (Scheme.Modules.pullback (pullback.lift (𝟙 X) q' hq')).obj
        ((Scheme.Modules.pullback (pullback.map sX sT' sX sT (𝟙 X) ψ (𝟙 S) (by simp)
          (by simp [hψ]))).obj M))) :
    Nonempty ((Scheme.Modules.pullback (pullback.lift (𝟙 X) gp hgp)).obj M ≅
      (Scheme.Modules.pullback (pullback.lift (𝟙 X) gq hgq)).obj M) := by
  subst hp hq
  have h (g : X ⟶ T') (hg : 𝟙 X ≫ sX = g ≫ sT') :
      pullback.lift (𝟙 X) (g ≫ ψ) (by simp [hψ, ← hg]) = pullback.lift (𝟙 X) g hg ≫
        pullback.map sX sT' sX sT (𝟙 X) ψ (𝟙 S) (by simp) (by simp [hψ]) := by
    ext <;> simp
  obtain ⟨e⟩ := H
  rw [h p' hp', h q' hq']
  exact ⟨(Scheme.Modules.pullbackComp _ _).symm.app M ≪≫ e ≪≫
    (Scheme.Modules.pullbackComp _ _).app M⟩


/-- A `k`-point of `Spec A` (a section of the structure morphism) as a `k`-algebra map. -/
noncomputable def algHomOfSpecSection {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    (p : Spec (.of k) ⟶ Spec (.of A))
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _) : A →ₐ[k] k where
  __ := (Spec.preimage p).hom
  commutes' c := by
    have h : CommRingCat.ofHom (algebraMap k A) ≫ Spec.preimage p = 𝟙 _ :=
      Spec.map_injective (by simpa using hp)
    exact congr($h c)

/-- `Spec` of the `k`-algebra map attached to a `k`-point recovers the point. -/
lemma spec_map_algHomOfSpecSection {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    (p : Spec (.of k) ⟶ Spec (.of A))
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _) :
    Spec.map (CommRingCat.ofHom (algHomOfSpecSection p hp).toRingHom) = p :=
  Spec.map_preimage p

/-- **Rigidity of invertible modules over a basic open of affine space** (Stacks 0BEH, for a
basic open `D(r)` of affine `d`-space). Let `k` be an algebraically closed field, `X` an integral
`k`-scheme whose local rings are unique factorization domains, and `p`, `q` two `k`-points of
`D(r) = Spec k[x₁, …, x_d]_r`. For every invertible module `ℒ` on `X ×_k D(r)`, the pullbacks of
`ℒ` along the sections `X ⟶ X ×_k D(r)` at `p` and at `q` are isomorphic. -/
@[stacks 0BEH]
theorem nonempty_iso_pullback_lift_of_isAlgClosed_mvPolynomial
    {k : Type u} [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsIntegral X]
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (sX : X ⟶ Spec (.of k))
    {d : ℕ} (r : MvPolynomial (Fin d) k)
    (p q : Spec (.of k) ⟶ Spec (.of (Localization.Away r)))
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) = 𝟙 _)
    (hq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) = 𝟙 _)
    (M : (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))))).Modules)
    [M.IsInvertible] :
    Nonempty ((Scheme.Modules.pullback (pullback.lift (𝟙 X) (sX ≫ p) (by simp [hp]))).obj M ≅
      (Scheme.Modules.pullback (pullback.lift (𝟙 X) (sX ≫ q) (by simp [hq]))).obj M) := by
  obtain ⟨f, Ψ, e₀, e₁, h₀, h₁⟩ := MvPolynomial.exists_algHom_localizationAway_polynomial r
    (algHomOfSpecSection p hp) (algHomOfSpecSection q hq)
  have hsec (e : Localization.Away f →ₐ[k] k) :
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away f))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, e.comp_algebraMap]
    exact Spec.map_id _
  have hcomp (e : Localization.Away f →ₐ[k] k) (φ : Localization.Away r →ₐ[k] k)
      (h : e.comp Ψ = φ) : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom Ψ.toRingHom) = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← h]
    rfl
  refine nonempty_iso_pullback_lift_of_comp (Spec.map (CommRingCat.ofHom Ψ.toRingHom))
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, Ψ.comp_algebraMap])
    (p' := sX ≫ Spec.map (CommRingCat.ofHom e₀.toRingHom))
    (q' := sX ≫ Spec.map (CommRingCat.ofHom e₁.toRingHom))
    (by rw [Category.assoc, hsec, Category.id_comp, Category.comp_id])
    (by rw [Category.assoc, hsec, Category.id_comp, Category.comp_id])
    _ _ ?_ ?_ M ?_
  · rw [Category.assoc, hcomp e₀ _ h₀, spec_map_algHomOfSpecSection]
  · rw [Category.assoc, hcomp e₁ _ h₁, spec_map_algHomOfSpecSection]
  · exact nonempty_iso_pullback_lift_of_isAlgClosed X hX sX f _ _ (hsec e₀) (hsec e₁) _

end AlgebraicGeometry
