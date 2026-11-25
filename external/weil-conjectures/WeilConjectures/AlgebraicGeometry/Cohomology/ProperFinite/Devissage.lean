/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveFinite
public import WeilConjectures.AlgebraicGeometry.Cohomology.PushforwardAcyclic

/-!
# Finiteness of cohomology along exact sequences

Let `A` be a noetherian ring and `p : X ⟶ Spec A`. We say that an `𝒪_X`-module `M` has finite
cohomology over `A` if every `H^q(X, M)` is a finite `A`-module, the module structure being the
one of `AlgebraicGeometry.Scheme.Modules.moduleHOfSpec`. This property is stable under
isomorphisms, under extensions and under passing to the middle term of a morphism: if
`φ : M ⟶ N` has kernel and cokernel with finite cohomology and `N` has finite cohomology, so
has `M`. It is invariant under pushforward along an affine morphism.

These are the formal steps of the dévissage proving finiteness of the cohomology of coherent
sheaves on proper schemes over `A` [Stacks, Tag 02O6].

## Main definitions and statements

- `AlgebraicGeometry.Scheme.Modules.HasFiniteH`: all `H^q(X, M)` are finite over `A`.
- `AlgebraicGeometry.Scheme.Modules.HasFiniteH.of_hom`: if `ker φ`, `coker φ` and the target of
  `φ` have finite cohomology, so has the source.
- `AlgebraicGeometry.Scheme.Modules.hasFiniteH_pushforward_iff`: finiteness of the cohomology is
  invariant under pushforward along an affine morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {A : Type u} [CommRing A] (p : X ⟶ Spec (.of A))

/-- The `𝒪_X`-module `M` **has finite cohomology over `A`**: for `p : X ⟶ Spec A`, every
`H^q(X, M)` is a finite `A`-module, `A` acting through `p`. -/
def HasFiniteH (M : X.Modules) : Prop :=
  ∀ q : ℕ, letI := moduleHOfSpec p M q; Module.Finite A (M.H q)

variable {p}

/-- Finiteness of the cohomology is invariant under isomorphism. -/
lemma HasFiniteH.of_iso {M N : X.Modules} (e : M ≅ N) (h : HasFiniteH p M) : HasFiniteH p N :=
  fun q ↦ finite_H_of_iso p e q (h q)

/-- The `A`-linear map `H^q(φ)`. -/
abbrev H.mapOfSpec {M N : X.Modules} (φ : M ⟶ N) (q : ℕ) :
    letI := moduleHOfSpec p M q
    letI := moduleHOfSpec p N q
    M.H q →ₗ[A] N.H q :=
  letI := moduleHOfSpec p M q
  letI := moduleHOfSpec p N q
  { toFun := H.map φ q
    map_add' := map_add _
    map_smul' := fun _ x ↦ H.map_smul φ q _ x }

/-- **The middle term of a short exact sequence.** If `H^q(M₁)` and `H^q(M₃)` are finite, so is
`H^q(M₂)`, by exactness of `H^q(M₁) ⟶ H^q(M₂) ⟶ H^q(M₃)`. -/
lemma finite_H_X₂_of_shortExact [IsNoetherianRing A] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (q : ℕ)
    (h₁ : letI := moduleHOfSpec p S.X₁ q; Module.Finite A (S.X₁.H q))
    (h₃ : letI := moduleHOfSpec p S.X₃ q; Module.Finite A (S.X₃.H q)) :
    letI := moduleHOfSpec p S.X₂ q; Module.Finite A (S.X₂.H q) := by
  let := moduleHOfSpec p S.X₁ q
  let := moduleHOfSpec p S.X₂ q
  let := moduleHOfSpec p S.X₃ q
  let f : S.X₁.H q →ₗ[A] S.X₂.H q := H.mapOfSpec S.f q
  let g : S.X₂.H q →ₗ[A] S.X₃.H q := H.mapOfSpec S.g q
  have hker : LinearMap.ker g = LinearMap.range f := by
    ext x
    exact SetLike.ext_iff.1 (H.ker_map_g_eq_range_map_f hS q) x
  have : _root_.IsNoetherian A (S.X₃.H q) := isNoetherian_of_isNoetherianRing_of_finite _ _
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker g (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, hker, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map f

/-- **The first term of a short exact sequence.** If `H^{q-1}(M₃)` and `H^q(M₂)` are finite,
so is `H^q(M₁)`, by exactness of `H^{q-1}(M₃) ⟶ H^q(M₁) ⟶ H^q(M₂)`. -/
lemma finite_H_X₁_of_shortExact [IsNoetherianRing A] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (q : ℕ)
    (h₂ : letI := moduleHOfSpec p S.X₂ q; Module.Finite A (S.X₂.H q))
    (h₃ : ∀ q' : ℕ, q' + 1 = q →
      letI := moduleHOfSpec p S.X₃ q'; Module.Finite A (S.X₃.H q')) :
    letI := moduleHOfSpec p S.X₁ q; Module.Finite A (S.X₁.H q) := by
  let := moduleHOfSpec p S.X₁ q
  let := moduleHOfSpec p S.X₂ q
  let f : S.X₁.H q →ₗ[A] S.X₂.H q := H.mapOfSpec S.f q
  have : _root_.IsNoetherian A (S.X₂.H q) := isNoetherian_of_isNoetherianRing_of_finite _ _
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker f (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq]
  cases q with
  | zero =>
    have hinj : LinearMap.ker f = ⊥ :=
      LinearMap.ker_eq_bot.2 (H.injective_map_zero_of_shortExact hS)
    rw [hinj]
    exact Submodule.fg_bot
  | succ q =>
    let := moduleHOfSpec p S.X₃ q
    have := h₃ q rfl
    let δ : S.X₃.H q →ₗ[A] S.X₁.H (q + 1) :=
      { toFun := H.δ hS q
        map_add' := map_add _
        map_smul' := fun a x ↦ H.δ_smul hS q _ x }
    have hker : LinearMap.ker f = LinearMap.range δ := by
      ext x
      exact SetLike.ext_iff.1 (H.ker_map_f_eq_range_δ hS q) x
    rw [hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map δ

variable [IsNoetherianRing A]

/-- **Finiteness of the cohomology along a morphism.** If `φ : M ⟶ N` is such that `ker φ`,
`coker φ` and `N` have finite cohomology, so has `M`: with `I` the image of `φ`, the short exact
sequences `0 ⟶ I ⟶ N ⟶ coker φ ⟶ 0` and `0 ⟶ ker φ ⟶ M ⟶ I ⟶ 0` give the finiteness of the
cohomology of `I`, then of `M`. -/
lemma HasFiniteH.of_hom {M N : X.Modules} (φ : M ⟶ N) (hK : HasFiniteH p (kernel φ))
    (hC : HasFiniteH p (cokernel φ)) (hN : HasFiniteH p N) : HasFiniteH p M := by
  have hS₂ : (ShortComplex.cokernelSequence (image.ι φ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
      (inferInstanceAs (Mono (image.ι φ))) (inferInstanceAs (Epi (cokernel.π (image.ι φ))))
  have hS₁ : (ShortComplex.kernelSequence (factorThruImage φ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _)
      (inferInstanceAs (Mono (kernel.ι (factorThruImage φ))))
      (inferInstanceAs (Epi (factorThruImage φ)))
  have hC' : HasFiniteH p (cokernel (image.ι φ)) := hC.of_iso (cokernelImageι φ).symm
  have hK' : HasFiniteH p (kernel (factorThruImage φ)) := hK.of_iso (kernelFactorThruImage φ).symm
  have hI : HasFiniteH p (image φ) := fun q ↦
    finite_H_X₁_of_shortExact hS₂ q (hN q) fun q' _ ↦ hC' q'
  exact fun q ↦ finite_H_X₂_of_shortExact hS₁ q (hK' q) (hI q)

omit [IsNoetherianRing A] in
/-- Finiteness of the cohomology transported along additive isomorphisms
`H^q(X, M) ≃ H^q(Y, N)` taking the action of `g^♯ r` to that of `r`, for `g : X ⟶ Y`. -/
lemma hasFiniteH_iff_of_addEquiv {Y : Scheme.{u}} (g : X ⟶ Y) (p : Y ⟶ Spec (.of A))
    (M : X.Modules) (N : Y.Modules)
    (e : ∀ q : ℕ, ∃ e : M.H q ≃+ N.H q, ∀ (r : Γ(Y, ⊤)) (x : M.H q), e (g.appTop r • x) = r • e x) :
    HasFiniteH p N ↔ HasFiniteH (g ≫ p) M := by
  have key (q : ℕ) : letI := moduleHOfSpec (g ≫ p) M q
      letI := moduleHOfSpec p N q
      Nonempty (M.H q ≃ₗ[A] N.H q) := by
    obtain ⟨e, he⟩ := e q
    let := moduleHOfSpec (g ≫ p) M q
    let := moduleHOfSpec p N q
    exact ⟨{ e with
      map_smul' := fun a x ↦ by
        change e ((((Scheme.ΓSpecIso (.of A)).inv ≫ (g ≫ p).appTop).hom a) • x) = _
        rw [Scheme.Hom.comp_appTop, ← Category.assoc, CommRingCat.hom_comp,
          RingHom.comp_apply]
        exact he _ x }⟩
  refine ⟨fun h q ↦ ?_, fun h q ↦ ?_⟩
  · let := moduleHOfSpec (g ≫ p) M q
    let := moduleHOfSpec p N q
    have := h q
    exact Module.Finite.equiv (key q).some.symm
  · let := moduleHOfSpec (g ≫ p) M q
    let := moduleHOfSpec p N q
    have := h q
    exact Module.Finite.equiv (key q).some

omit [IsNoetherianRing A] in
/-- **Finiteness of the cohomology along an affine morphism.** For `g : X ⟶ Y` affine and `M`
quasi-coherent, `M` has finite cohomology over `A` (acting through `g ≫ p`) if and only if
`g_* M` has (acting through `p`), since `H^q(X, M) ≅ H^q(Y, g_* M)` compatibly with the actions
of the global functions of `Y`. -/
lemma hasFiniteH_pushforward_iff {Y : Scheme.{u}} (g : X ⟶ Y) [IsAffineHom g]
    (p : Y ⟶ Spec (.of A)) (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] :
    HasFiniteH p ((pushforward g).obj M) ↔ HasFiniteH (g ≫ p) M :=
  hasFiniteH_iff_of_addEquiv g p M _ fun q ↦ exists_H_addEquiv_pushforward_of_isAffineHom g M q

omit [IsNoetherianRing A] in
/-- **Finiteness of the cohomology along a morphism with vanishing higher direct images.** If
`R^q g_* M = 0` for all `q > 0`, then `M` has finite cohomology over `A` (acting through
`g ≫ p`) if and only if `g_* M` has (acting through `p`), by the degenerate Leray spectral
sequence `H^q(X, M) ≅ H^q(Y, g_* M)`. -/
lemma hasFiniteH_pushforward_iff_of_isZero {Y : Scheme.{u}} (g : X ⟶ Y)
    [HasInjectiveResolutions X.Modules] (p : Y ⟶ Spec (.of A)) (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj M)) :
    HasFiniteH p ((pushforward g).obj M) ↔ HasFiniteH (g ≫ p) M :=
  hasFiniteH_iff_of_addEquiv g p M _ fun q ↦
    exists_H_addEquiv_pushforward_of_isZero_higherDirectImage (π := g) M hM q

end AlgebraicGeometry.Scheme.Modules
