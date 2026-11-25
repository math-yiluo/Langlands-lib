/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.MumfordComplex
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Model

/-!
# Perfectness of the higher direct images, with base change

For a proper morphism `f : X ⟶ T` of finite presentation and an `𝒪_X`-module `ℱ` of finite
presentation which is flat over `T`, the higher direct images are locally on `T` computed by a
bounded complex of finite free modules, compatibly with every base change: as an isomorphism
`g^* P ≅ R f'_* g'^* ℱ` in the derived category
(`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_derivedPushforward`), and on
cohomology sheaves
(`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`).

Over an affine open `V` of `T`, the pair `(f, ℱ)` is the base change of a pair `(p, 𝒢)` over an
affine scheme `S` with Noetherian ring of global sections
(`AlgebraicGeometry.Scheme.Modules.exists_isNoetherianRing_model`), for which the statement is
Mumford's complex
(`exists_isFiniteFreeComplex_derivedPushforward_of_isNoetherianRing`);
base changes of `f` over `V` are base changes of `p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits DerivedCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The pullback of a bounded complex of finite free modules is a bounded complex of finite free
modules. -/
lemma IsFiniteFreeComplex.pullback {X Z : Scheme.{u}} {P : CochainComplex X.Modules ℤ} {d : ℕ}
    (hP : IsFiniteFreeComplex P d) (j : Z ⟶ X) :
    IsFiniteFreeComplex (((Modules.pullback j).mapHomologicalComplex _).obj P) d where
  isStrictlyGE := by
    have := hP.isStrictlyGE
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ (Modules.pullback j).map_isZero (P.isZero_of_isStrictlyGE 0 i hi)
  isStrictlyLE := by
    have := hP.isStrictlyLE
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ (Modules.pullback j).map_isZero (P.isZero_of_isStrictlyLE d i hi)
  exists_iso_free n := by
    obtain ⟨r, ⟨e⟩⟩ := hP.exists_iso_free n
    exact ⟨r, ⟨(Modules.pullback j).mapIso e ≪≫ pullbackFreeIso j _⟩⟩

section General

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

/-- **Perfectness of the derived direct image, with base change**, in the derived category. With
`f : X ⟶ T` proper of finite presentation and `ℱ` an `𝒪_X`-module of finite presentation which
is flat over `T`, every point `t` of `T` has an open neighbourhood `U` over which `R f_* ℱ` is
represented by a bounded complex `P` of finite free `𝒪_U`-modules whose formation commutes with
every base change: for every `g : T' ⟶ U` and every cartesian square `sq`
```
X' ------g'-------> X
|                   |
f'                  f
v                   v
T' --g--> U --U.ι--> T
```
there is an isomorphism `g^* P ≅ R f'_* g'^* ℱ` in `D(𝒪_{T'})`.

Over an affine neighbourhood `V` of `t`, the pair `(f, ℱ)` is the base change of a pair `(p, 𝒢)`
over an affine scheme `S` with Noetherian ring of global sections
(`AlgebraicGeometry.Scheme.Modules.exists_isNoetherianRing_model`), and the statement for
`(p, 𝒢)` is Mumford's complex
`exists_isFiniteFreeComplex_derivedPushforward_of_isNoetherianRing`;
base changes of `f` over `V` are base changes of `p`. The per-degree form is
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem exists_isFiniteFreeComplex_derivedPushforward [IsProper f] [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] (hℱ : ℱ.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (P : CochainComplex U.toScheme.Modules ℤ) (d : ℕ), t ∈ U ∧
      IsFiniteFreeComplex P d ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T'),
        IsPullback g' f' f (g ≫ U.ι) →
        Nonempty (DerivedCategory.Q.obj (((Modules.pullback g).mapHomologicalComplex _).obj P) ≅
          (derivedPushforward f').obj
            ((DerivedCategory.singleFunctor _ 0).obj ((Modules.pullback g').obj ℱ))) := by
  -- an affine neighbourhood `V` of `t`, over which `(f, ℱ)` has a Noetherian model `(p, 𝒢)`
  obtain ⟨V, hV, htV, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens) (show t ∈ ⊤ from trivial)
  change T.Opens at V
  have : IsAffine V := hV
  have hflat : ((Modules.pullback (pullback.fst f V.ι)).obj ℱ).IsFlatOver (pullback.snd f V.ι) :=
    IsFlatOver.of_comp_isOpenImmersion V.ι (by
      rw [← pullback.condition]
      exact hℱ.pullback_of_isOpenImmersion _)
  obtain ⟨S, Y, _, _, π, p, _, _, 𝒢, _, h, h𝒢, hY, ⟨eY⟩⟩ :=
    exists_isNoetherianRing_model (pullback.snd f V.ι) _ hflat
  obtain ⟨a, P, d, hs, hP, hD⟩ :=
    exists_isFiniteFreeComplex_derivedPushforward_of_isNoetherianRing p 𝒢 h𝒢 (π ⟨t, htV⟩)
  -- the neighbourhood `U = V ∩ π⁻¹ D(a)` of `t`
  let U : T.Opens := V.ι ''ᵁ (π ⁻¹ᵁ S.basicOpen a)
  have hUV : U ≤ V := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  let ψ : U.toScheme ⟶ V.toScheme := T.homOfLE hUV
  have hψ : Set.range (ψ ≫ π).base ⊆ Set.range (S.basicOpen a).ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨y, hy, hxy⟩ := x.2
    have : ψ x = y := Subtype.ext (by
      change V.ι (ψ x) = V.ι y
      rw [← Scheme.Hom.comp_apply, T.homOfLE_ι]
      exact hxy.symm)
    rw [Scheme.Hom.comp_apply, this]
    exact hy
  let φ : U.toScheme ⟶ (S.basicOpen a).toScheme :=
    IsOpenImmersion.lift (S.basicOpen a).ι (ψ ≫ π) hψ
  have hφ : φ ≫ (S.basicOpen a).ι = ψ ≫ π := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, ((Modules.pullback φ).mapHomologicalComplex _).obj P, d, ⟨⟨t, htV⟩, hs, rfl⟩,
    hP.pullback φ, ?_⟩
  intro T' X' g g' f' H
  -- `X'` is the base change of `X_V` along `g ≫ ψ`, hence of `Y` along `g ≫ ψ ≫ π`
  have hgψ : (g ≫ ψ) ≫ V.ι = g ≫ U.ι := by rw [Category.assoc, T.homOfLE_ι]
  let gV : X' ⟶ Limits.pullback f V.ι := pullback.lift g' (f' ≫ g ≫ ψ) (by
    rw [H.w, Category.assoc, Category.assoc, ← hgψ, Category.assoc])
  have H₁ : IsPullback gV f' (pullback.snd f V.ι) (g ≫ ψ) :=
    IsPullback.of_right (by simpa [gV, hgψ] using H) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f V.ι)
  have H₂ : IsPullback (gV ≫ h) f' p ((g ≫ φ) ≫ (S.basicOpen a).ι) := by
    rw [Category.assoc, hφ, ← Category.assoc]
    exact H₁.paste_horiz hY
  obtain ⟨e⟩ := hD (g ≫ φ) (gV ≫ h) f' H₂
  -- comparison of the complexes and of the modules
  let eP : ((Modules.pullback g).mapHomologicalComplex _).obj
      (((Modules.pullback φ).mapHomologicalComplex _).obj P) ≅
      ((Modules.pullback (g ≫ φ)).mapHomologicalComplex _).obj P :=
    HomologicalComplex.Hom.isoOfComponents (fun n ↦ (Modules.pullbackComp g φ).app (P.X n))
      (fun i j _ ↦ ((Modules.pullbackComp g φ).hom.naturality (P.d i j)).symm)
  let eℱ : (Modules.pullback (gV ≫ h)).obj 𝒢 ≅ (Modules.pullback g').obj ℱ :=
    (Modules.pullbackComp gV h).symm.app 𝒢 ≪≫ (Modules.pullback gV).mapIso eY ≪≫
      (Modules.pullbackComp gV (pullback.fst f V.ι)).app ℱ ≪≫
      (Modules.pullbackCongr (pullback.lift_fst _ _ _)).app ℱ
  exact ⟨DerivedCategory.Q.mapIso eP ≪≫ e ≪≫
    (derivedPushforward f').mapIso ((DerivedCategory.singleFunctor _ 0).mapIso eℱ)⟩

end General

section Perfect

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)
  [IsAffine S] [Finite ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

include hU hU' in
/-- **Perfectness of `Rf_* ℱ` and base change.** Let `f : X ⟶ S` be proper of finite
presentation with `S = Spec A` affine, and `ℱ` an `𝒪_X`-module of finite presentation, flat over
`S`. Then `Rf_* ℱ` is perfect and its formation commutes with arbitrary base change:

* locally on `S`, `Rf_* ℱ` is represented by a bounded complex of finite free modules whose
  pullback along every `g : T' ⟶ S` computes the higher direct images of `ℱ_{T'}`; this is the
  classical input `exists_isFiniteFreeComplex_higherDirectImage` of
  `lemma-coherent-base-change-invertible-sheaves` [Stacks, Tag 0B91];
* over the affine base, `Rf_* ℱ` is represented by the bounded complex `K` of flat `A`-modules
  of `AlgebraicGeometry.Scheme.Modules.isIso_cechModuleComplexBaseChangeComparison`, and for every
  cartesian square with `T = Spec B` affine, `Lg^* Rf_* ℱ = B ⊗[A] K ≅ Rf_{T*} ℱ_T` in `D(B)`
  (`lemma-coherent-base-change-invertible-sheaves--2`; proper morphisms are quasi-compact and
  separated);
* if `A` is noetherian, `Rf_* ℱ` is a perfect object of `D(A)`, and so are all its base changes
  `Rf_{T*} ℱ_T` in `D(B)`
  (`AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_of_isNoetherianRing`,
  `AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_baseChange`).

Perfectness in `D(A)` over a non-noetherian base is the classical input of the first item; it is
not deduced here from it, as the comparison of the two representatives of `Rf_* ℱ` would need
the finite free complexes to be quasi-isomorphic to the Čech complex.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem perfect_and_baseChange_cechModuleComplex_of_isProper [IsProper f]
    [LocallyOfFinitePresentation f] [HasInjectiveResolutions X.Modules] [Fintype ι]
    [ℱ.IsFinitePresentation] (hℱ : ℱ.IsFlatOver f) :
    (∀ t : S, ∃ (V : S.Opens) (P : CochainComplex V.toScheme.Modules ℤ) (d : ℕ), t ∈ V ∧
      IsFiniteFreeComplex P d ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ V.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ V.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ))) ∧
    (∀ {T Y : Scheme.{u}} {g : T ⟶ S} {g' : Y ⟶ X} {f' : Y ⟶ T} (H : IsPullback g' f' f g)
      [IsAffine T] [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom),
      IsIso (cechModuleComplexBaseChangeComparison f ℱ U hU H hg)) ∧
    (IsNoetherianRing Γ(S, ⊤) → (Q.obj (cechModuleComplex f ℱ U)).IsPerfect ∧
      ∀ {T Y : Scheme.{u}} {g : T ⟶ S} {g' : Y ⟶ X} {f' : Y ⟶ T} (_ : IsPullback g' f' f g)
        [IsAffine T] [Algebra Γ(S, ⊤) Γ(T, ⊤)] (_ : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom),
        (Q.obj (cechModuleComplex f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i))).IsPerfect) := by
  refine ⟨fun t ↦ exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ t,
    fun H _ _ hg ↦ isIso_cechModuleComplexBaseChangeComparison f ℱ U hU hU' hℱ H hg,
    fun _ ↦ ?_⟩
  have hP := isPerfect_Q_cechModuleComplex_of_isNoetherianRing f ℱ U hU hU' hℱ
  exact ⟨hP, fun H _ _ hg ↦ (isPerfect_Q_cechModuleComplex_baseChange f ℱ U hU hU' hℱ hP H hg).2⟩

end Perfect

end AlgebraicGeometry.Scheme.Modules
