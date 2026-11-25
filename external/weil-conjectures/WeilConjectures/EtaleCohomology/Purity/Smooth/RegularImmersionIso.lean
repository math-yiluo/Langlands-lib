/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularImmersionChart
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale

/-!
# Purity for regular closed immersions: `cl_i` is an isomorphism

Let `i : Z ⟶ X` be a regular closed immersion of pure codimension `c`, with `X` smooth over a
perfect field `k` and `Z` regular. The morphism `cl_i : Λ_Z ⟶ Ri^! (Λ_X(c)[2c])`, `1 ↦ [Z ⊂ X]`,
adjoint to the fundamental class (`AlgebraicGeometry.Etale.fundamentalClassMap`), is an
isomorphism (clause (c) of blueprint `lemma-class-of-point--1`); in particular `[Z ⊂ X]` generates
the cohomology sheaf `𝓗⁰(Ri^! Λ_X(c)[2c])` at every geometric point (clause (b)).

This is Step 4 of the proof. The question is étale-local on `Z`. Near every point of `Z` there
is a Zariski frame `(U, f₁, …, f_c)` of `Z` together with an étale map
`u : U ⟶ 𝔸^c_B`, `B = 𝔸^m_k`, whose `c` fibre coordinates `t_a` pull back to the `f_a`
(`AlgebraicGeometry.IsRegularImmersion.exists_etale_affineSpace`). The frame class
`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` is the restriction along `u` of the class `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_c)` of the
zero section of `𝔸^c_B` (`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct`),
whose adjoint is an isomorphism by the model computation of `proposition-purity-vector-bundles`
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord`). Restriction of
supports along an étale map is an isomorphism
(`AlgebraicGeometry.Etale.isIso_supportedRestriction_of_etale`), so the adjoint of a class is an
isomorphism after étale restriction if and only if the class's adjoint is so there
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_restrictSupportedClass_iff`). Applying this
twice — along `u` and along the frame `U ⟶ X` — shows that `cl_i` becomes an isomorphism on a
Zariski cover of `Z`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_fundamentalClassMap`: clause (c).
- `AlgebraicGeometry.Etale.isIso_homology_zero_map_fundamentalClassMap`: clause (b), generation.
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_fundamentalClassMap`: finite reduction.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] {k : Type u}
  [Field k] [PerfectField k] (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]

attribute [local instance] HasInvertibleExponent.opens

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

*Step 4, locally.* Every point of `Z` lies in the zero locus of a Zariski frame `F` of `i` on
which `cl_i` restricts to an isomorphism: `F` is chosen with an étale map `u : F.U ⟶ 𝔸^c_B`
pulling the coordinates back to the frame functions, the frame class is the restriction of the
class of the zero section of `𝔸^c_B`, whose adjoint is an isomorphism
(`proposition-purity-vector-bundles`), and the restriction of supports along the étale maps `u` and
`F.U ⟶ X` is invertible. -/
theorem exists_etaleFrame_isIso_leftDerivedUpperStar_map_fundamentalClassMap
    (aX : X ⟶ Spec (.of k)) [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (z : Z) : ∃ F : i.EtaleFrame c, z ∈ Set.range F.toZ ∧
      IsIso ((L((F.toZ)^*[ModuleCat.{u + 1} Λ])).map (fundamentalClassMap Λ c i aX hZ)) := by
  obtain ⟨U, hzU, f, m, v, hspan, hv, hvf⟩ :=
    IsRegularImmersion.exists_etale_affineSpace c i aX hZ z
  let F := Scheme.Hom.EtaleFrame.ofSpanEq i U f hspan
  -- the model: the zero section of `𝔸^c_B`, `B = 𝔸^m_k`
  let B := 𝔸(ULift.{u} (Fin m); Spec (.of k))
  have : Nonempty X := ⟨i.base z⟩
  have : HasInvertibleExponent Λ (Spec (.of k)) := .of_hom_of_nonempty aX
  have : HasInvertibleExponent Λ B := .of_hom (𝔸(ULift.{u} (Fin m); Spec (.of k)) ↘ Spec (.of k))
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin c); B) := .of_hom (𝔸(ULift.{u} (Fin c); B) ↘ B)
  let t : Fin c → Γ(𝔸(ULift.{u} (Fin c); B), ⊤) := fun a ↦ AffineSpace.coord B (ULift.up a)
  have hmodel := isIso_supportedClassMap_kummerBoundaryProduct_coord Λ c B
  have hvt : ∀ a, v.appTop (t a) = F.f a := hvf
  obtain ⟨gv, hgv⟩ : ∃ g, IsPullback g (F.U.zeroLocusSubschemeι (Set.range F.f))
      (𝔸(ULift.{u} (Fin c); B).zeroLocusSubschemeι (Set.range t)) v :=
    ⟨_, isPullback_zeroLocusSubschemeι v (Set.range t) (Set.range F.f)
      (by rw [← Set.range_comp]; exact congrArg Set.range (funext hvt))⟩
  -- the frame class is the restriction of the class of the zero section along `v`
  have h₁ := restrictSupportedClass_kummerBoundaryProduct Λ v t F.f hvt gv hgv
  have hψv := isIso_supportedRestriction_of_etale Λ v _ _ gv hgv
    ((tateObject Λ _ c)⟦2 * (c : ℤ)⟧) ((tateObject Λ F.U c)⟦2 * (c : ℤ)⟧)
    (leftDerivedUpperStarTateShiftIso Λ v c)
  have h₂ : IsIso (supportedClassMap Λ _ (frameClass Λ F)) := by
    rw [frameClass, ← h₁]
    exact (isIso_supportedClassMap_restrictSupportedClass_iff Λ v _ _ gv hgv _ _ _ _ hψv).2
      inferInstance
  -- and it is the restriction of the fundamental class along the frame
  rw [← frameRestriction_fundamentalClass Λ c i aX hZ F, frameRestriction] at h₂
  have hψe := isIso_supportedRestriction_of_etale Λ F.e i _ F.toZ F.isPullback
    ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ((tateObject Λ F.U c)⟦2 * (c : ℤ)⟧)
    (leftDerivedUpperStarTateShiftIso Λ F.e c)
  exact ⟨F, Scheme.Hom.EtaleFrame.mem_range_ofSpanEq_toZ i U f hspan hzU,
    (isIso_supportedClassMap_restrictSupportedClass_iff Λ F.e _ _ _ F.isPullback _ _ _ _ hψe).1
      h₂⟩

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

**(c) `cl_i` is an isomorphism**, `cl_i : Λ_Z ≅ Ri^! (Λ_X(c)[2c])`, `1 ↦ [Z ⊂ X]`. Its
restrictions to the members of a Zariski cover of `Z` are isomorphisms
(`AlgebraicGeometry.Etale.exists_etaleFrame_isIso_leftDerivedUpperStar_map_fundamentalClassMap`),
and restrictions to a cover detect isomorphisms on cohomology sheaves.

It equals the isomorphism `Φ_i` assembled from smooth purity of `a_X` and `a_Z` in Steps 1–2
of the proof (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_of_isRegularImmersion`).
That isomorphism is recorded only as `Nonempty`, so the agreement is a remark rather
than a statement. Twisting by `(-c)[-2c]`, the inverse of `cl_i(-c)[-2c]` is the canonical
isomorphism `Ri^! Λ_X ≅ Λ_Z(-c)[-2c]`. -/
theorem isIso_fundamentalClassMap (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    IsIso (fundamentalClassMap Λ c i aX hZ) := by
  choose F hzF hF using
    exists_etaleFrame_isIso_leftDerivedUpperStar_map_fundamentalClassMap Λ c i aX hZ
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun z ↦ (F z).toZ) (fun z ↦ ⟨z, hzF z⟩) _ fun z ↦ ?_
  have h : IsIso (D(((F z).toZ)^*[ModuleCat.{u + 1} Λ]).map (fundamentalClassMap Λ c i aX hZ)) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ (F z).toZ) _).1 (hF z)
  exact (NatIso.isIso_map_iff
    ((((F z).toZ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n) _).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      (D(((F z).toZ)^*[ModuleCat.{u + 1} Λ]).map (fundamentalClassMap Λ c i aX hZ)))

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

**(b) The fundamental class generates.** `[Z ⊂ X]` generates `𝓗⁰(Ri^! Λ_X(c)[2c])` at every
geometric point: the map of sheaves `Λ_Z ⟶ 𝓗⁰(Ri^! Λ_X(c)[2c])` induced by `cl_i` is an
isomorphism, `cl_i` being one (`AlgebraicGeometry.Etale.isIso_fundamentalClassMap`). -/
theorem isIso_homology_zero_map_fundamentalClassMap (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map (fundamentalClassMap Λ c i aX hZ)) :=
  have := isIso_fundamentalClassMap Λ c i aX hZ
  inferInstance

/-- Blueprint `prop-pur-regular-immersion-purity-compatibilities`: Compatibilities of purity for
regular immersions

**Finite reduction** (item 4). Reduction of coefficients along a quotient `Λ ⟶ Λ / J`
(`AlgebraicGeometry.Etale.reductionModIdeal`, `K ↦ K ⊗ᴸ (Λ / J)`; for `Λ = A_{E,n}` and
`J = ϖ^{n-1}` this is the reduction `A_{E,n} ⟶ A_{E,n-1}`) carries the purity isomorphism
`cl_i : Λ_Z ≅ Ri^! (Λ_X(c)[2c])` to an isomorphism
`Λ_Z ⊗ᴸ (Λ / J) ≅ Ri^! (Λ_X(c)[2c]) ⊗ᴸ (Λ / J)`: the reduction functor is applied to every
step of the construction, which is natural in the coefficients.

In this formalisation a single coefficient ring `Λ` carries the rank-one datum
`AlgebraicGeometry.Etale.HasKummerClass`, so the reduction is expressed inside `D(Z_ét, Λ)`;
comparing with the purity isomorphism of a separate rank-one datum on `Λ / J` would need a
compatibility structure between the data of the tower, which is not part of the framework. -/
theorem isIso_reductionModIdeal_map_fundamentalClassMap (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (J : Ideal Λ) :
    IsIso ((reductionModIdeal Λ Z J).map (fundamentalClassMap Λ c i aX hZ)) :=
  have := isIso_fundamentalClassMap Λ c i aX hZ
  inferInstance

end Etale

end AlgebraicGeometry
