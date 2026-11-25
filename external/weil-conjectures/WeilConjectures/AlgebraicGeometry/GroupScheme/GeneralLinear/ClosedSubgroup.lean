/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal

/-!
# Closed subgroup schemes of `GL_n`

A Hopf ideal `I` of `k[x_ij, det⁻¹]` cuts out the closed subgroup scheme
`V(I) = Spec (k[x_ij, det⁻¹] ⧸ I)` of the group scheme `𝔾𝕃(n; k)`: a group object of
`Over (Spec k)` with a closed immersion `V(I) ⟶ 𝔾𝕃(n; k)` of group objects. An inclusion `I ≤ J`
of Hopf ideals gives a closed immersion `V(J) ⟶ V(I)` of group objects.

The `R`-points `Spec R ⟶ V(I)` of this group scheme are identified with the matrix group
`zeroLocus I R` of `WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal`: this is
a theorem (`range_homMulEquiv_comp`, packaged as the group isomorphism `zeroLocusMulEquiv`), not a
definition, and it is the only place where the scheme and the matrix groups meet.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.subgroupScheme`: the closed subgroup scheme `V(I)` of
  `𝔾𝕃(n; k)`, with its closed immersion `subgroupSchemeι` into `𝔾𝕃(n; k)`.
- `AlgebraicGeometry.GeneralLinearGroup.subgroupSchemeHom`: the closed immersion `V(J) ⟶ V(I)`
  induced by an inclusion `I ≤ J` of Hopf ideals.
- `AlgebraicGeometry.GeneralLinearGroup.zeroLocusMulEquiv`: the group of `R`-points
  `Spec R ⟶ V(I)` is the matrix group `zeroLocus I R`.
- `AlgebraicGeometry.GeneralLinearGroup.conjHom`,
  `AlgebraicGeometry.GeneralLinearGroup.subgroupSchemeConjIso`: conjugation by a `k`-point of
  `GL_n`, as an endomorphism of the group scheme `𝔾𝕃(n; k)` and as an automorphism of a closed
  subgroup scheme `V(I)` that it preserves.
- `AlgebraicGeometry.GeneralLinearGroup.derivedIdeal`: the Hopf ideal of the derived subgroup
  `[V(I), V(I)]`, the smallest closed subgroup scheme of `V(I)` with commutative quotient.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.range_homMulEquiv_comp`: the `R`-points of `V(I)` are the
  matrices satisfying the equations in `I`.
- `AlgebraicGeometry.GeneralLinearGroup.zeroLocusMulEquiv_map`: the identification of points is
  natural in `R`.
- `AlgebraicGeometry.GeneralLinearGroup.range_subgroupSchemeHom_le_identityComponent`: the closed
  subgroup scheme cut out by the ideal `identityComponent I` is the reduced identity component of
  `V(I)`.
- `AlgebraicGeometry.GeneralLinearGroup.finiteIndex_subgroupOf_zeroLocus_identityComponent`: the
  `k`-points of `G°` have finite index in the `k`-points of `G`.
- `AlgebraicGeometry.GeneralLinearGroup.containsCommutators_subgroupSchemeHom`: if `V(J)(R)`
  contains the commutators of `V(I)(R)` for all `R`, then `V(J) ⟶ V(I)` contains the commutators
  scheme-theoretically.
- `AlgebraicGeometry.GeneralLinearGroup.containsCommutators_iff_le_derivedIdeal`: a closed subgroup
  of `V(I)` contains the commutators if and only if it contains the derived subgroup.

## Blueprint

- `det-d-geometry`: matrix algebraic groups as closed subgroup schemes of `GL(V)`.
- `lemma-restriction-normal-subgroup`: closed subgroups containing the commutators, and the derived
subgroup.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry WithConv
open scoped MonObj

namespace AlgebraicGeometry.GeneralLinearGroup

open Matrix.GeneralLinearGroup

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [CommRing k]

section AffineFactor

/-- Two morphisms `Spec Γ(X) ⟶ Y` to an affine scheme agreeing after `X ⟶ Spec Γ(X)` agree. -/
theorem _root_.AlgebraicGeometry.Scheme.toSpecΓ_comp_injective (X : Scheme.{u}) {Y : Scheme.{u}}
    [IsAffine Y] {g₁ g₂ : Spec Γ(X, ⊤) ⟶ Y} (h : X.toSpecΓ ≫ g₁ = X.toSpecΓ ≫ g₂) : g₁ = g₂ := by
  apply ext_of_isAffine
  have := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at this
  exact (cancel_mono _).1 this

/-- Every morphism from a `k`-scheme `X` to the spectrum of a `k`-algebra factors uniquely through
`X ⟶ Spec Γ(X)`, as a morphism over `Spec k`. -/
theorem _root_.AlgebraicGeometry.Over.exists_bijective_comp_toSpecΓ (X : Over (Spec (.of k))) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra k R)
      (t : X ⟶ (Spec (.of R)).asOver (Spec (.of k))),
      ∀ (B : Type u) [CommRing B] [Algebra k B], Function.Bijective
        fun g : (Spec (.of R)).asOver (Spec (.of k)) ⟶ (Spec (.of B)).asOver (Spec (.of k)) ↦
          t ≫ g := by
  let : Algebra k Γ(X.left, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom.toAlgebra
  have hX : X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(X.left, ⊤))) = X.hom := by
    change X.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) = X.hom
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  refine ⟨Γ(X.left, ⊤), inferInstance, inferInstance, Over.homMk X.left.toSpecΓ hX,
    fun B _ _ ↦ ⟨fun g₁ g₂ h ↦ ?_, fun a ↦ ?_⟩⟩
  · exact Over.OverMorphism.ext
      (Scheme.toSpecΓ_comp_injective (Y := Spec (.of B)) X.left (g₁ := g₁.left) (g₂ := g₂.left)
        (congrArg Over.Hom.left h))
  · obtain ⟨a', ha'⟩ : ∃ a' : X.left ⟶ Spec (.of B), a' = a.left := ⟨_, rfl⟩
    have ha := Scheme.toSpecΓ_naturality a'
    let g : Spec Γ(X.left, ⊤) ⟶ Spec (.of B) :=
      Spec.map a'.appTop ≫ inv (Spec (.of B)).toSpecΓ
    have hg : X.left.toSpecΓ ≫ g = a.left := by
      rw [← Category.assoc, ← ha, Category.assoc, IsIso.hom_inv_id, Category.comp_id, ha']
    refine ⟨Over.homMk g (Scheme.toSpecΓ_comp_injective (Y := Spec (.of k)) X.left ?_),
      Over.OverMorphism.ext hg⟩
    change X.left.toSpecΓ ≫ g ≫ Spec.map _ = X.left.toSpecΓ ≫ Spec.map _
    rw [reassoc_of% hg, hX]
    exact Over.w a

end AffineFactor

section SubgroupScheme

/-- The closed subgroup scheme `V(I) = Spec (k[x_ij, det⁻¹] ⧸ I)` of `GL_n` cut out by a Hopf ideal
`I`. It is a group object by Mathlib's quotient Hopf algebra structure.
(blueprint: `det-d-geometry`) -/
noncomputable abbrev subgroupScheme (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    Over (Spec (.of k)) :=
  (Spec (.of (CoordinateRing n k ⧸ I))).asOver (Spec (.of k))

variable (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

noncomputable instance : GrpObj (subgroupScheme I) := inferInstance

instance : IsAffine (subgroupScheme I).left :=
  inferInstanceAs (IsAffine (Spec (.of (CoordinateRing n k ⧸ I))))

instance : LocallyOfFiniteType (subgroupScheme I).hom :=
  locallyOfFiniteType_specOverSpec

/-- The closed immersion of the closed subgroup scheme `V(I)` into `GL_n`.
(blueprint: `det-d-geometry`) -/
noncomputable def subgroupSchemeι : subgroupScheme I ⟶ 𝔾𝕃(n; k) :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ k I).toRingHom)).asOver (Spec (.of k))

instance : IsMonHom (subgroupSchemeι I) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom (Bialgebra.Quotient.mkBialgHom (R := k) I)).op).hom)

instance : IsClosedImmersion (subgroupSchemeι I).left :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance : Mono (subgroupSchemeι I) :=
  Over.mono_of_mono_left _

theorem subgroupSchemeι_comp_injective {X : Over (Spec (.of k))} :
    Function.Injective fun φ : X ⟶ subgroupScheme I ↦ φ ≫ subgroupSchemeι I :=
  fun _ _ h ↦ (cancel_mono _).1 h

theorem mapMulEquiv_comp_subgroupSchemeι {R : Type u} [CommRing R] [Algebra k R]
    (ψ : WithConv (CoordinateRing n k ⧸ I →ₐ[k] R)) :
    Spec.mapMulEquiv ψ ≫ subgroupSchemeι I =
      Spec.mapMulEquiv (toConv (ψ.ofConv.comp (Ideal.Quotient.mkₐ k I))) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The `R`-points of the closed subgroup scheme `V(I)` are the invertible matrices over `R`
satisfying the equations in `I`: the identification of `G(R)` with a classical matrix group is a
theorem, not a definition. (blueprint: `det-d-geometry`) -/
theorem range_homMulEquiv_comp (R : Type u) [CommRing R] [Algebra k R] :
    Set.range (fun φ : (Spec (.of R)).asOver (Spec (.of k)) ⟶ subgroupScheme I ↦
      GeneralLinearGroup.homMulEquiv n k R (φ ≫ subgroupSchemeι I)) = zeroLocus I R := by
  have key (χ : CoordinateRing n k ⧸ I →ₐ[k] R) :
      GeneralLinearGroup.homMulEquiv n k R (Spec.mapMulEquiv (toConv χ) ≫ subgroupSchemeι I) =
        algHomMulEquiv n k R (toConv (χ.comp (Ideal.Quotient.mkₐ k I))) := by
    rw [mapMulEquiv_comp_subgroupSchemeι, GeneralLinearGroup.homMulEquiv_mapMulEquiv,
      ofConv_toConv]
  have heval (χ : CoordinateRing n k →ₐ[k] R) :
      evalAlgHom (algHomMulEquiv n k R (toConv χ)) = χ :=
    congrArg ofConv ((algHomMulEquiv n k R).symm_apply_apply (toConv χ))
  ext g
  constructor
  · rintro ⟨φ, rfl⟩ a ha
    obtain ⟨χ, rfl⟩ := Spec.mapMulEquiv.surjective φ
    dsimp only
    rw [← toConv_ofConv χ, key, heval, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  · intro hg
    refine ⟨Spec.mapMulEquiv (toConv (Ideal.Quotient.liftₐ I (evalAlgHom g) fun a ha ↦ hg a ha)),
      ?_⟩
    dsimp only
    rw [key]
    exact (algHomMulEquiv n k R).apply_symm_apply g

theorem injective_homMulEquiv_comp (R : Type u) [CommRing R] [Algebra k R] :
    Function.Injective fun φ : (Spec (.of R)).asOver (Spec (.of k)) ⟶ subgroupScheme I ↦
      GeneralLinearGroup.homMulEquiv n k R (φ ≫ subgroupSchemeι I) :=
  (GeneralLinearGroup.homMulEquiv n k R).injective.comp (subgroupSchemeι_comp_injective I)

/-- The `R`-points of the closed subgroup scheme `V(I)` are the group `zeroLocus I R` of matrices
satisfying the equations in `I`: a point `φ : Spec R ⟶ V(I)` corresponds to the matrix of the
point `φ ≫ ι` of `GL_n`, where `ι : V(I) ⟶ GL_n` is the closed immersion.
(blueprint: `det-d-geometry`) -/
noncomputable def zeroLocusMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    zeroLocus I R ≃* ((Spec (.of R)).asOver (Spec (.of k)) ⟶ subgroupScheme I) :=
  (MulEquiv.subgroupCongr (SetLike.coe_injective (range_homMulEquiv_comp I R)).symm).trans
    (MonoidHom.ofInjective (f := (GeneralLinearGroup.homMulEquiv n k R).toMonoidHom.comp
      (IsMonHom.monoidHom (subgroupSchemeι I) _)) (injective_homMulEquiv_comp I R)).symm

variable {I}

@[simp]
theorem homMulEquiv_zeroLocusMulEquiv_comp {R : Type u} [CommRing R] [Algebra k R]
    (g : zeroLocus I R) :
    GeneralLinearGroup.homMulEquiv n k R (zeroLocusMulEquiv I R g ≫ subgroupSchemeι I) = g :=
  congrArg Subtype.val ((MonoidHom.ofInjective
    (f := (GeneralLinearGroup.homMulEquiv n k R).toMonoidHom.comp
      (IsMonHom.monoidHom (subgroupSchemeι I) _)) (injective_homMulEquiv_comp I R)).apply_symm_apply
      ⟨g, _⟩)

attribute [irreducible] zeroLocusMulEquiv

/-- The identification `zeroLocusMulEquiv` is natural in the algebra of values: the square
```
V(I)(R) ──zeroLocus.map φ──▶ V(I)(S)
   │                            │
   ▼                            ▼
(Spec R ⟶ V(I)) ──Spec φ ≫ ·──▶ (Spec S ⟶ V(I))
```
commutes. -/
theorem zeroLocusMulEquiv_map {R S : Type u} [CommRing R] [Algebra k R] [CommRing S]
    [Algebra k S] (φ : R →ₐ[k] S) (g : zeroLocus I R) :
    zeroLocusMulEquiv I S (zeroLocus.map I φ g) =
      (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (.of k)) ≫
        zeroLocusMulEquiv I R g := by
  apply injective_homMulEquiv_comp I S
  simp only [homMulEquiv_zeroLocusMulEquiv_comp, zeroLocus.coe_map_apply, Category.assoc,
    GeneralLinearGroup.homMulEquiv_specMap_comp]

end SubgroupScheme

section Inclusion

variable {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]

/-- The closed immersion `V(J) ⟶ V(I)` of closed subgroup schemes of `GL_n` induced by an
inclusion `I ≤ J` of Hopf ideals: the spectrum of the quotient map `k[GL_n] ⧸ I → k[GL_n] ⧸ J`.
(blueprint: `det-d-geometry`) -/
noncomputable def subgroupSchemeHom (h : I ≤ J) : subgroupScheme J ⟶ subgroupScheme I :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorₐ k h).toRingHom)).asOver (Spec (.of k))

variable (h : I ≤ J)

@[reassoc (attr := simp)]
theorem subgroupSchemeHom_comp_subgroupSchemeι :
    subgroupSchemeHom h ≫ subgroupSchemeι I = subgroupSchemeι J := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The inclusions of closed subgroup schemes compose: `V(K) ⟶ V(J) ⟶ V(I)` is `V(K) ⟶ V(I)`. -/
@[reassoc (attr := simp)]
theorem subgroupSchemeHom_comp {K : Ideal (CoordinateRing n k)} [K.IsHopfIdeal k] (h' : J ≤ K) :
    subgroupSchemeHom h' ≫ subgroupSchemeHom h = subgroupSchemeHom (h.trans h') := by
  rw [← cancel_mono (subgroupSchemeι I), Category.assoc, subgroupSchemeHom_comp_subgroupSchemeι,
    subgroupSchemeHom_comp_subgroupSchemeι, subgroupSchemeHom_comp_subgroupSchemeι]

instance : IsClosedImmersion (subgroupSchemeHom h).left :=
  IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective h)

instance : Mono (subgroupSchemeHom h) :=
  mono_of_mono_fac (subgroupSchemeHom_comp_subgroupSchemeι h)

/-- The inclusion `V(J) ⟶ V(I)` is a homomorphism of group schemes: it is the unique morphism
whose composite with the closed immersion `V(I) ⟶ GL_n` is the closed immersion `V(J) ⟶ GL_n`. -/
instance : IsMonHom (subgroupSchemeHom h) where
  one_hom := by
    rw [← cancel_mono (subgroupSchemeι I), Category.assoc,
      subgroupSchemeHom_comp_subgroupSchemeι, IsMonHom.one_hom, IsMonHom.one_hom]
  mul_hom := by
    rw [← cancel_mono (subgroupSchemeι I), Category.assoc,
      subgroupSchemeHom_comp_subgroupSchemeι, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, subgroupSchemeHom_comp_subgroupSchemeι]

/-- The inclusion `V(I) ⟶ V(I)` induced by `I ≤ I` is the identity. -/
@[simp]
theorem subgroupSchemeHom_refl : subgroupSchemeHom (le_refl I) = 𝟙 (subgroupScheme I) :=
  (cancel_mono (subgroupSchemeι I)).1 (by simp)

theorem mapMulEquiv_comp_subgroupSchemeHom {R : Type u} [CommRing R] [Algebra k R]
    (ψ : WithConv (CoordinateRing n k ⧸ J →ₐ[k] R)) :
    Spec.mapMulEquiv ψ ≫ subgroupSchemeHom h =
      Spec.mapMulEquiv (toConv (ψ.ofConv.comp (Ideal.Quotient.factorₐ k h))) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

include h in
theorem zeroLocus_le_zeroLocus (R : Type u) [CommRing R] [Algebra k R] :
    zeroLocus J R ≤ zeroLocus I R :=
  fun _ hg a ha ↦ hg a (h ha)

theorem zeroLocusMulEquiv_comp_subgroupSchemeHom {R : Type u} [CommRing R] [Algebra k R]
    (g : zeroLocus J R) :
    zeroLocusMulEquiv J R g ≫ subgroupSchemeHom h =
      zeroLocusMulEquiv I R ⟨g, zeroLocus_le_zeroLocus h R g.2⟩ := by
  apply injective_homMulEquiv_comp I R
  dsimp only
  rw [Category.assoc, subgroupSchemeHom_comp_subgroupSchemeι, homMulEquiv_zeroLocusMulEquiv_comp,
    homMulEquiv_zeroLocusMulEquiv_comp]

/-- If `V(I)(R)` has its commutators in `V(J)(R)` for every `k`-algebra `R`, then the closed
immersion `V(J) ⟶ V(I)` contains the commutators scheme-theoretically
(`AlgebraicGeometry.IsMonHom.ContainsCommutators`).

Two points `X ⟶ V(I)` factor through the affine scheme `Spec Γ(X)`, where they are matrices over
`Γ(X)`; the hypothesis for `R = Γ(X)`, transported through `zeroLocusMulEquiv`, factors their
commutator through `V(J)`. (blueprint: `lemma-restriction-normal-subgroup`) -/
theorem containsCommutators_subgroupSchemeHom
    (hIJ : ∀ (R : Type u) [CommRing R] [Algebra k R],
      ⁅zeroLocus I R, zeroLocus I R⁆ ≤ zeroLocus J R) :
    IsMonHom.ContainsCommutators (subgroupSchemeHom h) := by
  refine ⟨fun {X} a b ↦ ?_⟩
  obtain ⟨R, _, _, t, ht⟩ := Over.exists_bijective_comp_toSpecΓ X
  -- Fix the group of points used when transporting commutators.
  let : Group ((Spec (.of R)).asOver (Spec (.of k)) ⟶ subgroupScheme I) := Hom.group
  obtain ⟨a', rfl⟩ := (ht _).2 a
  obtain ⟨b', rfl⟩ := (ht _).2 b
  set x := (zeroLocusMulEquiv I R).symm a'
  set y := (zeroLocusMulEquiv I R).symm b'
  have hmem : ((x * y * x⁻¹ * y⁻¹ : zeroLocus I R) : GL n R) ∈ zeroLocus J R := by
    apply hIJ R
    exact Subgroup.commutator_mem_commutator x.2 y.2
  refine ⟨t ≫ zeroLocusMulEquiv J R ⟨_, hmem⟩, ?_⟩
  rw [Category.assoc, zeroLocusMulEquiv_comp_subgroupSchemeHom,
    show (⟨_, zeroLocus_le_zeroLocus h R hmem⟩ : zeroLocus I R) = x * y * x⁻¹ * y⁻¹ from rfl,
    ← commutatorElement_def, map_commutatorElement, commutatorElement_def,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MonObj.comp_mul, MonObj.comp_mul,
    MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv]

end Inclusion

section Conjugation

variable (g : GL n k)

/-- Conjugation `x ↦ g * x * g⁻¹` by a `k`-point `g` of `𝔾𝕃(n; k)`, as an endomorphism of the group
scheme: the spectrum of the bialgebra endomorphism `conjBialgHom g` of the coordinate ring. -/
noncomputable def conjHom : 𝔾𝕃(n; k) ⟶ 𝔾𝕃(n; k) :=
  (Spec.map (CommRingCat.ofHom (translate g g⁻¹).toRingHom)).asOver (Spec (.of k))

instance : IsMonHom (conjHom g) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom (conjBialgHom g)).op).hom)

/-- On `R`-points, `conjHom g` is conjugation by the image of `g` in `GL n R`. -/
theorem homMulEquiv_comp_conjHom {R : Type u} [CommRing R] [Algebra k R]
    (φ : (Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾𝕃(n; k)) :
    GeneralLinearGroup.homMulEquiv n k R (φ ≫ conjHom g) =
      map (algebraMap k R) g * GeneralLinearGroup.homMulEquiv n k R φ *
        map (algebraMap k R) g⁻¹ := by
  unfold GeneralLinearGroup at φ
  obtain ⟨χ, rfl⟩ := Spec.mapMulEquiv.surjective φ
  have h : Spec.mapMulEquiv χ ≫ conjHom g =
      Spec.mapMulEquiv (toConv (χ.ofConv.comp (translate g g⁻¹))) := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [h, GeneralLinearGroup.homMulEquiv_mapMulEquiv, GeneralLinearGroup.homMulEquiv_mapMulEquiv]
  apply (algHomMulEquiv n k R).symm.injective
  have hχ : evalAlgHom (algHomMulEquiv n k R χ) = χ.ofConv :=
    congrArg ofConv ((algHomMulEquiv n k R).symm_apply_apply χ)
  rw [MulEquiv.symm_apply_apply, algHomMulEquiv_symm_apply, ← evalAlgHom_comp_translate, hχ]

variable {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]
  (hg : ∀ a ∈ I, translate g g⁻¹ a ∈ I) (hg' : ∀ a ∈ I, translate g⁻¹ g a ∈ I)

include hg in
/-- A matrix `x` over `R` satisfying the equations of `I` is conjugated by `g` to such a
matrix, when conjugation by `g` preserves `I`. -/
theorem mul_mul_inv_mem_zeroLocus {R : Type u} [CommRing R] [Algebra k R] {x : GL n R}
    (hx : x ∈ zeroLocus I R) :
    map (algebraMap k R) g * x * map (algebraMap k R) g⁻¹ ∈ zeroLocus I R := fun a ha ↦ by
  rw [← evalAlgHom_comp_translate, AlgHom.comp_apply]
  exact hx _ (hg a ha)

/-- Conjugation by `g` as an automorphism of the closed subgroup scheme `V(I)`, when it preserves
the Hopf ideal `I` together with conjugation by `g⁻¹`: the spectrum of the automorphism of
`k[GL_n] ⧸ I` induced by `translate g g⁻¹`. -/
noncomputable def subgroupSchemeConjIso : subgroupScheme I ≅ subgroupScheme I where
  hom := (Spec.map (CommRingCat.ofHom
    (Ideal.quotientMapₐ (I := I) I (translate g g⁻¹) hg).toRingHom)).asOver (Spec (.of k))
  inv := (Spec.map (CommRingCat.ofHom
    (Ideal.quotientMapₐ (I := I) I (translate g⁻¹ g) hg').toRingHom)).asOver (Spec (.of k))
  hom_inv_id := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_))
    change Ideal.Quotient.mk I (translate g g⁻¹ (translate g⁻¹ g a)) = Ideal.Quotient.mk I a
    rw [← AlgHom.comp_apply, translate_comp_translate, inv_mul_cancel, translate_one_one,
      AlgHom.id_apply]
  inv_hom_id := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_))
    change Ideal.Quotient.mk I (translate g⁻¹ g (translate g g⁻¹ a)) = Ideal.Quotient.mk I a
    rw [← AlgHom.comp_apply, translate_comp_translate, mul_inv_cancel, translate_one_one,
      AlgHom.id_apply]

/-- The automorphism `subgroupSchemeConjIso` of `V(I)` is the restriction of the conjugation
`conjHom g` of `𝔾𝕃(n; k)`. -/
@[reassoc]
theorem subgroupSchemeConjIso_hom_comp_subgroupSchemeι :
    (subgroupSchemeConjIso g hg hg').hom ≫ subgroupSchemeι I =
      subgroupSchemeι I ≫ conjHom g := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Conjugation by `g` is an automorphism of the group scheme `V(I)`. -/
instance : IsMonHom (subgroupSchemeConjIso g hg hg').hom where
  one_hom := by
    rw [← cancel_mono (subgroupSchemeι I), Category.assoc,
      subgroupSchemeConjIso_hom_comp_subgroupSchemeι, IsMonHom.one_hom_assoc, IsMonHom.one_hom,
      IsMonHom.one_hom]
  mul_hom := by
    rw [← cancel_mono (subgroupSchemeι I), Category.assoc,
      subgroupSchemeConjIso_hom_comp_subgroupSchemeι, IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
      Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
      tensorHom_comp_tensorHom_assoc, subgroupSchemeConjIso_hom_comp_subgroupSchemeι]

/-- On `R`-points, the automorphism `subgroupSchemeConjIso` of `V(I)` is conjugation by the image
of `g` in `GL n R`. -/
theorem zeroLocusMulEquiv_comp_subgroupSchemeConjIso_hom {R : Type u} [CommRing R]
    [Algebra k R] (x : zeroLocus I R) :
    zeroLocusMulEquiv I R x ≫ (subgroupSchemeConjIso g hg hg').hom =
      zeroLocusMulEquiv I R ⟨_, mul_mul_inv_mem_zeroLocus g hg x.2⟩ := by
  apply injective_homMulEquiv_comp I R
  dsimp only
  rw [Category.assoc, subgroupSchemeConjIso_hom_comp_subgroupSchemeι, ← Category.assoc,
    homMulEquiv_comp_conjHom, homMulEquiv_zeroLocusMulEquiv_comp,
    homMulEquiv_zeroLocusMulEquiv_comp]

end Conjugation

section Derived

open scoped commutatorElement

/-! ### The derived subgroup

The *derived subgroup* `[G, G]` of `G = V(I)` is the smallest closed subgroup scheme `D ⊆ G` whose
inclusion `D ⟶ G` contains the commutators of `G`
(`AlgebraicGeometry.IsMonHom.ContainsCommutators`), that is, such that `G ⧸ D` is commutative; it
is normal
(`AlgebraicGeometry.IsMonHom.Normal.of_containsCommutators`). In Hopf-ideal terms it is cut out by
the largest Hopf ideal `J ≥ I` with this property, the sum of all of them. -/

variable (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The Hopf ideal of the derived subgroup `[V(I), V(I)]`: the sum of all Hopf ideals `J ≥ I` such
that `V(J) ⟶ V(I)` contains the commutators of `V(I)`. (blueprint:
`lemma-restriction-normal-subgroup`) -/
noncomputable def derivedIdeal : Ideal (CoordinateRing n k) :=
  sSup {J | ∃ (hJ : J.IsHopfIdeal k) (h : I ≤ J),
    haveI := hJ; IsMonHom.ContainsCommutators (subgroupSchemeHom h)}

/-- The derived subgroup is a subgroup: `[G, G] ⊆ G`. -/
theorem le_derivedIdeal : I ≤ derivedIdeal I :=
  le_sSup ⟨inferInstance, le_refl I,
    IsMonHom.ContainsCommutators.of_eq (subgroupSchemeHom_refl (I := I)).symm⟩

/-- The sum of Hopf ideals is a Hopf ideal, so the derived subgroup is a closed subgroup scheme.

Proof sketch (not formalised): if `Δ(a) ∈ J ⊗ A + A ⊗ J` and `Δ(b) ∈ J' ⊗ A + A ⊗ J'`, then
`Δ(a + b) ∈ (J + J') ⊗ A + A ⊗ (J + J')`; likewise for the counit and the antipode. -/
instance : (derivedIdeal I).IsHopfIdeal k :=
  Ideal.isHopfIdeal_sSup fun _ ⟨hJ, _, _⟩ ↦ hJ

/-- The derived subgroup contains the commutators of `G`: `G ⧸ [G, G]` is commutative.

Two points `X ⟶ V(I)` factor through the affine scheme `Spec Γ(X)`, where they are matrices over
`Γ(X)`. Their commutator satisfies the equations of every Hopf ideal in the family defining
`derivedIdeal I`, hence those of their sum. (blueprint: `lemma-restriction-normal-subgroup`) -/
instance : IsMonHom.ContainsCommutators (subgroupSchemeHom (le_derivedIdeal I)) := by
  refine ⟨fun {X} a b ↦ ?_⟩
  let : Group (X ⟶ subgroupScheme I) := Hom.group
  obtain ⟨R, _, _, t, ht⟩ := Over.exists_bijective_comp_toSpecΓ X
  let : Group ((Spec (.of R)).asOver (Spec (.of k)) ⟶ subgroupScheme I) := Hom.group
  obtain ⟨a', rfl⟩ := (ht _).2 a
  obtain ⟨b', rfl⟩ := (ht _).2 b
  have hγ : ⁅t ≫ a', t ≫ b'⁆ = t ≫ ⁅a', b'⁆ := by
    simp only [commutatorElement_def, MonObj.comp_mul, GrpObj.comp_inv]
  obtain ⟨ψ, hψ⟩ := Spec.mapMulEquiv.surjective ⁅a', b'⁆
  obtain ⟨ψ, rfl⟩ : ∃ ψ₀, toConv ψ₀ = ψ := ⟨_, toConv_ofConv ψ⟩
  have hkill (J : Ideal (CoordinateRing n k)) [J.IsHopfIdeal k] (hIJ : I ≤ J)
      (hc : IsMonHom.ContainsCommutators (subgroupSchemeHom hIJ)) :
      J ≤ RingHom.ker (ψ.comp (Ideal.Quotient.mkₐ k I)) := by
    intro j hj
    obtain ⟨c, hc'⟩ := hc.exists_comp_eq_commutator (t ≫ a') (t ≫ b')
    obtain ⟨c', rfl⟩ := (ht _).2 c
    obtain ⟨χ, rfl⟩ := Spec.mapMulEquiv.surjective c'
    have e : Spec.mapMulEquiv χ ≫ subgroupSchemeHom hIJ = ⁅a', b'⁆ :=
      (ht _).1 (by
        beta_reduce at hc' ⊢
        rw [← Category.assoc, hc']
        exact hγ)
    rw [mapMulEquiv_comp_subgroupSchemeHom, ← hψ] at e
    have e' : χ.ofConv.comp (Ideal.Quotient.factorₐ k hIJ) = ψ := by
      simpa using congrArg ofConv (Spec.mapMulEquiv.injective e)
    rw [RingHom.mem_ker, AlgHom.comp_apply, ← e']
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hj]
  have hker : derivedIdeal I ≤ RingHom.ker (ψ.comp (Ideal.Quotient.mkₐ k I)) :=
    sSup_le fun J ⟨hJ, hIJ, hc⟩ ↦ hkill J hIJ hc
  refine ⟨t ≫ Spec.mapMulEquiv (toConv (Ideal.Quotient.liftₐ (derivedIdeal I)
    (ψ.comp (Ideal.Quotient.mkₐ k I)) fun j hj ↦ hker hj)), ?_⟩
  rw [Category.assoc, mapMulEquiv_comp_subgroupSchemeHom, ← commutatorElement_def, hγ]
  congr 1
  rw [← hψ]
  congr 1
  rw [ofConv_toConv]
  congr 1
  apply Ideal.Quotient.algHom_ext
  ext a
  rfl

variable {I} {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k] (h : I ≤ J)

/-- A closed subgroup `V(J) ⊆ V(I)` contains the commutators of `V(I)` if and only if it contains
the derived subgroup `[V(I), V(I)]`, that is, `J ≤ derivedIdeal I`.
(blueprint: `lemma-restriction-normal-subgroup`) -/
theorem containsCommutators_iff_le_derivedIdeal :
    IsMonHom.ContainsCommutators (subgroupSchemeHom h) ↔ J ≤ derivedIdeal I := by
  refine ⟨fun hc ↦ le_sSup ⟨inferInstance, h, hc⟩, fun hJ ↦ ⟨fun a b ↦ ?_⟩⟩
  obtain ⟨c, hc⟩ := IsMonHom.ContainsCommutators.exists_comp_eq_commutator
    (subgroupSchemeHom (le_derivedIdeal I)) a b
  exact ⟨c ≫ subgroupSchemeHom hJ, by rw [Category.assoc, subgroupSchemeHom_comp, hc]⟩

end Derived

section OnePoint

variable {k : Type u} [Field k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The identity point of `GL_n` is the maximal ideal `ker(ev_1)` of the coordinate ring. -/
theorem onePoint_generalLinearGroup : GrpObj.onePoint 𝔾𝕃(n; k) = toPrimeSpectrum 1 := by
  have h₁ : (1 : (Spec (.of k)).asOver (Spec (.of k)) ⟶ 𝔾𝕃(n; k)) =
      Spec.mapMulEquiv (toConv (evalAlgHom (1 : GL n k))) := by
    apply (GeneralLinearGroup.homMulEquiv n k k).injective
    rw [map_one, GeneralLinearGroup.homMulEquiv_mapMulEquiv, ← algHomMulEquiv_symm_apply,
      MulEquiv.apply_symm_apply]
  have h₂ : (1 : (Spec (.of k)).asOver (Spec (.of k)) ⟶ 𝔾𝕃(n; k)).left
      (show Spec (.of k) from ⟨⊥, Ideal.isPrime_bot⟩) = GrpObj.onePoint 𝔾𝕃(n; k) := by
    rw [Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]
    exact congrArg _ (Subsingleton.elim (α := PrimeSpectrum k) _ _)
  rw [← h₂, h₁]
  apply PrimeSpectrum.ext
  exact (RingHom.ker_eq_comap_bot _).symm

/-- The closed immersion `V(I) ⟶ GL_n` maps the identity point to the identity point. -/
theorem subgroupSchemeι_onePoint :
    (subgroupSchemeι I).left (GrpObj.onePoint (subgroupScheme I)) = GrpObj.onePoint 𝔾𝕃(n; k) :=
  congrArg (fun g ↦ g.left (show Spec (.of k) from ⟨⊥, Ideal.isPrime_bot⟩))
    (IsMonHom.one_hom (subgroupSchemeι I))

theorem range_subgroupSchemeι {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k] :
    Set.range (subgroupSchemeι J).left =
      PrimeSpectrum.zeroLocus (J : Set (CoordinateRing n k)) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mkₐ k J).toRingHom) = _
  rw [range_comap_of_surjective (S := CoordinateRing n k ⧸ J) (Ideal.Quotient.mkₐ k J).toRingHom
    Ideal.Quotient.mk_surjective]
  exact congrArg _ (congrArg SetLike.coe (Ideal.mk_ker (I := J)))

omit [I.IsHopfIdeal k] in
/-- The connected component of the identity point in the zero locus of `I` is closed. -/
theorem isClosed_connectedComponentIn_zeroLocus :
    IsClosed (connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))
      (toPrimeSpectrum 1)) := by
  by_cases hx : toPrimeSpectrum 1 ∈ PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))
  · rw [connectedComponentIn_eq_image hx]
    exact (PrimeSpectrum.isClosed_zeroLocus _).isClosedEmbedding_subtypeVal.isClosedMap _
      isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

end OnePoint

section IdentityComponent

variable {k : Type u} [Field k] [IsAlgClosed k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The closed subgroup scheme `V(identityComponent I)` cut out by the ideal of the reduced
identity component is the reduced closed subscheme of `V(I)` on the identity component
`GrpObj.identityComponent (subgroupScheme I)`: its image in `V(I)` is the connected component of the
identity point. (blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem range_subgroupSchemeHom_le_identityComponent :
    Set.range (subgroupSchemeHom (le_identityComponent I)).left.base =
      connectedComponent (GrpObj.onePoint (subgroupScheme I)) := by
  have hemb := (subgroupSchemeι I).left.isClosedEmbedding
  apply hemb.injective.image_injective
  have hcomp : ⇑(subgroupSchemeι I).left ∘ ⇑(subgroupSchemeHom (le_identityComponent I)).left =
      ⇑(subgroupSchemeι (identityComponent I)).left := by
    funext x
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left,
      subgroupSchemeHom_comp_subgroupSchemeι]
  rw [← Set.range_comp, hcomp, hemb.isInducing.image_connectedComponent,
    subgroupSchemeι_onePoint, onePoint_generalLinearGroup, range_subgroupSchemeι,
    range_subgroupSchemeι, identityComponent, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact (isClosed_connectedComponentIn_zeroLocus I).closure_eq

/-- A `k`-point of `V(I)` whose image lies in the connected component of the identity is a
`k`-point of the identity component: its matrix satisfies the equations `identityComponent I`. -/
theorem mem_zeroLocus_identityComponent_of_range_subset {g : zeroLocus I k}
    (hg : Set.range (zeroLocusMulEquiv I k g).left.base ⊆
      connectedComponent (GrpObj.onePoint (subgroupScheme I))) :
    (g : GL n k) ∈ zeroLocus (identityComponent I) k := by
  obtain ⟨χ, hχ⟩ := Spec.mapMulEquiv.surjective (zeroLocusMulEquiv I k g)
  have hev : evalAlgHom (g : GL n k) = χ.ofConv.comp (Ideal.Quotient.mkₐ k I) := by
    have h := homMulEquiv_zeroLocusMulEquiv_comp g
    rw [← hχ, mapMulEquiv_comp_subgroupSchemeι, GeneralLinearGroup.homMulEquiv_mapMulEquiv] at h
    rw [← h]
    exact congrArg ofConv ((algHomMulEquiv n k k).symm_apply_apply _)
  let pt : Spec (.of k) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨y, hy⟩ := (range_subgroupSchemeHom_le_identityComponent I).symm ▸ hg ⟨pt, rfl⟩
  intro a ha
  rw [hev]
  have hx := congrArg PrimeSpectrum.asIdeal hy
  rw [← hχ] at hx
  change Ideal.comap _ y.asIdeal = Ideal.comap _ (⊥ : Ideal k) at hx
  have : Ideal.Quotient.mk I a ∈
      Ideal.comap (CommRingCat.Hom.hom (CommRingCat.ofHom χ.ofConv.toRingHom)) ⊥ := by
    rw [← hx, Ideal.mem_comap]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  simpa using this

/-- The `k`-points of the identity component `G°` have finite index in the `k`-points of
`G = V(I)`. This is `AlgebraicGeometry.GrpObj.finiteIndex_range_identityComponentι` for the group
scheme `V(I)`, read on matrices through `zeroLocusMulEquiv`. (blueprint:
`lemma-connected-components-images-homomorphisms`) -/
theorem finiteIndex_subgroupOf_zeroLocus_identityComponent :
    ((zeroLocus (identityComponent I) k).subgroupOf (zeroLocus I k)).FiniteIndex := by
  let X := (Spec (.of k)).asOver (Spec (.of k))
  let e : X ≅ 𝟙_ (Over (Spec (.of k))) := Over.isoMk (Iso.refl (Spec (.of k))) (by
    simp [X, specOverSpec_over, Algebra.algebraMap_self])
  let α : (𝟙_ (Over (Spec (.of k))) ⟶ subgroupScheme I) →* zeroLocus I k :=
    (zeroLocusMulEquiv I k).symm.toMonoidHom.comp
      { toFun p := CartesianMonoidalCategory.toUnit X ≫ p
        map_one' := MonObj.comp_one _
        map_mul' p q := MonObj.comp_mul _ _ _ }
  have hα : Function.Surjective α := fun g ↦ ⟨e.inv ≫ zeroLocusMulEquiv I k g, by
    simp [α, CartesianMonoidalCategory.toUnit_unique (CartesianMonoidalCategory.toUnit X) e.hom]⟩
  have := GrpObj.finiteIndex_range_identityComponentι (subgroupScheme I)
  have hle : (IsMonHom.monoidHom (GrpObj.identityComponentι (subgroupScheme I))
      (𝟙_ (Over (Spec (.of k))))).range ≤
        ((zeroLocus (identityComponent I) k).subgroupOf (zeroLocus I k)).comap α := by
    rintro _ ⟨q, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    refine mem_zeroLocus_identityComponent_of_range_subset I ?_
    rw [← GrpObj.range_identityComponentι]
    rintro _ ⟨x, rfl⟩
    simp only [α, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    exact ⟨_, rfl⟩
  have := Subgroup.finiteIndex_of_le hle
  rw [Subgroup.finiteIndex_iff, ← Subgroup.index_comap_of_surjective _ hα]
  exact Subgroup.FiniteIndex.index_ne_zero

end IdentityComponent

section Geometry

variable {k : Type u} [Field k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The closed subgroup scheme `V(I)` is reduced when `I` is a radical ideal. -/
theorem isReduced_subgroupScheme (hI : I.IsRadical) : IsReduced (subgroupScheme I).left :=
  haveI : _root_.IsReduced (CoordinateRing n k ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).1 hI
  inferInstanceAs (IsReduced (Spec (.of (CoordinateRing n k ⧸ I))))

/-- The closed subgroup scheme `V(I)` is connected when `I` is the ideal of its own reduced
identity component: `V(I)` is then the closure of the connected component of the identity in
`V(I)`, which is closed. -/
theorem connectedSpace_subgroupScheme (h : IsConnected I) :
    ConnectedSpace (subgroupScheme I).left := by
  have hemb := (subgroupSchemeι I).left.isClosedEmbedding
  have hr : Set.range (subgroupSchemeι I).left = connectedComponentIn
      (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) (toPrimeSpectrum 1) := by
    rw [range_subgroupSchemeι]
    conv_lhs => rw [← h]
    rw [identityComponent, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      (isClosed_connectedComponentIn_zeroLocus I).closure_eq]
  rw [connectedSpace_iff_univ]
  refine ⟨⟨GrpObj.onePoint _, trivial⟩, hemb.isInducing.isPreconnected_image.1 ?_⟩
  rw [Set.image_univ, hr]
  exact isPreconnected_connectedComponentIn

/-- The reduced centre `Z(G)` of a reduced `G = V(I)` over an algebraically closed field is
central scheme-theoretically: its points commute with all points of `G`.

Both points factor through the affine scheme `Spec Γ(X)`, where they are matrices, and these
commute by `Matrix.GeneralLinearGroup.commute_of_mem_zeroLocus_center`: the commutation equations
vanish on the rational points of `Z(G) × G`, which are dense in this reduced scheme.
(blueprint: `lemma-stable-subspaces-center`) -/
theorem central_subgroupSchemeHom_le_center [IsAlgClosed k] (hI : I.IsRadical)
    {X : Over (Spec (.of k))} (a : X ⟶ subgroupScheme (center I)) (b : X ⟶ subgroupScheme I) :
    (a ≫ subgroupSchemeHom (le_center I)) * b = b * (a ≫ subgroupSchemeHom (le_center I)) := by
  -- Both points factor through the affine scheme `Spec Γ(X)`, so we may assume `X` affine.
  let adj := algΓAlgSpecAdjunction (.of k)
  have hfac {Y : (CommAlgCat k)ᵒᵖ} (f : X ⟶ (algSpec (.of k)).obj Y) :
      ∃ f' : (algSpec (.of k)).obj ((algΓ (.of k)).obj X) ⟶ (algSpec (.of k)).obj Y,
        f = adj.unit.app X ≫ f' :=
    ⟨_, ((adj.homEquiv_unit (f := (adj.homEquiv X Y).symm f)).symm.trans
      ((adj.homEquiv X Y).apply_symm_apply f)).symm⟩
  obtain ⟨a, rfl⟩ : ∃ a' : (algSpec (.of k)).obj ((algΓ (.of k)).obj X) ⟶
      subgroupScheme (center I), a = (adj.unit.app X : X ⟶ _) ≫ a' :=
    hfac (Y := .op (.of k (CoordinateRing n k ⧸ center I))) a
  obtain ⟨b, rfl⟩ : ∃ b' : (algSpec (.of k)).obj ((algΓ (.of k)).obj X) ⟶
      subgroupScheme I, b = (adj.unit.app X : X ⟶ _) ≫ b' :=
    hfac (Y := .op (.of k (CoordinateRing n k ⧸ I))) b
  rw [Category.assoc, ← MonObj.comp_mul, ← MonObj.comp_mul]
  refine congrArg _ ?_
  -- For `X = Spec R`, the points are matrices over `R`.
  let R := ((algΓ (.of k)).obj X).unop
  apply injective_homMulEquiv_comp I R
  have ha : GeneralLinearGroup.homMulEquiv n k R (a ≫ subgroupSchemeι (center I)) ∈
      zeroLocus (center I) R := by
    rw [← SetLike.mem_coe, ← range_homMulEquiv_comp]
    exact ⟨a, rfl⟩
  have hb : GeneralLinearGroup.homMulEquiv n k R (b ≫ subgroupSchemeι I) ∈ zeroLocus I R := by
    rw [← SetLike.mem_coe, ← range_homMulEquiv_comp]
    exact ⟨b, rfl⟩
  dsimp only
  rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, subgroupSchemeHom_comp_subgroupSchemeι,
    map_mul, map_mul]
  exact (commute_of_mem_zeroLocus_center hI ha hb).eq

end Geometry

end AlgebraicGeometry.GeneralLinearGroup
