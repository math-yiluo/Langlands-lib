/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Higher direct images of sheaves of modules

The higher direct images `R^q f_* ℱ` of a sheaf of modules along a morphism of schemes
(`AlgebraicGeometry.Scheme.Modules.higherDirectImage`), flatness over the base, the fibre
cohomology dimensions `h^q(X_t, ℱ_t)` (`AlgebraicGeometry.Scheme.Modules.hFiber`), the
fibrewise Euler characteristic and the perfect loci.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

/-- `X.Modules` is a Grothendieck abelian category (`SheafOfModules.isGrothendieckAbelian`).

Together with `CategoryTheory.IsGrothendieckAbelian.enoughInjectives` it supplies the
`HasInjectiveResolutions X.Modules` instance that every statement below, and every statement
about the Picard functor `F` downstream, assumes. -/
theorem isGrothendieckAbelian (X : Scheme.{u}) : IsGrothendieckAbelian.{u} X.Modules :=
  SheafOfModules.isGrothendieckAbelian X.ringCatSheaf

/-- The `q`-th **higher direct image** functor `R^q f_*` along a morphism of schemes
`f : X ⟶ T`: the `q`-th right derived functor of the pushforward functor
`AlgebraicGeometry.Scheme.Modules.pushforward f : X.Modules ⥤ T.Modules`.

Both `X.Modules` and `T.Modules` are abelian and the pushforward is additive, so the only
extra input is the existence of injective resolutions in `X.Modules`, which is taken as an
instance hypothesis. -/
noncomputable def higherDirectImage (f : X ⟶ T) [HasInjectiveResolutions X.Modules] (q : ℕ) :
    X.Modules ⥤ T.Modules :=
  (pushforward f).rightDerived q

/-- **The higher direct images are linear over the base.** Applying `R^q f_*` to multiplication
by `f^♯ a` on `M` gives multiplication by `a` on `R^q f_* M`. -/
lemma higherDirectImage_map_smulHom (f : X ⟶ T) [HasInjectiveResolutions X.Modules] (q : ℕ)
    (M : X.Modules)
    (a : Γ(T, ⊤)) :
    (higherDirectImage f q).map (M.smulHom (f.appTop a)) =
      ((higherDirectImage f q).obj M).smulHom a :=
  (pushforward f).rightDerived_map_app_eq
    { app M := M.smulHom (f.appTop a), naturality _ _ φ := (smulHom_naturality φ _).symm }
    { app N := N.smulHom a, naturality _ _ φ := (smulHom_naturality φ _).symm }
    (fun M ↦ pushforward_map_smulHom f M a) q M

/-- `ℱ.IsFlatOver f` says that the `𝒪_X`-module `ℱ` is **flat over the base** of the morphism
`f : X ⟶ T`: for every affine open `V` of `T` and every affine open `U` of `X` contained in
`f ⁻¹ᵁ V`, the sections `Γ(ℱ, U)` form a flat `Γ(T, V)`-module, the module structure being
restriction of scalars along `f.appLE V U`.

This is the affine-local form of the stalkwise condition "`ℱ_x` is flat over `𝒪_{T, f x}` for
every `x`", and the two are equivalent. -/
def IsFlatOver (ℱ : X.Modules) (f : X ⟶ T) : Prop :=
  ∀ (V : T.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1),
    letI : Module Γ(T, V.1) Γ(ℱ, U.1) := Module.compHom _ (f.appLE V.1 U.1 e).hom
    Module.Flat Γ(T, V.1) Γ(ℱ, U.1)

/-- **An invertible module is flat over the base of a flat morphism.** If `f : X ⟶ T` is flat
and `ℱ` is an invertible `𝒪_X`-module, then `ℱ` is flat over `T`: on an affine open `U` the
sections `Γ(ℱ, U)` form an invertible, hence flat, `Γ(X, U)`-module, and `Γ(X, U)` is flat over
`Γ(T, V)` by flatness of `f`. -/
theorem isFlatOver_of_isInvertible (f : X ⟶ T) [Flat f] (ℱ : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} ℱ] : ℱ.IsFlatOver f := by
  intro V U e
  let := (f.appLE V.1 U.1 e).hom.toAlgebra
  have : Module.Flat Γ(T, V.1) Γ(X, U.1) := HasRingHomProperty.appLE @Flat f ‹_› V U e
  have := flat_sections_of_isInvertible ℱ U.2
  let : Module Γ(T, V.1) Γ(ℱ, U.1) := Module.compHom _ (f.appLE V.1 U.1 e).hom
  have : IsScalarTower Γ(T, V.1) Γ(X, U.1) Γ(ℱ, U.1) := ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(T, V.1) Γ(X, U.1) Γ(ℱ, U.1)

/-- The `q`-th **fibre dimension** `dim_{κ(t)} H^q(X_t, ℱ_t)` of an `𝒪_X`-module `ℱ` along a
morphism `f : X ⟶ T` at a point `t` of `T`: the fibre `X_t = f.fiber t` is a scheme over the
residue field `κ(t) = T.residueField t`, the restriction `ℱ_t` is the pullback of `ℱ` along
`f.fiberι t`, and the dimension is `AlgebraicGeometry.Scheme.Modules.finrankH` for that base
field. -/
noncomputable def hFiber (ℱ : X.Modules) (f : X ⟶ T) (q : ℕ) (t : T) : ℕ :=
  letI := f.fiberOverSpecResidueField t
  ((Modules.pullback (f.fiberι t)).obj ℱ).finrankH (T.residueField t) q

/-- The **perfect locus** `U_i` of an `𝒪_X`-module `ℱ` along `f : X ⟶ T` in degree `i`: the set
of points `t` of `T` at which the fibre cohomology `H^q(X_t, ℱ_t)` vanishes for all `q ≠ i`. -/
def perfectLocus (ℱ : X.Modules) (f : X ⟶ T) (i : ℕ) : Set T :=
  {t | ∀ q ≠ i, ℱ.hFiber f q t = 0}

/-- The **rank-`r` perfect locus** `U_{i,r}` of an `𝒪_X`-module `ℱ` along `f : X ⟶ T`: the set
of points `t` of the perfect locus `U_i` at which `H^i(X_t, ℱ_t)` has dimension `r`. -/
def perfectLocusOfRank (ℱ : X.Modules) (f : X ⟶ T) (i r : ℕ) : Set T :=
  {t ∈ ℱ.perfectLocus f i | ℱ.hFiber f i t = r}

/-- The **fibre Euler characteristic** `Σ_q (-1)^q dim_{κ(t)} H^q(X_t, ℱ_t)` of an `𝒪_X`-module
`ℱ` along `f : X ⟶ T` at a point `t` of `T`. -/
noncomputable def eulerCharFiber (ℱ : X.Modules) (f : X ⟶ T) (t : T) : ℤ :=
  ∑ᶠ q : ℕ, (-1) ^ q * (ℱ.hFiber f q t : ℤ)

/-- The fibre dimensions only depend on the isomorphism class of the module. -/
lemma hFiber_congr {ℱ 𝒢 : X.Modules} (e : ℱ ≅ 𝒢) (f : X ⟶ T) (q : ℕ) (t : T) :
    ℱ.hFiber f q t = 𝒢.hFiber f q t :=
  letI := f.fiberOverSpecResidueField t
  finrankH_congr _ ((Modules.pullback (f.fiberι t)).mapIso e) q

/-- The fibre Euler characteristic only depends on the isomorphism class of the module. -/
lemma eulerCharFiber_congr {ℱ 𝒢 : X.Modules} (e : ℱ ≅ 𝒢) (f : X ⟶ T) :
    ℱ.eulerCharFiber f = 𝒢.eulerCharFiber f := by
  ext t
  simp only [eulerCharFiber, hFiber_congr e]

/-- **The fibre dimension over a field.** For a scheme `X` over a field `K`, through
`f : X ⟶ Spec K`, and a quasi-coherent `𝒪_X`-module `ℱ`, the fibre dimension of `ℱ` at the
unique point of `Spec K` is `dim_K H^q(X, ℱ)`: the fibre of `f` is `X` itself, base changed along
the isomorphism `Spec κ(s) ≅ Spec K`. -/
theorem hFiber_eq_finrankH {K : Type u} [Field K] (f : X ⟶ Spec (.of K)) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) (s : Spec (.of K)) :
    ℱ.hFiber f q s = letI : X.Over (Spec (.of K)) := ⟨f⟩; ℱ.finrankH K q := by
  let φ := (Spec (.of K)).fromSpecResidueField s
  have : IsClosedImmersion φ := isClosed_singleton_iff_isClosedImmersion.1 (by
    rw [← (Set.subsingleton_of_subsingleton).eq_singleton_of_mem (Set.mem_univ s)]
    exact isClosed_univ)
  have : Surjective φ := ⟨fun t ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  have : IsIso φ := isIso_of_isClosedImmersion_of_surjective φ
  have : IsIso (f.fiberι s) := by unfold Scheme.Hom.fiberι; infer_instance
  have : IsIso (Spec.preimage φ) := by
    have : IsIso (Scheme.Spec.map (Spec.preimage φ).op) := by
      change IsIso (Spec.map (Spec.preimage φ))
      rw [Spec.map_preimage]
      infer_instance
    have := isIso_of_reflects_iso (Spec.preimage φ).op Scheme.Spec
    exact isIso_of_op _
  have hfac : f.fiberι s ≫ f = f.fiberToSpecResidueField s ≫ Spec.map (Spec.preimage φ) := by
    rw [Spec.map_preimage]
    exact pullback.condition
  let : X.Over (Spec (.of K)) := ⟨f⟩
  let : (f.fiber s).Over (Spec (.of K)) :=
    ⟨f.fiberToSpecResidueField s ≫ Spec.map (Spec.preimage φ)⟩
  have : (inv (f.fiberι s)).IsOver (Spec (.of K)) := ⟨by
    change inv _ ≫ (_ ≫ _) = f
    rw [← hfac, IsIso.inv_hom_id_assoc]⟩
  -- change the base field from `κ(s)` to `K`, then transport along `f.fiberι s`
  refine (finrankH_eq_of_comp_specMap (k := K) (L := (Spec (.of K)).residueField s)
    (Spec.preimage φ) (f.fiberToSpecResidueField s) _ q).symm.trans ?_
  rw [← finrankH_pushforward_of_isAffineHom K (inv (f.fiberι s)) ℱ q]
  exact finrankH_congr K ((pullbackIsoPushforwardInv (f.fiberι s)).app ℱ) q

/-- **The fibre Euler characteristic over a field** is the Euler characteristic, in the
situation of `AlgebraicGeometry.Scheme.Modules.hFiber_eq_finrankH`. -/
theorem eulerCharFiber_eq_eulerChar {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (s : Spec (.of K)) :
    ℱ.eulerCharFiber f s = letI : X.Over (Spec (.of K)) := ⟨f⟩; ℱ.eulerChar K := by
  simp only [eulerCharFiber, eulerChar, hFiber_eq_finrankH f ℱ _ s]

@[simp]
theorem mem_perfectLocus (ℱ : X.Modules) (f : X ⟶ T) (i : ℕ) (t : T) :
    t ∈ ℱ.perfectLocus f i ↔ ∀ q ≠ i, ℱ.hFiber f q t = 0 :=
  Iff.rfl

@[simp]
theorem mem_perfectLocusOfRank (ℱ : X.Modules) (f : X ⟶ T) (i r : ℕ) (t : T) :
    t ∈ ℱ.perfectLocusOfRank f i r ↔ t ∈ ℱ.perfectLocus f i ∧ ℱ.hFiber f i t = r :=
  Iff.rfl

theorem perfectLocusOfRank_subset (ℱ : X.Modules) (f : X ⟶ T) (i r : ℕ) :
    ℱ.perfectLocusOfRank f i r ⊆ ℱ.perfectLocus f i :=
  fun _ ht ↦ ht.1

end AlgebraicGeometry.Scheme.Modules
