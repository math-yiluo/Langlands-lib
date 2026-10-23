import Langlands.Cohomology.DivisibleSystem
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.FiniteIndex

/-!
# The standard resolution of `ℓ`-divisible systems

Harris 1999, §2, pp.305–306, writes `M_m^{q,H} = G_m^q(U(ẽ)_F̄)^H` and obtains "the standard
resolution by iterating the functorial surjection" (2.4) `ℤ_ℓ[S(ẽ)/H] ⊗_{ℤ_ℓ} (•) → •`.
(2.5) is the resulting resolution `⋯ → K_m^{-r,q,H} → ⋯ → K_m^{-1,q,H} → M_m^{q,H} → 0`.

This module iterates an endofunctor `P` of an abelian category along a natural transformation
`ε : P ⟶ 𝟭`. The degree `r` term is `P^(r+1)`. The differential `P^(r+2) ⟶ P^(r+1)` is `ε` at
`P^(r+1)` minus `P` applied to the differential `P^(r+1) ⟶ P^r`, starting from
`ε : P ⟶ 𝟭`. These differentials square to zero when `P` preserves zero morphisms, by
naturality of `ε`. When `P` is additive and exact, so is the resulting functor to chain
complexes. It therefore carries `ℓ`-divisible systems to `ℓ`-divisible systems of chain
complexes, augmented by `ε`, and `ℓ`-divisible systems of cochain complexes to `ℓ`-divisible
systems of double complexes. In the group case `Γ` is finite, `P` is restriction to the trivial
subgroup followed by induction, and `ε` is the counit of Mathlib's induction–restriction
adjunction.

The exactness of the augmented complex and any freeness of its terms are not proved here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe w v u

section Standard

variable {A : Type u} [Category.{v} A] [Abelian A] (P : A ⥤ A) (ε : P ⟶ 𝟭 A)

/-- The iterates of an endofunctor: `P^0 = 𝟭` and `P^(n+1) = P^n ⋙ P`, so the last `P` is
applied outermost. -/
def standardPow : ℕ → A ⥤ A
  | 0 => 𝟭 A
  | n + 1 => standardPow n ⋙ P

/-- `ε` at `P^(n+1)`, as a natural transformation `P^(n+2) ⟶ P^(n+1)`. -/
@[simps]
def standardCounit (n : ℕ) : standardPow P (n + 2) ⟶ standardPow P (n + 1) where
  app X := ε.app ((standardPow P (n + 1)).obj X)
  naturality _ _ f := ε.naturality ((standardPow P (n + 1)).map f)

/-- `P` applied to a natural transformation `P^(n+1) ⟶ P^n`. -/
@[simps]
def standardPowMap {n : ℕ} (φ : standardPow P (n + 1) ⟶ standardPow P n) :
    standardPow P (n + 2) ⟶ standardPow P (n + 1) where
  app X := P.map (φ.app X)
  naturality X Y f := by
    have h := congrArg P.map (φ.naturality f)
    rw [P.map_comp, P.map_comp] at h
    exact h

/-- The augmented differentials `P^(n+1) ⟶ P^n` of the standard resolution: `ε` for `n = 0`;
for `n + 1`, `ε` at `P^(n+1)` minus `P` applied to the differential `P^(n+1) ⟶ P^n`. -/
def standardDifferential : (n : ℕ) → standardPow P (n + 1) ⟶ standardPow P n
  | 0 =>
    { app X := ε.app X
      naturality _ _ f := ε.naturality f }
  | n + 1 => standardCounit P ε n - standardPowMap P (standardDifferential n)

lemma standardDifferential_zero_app (X : A) : (standardDifferential P ε 0).app X = ε.app X :=
  rfl

lemma standardDifferential_succ (n : ℕ) :
    standardDifferential P ε (n + 1) =
      standardCounit P ε n - standardPowMap P (standardDifferential P ε n) :=
  rfl

omit [Abelian A] in
/-- Naturality of `ε` at the components of `φ : P^(n+2) ⟶ P^(n+1)`. -/
lemma standardPowMap_comp_standardCounit {n : ℕ}
    (φ : standardPow P (n + 2) ⟶ standardPow P (n + 1)) :
    standardPowMap P φ ≫ standardCounit P ε n = standardCounit P ε (n + 1) ≫ φ := by
  ext X
  exact ε.naturality (φ.app X)

variable [P.PreservesZeroMorphisms]

/-- If `φ` composes to zero with the differential `P^(n+1) ⟶ P^n`, then `P φ` followed by the
next differential is `ε` followed by `φ`. -/
lemma standardPowMap_comp_standardDifferential_succ {n : ℕ}
    (φ : standardPow P (n + 2) ⟶ standardPow P (n + 1))
    (hφ : φ ≫ standardDifferential P ε n = 0) :
    standardPowMap P φ ≫ standardDifferential P ε (n + 1) = standardCounit P ε (n + 1) ≫ φ := by
  have h : standardPowMap P φ ≫ standardPowMap P (standardDifferential P ε n) = 0 := by
    ext X
    have h' := congr_app hφ X
    rw [NatTrans.comp_app, NatTrans.app_zero] at h'
    rw [NatTrans.comp_app, NatTrans.app_zero]
    exact (P.map_comp _ _).symm.trans ((congrArg P.map h').trans (P.map_zero _ _))
  rw [standardDifferential_succ, Preadditive.comp_sub, h, sub_zero,
    standardPowMap_comp_standardCounit]

/-- The augmented differentials square to zero. -/
theorem standardDifferential_comp (n : ℕ) :
    standardDifferential P ε (n + 1) ≫ standardDifferential P ε n = 0 := by
  induction n with
  | zero =>
    have h : standardPowMap P (standardDifferential P ε 0) ≫ standardDifferential P ε 0 =
        standardCounit P ε 0 ≫ standardDifferential P ε 0 := by
      ext X
      exact ε.naturality ((standardDifferential P ε 0).app X)
    rw [standardDifferential_succ, Preadditive.sub_comp, h, sub_self]
  | succ n ih =>
    rw [standardDifferential_succ P ε (n + 1), Preadditive.sub_comp,
      standardPowMap_comp_standardDifferential_succ P ε _ ih, sub_self]

/-- The standard complex of functors `⋯ ⟶ P^3 ⟶ P^2 ⟶ P`, with `P^(r+1)` in degree `r`. -/
def standardComplex : ChainComplex (A ⥤ A) ℕ :=
  ChainComplex.of (fun r => standardPow P (r + 1)) (fun r => standardDifferential P ε (r + 1))
    (fun r => standardDifferential_comp P ε (r + 1))

lemma standardComplex_X (r : ℕ) : (standardComplex P ε).X r = standardPow P (r + 1) :=
  rfl

lemma standardComplex_d (r : ℕ) :
    (standardComplex P ε).d (r + 1) r = standardDifferential P ε (r + 1) :=
  ChainComplex.of_d (fun r => standardPow P (r + 1)) (fun r => standardDifferential P ε (r + 1)) r

/-- The standard resolution `X ↦ (⋯ ⟶ P^3 X ⟶ P^2 X ⟶ P X)`, without its augmentation. -/
def standardResolution : A ⥤ ChainComplex A ℕ :=
  (standardComplex P ε).asFunctor

lemma standardResolution_obj_X (X : A) (r : ℕ) :
    ((standardResolution P ε).obj X).X r = (standardPow P (r + 1)).obj X :=
  rfl

lemma standardResolution_obj_d (X : A) (r : ℕ) :
    ((standardResolution P ε).obj X).d (r + 1) r = (standardDifferential P ε (r + 1)).app X :=
  congr_app (standardComplex_d P ε r) X

lemma standardResolution_map_f {X Y : A} (f : X ⟶ Y) (r : ℕ) :
    ((standardResolution P ε).map f).f r = (standardPow P (r + 1)).map f :=
  rfl

/-- The augmentation `ε : P X ⟶ X` kills the first differential. -/
lemma standardResolution_obj_d_comp (X : A) :
    ((standardResolution P ε).obj X).d 1 0 ≫ ε.app X = 0 := by
  have h := congr_app (standardDifferential_comp P ε 0) X
  rw [NatTrans.comp_app, NatTrans.app_zero] at h
  exact (congrArg (· ≫ ε.app X) (standardResolution_obj_d P ε X 0)).trans h

/-- The augmentation of the standard resolution, given by `ε` in degree `0`. -/
@[simps]
def standardResolutionAugmentation : standardResolution P ε ⟶ ChainComplex.single₀ A where
  app X := (ChainComplex.toSingle₀Equiv _ X).symm ⟨ε.app X, standardResolution_obj_d_comp P ε X⟩
  naturality X Y f := by
    ext
    have hX := ChainComplex.toSingle₀Equiv_symm_apply_f_zero
      (C := (standardResolution P ε).obj X) (X := X) (ε.app X) (standardResolution_obj_d_comp P ε X)
    have hY := ChainComplex.toSingle₀Equiv_symm_apply_f_zero
      (C := (standardResolution P ε).obj Y) (X := Y) (ε.app Y) (standardResolution_obj_d_comp P ε Y)
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    exact (congrArg (((standardResolution P ε).map f).f 0 ≫ ·) hY).trans ((ε.naturality f).trans
      (congrArg₂ (· ≫ ·) hX.symm (ChainComplex.single₀_map_f_zero (V := A) f).symm))

instance standardPow_additive [P.Additive] (n : ℕ) : (standardPow P n).Additive := by
  induction n with
  | zero => exact inferInstanceAs (𝟭 A).Additive
  | succ n ih => exact inferInstanceAs (standardPow P n ⋙ P).Additive

instance standardPow_preservesFiniteLimits [PreservesFiniteLimits P] (n : ℕ) :
    PreservesFiniteLimits (standardPow P n) := by
  induction n with
  | zero => exact inferInstanceAs (PreservesFiniteLimits (𝟭 A))
  | succ n ih => exact inferInstanceAs (PreservesFiniteLimits (standardPow P n ⋙ P))

instance standardPow_preservesFiniteColimits [PreservesFiniteColimits P] (n : ℕ) :
    PreservesFiniteColimits (standardPow P n) := by
  induction n with
  | zero => exact inferInstanceAs (PreservesFiniteColimits (𝟭 A))
  | succ n ih => exact inferInstanceAs (PreservesFiniteColimits (standardPow P n ⋙ P))

instance standardResolution_additive [P.Additive] : (standardResolution P ε).Additive where
  map_add {_ _ f g} := by
    ext r
    exact (standardPow P (r + 1)).map_add

/-- The standard resolution of an exact `P` is exact: each degree is an iterate of `P`. -/
instance standardResolution_preservesFiniteLimits [PreservesFiniteLimits P] :
    PreservesFiniteLimits (standardResolution P ε) :=
  ⟨fun J _ _ => HomologicalComplex.preservesLimitsOfShape_of_eval _ fun r =>
    inferInstanceAs (PreservesLimitsOfShape J (standardPow P (r + 1)))⟩

instance standardResolution_preservesFiniteColimits [PreservesFiniteColimits P] :
    PreservesFiniteColimits (standardResolution P ε) :=
  ⟨fun J _ _ => HomologicalComplex.preservesColimitsOfShape_of_eval _ fun r =>
    inferInstanceAs (PreservesColimitsOfShape J (standardPow P (r + 1)))⟩

end Standard

namespace DivisibleSystem

section Standard

variable {A : Type u} [Category.{v} A] [Abelian A] (P : A ⥤ A) (ε : P ⟶ 𝟭 A) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P] {ℓ : ℕ}

/-- The standard resolutions of the members of an `ℓ`-divisible system, as an `ℓ`-divisible
system of chain complexes. -/
abbrev standardResolutionSystem (T : DivisibleSystem A ℓ) :
    DivisibleSystem (ChainComplex A ℕ) ℓ :=
  T.map (standardResolution P ε)

/-- The degree `r` system of the standard resolutions is `P^(r+1)` applied to the system. -/
lemma standardResolutionSystem_degree (T : DivisibleSystem A ℓ) (r : ℕ) :
    (T.standardResolutionSystem P ε).degree r = T.map (standardPow P (r + 1)) :=
  rfl

/-- The augmentation `ε`, as a morphism from the standard resolutions to the system placed in
degree `0`. -/
abbrev standardResolutionSystemAugmentation (T : DivisibleSystem A ℓ) :
    T.standardResolutionSystem P ε ⟶ T.map (ChainComplex.single₀ A) :=
  T.mapNatTrans (standardResolutionAugmentation P ε)

/-- The standard resolutions of the terms of an `ℓ`-divisible system of `ℕ`-graded cochain
complexes, as an `ℓ`-divisible system of double complexes: the `(q, r)` term at level `m` is
`P^(r+1)` applied to the degree `q` term at level `m` (Harris's `K_m^{-(r+1),q,H}`). -/
abbrev standardResolutionDoubleComplexes (K : DivisibleSystem (CochainComplex A ℕ) ℓ) :
    DivisibleSystem (HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ)) ℓ :=
  K.map ((standardResolution P ε).mapHomologicalComplex (ComplexShape.up ℕ))

lemma standardResolutionDoubleComplexes_obj_X_X (K : DivisibleSystem (CochainComplex A ℕ) ℓ)
    (m q r : ℕ) :
    (((K.standardResolutionDoubleComplexes P ε).obj m).X q).X r =
      (standardPow P (r + 1)).obj ((K.obj m).X q) :=
  rfl

/-- The augmentation `ε` in each degree `q`, from the double complexes to the system of cochain
complexes placed in resolution degree `0`. -/
abbrev standardResolutionDoubleComplexesAugmentation
    (K : DivisibleSystem (CochainComplex A ℕ) ℓ) :
    K.standardResolutionDoubleComplexes P ε ⟶
      K.map ((ChainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℕ)) :=
  K.mapNatTrans (NatTrans.mapHomologicalComplex (standardResolutionAugmentation P ε) _)

end Standard

end DivisibleSystem

section Group

variable (k : Type u) [CommRing k] (Γ : Type v) [Group Γ]

/-- Restriction to the trivial subgroup followed by induction, `M ↦ Ind_1^Γ Res_1^Γ M`. Mathlib's
induction from the trivial subgroup is the quotient of `k[Γ] ⊗_k M` by the coinvariant relations
of the trivial group, which are zero, with `Γ` acting on `k[Γ]` only. Up to an isomorphism not
formalized here, this is the functor `ℤ_ℓ[S(ẽ)/H] ⊗_{ℤ_ℓ} (•)` of Harris's (2.4) for `k = ℤ_ℓ`
and `Γ = S(ẽ)/H`, with integral coefficients; nothing here passes to `ℤ/ℓ^m`-coefficients. -/
abbrev indResBot : Rep.{max w u v} k Γ ⥤ Rep.{max w u v} k Γ :=
  Rep.resFunctor (⊥ : Subgroup Γ).subtype ⋙ Rep.indFunctor k (⊥ : Subgroup Γ).subtype

/-- The counit `Ind_1^Γ Res_1^Γ M ⟶ M` of Mathlib's induction–restriction adjunction. -/
abbrev indResBotCounit : indResBot.{w} k Γ ⟶ 𝟭 (Rep.{max w u v} k Γ) :=
  (Rep.indResAdjunction.{max w u v} k (⊥ : Subgroup Γ).subtype).counit

variable [Finite Γ]

/-- Induction from the trivial subgroup of a finite group is additive: it preserves binary
products, being right adjoint to restriction (Mathlib, finite index). -/
instance indFunctor_bot_additive :
    (Rep.indFunctor.{max w u v} k (⊥ : Subgroup Γ).subtype).Additive :=
  Functor.additive_of_preserves_binary_products _

instance indFunctor_bot_preservesFiniteLimits :
    PreservesFiniteLimits (Rep.indFunctor.{max w u v} k (⊥ : Subgroup Γ).subtype) :=
  inferInstance

instance indFunctor_bot_preservesFiniteColimits :
    PreservesFiniteColimits (Rep.indFunctor.{max w u v} k (⊥ : Subgroup Γ).subtype) :=
  inferInstance

end Group

namespace DivisibleSystem

section Group

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ] [Finite Γ] {ℓ : ℕ}

/-- The standard resolutions along `Ind_1^Γ Res_1^Γ` of an `ℓ`-divisible system of
representations of a finite group. -/
abbrev groupStandardResolutionSystem (T : DivisibleSystem (Rep.{max w u v} k Γ) ℓ) :
    DivisibleSystem (ChainComplex (Rep.{max w u v} k Γ) ℕ) ℓ :=
  T.standardResolutionSystem (indResBot.{w} k Γ) (indResBotCounit k Γ)

/-- The standard resolutions along `Ind_1^Γ Res_1^Γ`, in each degree, of an `ℓ`-divisible system
of `ℕ`-graded cochain complexes of representations of a finite group (the double complexes
`K_m^{-•,•,H}` of Harris's (2.5) for `Γ = S(ẽ)/H`). -/
abbrev groupStandardResolutionDoubleComplexes
    (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ) :
    DivisibleSystem
      (HomologicalComplex₂ (Rep.{max w u v} k Γ) (ComplexShape.up ℕ) (ComplexShape.down ℕ)) ℓ :=
  K.standardResolutionDoubleComplexes (indResBot.{w} k Γ) (indResBotCounit k Γ)

end Group

end DivisibleSystem

end Langlands.Cohomology
