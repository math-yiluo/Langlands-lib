import Langlands.Cohomology.DivisibleSystem.StandardResolution
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Exactness of the standard resolution

Harris 1999, §2, p.306, calls the resolution (2.5) of `M_m^{q,H}`, obtained by iterating (2.4),
"the canonical free resolution". This module proves that the standard resolution of the
`StandardResolution` module is a resolution whenever `F ε` has a natural section for a faithful
exact functor `F`, and constructs such a section for `Ind_1^Γ Res_1^Γ` after forgetting the action
of `Γ`.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u'

/-- A short complex `X₁ ⟶ X₂ ⟶ X₃` is exact if there are `h₁ : X₂ ⟶ X₁` and `h₂ : X₃ ⟶ X₂` with
`h₁ ≫ f + g ≫ h₂ = 𝟙 X₂`. -/
lemma shortComplex_exact_of_contraction {C : Type u'} [Category.{v'} C] [Preadditive C]
    (S : ShortComplex C) [S.HasHomology] (h₁ : S.X₂ ⟶ S.X₁) (h₂ : S.X₃ ⟶ S.X₂)
    (w : h₁ ≫ S.f + S.g ≫ h₂ = 𝟙 S.X₂) : S.Exact := by
  have hf : S.f ≫ h₁ ≫ S.f = S.f := by
    rw [eq_sub_of_add_eq w, Preadditive.comp_sub, Category.comp_id, S.zero_assoc, zero_comp,
      sub_zero]
  have hg : S.g ≫ h₂ ≫ S.g = S.g := by
    rw [← Category.assoc, eq_sub_of_add_eq' w, Preadditive.sub_comp, Category.id_comp,
      Category.assoc, S.zero, Limits.comp_zero, sub_zero]
  let H : ShortComplex.Homotopy (𝟙 S) 0 :=
    { h₀ := 𝟙 S.X₁ - S.f ≫ h₁
      h₀_f := by rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hf, sub_self]
      h₁ := h₁
      h₂ := h₂
      h₃ := 𝟙 S.X₃ - h₂ ≫ S.g
      g_h₃ := by rw [Preadditive.comp_sub, Category.comp_id, hg, sub_self]
      comm₁ := by simp
      comm₂ := by simp [← w, add_comm]
      comm₃ := by simp }
  rw [S.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  simpa using H.homologyMap_congr

/-- A short complex in an abelian category is exact if, after a faithful exact functor `F`, there
are `h₁ : F X₂ ⟶ F X₁` and `h₂ : F X₃ ⟶ F X₂` with `h₁ ≫ F f + F g ≫ h₂ = 𝟙 (F X₂)`. The images
`F f`, `F g` may be given through equal morphisms `f'`, `g'`. -/
lemma shortComplex_exact_of_map_contraction {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B] (S : ShortComplex A) (F : A ⥤ B) [F.Additive]
    [F.Faithful] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {f' : F.obj S.X₁ ⟶ F.obj S.X₂} {g' : F.obj S.X₂ ⟶ F.obj S.X₃} (hf : F.map S.f = f')
    (hg : F.map S.g = g') (h₁ : F.obj S.X₂ ⟶ F.obj S.X₁) (h₂ : F.obj S.X₃ ⟶ F.obj S.X₂)
    (w : h₁ ≫ f' + g' ≫ h₂ = 𝟙 (F.obj S.X₂)) : S.Exact := by
  subst hf hg
  exact (S.exact_map_iff_of_faithful F).1 (shortComplex_exact_of_contraction (S.map F) h₁ h₂ w)

section Contraction

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]

/-- A natural section `σ : F ⟶ P ⋙ F` of `F ε`, for a functor `F : A ⥤ B`. Its components at the
iterates of `P` contract the standard resolution of `P` along `ε` after applying `F`. -/
structure StandardContraction (F : A ⥤ B) (P : A ⥤ A) (ε : P ⟶ 𝟭 A) where
  /-- The section, natural in `X`. -/
  σ : F ⟶ P ⋙ F
  /-- `σ` is a section of `F ε`. -/
  σ_comp (X : A) : σ.app X ≫ F.map (ε.app X) = 𝟙 (F.obj X)

namespace StandardContraction

variable {F : A ⥤ B} {P : A ⥤ A} {ε : P ⟶ 𝟭 A} (c : StandardContraction F P ε) [F.Additive]

/-- The component `F (P^n X) ⟶ F (P^(n+1) X)` of `σ` at `P^n X`, typed with the iterates of `P`. -/
def app (n : ℕ) (X : A) : F.obj ((standardPow P n).obj X) ⟶ F.obj ((standardPow P (n + 1)).obj X) :=
  c.σ.app ((standardPow P n).obj X)

/-- The contraction identity `σ ≫ F d_(n+1) = 𝟙 - F d_n ≫ σ` on `F (P^(n+1) X)`, where `d_n` is
the augmented differential `P^(n+1) ⟶ P^n` of the standard resolution (`d_0 = ε`). -/
lemma identity (n : ℕ) (X : A) :
    c.app (n + 1) X ≫ F.map ((standardDifferential P ε (n + 1)).app X) =
      𝟙 _ - F.map ((standardDifferential P ε n).app X) ≫ c.app n X := by
  have h : (standardDifferential P ε (n + 1)).app X =
      (standardCounit P ε n).app X - (standardPowMap P (standardDifferential P ε n)).app X := by
    rw [standardDifferential_succ, NatTrans.app_sub]
  have h₁ : c.app (n + 1) X ≫ F.map ((standardCounit P ε n).app X) = 𝟙 _ :=
    c.σ_comp _
  have h₂ : c.app (n + 1) X ≫ F.map ((standardPowMap P (standardDifferential P ε n)).app X) =
      F.map ((standardDifferential P ε n).app X) ≫ c.app n X :=
    (c.σ.naturality ((standardDifferential P ε n).app X)).symm
  calc c.app (n + 1) X ≫ F.map ((standardDifferential P ε (n + 1)).app X)
      = c.app (n + 1) X ≫ (F.map ((standardCounit P ε n).app X) -
          F.map ((standardPowMap P (standardDifferential P ε n)).app X)) :=
        congrArg (c.app (n + 1) X ≫ ·) ((congrArg F.map h).trans F.map_sub)
    _ = 𝟙 _ - F.map ((standardDifferential P ε n).app X) ≫ c.app n X :=
        (Preadditive.comp_sub _ _ _).trans (congrArg₂ (· - ·) h₁ h₂)

/-- The contraction identity in the form `σ ≫ F d_(n+1) + F d_n ≫ σ = 𝟙`. -/
lemma identity' (n : ℕ) (X : A) :
    c.app (n + 1) X ≫ F.map ((standardDifferential P ε (n + 1)).app X) +
      F.map ((standardDifferential P ε n).app X) ≫ c.app n X = 𝟙 _ := by
  rw [c.identity, sub_add_cancel]

omit [Abelian A] [Abelian B] [F.Additive] in
include c in
/-- `ε : P X ⟶ X` is an epimorphism: `F ε` has the section `σ`. -/
theorem epi_ε [F.Faithful] (X : A) : Epi (ε.app X) := by
  have : Epi (F.map (ε.app X)) := ⟨fun g h e => by
    calc g = (c.σ.app X ≫ F.map (ε.app X)) ≫ g := by rw [c.σ_comp, Category.id_comp]
      _ = c.σ.app X ≫ F.map (ε.app X) ≫ g := Category.assoc _ _ _
      _ = c.σ.app X ≫ F.map (ε.app X) ≫ h := by rw [e]
      _ = (c.σ.app X ≫ F.map (ε.app X)) ≫ h := (Category.assoc _ _ _).symm
      _ = h := by rw [c.σ_comp, Category.id_comp]⟩
  exact F.epi_of_epi_map this

variable [P.PreservesZeroMorphisms] [F.Faithful] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

include c in
/-- The standard resolution is exact in positive degrees. -/
theorem exactAt_succ (X : A) (n : ℕ) : ((standardResolution P ε).obj X).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  exact shortComplex_exact_of_map_contraction _ F
    (f' := F.map ((standardDifferential P ε (n + 1 + 1)).app X))
    (g' := F.map ((standardDifferential P ε (n + 1)).app X))
    (congrArg F.map (standardResolution_obj_d P ε X (n + 1)))
    (congrArg F.map (standardResolution_obj_d P ε X n)) (c.app (n + 1 + 1) X) (c.app (n + 1) X)
    (c.identity' (n + 1) X)

/-- The degree `0` component of the augmentation is `ε`. -/
lemma augmentation_app_f_zero (X : A) :
    ((standardResolutionAugmentation P ε).app X).f 0 = ε.app X :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := (standardResolution P ε).obj X) (X := X)
    (ε.app X) (standardResolution_obj_d_comp P ε X)

include c in
/-- The augmentation of the standard resolution is a quasi-isomorphism. -/
theorem quasiIso_augmentation (X : A) :
    QuasiIso ((standardResolutionAugmentation P ε).app X) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · constructor
      · exact shortComplex_exact_of_map_contraction _ F
          (f' := F.map ((standardDifferential P ε (0 + 1)).app X))
          (g' := F.map ((standardDifferential P ε 0).app X))
          (congrArg F.map (standardResolution_obj_d P ε X 0))
          (congrArg F.map (augmentation_app_f_zero X)) (c.app (0 + 1) X) (c.app 0 X)
          (c.identity' 0 X)
      · have h := c.epi_ε X
        rw [← augmentation_app_f_zero (P := P) (ε := ε) X] at h
        exact h
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact c.exactAt_succ X n

end StandardContraction

end Contraction

namespace DivisibleSystem

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  {F : A ⥤ B} {P : A ⥤ A} {ε : P ⟶ 𝟭 A} [F.Additive] [F.Faithful] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {ℓ : ℕ}

/-- Each level of the augmentation from the standard resolutions of an `ℓ`-divisible system is a
quasi-isomorphism. -/
theorem quasiIso_standardResolutionSystemAugmentation (c : StandardContraction F P ε)
    (T : DivisibleSystem A ℓ) (m : ℕ) :
    QuasiIso ((T.standardResolutionSystemAugmentation P ε).tower.app (op m)) :=
  c.quasiIso_augmentation (T.obj m)

/-- For an `ℓ`-divisible system of cochain complexes, each column `q` of the augmentation from the
double complexes of standard resolutions, at each level `m`, is a quasi-isomorphism. -/
theorem quasiIso_standardResolutionDoubleComplexesAugmentation (c : StandardContraction F P ε)
    (K : DivisibleSystem (CochainComplex A ℕ) ℓ) (m q : ℕ) :
    QuasiIso (((K.standardResolutionDoubleComplexesAugmentation P ε).tower.app (op m)).f q) :=
  c.quasiIso_augmentation ((K.obj m).X q)

end DivisibleSystem

section Group

variable (k : Type u) [CommRing k] (Γ : Type v) [Group Γ]

/-- The section `v ↦ [1 ⊗ v]` of the counit `Ind_1^Γ Res_1^Γ V ⟶ V`, which is `k`-linear but not
`Γ`-equivariant: a natural section after forgetting the action of `Γ`. -/
def indResBotContraction :
    StandardContraction (forget₂ (Rep.{max w u v} k Γ) (ModuleCat.{max w u v} k))
      (indResBot.{w} k Γ) (indResBotCounit.{w} k Γ) where
  σ :=
    { app V := ModuleCat.ofHom
        (Representation.IndV.mk (⊥ : Subgroup Γ).subtype (V.ρ.comp (⊥ : Subgroup Γ).subtype) 1)
      naturality V W f := by
        ext v
        rfl }
  σ_comp V := by
    have h : (indResBotCounit.{w} k Γ).app V =
        ((Rep.indResAdjunction.{max w u v} k (⊥ : Subgroup Γ).subtype).homEquiv _ V).symm
          (𝟙 _) := by
      rw [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]
    have h' := (Rep.indResHomEquiv (⊥ : Subgroup Γ).subtype
      ((Rep.resFunctor (⊥ : Subgroup Γ).subtype).obj V) V).apply_symm_apply (𝟙 _)
    ext v
    rw [h]
    exact congrArg (fun f => f.hom v) h'

end Group

namespace DivisibleSystem

section Group

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ] [Finite Γ] {ℓ : ℕ}

/-- Each level of the augmentation from the standard resolutions along `Ind_1^Γ Res_1^Γ` of an
`ℓ`-divisible system of representations of a finite group is a quasi-isomorphism. -/
theorem quasiIso_groupStandardResolutionSystemAugmentation
    (T : DivisibleSystem (Rep.{max w u v} k Γ) ℓ) (m : ℕ) :
    QuasiIso ((T.standardResolutionSystemAugmentation (indResBot.{w} k Γ)
      (indResBotCounit k Γ)).tower.app (op m)) :=
  quasiIso_standardResolutionSystemAugmentation (indResBotContraction.{w} k Γ) T m

/-- Each column of the augmentation from the double complexes `K_m^{-•,•,H}` of Harris's (2.5)
along `Ind_1^Γ Res_1^Γ`, at each level, is a quasi-isomorphism. -/
theorem quasiIso_groupStandardResolutionDoubleComplexesAugmentation
    (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ) (m q : ℕ) :
    QuasiIso (((K.standardResolutionDoubleComplexesAugmentation (indResBot.{w} k Γ)
      (indResBotCounit k Γ)).tower.app (op m)).f q) :=
  quasiIso_standardResolutionDoubleComplexesAugmentation (indResBotContraction.{w} k Γ) K m q

end Group

end DivisibleSystem

end Langlands.Cohomology
