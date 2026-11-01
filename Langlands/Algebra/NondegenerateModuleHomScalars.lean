import Langlands.Algebra.NondegenerateScalars
import Langlands.Algebra.NonUnitalModuleAdditive
import Langlands.Algebra.CompatibleUnitization

/-!
# Canonical scalars on original Hom spaces

The pointwise scalar module and actual unitized Hom comparison of Renard
(9 July 2026), I.2.1. All scalar modules are named local constructions.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NondegenerateModuleHomScalars

universe uK uA uM uN uP

section General

variable (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP}
  [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup M] [NonUnitalModule A M]
  [AddCommGroup N] [NonUnitalModule A N]
  [AddCommGroup P] [NonUnitalModule A P]

/-- Scalar multiplication on the original Hom carrier, using only target recovery. -/
noncomputable def scalarMul (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N) : NonUnitalModuleHom A M N :=
  letI := NondegenerateScalars.module k hA hN
  letI := NondegenerateScalars.smulCommClass k hA hN
  { toAddMonoidHom := c • f.toAddMonoidHom
    map_smul' a m := by
      change c • f (a • m) = a • (c • f m)
      rw [f.map_smul, smul_comm c a] }

@[simp] theorem scalarMul_apply (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N) (m : M) :
    letI := NondegenerateScalars.module k hA hN
    scalarMul k hA hN c f m = c • f m := rfl

/-- The named scalar module on exactly the published pointwise additive Hom group. -/
noncomputable abbrev homModule (hA : IsIdempotented A) (hN : IsNondegenerate A N) :
    Module k (NonUnitalModuleHom A M N) :=
  letI := NondegenerateScalars.module k hA hN
  { smul := scalarMul k hA hN
    one_smul f := by ext m; exact one_smul k (f m)
    mul_smul c d f := by ext m; exact mul_smul c d (f m)
    smul_zero c := by ext m; exact smul_zero c
    smul_add c f g := by ext m; exact smul_add c (f m) (g m)
    add_smul c d f := by ext m; exact add_smul c d (f m)
    zero_smul f := by ext m; exact zero_smul k (f m) }

@[simp] theorem smul_apply (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N) (m : M) :
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (c • f) m = c • f m := rfl

/-- Scalar multiplication retains the entire pointwise additive map. -/
theorem smul_toAddMonoidHom (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N) :
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (c • f).toAddMonoidHom = c • f.toAddMonoidHom := rfl

theorem smul_function (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N) :
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (c • f : M → N) = fun m => c • f m := rfl

/-- The two source formulas agree by automatic linearity of the original map. -/
theorem smul_apply_eq_source (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N) (m : M) :
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (c • f) m = f (c • m) :=
  (NondegenerateScalars.map_smul k hA hM hN f c m).symm

/-- The actual linear inclusion into scalar-linear maps, using automatic linearity. -/
noncomputable def toLinearMap (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    NonUnitalModuleHom A M N →ₗ[k] (M →ₗ[k] N) :=
  letI := NondegenerateScalars.module k hA hM
  letI := NondegenerateScalars.module k hA hN
  letI := homModule k hA hN (M := M)
  { toFun := NondegenerateScalars.toLinearMap k hA hM hN
    map_add' _ _ := by ext m; rfl
    map_smul' _ _ := by ext m; rfl }

@[simp] theorem toLinearMap_apply (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) (m : M) :
    toLinearMap k hA hM hN f m = f m := rfl

theorem toLinearMap_toAddMonoidHom (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    LinearMap.toAddMonoidHom ∘ toLinearMap k hA hM hN =
      NonUnitalModuleHom.toAddMonoidHom := rfl

theorem toLinearMap_function (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    (fun f : NonUnitalModuleHom A M N => (toLinearMap k hA hM hN f : M → N)) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := rfl

theorem toLinearMap_injective (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    Function.Injective (toLinearMap k hA hM hN) := by
  intro f g h
  exact NonUnitalModuleHom.ext (fun m => congrArg (fun q => q m) h)

/-- The original Hom is exactly the existing actual submodule of intertwiners. -/
noncomputable def intertwinersEquiv (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    NonUnitalModuleHom A M N ≃ₗ[k]
      CompatibleUnitization.intertwiners (NondegenerateScalars.toLinearEndHom k hA hM)
        (NondegenerateScalars.toLinearEndHom k hA hN) :=
  letI := NondegenerateScalars.module k hA hM
  letI := NondegenerateScalars.module k hA hN
  letI := homModule k hA hN (M := M)
  { toFun f := ⟨toLinearMap k hA hM hN f, f.map_smul⟩
    invFun f := { toAddMonoidHom := f.val.toAddMonoidHom, map_smul' := f.property }
    left_inv f := by ext m; rfl
    right_inv f := by apply Subtype.ext; ext m; rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

@[simp] theorem intertwinersEquiv_apply (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) :
    (intertwinersEquiv k hA hM hN f).val = toLinearMap k hA hM hN f := rfl

theorem intertwinersEquiv_toAddMonoidHom (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    (fun f => (intertwinersEquiv k hA hM hN f).val.toAddMonoidHom) =
      NonUnitalModuleHom.toAddMonoidHom := rfl

theorem intertwinersEquiv_symm_toAddMonoidHom (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    (fun f => ((intertwinersEquiv k hA hM hN).symm f).toAddMonoidHom) =
      fun f => f.val.toAddMonoidHom := rfl

theorem intertwinersEquiv_function (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    (fun f : NonUnitalModuleHom A M N => (intertwinersEquiv k hA hM hN f).val.toFun) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := rfl

@[simp] theorem intertwinersEquiv_symm_apply (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : letI := NondegenerateScalars.module k hA hM
      letI := NondegenerateScalars.module k hA hN
      CompatibleUnitization.intertwiners (NondegenerateScalars.toLinearEndHom k hA hM)
        (NondegenerateScalars.toLinearEndHom k hA hN)) (m : M) :
    (intertwinersEquiv k hA hM hN).symm f m = f.val m := rfl

theorem intertwinersEquiv_symm_function (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    (fun f => ((intertwinersEquiv k hA hM hN).symm f : M → N)) =
      fun f : CompatibleUnitization.intertwiners
          (NondegenerateScalars.toLinearEndHom k hA hM)
          (NondegenerateScalars.toLinearEndHom k hA hN) => (f.val : M → N) := rfl

theorem intertwinersEquiv_left_inv (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) :
    (intertwinersEquiv k hA hM hN).symm (intertwinersEquiv k hA hM hN f) = f :=
  (intertwinersEquiv k hA hM hN).symm_apply_apply f

theorem intertwinersEquiv_right_inv (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : letI := NondegenerateScalars.module k hA hM
      letI := NondegenerateScalars.module k hA hN
      CompatibleUnitization.intertwiners (NondegenerateScalars.toLinearEndHom k hA hM)
        (NondegenerateScalars.toLinearEndHom k hA hN)) :
    intertwinersEquiv k hA hM hN ((intertwinersEquiv k hA hM hN).symm f) = f :=
  (intertwinersEquiv k hA hM hN).apply_symm_apply f

/-- The linear inclusion retains the original identity. -/
theorem toLinearMap_id (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := NondegenerateScalars.module k hA hM
    toLinearMap k hA hM hM (NonUnitalModuleHom.id A M) = LinearMap.id := rfl

/-- The equivalence retains the original identity map. -/
theorem intertwinersEquiv_id (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := NondegenerateScalars.module k hA hM
    (intertwinersEquiv k hA hM hM (NonUnitalModuleHom.id A M)).val = LinearMap.id := rfl

theorem toLinearMap_comp (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := NondegenerateScalars.module k hA hP
    toLinearMap k hA hM hP (g.comp f) =
      (toLinearMap k hA hN hP g).comp (toLinearMap k hA hM hN f) := rfl

theorem intertwinersEquiv_comp (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := NondegenerateScalars.module k hA hP
    (intertwinersEquiv k hA hM hP (g.comp f)).val =
      (intertwinersEquiv k hA hN hP g).val.comp
        (intertwinersEquiv k hA hM hN f).val := rfl

/-- Postcomposition preserves the pointwise scalar multiplication. -/
theorem comp_smul (hA : IsIdempotented A)
    (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (c : k) (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    letI := homModule k hA hN (M := M)
    letI := homModule k hA hP (M := M)
    g.comp (c • f) = c • (g.comp f) := by
  apply NonUnitalModuleHom.ext
  intro m
  exact NondegenerateScalars.map_smul k hA hN hP g c (f m)

/-- Precomposition preserves the pointwise scalar multiplication. -/
theorem smul_comp (hA : IsIdempotented A) (hP : IsNondegenerate A P)
    (c : k) (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    letI := homModule k hA hP (M := N)
    letI := homModule k hA hP (M := M)
    (c • g).comp f = c • (g.comp f) := rfl

/-- The published unitized module of the actual recovered action. -/
noncomputable abbrev unitizedModule (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    Module (Unitization k A) M :=
  letI := NondegenerateScalars.module k hA hM
  CompatibleUnitization.module (NondegenerateScalars.toLinearEndHom k hA hM)

theorem unitized_smul (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x : Unitization k A) (m : M) :
    letI := NondegenerateScalars.module k hA hM
    (letI := unitizedModule k hA hM; x • m) = x.fst • m + x.snd • m := rfl

theorem unitized_smul_function (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := NondegenerateScalars.module k hA hM
    (fun (x : Unitization k A) (m : M) => (letI := unitizedModule k hA hM; x • m)) =
      fun x m => x.fst • m + x.snd • m := rfl

theorem unitized_inr_smul (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (a : A) (m : M) :
    (letI := unitizedModule k hA hM; (a : Unitization k A) • m) = a • m :=
  letI := NondegenerateScalars.module k hA hM
  CompatibleUnitization.inr_smul (NondegenerateScalars.toLinearEndHom k hA hM) a m

theorem unitized_inl_smul (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (c : k) (m : M) :
    letI := NondegenerateScalars.module k hA hM
    (letI := unitizedModule k hA hM; (Unitization.inl c : Unitization k A) • m) = c • m :=
  letI := NondegenerateScalars.module k hA hM
  CompatibleUnitization.inl_smul (NondegenerateScalars.toLinearEndHom k hA hM) c m

/-- Named commuting adapter for the scalar module of unitized linear maps. -/
theorem unitizedSmulCommClass (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := NondegenerateScalars.module k hA hM
    letI := unitizedModule k hA hM
    SMulCommClass (Unitization k A) k M :=
  letI := NondegenerateScalars.module k hA hM
  CompatibleUnitization.smulCommClass' (NondegenerateScalars.toLinearEndHom k hA hM)

/-- The Hom equality of I.2.1.2 as an actual linear equivalence of existing carriers. -/
noncomputable def unitizedHomEquiv (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedSmulCommClass k hA hN
    NonUnitalModuleHom A M N ≃ₗ[k] (M →ₗ[Unitization k A] N) :=
  letI := NondegenerateScalars.module k hA hM
  letI := NondegenerateScalars.module k hA hN
  letI := homModule k hA hN (M := M)
  letI := unitizedModule k hA hM
  letI := unitizedModule k hA hN
  letI := unitizedSmulCommClass k hA hN
  (intertwinersEquiv k hA hM hN).trans
    (CompatibleUnitization.linearMapEquiv (NondegenerateScalars.toLinearEndHom k hA hM)
      (NondegenerateScalars.toLinearEndHom k hA hN)).symm

@[simp] theorem unitizedHomEquiv_apply (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) (m : M) :
    unitizedHomEquiv k hA hM hN f m = f m := rfl

theorem unitizedHomEquiv_toAddMonoidHom (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    (fun f => (unitizedHomEquiv k hA hM hN f).toAddMonoidHom) =
      NonUnitalModuleHom.toAddMonoidHom := rfl

theorem unitizedHomEquiv_function (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    (fun f : NonUnitalModuleHom A M N => (unitizedHomEquiv k hA hM hN f : M → N)) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := rfl

theorem unitizedHomEquiv_symm_toAddMonoidHom (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    (fun f => ((unitizedHomEquiv k hA hM hN).symm f).toAddMonoidHom) =
      fun f => f.toAddMonoidHom := rfl

theorem unitizedHomEquiv_symm_function (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    (fun f => ((unitizedHomEquiv k hA hM hN).symm f : M → N)) =
      fun f : M →ₗ[Unitization k A] N => (f : M → N) := rfl

@[simp] theorem unitizedHomEquiv_symm_apply (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : letI := unitizedModule k hA hM
      letI := unitizedModule k hA hN
      M →ₗ[Unitization k A] N) (m : M) :
    (unitizedHomEquiv k hA hM hN).symm f m = f m := rfl

theorem unitizedHomEquiv_left_inv (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) :
    (unitizedHomEquiv k hA hM hN).symm (unitizedHomEquiv k hA hM hN f) = f :=
  (unitizedHomEquiv k hA hM hN).symm_apply_apply f

theorem unitizedHomEquiv_right_inv (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : letI := unitizedModule k hA hM
      letI := unitizedModule k hA hN
      M →ₗ[Unitization k A] N) :
    unitizedHomEquiv k hA hM hN ((unitizedHomEquiv k hA hM hN).symm f) = f :=
  (unitizedHomEquiv k hA hM hN).apply_symm_apply f

theorem unitizedHomEquiv_id (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := unitizedModule k hA hM
    unitizedHomEquiv k hA hM hM (NonUnitalModuleHom.id A M) = LinearMap.id := rfl

theorem unitizedHomEquiv_comp (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedModule k hA hP
    unitizedHomEquiv k hA hM hP (g.comp f) =
      (unitizedHomEquiv k hA hN hP g).comp (unitizedHomEquiv k hA hM hN f) := rfl

theorem unitizedHomEquiv_symm_id (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    (unitizedHomEquiv k hA hM hM).symm
      (letI := unitizedModule k hA hM; (LinearMap.id : M →ₗ[Unitization k A] M)) =
      NonUnitalModuleHom.id A M := rfl

theorem unitizedHomEquiv_symm_comp (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P) :
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedModule k hA hP
    ∀ (g : N →ₗ[Unitization k A] P) (f : M →ₗ[Unitization k A] N),
      (unitizedHomEquiv k hA hM hP).symm (g.comp f) =
        ((unitizedHomEquiv k hA hN hP).symm g).comp
          ((unitizedHomEquiv k hA hM hN).symm f) := by
  intro g f
  rfl

end General

section Complex

variable {A : Type uA} {M : Type uM} {N : Type uN}
  [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [AddCommGroup M] [NonUnitalModule A M]
  [AddCommGroup N] [NonUnitalModule A N]

/-- The source complex vector space on the original additive Hom group. -/
noncomputable abbrev complexHomModule (hA : IsIdempotented A) (hN : IsNondegenerate A N) :
    Module ℂ (NonUnitalModuleHom A M N) := homModule ℂ hA hN

/-- The source Hom equality with the unitized algebra, retaining arbitrary dimensions. -/
noncomputable abbrev complexUnitizedHomEquiv (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA hN
    letI := complexHomModule hA hN (M := M)
    letI := unitizedModule ℂ hA hM
    letI := unitizedModule ℂ hA hN
    letI := unitizedSmulCommClass ℂ hA hN
    NonUnitalModuleHom A M N ≃ₗ[ℂ] (M →ₗ[Unitization ℂ A] N) :=
  unitizedHomEquiv ℂ hA hM hN

end Complex

/-! Complete unapplied interfaces and independent universe specializations. -/

noncomputable section

section ArbitraryUniverses

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (_hA : IsIdempotented A) (_hN : IsNondegenerate A N),
    k → NonUnitalModuleHom A M N → NonUnitalModuleHom A M N := @scalarMul

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (_hA : IsIdempotented A) (_hN : IsNondegenerate A N),
    Module k (NonUnitalModuleHom A M N) := @homModule

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N),
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (c • f).toAddMonoidHom = c • f.toAddMonoidHom := @smul_toAddMonoidHom

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N),
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (c • f : M → N) = fun m => c • f m := @smul_function

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    NonUnitalModuleHom A M N →ₗ[k] (M →ₗ[k] N) := @toLinearMap

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    LinearMap.toAddMonoidHom ∘ toLinearMap k hA hM hN =
      NonUnitalModuleHom.toAddMonoidHom := @toLinearMap_toAddMonoidHom

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f : NonUnitalModuleHom A M N => (toLinearMap k hA hM hN f : M → N)) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := @toLinearMap_function

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    NonUnitalModuleHom A M N ≃ₗ[k] CompatibleUnitization.intertwiners (NondegenerateScalars.toLinearEndHom k hA hM)
        (NondegenerateScalars.toLinearEndHom k hA hN) := @intertwinersEquiv

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => (intertwinersEquiv k hA hM hN f).val.toAddMonoidHom) =
      NonUnitalModuleHom.toAddMonoidHom := @intertwinersEquiv_toAddMonoidHom

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => ((intertwinersEquiv k hA hM hN).symm f).toAddMonoidHom) =
      fun f => f.val.toAddMonoidHom := @intertwinersEquiv_symm_toAddMonoidHom

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (_hA : IsIdempotented A) (_hM : IsNondegenerate A M),
    Module (Unitization k A) M := @unitizedModule

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M),
    letI := NondegenerateScalars.module k hA hM
    (fun (x : Unitization k A) (m : M) => (letI := unitizedModule k hA hM; x • m)) =
      fun x m => x.fst • m + x.snd • m := @unitized_smul_function

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M),
    letI := NondegenerateScalars.module k hA hM
    letI := unitizedModule k hA hM
    SMulCommClass (Unitization k A) k M := @unitizedSmulCommClass

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedSmulCommClass k hA hN
    NonUnitalModuleHom A M N ≃ₗ[k] (M →ₗ[Unitization k A] N) := @unitizedHomEquiv

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => (unitizedHomEquiv k hA hM hN f).toAddMonoidHom) =
      NonUnitalModuleHom.toAddMonoidHom := @unitizedHomEquiv_toAddMonoidHom

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => ((unitizedHomEquiv k hA hM hN).symm f).toAddMonoidHom) =
      fun f => f.toAddMonoidHom := @unitizedHomEquiv_symm_toAddMonoidHom

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f : NonUnitalModuleHom A M N => (unitizedHomEquiv k hA hM hN f : M → N)) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := @unitizedHomEquiv_function

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    (fun f => ((unitizedHomEquiv k hA hM hN).symm f : M → N)) =
      fun f : M →ₗ[Unitization k A] N => (f : M → N) := @unitizedHomEquiv_symm_function

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (fun f : NonUnitalModuleHom A M N => (intertwinersEquiv k hA hM hN f).val.toFun) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := @intertwinersEquiv_function

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (fun f => ((intertwinersEquiv k hA hM hN).symm f : M → N)) =
      fun f : CompatibleUnitization.intertwiners (NondegenerateScalars.toLinearEndHom k hA hM)
        (NondegenerateScalars.toLinearEndHom k hA hN) => (f.val : M → N) := @intertwinersEquiv_symm_function

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    [AddCommGroup P] [NonUnitalModule A P]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N),
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedModule k hA hP
    unitizedHomEquiv k hA hM hP (g.comp f) =
      (unitizedHomEquiv k hA hN hP g).comp (unitizedHomEquiv k hA hM hN f) := @unitizedHomEquiv_comp

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    [AddCommGroup P] [NonUnitalModule A P]
    (hA : IsIdempotented A) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (c : k) (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N),
    letI := homModule k hA hN (M := M)
    letI := homModule k hA hP (M := M)
    g.comp (c • f) = c • (g.comp f) := @comp_smul

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    [AddCommGroup P] [NonUnitalModule A P]
    (hA : IsIdempotented A) (hP : IsNondegenerate A P)
    (c : k) (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N),
    letI := homModule k hA hP (M := N)
    letI := homModule k hA hP (M := M)
    (c • g).comp f = c • (g.comp f) := @smul_comp

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N) (m : M),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (c • f) m = f (c • m) := @smul_apply_eq_source

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    Function.Injective (toLinearMap k hA hM hN) := @toLinearMap_injective

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (a : A) (m : M),
    (letI := unitizedModule k hA hM; (a : Unitization k A) • m) = a • m :=
  @unitized_inr_smul

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (c : k) (m : M),
    letI := NondegenerateScalars.module k hA hM
    (letI := unitizedModule k hA hM; (Unitization.inl c : Unitization k A) • m) = c • m :=
  @unitized_inl_smul

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    [AddCommGroup P] [NonUnitalModule A P]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (hP : IsNondegenerate A P)
    (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := NondegenerateScalars.module k hA hP
    (intertwinersEquiv k hA hM hP (g.comp f)).val =
      (intertwinersEquiv k hA hN hP g).val.comp
        (intertwinersEquiv k hA hM hN f).val := @intertwinersEquiv_comp

example : ∀ (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    [AddCommGroup P] [NonUnitalModule A P]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (hP : IsNondegenerate A P),
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedModule k hA hP
    ∀ (g : N →ₗ[Unitization k A] P) (f : M →ₗ[Unitization k A] N),
      (unitizedHomEquiv k hA hM hP).symm (g.comp f) =
        ((unitizedHomEquiv k hA hN hP).symm g).comp
          ((unitizedHomEquiv k hA hM hN).symm f) := @unitizedHomEquiv_symm_comp

end ArbitraryUniverses

section ZeroOneZeroOne

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (_hA : IsIdempotented A) (_hN : IsNondegenerate A N),
    k → NonUnitalModuleHom A M N → NonUnitalModuleHom A M N := @scalarMul

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (_hA : IsIdempotented A) (_hN : IsNondegenerate A N),
    Module k (NonUnitalModuleHom A M N) := @homModule

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N),
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (c • f).toAddMonoidHom = c • f.toAddMonoidHom := @smul_toAddMonoidHom

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N),
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (c • f : M → N) = fun m => c • f m := @smul_function

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    NonUnitalModuleHom A M N →ₗ[k] (M →ₗ[k] N) := @toLinearMap

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    LinearMap.toAddMonoidHom ∘ toLinearMap k hA hM hN =
      NonUnitalModuleHom.toAddMonoidHom := @toLinearMap_toAddMonoidHom

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f : NonUnitalModuleHom A M N => (toLinearMap k hA hM hN f : M → N)) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := @toLinearMap_function

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    NonUnitalModuleHom A M N ≃ₗ[k] CompatibleUnitization.intertwiners (NondegenerateScalars.toLinearEndHom k hA hM)
        (NondegenerateScalars.toLinearEndHom k hA hN) := @intertwinersEquiv

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => (intertwinersEquiv k hA hM hN f).val.toAddMonoidHom) =
      NonUnitalModuleHom.toAddMonoidHom := @intertwinersEquiv_toAddMonoidHom

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => ((intertwinersEquiv k hA hM hN).symm f).toAddMonoidHom) =
      fun f => f.val.toAddMonoidHom := @intertwinersEquiv_symm_toAddMonoidHom

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (_hA : IsIdempotented A) (_hM : IsNondegenerate A M),
    Module (Unitization k A) M := @unitizedModule

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M),
    letI := NondegenerateScalars.module k hA hM
    (fun (x : Unitization k A) (m : M) => (letI := unitizedModule k hA hM; x • m)) =
      fun x m => x.fst • m + x.snd • m := @unitized_smul_function

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M),
    letI := NondegenerateScalars.module k hA hM
    letI := unitizedModule k hA hM
    SMulCommClass (Unitization k A) k M := @unitizedSmulCommClass

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedSmulCommClass k hA hN
    NonUnitalModuleHom A M N ≃ₗ[k] (M →ₗ[Unitization k A] N) := @unitizedHomEquiv

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => (unitizedHomEquiv k hA hM hN f).toAddMonoidHom) =
      NonUnitalModuleHom.toAddMonoidHom := @unitizedHomEquiv_toAddMonoidHom

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => ((unitizedHomEquiv k hA hM hN).symm f).toAddMonoidHom) =
      fun f => f.toAddMonoidHom := @unitizedHomEquiv_symm_toAddMonoidHom

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f : NonUnitalModuleHom A M N => (unitizedHomEquiv k hA hM hN f : M → N)) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := @unitizedHomEquiv_function

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    (fun f => ((unitizedHomEquiv k hA hM hN).symm f : M → N)) =
      fun f : M →ₗ[Unitization k A] N => (f : M → N) := @unitizedHomEquiv_symm_function

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (fun f : NonUnitalModuleHom A M N => (intertwinersEquiv k hA hM hN f).val.toFun) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := @intertwinersEquiv_function

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (fun f => ((intertwinersEquiv k hA hM hN).symm f : M → N)) =
      fun f : CompatibleUnitization.intertwiners (NondegenerateScalars.toLinearEndHom k hA hM)
        (NondegenerateScalars.toLinearEndHom k hA hN) => (f.val : M → N) := @intertwinersEquiv_symm_function

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1} {P : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    [AddCommGroup P] [NonUnitalModule A P]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N),
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedModule k hA hP
    unitizedHomEquiv k hA hM hP (g.comp f) =
      (unitizedHomEquiv k hA hN hP g).comp (unitizedHomEquiv k hA hM hN f) := @unitizedHomEquiv_comp

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1} {P : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    [AddCommGroup P] [NonUnitalModule A P]
    (hA : IsIdempotented A) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (c : k) (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N),
    letI := homModule k hA hN (M := M)
    letI := homModule k hA hP (M := M)
    g.comp (c • f) = c • (g.comp f) := @comp_smul

example : ∀ (k : Type 0) {A : Type 1} {M : Type 0} {N : Type 1} {P : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    [AddCommGroup P] [NonUnitalModule A P]
    (hA : IsIdempotented A) (hP : IsNondegenerate A P)
    (c : k) (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N),
    letI := homModule k hA hP (M := N)
    letI := homModule k hA hP (M := M)
    (c • g).comp f = c • (g.comp f) := @smul_comp

end ZeroOneZeroOne

section OneZeroOneZero

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (_hA : IsIdempotented A) (_hN : IsNondegenerate A N),
    k → NonUnitalModuleHom A M N → NonUnitalModuleHom A M N := @scalarMul

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (_hA : IsIdempotented A) (_hN : IsNondegenerate A N),
    Module k (NonUnitalModuleHom A M N) := @homModule

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N),
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (c • f).toAddMonoidHom = c • f.toAddMonoidHom := @smul_toAddMonoidHom

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N),
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (c • f : M → N) = fun m => c • f m := @smul_function

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    NonUnitalModuleHom A M N →ₗ[k] (M →ₗ[k] N) := @toLinearMap

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    LinearMap.toAddMonoidHom ∘ toLinearMap k hA hM hN =
      NonUnitalModuleHom.toAddMonoidHom := @toLinearMap_toAddMonoidHom

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f : NonUnitalModuleHom A M N => (toLinearMap k hA hM hN f : M → N)) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := @toLinearMap_function

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    NonUnitalModuleHom A M N ≃ₗ[k] CompatibleUnitization.intertwiners (NondegenerateScalars.toLinearEndHom k hA hM)
        (NondegenerateScalars.toLinearEndHom k hA hN) := @intertwinersEquiv

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => (intertwinersEquiv k hA hM hN f).val.toAddMonoidHom) =
      NonUnitalModuleHom.toAddMonoidHom := @intertwinersEquiv_toAddMonoidHom

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => ((intertwinersEquiv k hA hM hN).symm f).toAddMonoidHom) =
      fun f => f.val.toAddMonoidHom := @intertwinersEquiv_symm_toAddMonoidHom

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (_hA : IsIdempotented A) (_hM : IsNondegenerate A M),
    Module (Unitization k A) M := @unitizedModule

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M),
    letI := NondegenerateScalars.module k hA hM
    (fun (x : Unitization k A) (m : M) => (letI := unitizedModule k hA hM; x • m)) =
      fun x m => x.fst • m + x.snd • m := @unitized_smul_function

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M),
    letI := NondegenerateScalars.module k hA hM
    letI := unitizedModule k hA hM
    SMulCommClass (Unitization k A) k M := @unitizedSmulCommClass

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedSmulCommClass k hA hN
    NonUnitalModuleHom A M N ≃ₗ[k] (M →ₗ[Unitization k A] N) := @unitizedHomEquiv

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => (unitizedHomEquiv k hA hM hN f).toAddMonoidHom) =
      NonUnitalModuleHom.toAddMonoidHom := @unitizedHomEquiv_toAddMonoidHom

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f => ((unitizedHomEquiv k hA hM hN).symm f).toAddMonoidHom) =
      fun f => f.toAddMonoidHom := @unitizedHomEquiv_symm_toAddMonoidHom

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    (fun f : NonUnitalModuleHom A M N => (unitizedHomEquiv k hA hM hN f : M → N)) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := @unitizedHomEquiv_function

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    (fun f => ((unitizedHomEquiv k hA hM hN).symm f : M → N)) =
      fun f : M →ₗ[Unitization k A] N => (f : M → N) := @unitizedHomEquiv_symm_function

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (fun f : NonUnitalModuleHom A M N => (intertwinersEquiv k hA hM hN f).val.toFun) =
      fun f : NonUnitalModuleHom A M N => (f : M → N) := @intertwinersEquiv_function

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    (fun f => ((intertwinersEquiv k hA hM hN).symm f : M → N)) =
      fun f : CompatibleUnitization.intertwiners (NondegenerateScalars.toLinearEndHom k hA hM)
        (NondegenerateScalars.toLinearEndHom k hA hN) => (f.val : M → N) := @intertwinersEquiv_symm_function

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0} {P : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    [AddCommGroup P] [NonUnitalModule A P]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N),
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedModule k hA hP
    unitizedHomEquiv k hA hM hP (g.comp f) =
      (unitizedHomEquiv k hA hN hP g).comp (unitizedHomEquiv k hA hM hN f) := @unitizedHomEquiv_comp

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0} {P : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    [AddCommGroup P] [NonUnitalModule A P]
    (hA : IsIdempotented A) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (c : k) (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N),
    letI := homModule k hA hN (M := M)
    letI := homModule k hA hP (M := M)
    g.comp (c • f) = c • (g.comp f) := @comp_smul

example : ∀ (k : Type 1) {A : Type 0} {M : Type 1} {N : Type 0} {P : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    [AddCommGroup N] [NonUnitalModule A N]
    [AddCommGroup P] [NonUnitalModule A P]
    (hA : IsIdempotented A) (hP : IsNondegenerate A P)
    (c : k) (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N),
    letI := homModule k hA hP (M := N)
    letI := homModule k hA hP (M := M)
    (c • g).comp f = c • (g.comp f) := @smul_comp

end OneZeroOneZero

/-! Original carrier structures remain selectable when competing ones coexist. -/
section CompetingCarrierStructures

set_option linter.overlappingInstances false

variable {k : Type uK} {A : Type uA} {M : Type uM} {N : Type uN}
  [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [originalMGroup : AddCommGroup M] [originalMAction : NonUnitalModule A M]
  [originalNGroup : AddCommGroup N] [originalNAction : NonUnitalModule A N]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
  [competingMGroup : AddCommGroup M] [competingNGroup : AddCommGroup N]

example :
    letI := originalMGroup
    letI := originalNGroup
    Module k (NonUnitalModuleHom A M N) :=
  @homModule k A M N _ _ _ _ _ originalMGroup originalMAction originalNGroup originalNAction hA hN

example :
    letI := originalMGroup
    letI := originalNGroup
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    NonUnitalModuleHom A M N →ₗ[k] (M →ₗ[k] N) :=
  @toLinearMap k A M N _ _ _ _ _ originalMGroup originalMAction originalNGroup originalNAction
    hA hM hN

example :
    letI := originalMGroup
    letI := originalNGroup
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedSmulCommClass k hA hN
    NonUnitalModuleHom A M N ≃ₗ[k] (M →ₗ[Unitization k A] N) :=
  @unitizedHomEquiv k A M N _ _ _ _ _ originalMGroup originalMAction originalNGroup originalNAction
    hA hM hN

end CompetingCarrierStructures

section CompetingActions

set_option linter.overlappingInstances false

variable {k : Type uK} {A : Type uA} {M : Type uM} {N : Type uN}
  [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup M] [originalMAction : NonUnitalModule A M]
  [AddCommGroup N] [originalNAction : NonUnitalModule A N]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
  [competingMAction : NonUnitalModule A M] [competingNAction : NonUnitalModule A N]

example :
    letI := originalMAction
    letI := originalNAction
    Module k (NonUnitalModuleHom A M N) :=
  @homModule k A M N _ _ _ _ _ _ originalMAction _ originalNAction hA hN

example :
    letI := originalMAction
    letI := originalNAction
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedSmulCommClass k hA hN
    NonUnitalModuleHom A M N ≃ₗ[k] (M →ₗ[Unitization k A] N) :=
  @unitizedHomEquiv k A M N _ _ _ _ _ _ originalMAction _ originalNAction hA hM hN

end CompetingActions

section CompetingScalarStructures

variable {k : Type uK} {A : Type uA} {M : Type uM} {N : Type uN}
  [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup M] [NonUnitalModule A M] [AddCommGroup N] [NonUnitalModule A N]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
  [competingMScalar : Module k M] [competingNScalar : Module k N]
  [competingHomScalar : Module k (NonUnitalModuleHom A M N)]
  [competingUnitizedM : Module (Unitization k A) M]
  [competingUnitizedN : Module (Unitization k A) N]

example :
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    NonUnitalModuleHom A M N →ₗ[k] (M →ₗ[k] N) := @toLinearMap k A M N _ _ _ _ _ _ _ _ _ hA hM hN

example :
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    NonUnitalModuleHom A M N ≃ₗ[k]
      CompatibleUnitization.intertwiners (NondegenerateScalars.toLinearEndHom k hA hM)
        (NondegenerateScalars.toLinearEndHom k hA hN) :=
  @intertwinersEquiv k A M N _ _ _ _ _ _ _ _ _ hA hM hN

example :
    letI := NondegenerateScalars.module k hA hM
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    letI := unitizedModule k hA hM
    letI := unitizedModule k hA hN
    letI := unitizedSmulCommClass k hA hN
    NonUnitalModuleHom A M N ≃ₗ[k] (M →ₗ[Unitization k A] N) :=
  @unitizedHomEquiv k A M N _ _ _ _ _ _ _ _ _ hA hM hN

example :
    letI := NondegenerateScalars.module k hA hN
    letI := homModule k hA hN (M := M)
    ∀ (c : k) (f : NonUnitalModuleHom A M N), (c • f : M → N) = fun m => c • f m :=
  @smul_function k A M N _ _ _ _ _ _ _ _ _ hA hN

example :
    letI := NondegenerateScalars.module k hA hM
    ∀ (x : Unitization k A) (m : M),
      (letI := unitizedModule k hA hM; x • m) = x.fst • m + x.snd • m :=
  @unitized_smul k A M _ _ _ _ _ _ _ hA hM

end CompetingScalarStructures

section CompetingAmbientRing

set_option linter.overlappingInstances false

variable (k : Type uK) (A : Type uA) [CommRing k]
  [originalAmbient : NonUnitalRing A] [competingAmbient : NonUnitalRing A]

example :
    letI := originalAmbient
    ∀ {M : Type uM} {N : Type uN} [Module k A]
      [IsScalarTower k A A] [SMulCommClass k A A]
      [AddCommGroup M] [NonUnitalModule A M] [AddCommGroup N] [NonUnitalModule A N]
      (_hA : IsIdempotented A) (_hN : IsNondegenerate A N),
      Module k (NonUnitalModuleHom A M N) :=
  fun {M} {N} => @homModule k A M N _ originalAmbient

example :
    letI := originalAmbient
    ∀ {M : Type uM} {N : Type uN} [Module k A]
      [IsScalarTower k A A] [SMulCommClass k A A]
      [AddCommGroup M] [NonUnitalModule A M] [AddCommGroup N] [NonUnitalModule A N]
      (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
      letI := NondegenerateScalars.module k hA hM
      letI := NondegenerateScalars.module k hA hN
      letI := homModule k hA hN (M := M)
      letI := unitizedModule k hA hM
      letI := unitizedModule k hA hN
      letI := unitizedSmulCommClass k hA hN
      NonUnitalModuleHom A M N ≃ₗ[k] (M →ₗ[Unitization k A] N) :=
  fun {M} {N} => @unitizedHomEquiv k A M N _ originalAmbient

end CompetingAmbientRing

section ZeroCases

variable {k : Type uK} {A : Type uA} {M : Type uM} {N : Type uN}
  [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup M] [NonUnitalModule A M] [AddCommGroup N] [NonUnitalModule A N]

example [Subsingleton N] : Subsingleton (NonUnitalModuleHom A M N) :=
  ⟨fun _f _g => NonUnitalModuleHom.ext (fun _m => Subsingleton.elim _ _)⟩

example [Subsingleton N] (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (c : k) (f : NonUnitalModuleHom A M N) : scalarMul k hA hN c f = 0 := by
  apply NonUnitalModuleHom.ext
  intro m
  exact Subsingleton.elim _ _

example [Subsingleton k] (hA : IsIdempotented A) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) : f = 0 := by
  let _ := homModule k hA hN (M := M)
  calc
    f = (1 : k) • f := (one_smul k f).symm
    _ = (0 : k) • f := congrArg (fun c : k => c • f) (Subsingleton.elim _ _)
    _ = 0 := zero_smul k f

example [Subsingleton A] (hM : IsNondegenerate A M) (m : M) : m = 0 := by
  obtain ⟨e, he⟩ := hM m
  exact he.symm.trans ((congrArg (fun a : A => a • m)
    (Subsingleton.elim (e : A) 0)).trans (NonUnitalModule.zero_smul m))

example [Subsingleton A] (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (hN : IsNondegenerate A N) (f : NonUnitalModuleHom A M N) (m : M) :
    unitizedHomEquiv k hA hM hN f m = 0 := by
  obtain ⟨e, he⟩ := hN (f m)
  exact he.symm.trans ((congrArg (fun a : A => a • f m)
    (Subsingleton.elim (e : A) 0)).trans (NonUnitalModule.zero_smul (f m)))

example [Subsingleton M] (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (hN : IsNondegenerate A N) (f : NonUnitalModuleHom A M N) :
    unitizedHomEquiv k hA hM hN f = 0 := by
  let _ := unitizedModule k hA hM
  let _ := unitizedModule k hA hN
  apply LinearMap.ext
  intro m
  change f m = 0
  rw [Subsingleton.elim m 0, f.map_zero]

end ZeroCases

section FullComplexInterfaces

example : ∀ {A : Type uA} {M : Type uM} {N : Type uN}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup M] [NonUnitalModule A M] [AddCommGroup N] [NonUnitalModule A N]
    (_hA : IsIdempotented A) (_hN : IsNondegenerate A N),
    Module ℂ (NonUnitalModuleHom A M N) := @complexHomModule

example : ∀ {A : Type uA} {M : Type uM} {N : Type uN}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup M] [NonUnitalModule A M] [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N),
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA hN
    letI := complexHomModule hA hN (M := M)
    letI := unitizedModule ℂ hA hM
    letI := unitizedModule ℂ hA hN
    letI := unitizedSmulCommClass ℂ hA hN
    NonUnitalModuleHom A M N ≃ₗ[ℂ] (M →ₗ[Unitization ℂ A] N) := @complexUnitizedHomEquiv

end FullComplexInterfaces

end

end Langlands.Algebra.NondegenerateModuleHomScalars
