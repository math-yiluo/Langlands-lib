import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.FunctionDescent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # The subsheaf of `p_* 𝒪_X` cut out by a unit cocycle -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.Scheme.UnitCocycleDescent

variable {X Y : Scheme.{u}} (p : X ⟶ Y)
  (c : ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p → Γ(U, ⊤)ˣ)

/-- Maps with equal composites to `Y` have equal preimages of preimages of opens of `Y`. -/
lemma preimage_preimage_eq {U : Scheme.{u}} {a b : U ⟶ X} (h : a ≫ p = b ≫ p) (W : Y.Opens) :
    a ⁻¹ᵁ p ⁻¹ᵁ W = b ⁻¹ᵁ p ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage]

/-- Functions pulled back from `Y` along maps with equal composites agree. -/
lemma appLE_app_eq {U : Scheme.{u}} {a b : U ⟶ X} (h : a ≫ p = b ≫ p) {W : Y.Opens}
    {V : U.Opens} (ha : V ≤ a ⁻¹ᵁ p ⁻¹ᵁ W) (hb : V ≤ b ⁻¹ᵁ p ⁻¹ᵁ W) (r : Γ(Y, W)) :
    a.appLE (p ⁻¹ᵁ W) V ha (p.app W r) = b.appLE (p ⁻¹ᵁ W) V hb (p.app W r) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun f ↦ f r) (appLE_eq_of_eq h W V _ _)

/-- A section `σ` of `𝒪_X` over `p ⁻¹ᵁ W` satisfies the cocycle condition if, for every pair
`a b : U ⟶ X` with equal composites to `Y` and every open `V` of `U` mapped into `p ⁻¹ᵁ W`
by both, the restriction of `c U a b h` to `V` times `a^* σ` equals `b^* σ` on `V`. -/
def IsCocycleSection (W : Y.Opens) (σ : Γ(X, p ⁻¹ᵁ W)) : Prop :=
  ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p) (V : U.Opens)
    (ha : V ≤ a ⁻¹ᵁ p ⁻¹ᵁ W) (hb : V ≤ b ⁻¹ᵁ p ⁻¹ᵁ W),
    U.presheaf.map (homOfLE le_top).op (c U a b h).1 * a.appLE (p ⁻¹ᵁ W) V ha σ =
      b.appLE (p ⁻¹ᵁ W) V hb σ

namespace IsCocycleSection

variable {p c}

lemma zero (W : Y.Opens) : IsCocycleSection p c W 0 := by
  intro U a b h V ha hb
  simp only [map_zero, mul_zero]

lemma add {W : Y.Opens} {σ τ : Γ(X, p ⁻¹ᵁ W)} (hσ : IsCocycleSection p c W σ)
    (hτ : IsCocycleSection p c W τ) : IsCocycleSection p c W (σ + τ) := by
  intro U a b h V ha hb
  rw [map_add, map_add, mul_add, hσ U a b h V ha hb, hτ U a b h V ha hb]

lemma mul {W : Y.Opens} {σ τ : Γ(X, p ⁻¹ᵁ W)} (hσ : IsCocycleSection p c W σ)
    (hτ : ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p → ∀ (V : U.Opens)
      (ha : V ≤ a ⁻¹ᵁ p ⁻¹ᵁ W) (hb : V ≤ b ⁻¹ᵁ p ⁻¹ᵁ W),
      a.appLE (p ⁻¹ᵁ W) V ha τ = b.appLE (p ⁻¹ᵁ W) V hb τ) :
    IsCocycleSection p c W (τ * σ) := by
  intro U a b h V ha hb
  rw [map_mul, map_mul, ← hσ U a b h V ha hb, hτ U a b h V ha hb, mul_left_comm]

lemma app_mul {W : Y.Opens} (r : Γ(Y, W)) {σ : Γ(X, p ⁻¹ᵁ W)}
    (hσ : IsCocycleSection p c W σ) : IsCocycleSection p c W (p.app W r * σ) :=
  hσ.mul fun _ _ _ h _ ha hb ↦ appLE_app_eq p h ha hb r

lemma map {W W' : Y.Opens} (i : W' ≤ W) {σ : Γ(X, p ⁻¹ᵁ W)}
    (hσ : IsCocycleSection p c W σ) :
    IsCocycleSection p c W' (X.presheaf.map (homOfLE (p.preimage_mono i)).op σ) := by
  intro U a b h V ha hb
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.map_appLE]
  exact hσ U a b h V _ _

/-- The cocycle condition is local on `Y`. -/
lemma of_locally {W : Y.Opens} (σ : Γ(X, p ⁻¹ᵁ W))
    (hσ : ∀ y ∈ W, ∃ (W' : Y.Opens) (i : W' ≤ W), y ∈ W' ∧
      IsCocycleSection p c W' (X.presheaf.map (homOfLE (p.preimage_mono i)).op σ)) :
    IsCocycleSection p c W σ := by
  intro U a b h V ha hb
  choose W' i hyW' hW' using hσ
  let Vs : V → U.Opens := fun v ↦ V ⊓ a ⁻¹ᵁ p ⁻¹ᵁ W' _ (ha v.2)
  have hcov : V ≤ iSup Vs := fun v hv ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨v, hv⟩, hv, hyW' _ (ha hv)⟩
  refine U.sheaf.eq_of_locally_eq' Vs V (fun v ↦ homOfLE inf_le_left) hcov _ _ fun v ↦ ?_
  have hva : Vs v ≤ a ⁻¹ᵁ p ⁻¹ᵁ W' _ (ha v.2) := inf_le_right
  have hvb : Vs v ≤ b ⁻¹ᵁ p ⁻¹ᵁ W' _ (ha v.2) :=
    (preimage_preimage_eq p h _).le.trans' hva
  have key := hW' _ (ha v.2) U a b h (Vs v) hva hvb
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.map_appLE] at key
  change U.presheaf.map _ (_ * _) = U.presheaf.map _ _
  rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map, Scheme.Hom.appLE_map, ← Functor.map_comp]
  exact key

end IsCocycleSection

/-- The pushforward of the structure sheaf of `X` along `p`. -/
noncomputable abbrev pushforwardUnit : Y.Modules :=
  (Scheme.Modules.pushforward p).obj (SheafOfModules.unit X.ringCatSheaf)

/-- A function `r` on `W` acts on sections of `p_* 𝒪_X` over `W` by multiplication with
its pullback `p^* r`. -/
lemma pushforwardUnit_smul (W : Y.Opens) (r : Γ(Y, W)) (σ : Γ(pushforwardUnit p, W)) :
    (show Γ(X, p ⁻¹ᵁ W) from r • σ) = p.app W r * (show Γ(X, p ⁻¹ᵁ W) from σ) := rfl

/-- The presheaf submodule of `p_* 𝒪_X` of sections satisfying the cocycle condition. -/
def cocyclePresheafSubmodule : PresheafOfModules.Submodule (pushforwardUnit p).val where
  obj W :=
    { carrier := {σ | IsCocycleSection p c W.unop (show Γ(X, p ⁻¹ᵁ W.unop) from σ)}
      add_mem' := fun hσ hτ ↦ hσ.add hτ
      zero_mem' := IsCocycleSection.zero W.unop
      smul_mem' := fun r _ hσ ↦ hσ.app_mul r }
  map f _ hσ := hσ.map (leOfHom f.unop)

/-- The subsheaf `L` of `p_* 𝒪_X` of sections satisfying the cocycle condition. -/
def cocycleSubmodule : SheafOfModules.Submodule (pushforwardUnit p) where
  toSubmodule := cocyclePresheafSubmodule p c
  isSheaf W σ hσ := by
    refine IsCocycleSection.of_locally _ fun y hy ↦ ?_
    obtain ⟨W', f, hf, hyW'⟩ := hσ y hy
    exact ⟨W', leOfHom f, hyW', hf⟩

/-- The sheaf of modules `L` on `Y` attached to the unit cocycle `c`. -/
noncomputable abbrev cocycleModule : Y.Modules :=
  (cocycleSubmodule p c).toSheafOfModules

end Langlands.Scheme.UnitCocycleDescent
