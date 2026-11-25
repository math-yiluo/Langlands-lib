/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Evaluation
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular

/-!
# The pairing induced by the evaluation of internal homs of modules

Let `A` be a commutative monoid in a braided monoidal abelian category `C` and let
`Φ : C ⥤ ModuleCat R` be a lax monoidal functor. For modules `M` and `N` over `A`, the
evaluation `Hom_A(M, N) ⊗ M ⟶ N` (`CategoryTheory.Mod.evaluation`) induces an `R`-bilinear
pairing `Φ Hom_A(M, N) × Φ M → Φ N`, that is an `R`-linear map
`Φ Hom_A(M, N) → Hom_R(Φ M, Φ N)` (`CategoryTheory.Mod.evaluationPairing`).

If `Φ` is additive and the unit `R → Φ A` is an isomorphism, this map is bijective for `M` free
of finite rank (`CategoryTheory.Mod.bijective_evaluationPairing_of_iso_biproduct`): it is
compatible with finite direct sums in `M`, and for `M = A` it is the identification
`Φ Hom_A(A, N) ≅ Φ N ≅ Hom_R(R, Φ N)`.
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

local notation "η[" M "]" => MonObj.one (X := M)
local notation "μ[" M "]" => MonObj.mul (X := M)

namespace LinearMap

variable {R : Type*} [CommRing R] {V W U V' W' U' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup U] [Module R U] [AddCommGroup V'] [Module R V']
  [AddCommGroup W'] [Module R W'] [AddCommGroup U'] [Module R U']

/-- Bijectivity of the curried form of a bilinear map is invariant under linear isomorphisms of
the three spaces. -/
lemma bijective_iff_of_linearEquiv (p : V →ₗ[R] W →ₗ[R] U) (p' : V' →ₗ[R] W' →ₗ[R] U')
    (a : V ≃ₗ[R] V') (b : W ≃ₗ[R] W') (c : U ≃ₗ[R] U')
    (h : ∀ v w, p' (a v) (b w) = c (p v w)) :
    Function.Bijective p ↔ Function.Bijective p' := by
  have hp : (p' : V' → W' →ₗ[R] U') = (b.arrowCongr c) ∘ p ∘ a.symm := by
    ext v' w'
    simp only [Function.comp_apply, LinearEquiv.arrowCongr_apply]
    rw [← h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [hp, EquivLike.comp_bijective, EquivLike.bijective_comp]

end LinearMap

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [BraidedCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

/-- The evaluation of `Hom_A(A, N) ≅ N` is the right action of `A` on `N`. -/
lemma evaluation_regular (N : Mod C A) :
    evaluation (regular A) N = (ihomRegularIso.hom.app N).hom ▷ A ≫ rightAct N := by
  have h₁ := (ihomAdjunction (regular A)).rightAdjointUniq_hom_app_counit
    (Adjunction.id.ofNatIsoLeft tensorLeftRegularIso.symm) N
  have h₂ : tensorπ N (regular A) ≫ (tensorLeftRegularHom.app N).hom = rightAct N := by
    change (colimit.ι _ _ ≫ colimit.desc _ (rightActCocone N)).hom = _
    rw [colimit.ι_desc]
    change (_ ≫ rightActHom N).hom = _
    erw [Category.id_comp]
    rfl
  rw [evaluation, ← h₁, ihomRegularIso, Mod.comp_hom', tensorπ_map_assoc]
  simp only [Adjunction.ofNatIsoLeft_counit, Iso.symm_inv, Adjunction.id_counit,
    Category.comp_id]
  exact congrArg (_ ≫ ·) h₂

variable {R : Type w} [CommRing R] (Φ : C ⥤ ModuleCat.{w} R) [Φ.LaxMonoidal]

/-- The pairing `Φ Hom_A(M, N) → Hom_R(Φ M, Φ N)` induced by the evaluation
`Hom_A(M, N) ⊗ M ⟶ N` and the lax monoidal structure of `Φ`. -/
noncomputable def evaluationPairing (M N : Mod C A) :
    Φ.obj ((ihom M).obj N).X →ₗ[R] Φ.obj M.X →ₗ[R] Φ.obj N.X :=
  TensorProduct.curry (μ Φ ((ihom M).obj N).X M.X ≫ Φ.map (evaluation M N)).hom

lemma evaluationPairing_apply (M N : Mod C A) (f : Φ.obj ((ihom M).obj N).X) (x : Φ.obj M.X) :
    evaluationPairing Φ M N f x =
      (Φ.map (evaluation M N)).hom ((μ Φ ((ihom M).obj N).X M.X).hom (f ⊗ₜ x)) :=
  rfl

/-- The pairing is dinatural in the source. -/
lemma evaluationPairing_ihomMap {M M' : Mod C A} (g : M ⟶ M') (N : Mod C A)
    (f : Φ.obj ((ihom M').obj N).X) (x : Φ.obj M.X) :
    evaluationPairing Φ M N ((Φ.map ((ihomMap g).app N).hom).hom f) x =
      evaluationPairing Φ M' N f ((Φ.map g.hom).hom x) := by
  have h := congrArg (fun m ↦ (μ Φ _ _ ≫ Φ.map m).hom (f ⊗ₜ x)) (evaluation_ihomMap g N)
  simp only [Functor.map_comp, ← μ_natural_left_assoc, ← μ_natural_right_assoc] at h
  exact h

/-- The pairing is natural in the target. -/
lemma evaluationPairing_naturality (M : Mod C A) {N N' : Mod C A} (g : N ⟶ N')
    (f : Φ.obj ((ihom M).obj N).X) (x : Φ.obj M.X) :
    evaluationPairing Φ M N' ((Φ.map ((ihom M).map g).hom).hom f) x =
      (Φ.map g.hom).hom (evaluationPairing Φ M N f x) := by
  have h := congrArg (fun m ↦ (μ Φ _ _ ≫ Φ.map m).hom (f ⊗ₜ x))
    (evaluation_naturality M g)
  simp only [Functor.map_comp, ← μ_natural_left_assoc] at h
  exact h

/-- Bijectivity of the pairing only depends on the isomorphism class of the source. -/
lemma bijective_evaluationPairing_iff_of_iso_left {M M' : Mod C A} (e : M ≅ M') (N : Mod C A) :
    Function.Bijective (evaluationPairing Φ M N) ↔
      Function.Bijective (evaluationPairing Φ M' N) := by
  refine (LinearMap.bijective_iff_of_linearEquiv (evaluationPairing Φ M' N)
    (evaluationPairing Φ M N)
    (Φ.mapIso ((forget A).mapIso ((ihomMapIso e).app N))).toLinearEquiv
    (Φ.mapIso ((forget A).mapIso e.symm)).toLinearEquiv (LinearEquiv.refl R _)
    fun f x ↦ ?_).symm
  have he : ((ihomMapIso e).app N).hom = (ihomMap e.hom).app N := rfl
  change evaluationPairing Φ M N ((Φ.map ((ihomMap e.hom).app N).hom).hom f)
    ((Φ.map e.inv.hom).hom x) = evaluationPairing Φ M' N f x
  rw [evaluationPairing_ihomMap, ← ModuleCat.comp_apply, ← Functor.map_comp,
    ← Mod.comp_hom', e.inv_hom_id, Mod.id_hom', Functor.map_id]
  rfl

/-- Bijectivity of the pairing only depends on the isomorphism class of the target. -/
lemma bijective_evaluationPairing_iff_of_iso_right (M : Mod C A) {N N' : Mod C A} (e : N ≅ N') :
    Function.Bijective (evaluationPairing Φ M N) ↔
      Function.Bijective (evaluationPairing Φ M N') :=
  LinearMap.bijective_iff_of_linearEquiv _ _
    (Φ.mapIso ((forget A).mapIso ((ihom M).mapIso e))).toLinearEquiv (LinearEquiv.refl R _)
    (Φ.mapIso ((forget A).mapIso e)).toLinearEquiv fun f x ↦
      evaluationPairing_naturality Φ M e.hom f x

/-- Bijectivity of the pairing is invariant under monoidal natural isomorphisms of `Φ`. -/
lemma bijective_evaluationPairing_iff_of_iso {Ψ : C ⥤ ModuleCat.{w} R} [Ψ.LaxMonoidal]
    (τ : Φ ≅ Ψ) [NatTrans.IsMonoidal τ.hom] (M N : Mod C A) :
    Function.Bijective (evaluationPairing Φ M N) ↔
      Function.Bijective (evaluationPairing Ψ M N) := by
  refine LinearMap.bijective_iff_of_linearEquiv _ _ (τ.app _).toLinearEquiv
    (τ.app _).toLinearEquiv (τ.app _).toLinearEquiv fun f x ↦ ?_
  have h := congrArg (fun m ↦ m.hom (f ⊗ₜ x))
    (NatTrans.IsMonoidal.tensor (τ := τ.hom) ((ihom M).obj N).X M.X)
  have hn := congrArg (fun m ↦ m.hom ((μ Φ _ _).hom (f ⊗ₜ x)))
    (τ.hom.naturality (evaluation M N))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h hn
  simp only [Iso.toLinearEquiv_apply, Iso.app_hom, evaluationPairing_apply]
  rw [hn, h]
  rfl

section Regular

/-- The pairing of `Hom_A(A, N)` with `A` is bijective if the unit `R → Φ A` is an isomorphism:
evaluating at the unit of `Φ A` it is the identification `Φ Hom_A(A, N) ≅ Φ N`. -/
lemma bijective_evaluationPairing_regular [IsIso (ε Φ ≫ Φ.map η[A])] (N : Mod C A) :
    Function.Bijective (evaluationPairing Φ (regular A) N) := by
  have : IsIso (X := 𝟙_ (ModuleCat R)) (Y := Φ.obj (regular A).X) (ε Φ ≫ Φ.map η[A]) :=
    (inferInstance : IsIso (ε Φ ≫ Φ.map η[A]))
  obtain ⟨e, he⟩ : ∃ e : 𝟙_ (ModuleCat R) ≅ Φ.obj (regular A).X,
      e.hom = ε Φ ≫ Φ.map η[A] := ⟨asIso (ε Φ ≫ Φ.map η[A]), rfl⟩
  have hu (f) : evaluationPairing Φ (regular A) N f (e.hom.hom (1 : R)) =
      (Φ.map (ihomRegularIso.hom.app N).hom).hom f := by
    have h₁ : ((ihom (regular A)).obj N).X ◁ η[A] ≫ evaluation (regular A) N =
        (ρ_ _).hom ≫ (ihomRegularIso.hom.app N).hom := by
      rw [evaluation_regular, whisker_exchange_assoc, ← cancel_epi (ρ_ _).inv,
        Iso.inv_hom_id_assoc, ← rightUnitor_inv_naturality_assoc]
      have h : (ρ_ N.X).inv ≫ N.X ◁ η[A] ≫ rightAct N = 𝟙 _ := by
        have := congrArg Mod.Hom.hom (unitRight_rightActHom N)
        rw [Mod.comp_hom', Mod.id_hom'] at this
        change ((ρ_ N.X).inv ≫ N.X ◁ η[A]) ≫ rightAct N = 𝟙 _ at this
        simpa only [Category.assoc] using this
      erw [h]
      exact Category.comp_id _
    have key : Φ.obj ((ihom (regular A)).obj N).X ◁ (ε Φ ≫ Φ.map η[A]) ≫
        μ Φ _ (regular A).X ≫ Φ.map (evaluation (regular A) N) =
          (ρ_ _).hom ≫ Φ.map (ihomRegularIso.hom.app N).hom := by
      rw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      erw [μ_natural_right_assoc]
      erw [← Φ.map_comp, h₁]
      rw [Φ.map_comp, ← Category.assoc, ← Category.assoc, Category.assoc (_ ◁ ε Φ),
        ← Functor.LaxMonoidal.right_unitality]
    have h₂ := congrArg (fun m ↦ m.hom (f ⊗ₜ (1 : R))) key
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.rightUnitor_hom_apply, one_smul] at h₂
    rw [he]
    exact h₂
  have hΦe : Function.Bijective (Φ.map (ihomRegularIso.hom.app N).hom).hom :=
    (Φ.mapIso ((forget A).mapIso (ihomRegularIso.app N))).toLinearEquiv.bijective
  have hspan (y : Φ.obj (regular A).X) : y = (e.inv.hom y : R) • e.hom.hom (1 : R) := by
    rw [← map_smul, smul_eq_mul, mul_one, ← ModuleCat.comp_apply, e.inv_hom_id]
    rfl
  refine ⟨fun f g hfg ↦ hΦe.1 ?_, fun φ ↦ ?_⟩
  · rw [← hu, ← hu, hfg]
  · obtain ⟨f, hf⟩ := hΦe.2 (φ (e.hom.hom 1))
    refine ⟨f, LinearMap.ext fun y ↦ ?_⟩
    rw [hspan y, map_smul, map_smul, hu, hf]

end Regular

section Biproduct

attribute [local instance] Abelian.hasFiniteBiproducts

variable [Φ.Additive]

/-- The pairing of a finite direct sum is bijective if the pairings of the summands are. -/
lemma bijective_evaluationPairing_biproduct {n : ℕ} (M : Fin n → Mod C A) (N : Mod C A)
    (h : ∀ i, Function.Bijective (evaluationPairing Φ (M i) N)) :
    Function.Bijective (evaluationPairing Φ (⨁ M) N) := by
  have hba (f) : ∑ i, (Φ.map ((ihomMap (biproduct.π M i)).app N).hom).hom
      ((Φ.map ((ihomMap (biproduct.ι M i)).app N).hom).hom f) = f := by
    have h₀ : ∑ i, ((ihomMap (biproduct.ι M i)).app N).hom ≫
        ((ihomMap (biproduct.π M i)).app N).hom = 𝟙 _ := by
      have := congrArg (fun τ ↦ (forget A).map (τ.app N)) (sum_ihomMap_ι_comp_ihomMap_π M)
      simp only [NatTrans.app_sum, NatTrans.comp_app, NatTrans.id_app, Functor.map_sum,
        Functor.map_comp, Functor.map_id] at this
      exact this
    have h₁ := congrArg (fun m ↦ (Φ.map m).hom f) h₀
    simp only [Functor.map_sum, ModuleCat.hom_sum, Functor.map_comp, ModuleCat.hom_comp,
      Functor.map_id, ModuleCat.hom_id] at h₁
    rw [LinearMap.sum_apply] at h₁
    exact h₁
  have htot (x : Φ.obj (⨁ M).X) :
      ∑ i, (Φ.map (biproduct.ι M i).hom).hom ((Φ.map (biproduct.π M i).hom).hom x) = x := by
    have h₀ : ∑ i, (biproduct.π M i).hom ≫ (biproduct.ι M i).hom = 𝟙 _ := by
      have := congrArg (fun m ↦ (forget A).map m) (biproduct.total (f := M))
      simp only [Functor.map_sum, Functor.map_comp, Functor.map_id] at this
      exact this
    have h₁ := congrArg (fun m ↦ (Φ.map m).hom x) h₀
    simp only [Functor.map_sum, ModuleCat.hom_sum, Functor.map_comp, ModuleCat.hom_comp,
      Functor.map_id, ModuleCat.hom_id] at h₁
    rw [LinearMap.sum_apply] at h₁
    exact h₁
  refine ⟨fun f g hfg ↦ ?_, fun φ ↦ ?_⟩
  · have hi (i : Fin n) : (Φ.map ((ihomMap (biproduct.ι M i)).app N).hom).hom f =
        (Φ.map ((ihomMap (biproduct.ι M i)).app N).hom).hom g :=
      (h i).1 (LinearMap.ext fun x ↦ by
        rw [evaluationPairing_ihomMap, evaluationPairing_ihomMap, hfg])
    rw [← hba f, ← hba g]
    simp only [hi]
  · choose v hv using fun i ↦ (h i).2 (φ ∘ₗ (Φ.map (biproduct.ι M i).hom).hom)
    refine ⟨∑ i, (Φ.map ((ihomMap (biproduct.π M i)).app N).hom).hom (v i),
      LinearMap.ext fun x ↦ ?_⟩
    rw [map_sum, LinearMap.sum_apply]
    conv_rhs => rw [← htot x, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [evaluationPairing_ihomMap, hv i]
    rfl

/-- The pairing of a free module of finite rank is bijective if the unit `R → Φ A` is an
isomorphism. -/
lemma bijective_evaluationPairing_of_iso_biproduct [IsIso (ε Φ ≫ Φ.map η[A])] {M : Mod C A}
    {n : ℕ} (e : M ≅ ⨁ fun _ : Fin n ↦ regular A) (N : Mod C A) :
    Function.Bijective (evaluationPairing Φ M N) :=
  (bijective_evaluationPairing_iff_of_iso_left Φ e N).2
    (bijective_evaluationPairing_biproduct Φ _ N fun _ ↦
      bijective_evaluationPairing_regular Φ N)

end Biproduct

end CategoryTheory.Mod

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]

/-- A morphism of modules out of the regular module `A` is determined by the image of the unit,
and every morphism `𝟙 ⟶ M` is the image of the unit of such a morphism: `A` is the free module
on `𝟙`. -/
lemma bijective_one_comp_hom (M : Mod C A) :
    Function.Bijective (fun v : regular A ⟶ M ↦ η[A] ≫ v.hom) := by
  have key (v : regular A ⟶ M) :
      v.hom = (ρ_ A).inv ≫ A ◁ (η[A] ≫ v.hom) ≫ act M.X := by
    have hv : μ[A] ≫ v.hom = A ◁ v.hom ≫ act M.X := act_hom v
    rw [MonoidalCategory.whiskerLeft_comp_assoc, ← hv, ← Category.assoc (A ◁ η[A]),
      MonObj.mul_one, Iso.inv_hom_id_assoc]
  refine ⟨fun v v' h ↦ Mod.hom_ext _ _ ?_, fun g ↦ ?_⟩
  · rw [key v, key v']
    exact congrArg (fun g ↦ (ρ_ A).inv ≫ A ◁ g ≫ act M.X) h
  · let ι : regular A ⟶ (free A).obj (𝟙_ C) :=
      homMk (M := regular A) (N := (free A).obj (𝟙_ C)) (ρ_ A).inv (by
        change μ[A] ≫ (ρ_ A).inv = A ◁ (ρ_ A).inv ≫ (α_ A A (𝟙_ C)).inv ≫ μ[A] ▷ 𝟙_ C
        rw [rightUnitor_inv_naturality]
        monoidal)
    refine ⟨ι ≫ freeDesc A g, ?_⟩
    have h := unit_freeDesc A g
    change η[A] ≫ (ρ_ A).inv ≫ (freeDesc A g).hom = g
    rw [rightUnitor_inv_naturality_assoc, ← unitors_inv_equal]
    exact h

end CategoryTheory.Mod

namespace ModuleCat

variable {R : Type*} [CommRing R] {P Q T : ModuleCat R}

/-- A morphism `g : P ⊗ Q ⟶ T` intertwining `a ⊗ b` and `c` satisfies
`g (a p ⊗ b q) = c (g (p ⊗ q))`. -/
lemma tmul_eq_of_tensorHom_comp {a : P ⟶ P} {b : Q ⟶ Q} {c : T ⟶ T} {g : P ⊗ Q ⟶ T}
    (h : (a ⊗ₘ b) ≫ g = g ≫ c) (p : P) (q : Q) :
    g.hom (a.hom p ⊗ₜ b.hom q) = c.hom (g.hom (p ⊗ₜ q)) := by
  have := congrArg (fun f ↦ f.hom (p ⊗ₜ q)) h
  simpa only [hom_comp, LinearMap.coe_comp, Function.comp_apply,
    MonoidalCategory.tensorHom_tmul] using this

end ModuleCat
