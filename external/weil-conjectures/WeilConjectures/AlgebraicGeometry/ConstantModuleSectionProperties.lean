/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.RingTheory.Flat.Tensor

/-!
# Sections of constant module sheaves

Source: Stacks Project, sites-modules, Tags 093J, 093K, 093L
(auxiliary; not a blueprint node).
-/

universe u

open CategoryTheory Opposite TensorProduct

namespace CategoryTheory

open Limits

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Type u) [CommRing R]

private noncomputable abbrev sectionFunctor (U : C) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  constantSheaf J (ModuleCat.{u} R) ⋙ sheafToPresheaf J (ModuleCat.{u} R) ⋙
    (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op U)

private theorem section_preservesFiniteLimits (U : C) :
    PreservesFiniteLimits (sectionFunctor J R U) := by
  have h₁ : PreservesFiniteLimits (constantSheaf J (ModuleCat.{u} R)) :=
    comp_preservesFiniteLimits
      (Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _) (presheafToSheaf J _)
  have h₂ : PreservesFiniteLimits (sheafToPresheaf J (ModuleCat.{u} R) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op U)) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

attribute [local instance] section_preservesFiniteLimits

private theorem section_injective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Injective f) (U : C) : Function.Injective ((sectionFunctor J R U).map f) := by
  have : Mono f := (ModuleCat.mono_iff_injective f).2 hf
  exact (ModuleCat.mono_iff_injective _).1 (inferInstance : Mono _)

private theorem section_exact {A B D : ModuleCat.{u} R} (f : A ⟶ B) (g : B ⟶ D)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (U : C) : Function.Exact ((sectionFunctor J R U).map f)
      ((sectionFunctor J R U).map g) := by
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk f g (ModuleCat.hom_ext hfg.linearMap_comp_eq_zero)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hfg hf hg
  have h := ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (sectionFunctor J R U)).1 inferInstance S hS).1
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h

-- Forgetting modules commutes with constant sheaves, so a set-theoretic splitting suffices.
private theorem section_surjective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Surjective f) (U : C) : Function.Surjective ((sectionFunctor J R U).map f) := by
  classical
  let e := constantCommuteCompose J (forget (ModuleCat.{u} R))
  let s : N → M := Function.surjInv hf
  let s' := (constantSheaf J (Type u)).map (TypeCat.ofHom s)
  have hs : s' ≫ (constantSheaf J (Type u)).map ((forget _).map f) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_id]
    congr 1
    ext x
    exact Function.surjInv_eq hf x
  have hnat := NatTrans.naturality e.hom f
  intro y
  let y' := ((e.hom.app N).hom.app (op U)) y
  let x' := (s'.hom.app (op U)) y'
  refine ⟨((e.inv.app M).hom.app (op U)) x', ?_⟩
  have hn := congrArg (fun t ↦ t.hom.app (op U)) hnat
  have hh := congrArg (fun t ↦ t.hom.app (op U)) hs
  have hcomp := congrArg (fun t ↦ t.hom.app (op U)) (e.inv_hom_id_app M)
  have hycomp := congrArg (fun t ↦ t.hom.app (op U)) (e.hom_inv_id_app N)
  have hnx := congrArg (fun t ↦ t (((e.inv.app M).hom.app (op U)) x')) hn
  have hcx := congrArg (fun t ↦ t x') hcomp
  have hhx := congrArg (fun t ↦ t y') hh
  have hy := congrArg (fun t ↦ t y) hycomp
  dsimp at hnx hcx hhx hy
  have hx : ((e.hom.app N).hom.app (op U))
      (((sectionFunctor J R U).map f) (((e.inv.app M).hom.app (op U)) x')) = y' := by
    change _ = x' at hcx
    change _ = y' at hhx
    calc
      _ = _ := hnx
      _ = _ := congrArg _ hcx
      _ = _ := hhx
  calc
    _ = ((e.inv.app N).hom.app (op U))
        (((e.hom.app N).hom.app (op U))
          (((sectionFunctor J R U).map f) (((e.inv.app M).hom.app (op U)) x'))) := by
      symm
      exact congrArg (fun t ↦ t
        (((sectionFunctor J R U).map f) (((e.inv.app M).hom.app (op U)) x'))) hycomp
    _ = _ := congrArg _ hx
    _ = y := hy

private theorem section_map_smul (U : C) {M N : ModuleCat.{u} R}
    (r : R) (f : M ⟶ N) :
    (sectionFunctor J R U).map (r • f) = r • (sectionFunctor J R U).map f := by
  have h : (sheafifyMap J ((Functor.const Cᵒᵖ).map (r • f))) =
      r • (sheafifyMap J ((Functor.const Cᵒᵖ).map f)) := by
    apply sheafify_hom_ext J _ _ ((constantSheaf J (ModuleCat.{u} R)).obj N).property
    rw [← toSheafify_naturality]
    ext X x
    simp only [NatTrans.comp_app, NatTrans.app_smul, ModuleCat.comp_apply,
      ModuleCat.hom_smul, LinearMap.smul_apply, Functor.const_map_app]
    rw [map_smul]
    have hn := congrArg (fun t ↦ t.app X)
      (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f))
    exact congrArg (fun t ↦ r • t x) hn
  exact congrArg (fun t ↦ t.app (op U)) h

private theorem section_linear (U : C) : (sectionFunctor J R U).Linear R where
  map_smul := fun f r ↦ section_map_smul J R U r f

attribute [local instance] section_linear

private theorem section_preservesFiniteColimits (U : C) :
    PreservesFiniteColimits (sectionFunctor J R U) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2
  intro S hS
  refine ⟨?_, (ModuleCat.epi_iff_surjective _).2
    (section_surjective J R S.g hS.moduleCat_surjective_g U)⟩
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    (section_exact J R S.f S.g hS.moduleCat_injective_f
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS.exact)
      hS.moduleCat_surjective_g U)

attribute [local instance] section_preservesFiniteColimits

section TensorComparison

variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [Functor.Linear R F]

private noncomputable def tensorComparison (M Q : ModuleCat.{u} R) :
    F.obj M ⊗[R] Q →ₗ[R] F.obj (ModuleCat.of R (M ⊗[R] Q)) :=
  TensorProduct.lift
    ((ModuleCat.homLinearEquiv.toLinearMap ∘ₗ F.mapLinearMap R ∘ₗ
      ModuleCat.homLinearEquiv.symm.toLinearMap ∘ₗ (TensorProduct.mk R M Q).flip).flip)

private theorem tensorComparison_tmul (M Q : ModuleCat.{u} R) (s : F.obj M) (q : Q) :
    tensorComparison R F M Q (s ⊗ₜ[R] q) =
      F.map (ModuleCat.ofHom ((TensorProduct.mk R M Q).flip q)) s := rfl

private theorem tensorComparison_naturality
    {M M' Q Q' : ModuleCat.{u} R} (f : M ⟶ M') (g : Q ⟶ Q') :
    (tensorComparison R F M' Q').comp (TensorProduct.map (F.map f).hom g.hom) =
      (F.map (ModuleCat.ofHom (TensorProduct.map f.hom g.hom))).hom.comp
        (tensorComparison R F M Q) := by
  ext s q
  change (F.map f ≫ F.map
    (ModuleCat.ofHom ((TensorProduct.mk R M' Q').flip (g q)))) s =
      (F.map (ModuleCat.ofHom ((TensorProduct.mk R M Q).flip q)) ≫
        F.map (ModuleCat.ofHom (TensorProduct.map f.hom g.hom))) s
  rw [← F.map_comp, ← F.map_comp]
  congr 2

private noncomputable def freeProjection (M : ModuleCat.{u} R) (n : ℕ) (i : Fin n) :
    ModuleCat.of R (M ⊗[R] (Fin n → R)) ⟶ M :=
  ModuleCat.ofHom ((TensorProduct.rid R M).toLinearMap.comp
    (LinearMap.lTensor M (LinearMap.proj i)))

-- Coordinate projections and standard-basis inclusions give the inverse in finite rank.
private theorem tensorComparison_free_bijective (M : ModuleCat.{u} R) (n : ℕ) :
    Function.Bijective (tensorComparison R F M (ModuleCat.of R (Fin n → R))) := by
  classical
  let Q := ModuleCat.of R (Fin n → R)
  let b : Fin n → Q := fun i ↦ Pi.single i 1
  let ins (i : Fin n) : M ⟶ ModuleCat.of R (M ⊗[R] Q) :=
    ModuleCat.ofHom ((TensorProduct.mk R M Q).flip (b i))
  let out (i : Fin n) := freeProjection R M n i
  let inv : F.obj (ModuleCat.of R (M ⊗[R] Q)) →ₗ[R] F.obj M ⊗[R] Q :=
    ∑ i, (TensorProduct.mk R (F.obj M) Q).flip (b i) ∘ₗ (F.map (out i)).hom
  have htotal : ∑ i, out i ≫ ins i = 𝟙 (ModuleCat.of R (M ⊗[R] Q)) := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m q
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    change ∑ i, (q i • m) ⊗ₜ[R] b i = m ⊗ₜ[R] q
    simp_rw [TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum]
    congr 1
    ext i
    change (∑ j : Fin n, q j • Pi.single j (1 : R)) i = q i
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  have hright : Function.RightInverse inv (tensorComparison R F M Q) := by
    intro x
    dsimp only [inv]
    rw [LinearMap.sum_apply, map_sum]
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    change ∑ i, (F.map (out i) ≫ F.map (ins i)) x = x
    simp_rw [← F.map_comp]
    change (∑ i, (F.map (out i ≫ ins i)).hom x) = x
    rw [← LinearMap.sum_apply, ← ModuleCat.hom_sum, ← F.map_sum, htotal, F.map_id]
    rfl
  have hleft : Function.LeftInverse inv (tensorComparison R F M Q) := by
    intro z
    have hl : inv.comp (tensorComparison R F M Q) = LinearMap.id := by
      apply TensorProduct.ext'
      intro s q
      dsimp only [LinearMap.comp_apply, inv]
      rw [LinearMap.sum_apply]
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, tensorComparison_tmul]
      have ho (i : Fin n) :
          ModuleCat.ofHom ((TensorProduct.mk R M Q).flip q) ≫ out i = q i • 𝟙 M := by
        ext m
        rfl
      have hval (i : Fin n) : (F.map (out i))
          (F.map (ModuleCat.ofHom ((TensorProduct.mk R M Q).flip q)) s) = q i • s := by
        change (F.map (ModuleCat.ofHom ((TensorProduct.mk R M Q).flip q)) ≫
          F.map (out i)) s = _
        rw [← F.map_comp, ho, F.map_smul, F.map_id]
        rfl
      change (∑ i, (F.map (out i))
        (F.map (ModuleCat.ofHom ((TensorProduct.mk R M Q).flip q)) s) ⊗ₜ[R] b i) =
          s ⊗ₜ[R] q
      simp_rw [hval, TensorProduct.smul_tmul]
      rw [← TensorProduct.tmul_sum]
      congr 1
      ext i
      change (∑ j : Fin n, q j • Pi.single j (1 : R)) i = q i
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    exact LinearMap.congr_fun hl z
  exact ⟨hleft.injective, hright.surjective⟩

-- A right-exact diagram chase; only surjectivity of the first comparison is needed.
private theorem cokernel_bijective
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : ModuleCat.{u} R}
    (f : X₁ →ₗ[R] X₂) (g : X₂ →ₗ[R] X₃)
    (f' : Y₁ →ₗ[R] Y₂) (g' : Y₂ →ₗ[R] Y₃)
    (a : X₁ →ₗ[R] Y₁) (b : X₂ →ₗ[R] Y₂) (c : X₃ →ₗ[R] Y₃)
    (ha : Function.Surjective a) (hb : Function.Bijective b)
    (ex : Function.Exact f g) (eg : Function.Surjective g)
    (ex' : Function.Exact f' g') (eg' : Function.Surjective g')
    (h₁ : b.comp f = f'.comp a) (h₂ : c.comp g = g'.comp b) :
    Function.Bijective c := by
  constructor
  · have hc : ∀ z, c z = 0 → z = 0 := by
      intro z hz
      obtain ⟨x, rfl⟩ := eg z
      have hx : g' (b x) = 0 := by
        rw [← LinearMap.comp_apply, ← h₂, LinearMap.comp_apply, hz]
      obtain ⟨y, hy⟩ := (ex' (b x)).1 hx
      obtain ⟨w, rfl⟩ := ha y
      have hw : f w = x := hb.1 (by
        rw [← LinearMap.comp_apply, h₁, LinearMap.comp_apply, hy])
      rw [← hw]
      exact (ex (f w)).2 ⟨w, rfl⟩
    intro z z' hzz
    apply sub_eq_zero.mp
    apply hc
    rw [map_sub, hzz, sub_self]
  · intro z
    obtain ⟨y, rfl⟩ := eg' z
    obtain ⟨x, rfl⟩ := hb.2 y
    exact ⟨g x, LinearMap.congr_fun h₂ x⟩

private theorem tensorComparison_bijective [PreservesFiniteColimits F]
    (M Q : ModuleCat.{u} R) [Module.FinitePresentation R Q] :
    Function.Bijective (tensorComparison R F M Q) := by
  obtain ⟨n, m, g, f, hg, hfg⟩ := Module.FinitePresentation.exists_fin' R Q
  let P₁ := ModuleCat.of R (Fin m → R)
  let P₂ := ModuleCat.of R (Fin n → R)
  let fM := LinearMap.lTensor M f
  let gM := LinearMap.lTensor M g
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.moduleCatMk fM gM (lTensor_exact M hfg hg).linearMap_comp_eq_zero
  have hS : S.Exact := ModuleCat.shortComplex_exact S (lTensor_exact M hfg hg)
  have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 (LinearMap.lTensor_surjective M hg)
  have hFS := ((Functor.preservesFiniteColimits_tfae F).out 4 2 rfl rfl).1 inferInstance S
    ⟨hS, inferInstance⟩
  refine cokernel_bijective R
    (X₁ := ModuleCat.of R (F.obj M ⊗[R] P₁))
    (X₂ := ModuleCat.of R (F.obj M ⊗[R] P₂))
    (X₃ := ModuleCat.of R (F.obj M ⊗[R] Q))
    (Y₁ := F.obj S.X₁) (Y₂ := F.obj S.X₂) (Y₃ := F.obj S.X₃)
    (LinearMap.lTensor (F.obj M) f) (LinearMap.lTensor (F.obj M) g)
    (F.map S.f).hom (F.map S.g).hom
    (tensorComparison R F M P₁) (tensorComparison R F M P₂) (tensorComparison R F M Q)
    (tensorComparison_free_bijective R F M m).2 (tensorComparison_free_bijective R F M n)
    (lTensor_exact (F.obj M) hfg hg) (LinearMap.lTensor_surjective (F.obj M) hg)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hFS.1)
    ((ModuleCat.epi_iff_surjective _).1 hFS.2) ?_ ?_
  · simpa only [S, ShortComplex.moduleCatMk, fM, gM, P₁, P₂,
      Functor.map_id, ModuleCat.hom_id, ModuleCat.hom_ofHom, LinearMap.lTensor_def] using
      tensorComparison_naturality R F (M := M) (M' := M) (Q := P₁) (Q' := P₂)
        (𝟙 M) (ModuleCat.ofHom f)
  · simpa only [S, ShortComplex.moduleCatMk, fM, gM, P₁, P₂,
      Functor.map_id, ModuleCat.hom_id, ModuleCat.hom_ofHom, LinearMap.lTensor_def] using
      tensorComparison_naturality R F (M := M) (M' := M) (Q := P₂) (Q' := Q)
        (𝟙 M) (ModuleCat.ofHom g)

end TensorComparison

@[expose] public section

/-- Sections of constant modules are exact, commute with finitely presented tensor
factors by the canonical comparison, naturally in both modules and the site object,
and preserve flatness over a commutative Noetherian ring.
Source: Stacks Project, sites-modules, Tags 093J, 093K, 093L
(auxiliary; not a blueprint node).

Proof: (1) Sheafification is exact and kernels of sheaves are sectionwise kernels
(situation-conventions). The module sheafification interface
(lem-pc-sites-module-sheafification-interface) identifies the underlying abelian
sheafification. A set-theoretic section of a surjective module map induces a section
of its constant sheaf of sets, hence surjectivity on every object's sections.
(2) Choose a finite presentation of Q. Tensor right exactness
(lem-weil-pbc-tensor-right-exact) and (1), together with preservation of finite
sums by evaluation, identify the same cokernel on both sides. The displayed formula
on pure tensors specifies the canonical comparison. All maps used commute with
module morphisms and restrictions, giving the two naturality identities.
(3) A finitely generated ideal is finitely presented over a Noetherian ring
(lem-sc-noetherian-finite-module-finite-presentation). Apply (2) to that ideal;
flatness of M and (1) make its tensor inclusion injective on sections. Use tensor
symmetry and the finitely generated ideal flatness criterion
(lem-weil-pbc-flat-fg-ideal-criterion) to conclude flatness of the sections. -/
theorem constantModule_section_properties
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type (u)) [CommRing R] [IsNoetherianRing R] :
    (∀ (A B D : ModuleCat.{u} R) (f : A ⟶ B) (g : B ⟶ D),
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      ∀ U : C,
        Function.Injective (((constantSheaf J (ModuleCat.{u} R)).map f).hom.app (op U)) ∧
        Function.Exact (((constantSheaf J (ModuleCat.{u} R)).map f).hom.app (op U))
          (((constantSheaf J (ModuleCat.{u} R)).map g).hom.app (op U)) ∧
        Function.Surjective (((constantSheaf J (ModuleCat.{u} R)).map g).hom.app (op U))) ∧
    (∃ e : ∀ (M Q : ModuleCat.{u} R), Module.FinitePresentation R Q → ∀ U : C,
        (((constantSheaf J (ModuleCat.{u} R)).obj M).obj.obj (op U) ⊗[R] Q) ≃ₗ[R]
          ((constantSheaf J (ModuleCat.{u} R)).obj
            (ModuleCat.of R (M ⊗[R] Q))).obj.obj (op U),
      (∀ (M Q : ModuleCat.{u} R) (hQ : Module.FinitePresentation R Q)
          (U : C) (s : ((constantSheaf J (ModuleCat.{u} R)).obj M).obj.obj (op U)) (q : Q),
        e M Q hQ U (s ⊗ₜ[R] q) =
          (((constantSheaf J (ModuleCat.{u} R)).map
            (ModuleCat.ofHom ((TensorProduct.mk R M Q).flip q))).hom.app (op U)) s) ∧
      (∀ (M M' Q Q' : ModuleCat.{u} R)
          (hQ : Module.FinitePresentation R Q) (hQ' : Module.FinitePresentation R Q')
          (f : M ⟶ M') (g : Q ⟶ Q') (U : C)
          (z : ((constantSheaf J (ModuleCat.{u} R)).obj M).obj.obj (op U) ⊗[R] Q),
        e M' Q' hQ' U
            (TensorProduct.map
              (((constantSheaf J (ModuleCat.{u} R)).map f).hom.app (op U)).hom g.hom z) =
          (((constantSheaf J (ModuleCat.{u} R)).map
            (ModuleCat.ofHom (TensorProduct.map f.hom g.hom))).hom.app (op U))
              (e M Q hQ U z)) ∧
      (∀ (M Q : ModuleCat.{u} R) (hQ : Module.FinitePresentation R Q)
          (U V : C) (h : V ⟶ U)
          (z : ((constantSheaf J (ModuleCat.{u} R)).obj M).obj.obj (op U) ⊗[R] Q),
        e M Q hQ V
            (TensorProduct.map (((constantSheaf J (ModuleCat.{u} R)).obj M).obj.map h.op).hom
              (LinearMap.id : Q →ₗ[R] Q) z) =
          (((constantSheaf J (ModuleCat.{u} R)).obj
            (ModuleCat.of R (M ⊗[R] Q))).obj.map h.op) (e M Q hQ U z))) ∧
    (∀ (M : ModuleCat.{u} R), Module.Flat R M → ∀ U : C,
      Module.Flat R (((constantSheaf J (ModuleCat.{u} R)).obj M).obj.obj (op U))) := by
  classical
  let e (M Q : ModuleCat.{u} R) (hQ : Module.FinitePresentation R Q) (U : C) :=
    LinearEquiv.ofBijective (tensorComparison R (sectionFunctor J R U) M Q)
      (by
        let := hQ
        exact tensorComparison_bijective R (sectionFunctor J R U) M Q)
  refine ⟨?_, ⟨e, ?_, ?_, ?_⟩, ?_⟩
  · intro A B D f g hf hfg hg U
    exact ⟨section_injective J R f hf U, section_exact J R f g hf hfg hg U,
      section_surjective J R g hg U⟩
  · intro M Q hQ U s q
    rfl
  · intro M M' Q Q' hQ hQ' f g U z
    exact LinearMap.congr_fun (tensorComparison_naturality R (sectionFunctor J R U) f g) z
  · intro M Q hQ U V h z
    change tensorComparison R (sectionFunctor J R V) M Q
        (TensorProduct.map
          (((constantSheaf J (ModuleCat.{u} R)).obj M).obj.map h.op).hom
          (LinearMap.id : Q →ₗ[R] Q) z) =
      (((constantSheaf J (ModuleCat.{u} R)).obj
        (ModuleCat.of R (M ⊗[R] Q))).obj.map h.op)
        (tensorComparison R (sectionFunctor J R U) M Q z)
    induction z using TensorProduct.inductionOn with
    | tmul s q =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, tensorComparison_tmul]
      exact (NatTrans.naturality_apply
        ((constantSheaf J (ModuleCat.{u} R)).map
          (ModuleCat.ofHom ((TensorProduct.mk R M Q).flip q))).hom h.op s)
    | add z w hz hw => simp only [map_add, hz, hw]
  · intro M hM U
    let := hM
    apply Module.Flat.iff_lTensor_injective.mpr
    intro I hI
    let Q := ModuleCat.of R I
    let Q' := ModuleCat.of R R
    let f : Q ⟶ Q' := ModuleCat.ofHom I.subtype
    let : Module.FinitePresentation R I := Module.finitePresentation_of_finite R I
    have hinj : Function.Injective (LinearMap.lTensor M I.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap I.subtype I.injective_subtype
    have hi := section_injective J R
      (ModuleCat.ofHom (LinearMap.lTensor M I.subtype)) hinj U
    have hnat := tensorComparison_naturality R (sectionFunctor J R U) (𝟙 M) f
    have hbij := tensorComparison_bijective R (sectionFunctor J R U) M Q
    intro x y hxy
    apply hbij.1
    apply hi
    have hx := LinearMap.congr_fun hnat x
    have hy := LinearMap.congr_fun hnat y
    simp only [Functor.map_id, ModuleCat.hom_id, LinearMap.comp_apply] at hx hy
    exact hx.symm.trans ((congrArg (tensorComparison R (sectionFunctor J R U) M Q')
      hxy).trans hy)

end

end CategoryTheory
