/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Pi
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The relation criterion for flatness of sheaves of modules

A presheaf of modules over a commutative ring `R` *has locally trivial relations*
(`CategoryTheory.Presheaf.HasLocallyTrivialRelations`) if every finite system of `R`-linear
relations `∑ⱼ eₗⱼ yⱼ = 0` between sections `yⱼ` over `V` is trivial locally on `V`: there the
`yⱼ` are combinations `yⱼ = ∑ₘ bⱼₘ zₘ` with `∑ⱼ eₗⱼ bⱼₘ = 0`. This is the local form of the
equational criterion for flatness, and over a Noetherian ring it characterizes flat sheaves
(`CategoryTheory.Sheaf.flat_iff_hasLocallyTrivialRelations`).

* If `P` has locally trivial relations, its sheafification is flat
  (`CategoryTheory.Presheaf.flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations`): a section
  `∑ₖ mₖ ⊗ gₖ` of `P ⊗ M` killed in `P ⊗ N` vanishes through finitely many relations between
  the `mₖ` (`TensorProduct.exists_relations_of_sum_tmul_eq_zero`), which are locally trivial, so
  tensoring with `P` is locally injective.
* If `F` is flat, tensoring the exact sequence `R^t ⟶ R^s ⟶ R^q` (the kernel of `e` being
  finitely generated) with `F` gives an exact sequence of sheaves, the sheafification of
  `F(-) ⊗ R^t ⟶ F(-) ⊗ R^s ⟶ F(-) ⊗ R^q`; exactness of the sheafification means local
  exactness of the presheaves
  (`CategoryTheory.Presheaf.imageSieve_mem_of_exact_map_presheafToSheaf`), which is the local
  triviality of the relations (`CategoryTheory.Sheaf.hasLocallyTrivialRelations_of_flat`).

## Main results

- `CategoryTheory.Sheaf.imageSieve_mem_of_exact`: in an exact sequence of sheaves of modules,
  a section of the middle term killed by the second map is locally in the image of the first.
- `CategoryTheory.Presheaf.imageSieve_mem_of_exact_map_presheafToSheaf`: the same for a short
  complex of presheaves whose sheafification is exact.
- `CategoryTheory.Presheaf.flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations` and
  `CategoryTheory.Sheaf.hasLocallyTrivialRelations_of_flat`: the two directions of the relation
  criterion `CategoryTheory.Sheaf.flat_iff_hasLocallyTrivialRelations`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

namespace CategoryTheory

section LocalExactness

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Type w} [Ring R] [HasSheafify J (ModuleCat.{w} R)]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))] [J.WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- **Exact sequences of sheaves are locally exact on sections.** If `S` is an exact short
complex of sheaves of modules and `x` is a section of `S.X₂` over `V` killed by `S.g`, then `x`
is locally in the image of `S.f`. -/
theorem Sheaf.imageSieve_mem_of_exact {S : ShortComplex (Sheaf J (ModuleCat.{w} R))}
    (hS : S.Exact) {V : C} (x : S.X₂.obj.obj (op V)) (hx : S.g.hom.app (op V) x = 0) :
    Presheaf.imageSieve S.f.hom x ∈ J V := by
  have := hS.epi_toCycles
  have : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := S.toCycles)).2 this
  -- lift `x` to a section `c` of the cycles, a kernel of `S.g` computed sectionwise
  let E : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
    sheafToPresheaf J _ ⋙ (evaluation _ _).obj (op V)
  let hk := KernelFork.mapIsLimit _ S.cyclesIsKernel E
  let φ : ModuleCat.of R R ⟶ E.obj S.X₂ := ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x)
  have hφ : φ ≫ E.map S.g = 0 :=
    ModuleCat.hom_ext (LinearMap.ext_ring (by simpa [φ, E] using hx))
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hk φ hφ
  let c : ToType (S.cycles.obj.obj (op V)) := l (1 : R)
  have hc : S.iCycles.hom.app (op V) c = x := by
    have h := ConcreteCategory.congr_hom hl (1 : R)
    simp only [φ, E] at h
    rw [ConcreteCategory.comp_apply] at h
    exact h.trans (by simp)
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J S.toCycles.hom c)
  rintro W f ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have h := congrArg (fun g ↦ g.hom.app (op W) z) S.toCycles_i
  dsimp only at h
  rw [← h, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, hz,
    NatTrans.naturality_apply, hc]

/-- **Short complexes of presheaves with exact sheafification are locally exact.** If `S` is a
short complex of presheaves of modules whose sheafification is exact and `x` is a section of
`S.X₂` over `V` killed by `S.g`, then `x` is locally in the image of `S.f`. -/
theorem Presheaf.imageSieve_mem_of_exact_map_presheafToSheaf
    {S : ShortComplex (Cᵒᵖ ⥤ ModuleCat.{w} R)} (hS : (S.map (presheafToSheaf J _)).Exact)
    {V : C} (x : S.X₂.obj (op V)) (hx : S.g.app (op V) x = 0) :
    Presheaf.imageSieve S.f x ∈ J V := by
  let x' := (toSheafify J S.X₂).app (op V) x
  have hx' : ((presheafToSheaf J _).map S.g).hom.app (op V) x' = 0 := by
    have := ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality J S.g) (op V)) x
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
    rw [← this, hx, map_zero]
  refine J.transitive (Sheaf.imageSieve_mem_of_exact hS x' hx') _ ?_
  rintro W f ⟨z', hz'⟩
  refine J.transitive (Presheaf.imageSieve_mem J (toSheafify J S.X₁) z') _ ?_
  rintro U g ⟨z₀, hz₀⟩
  -- `S.f z₀` and the restriction of `x` agree after sheafification, hence locally
  have heq : (toSheafify J S.X₂).app (op U) (S.f.app (op U) z₀) =
      (toSheafify J S.X₂).app (op U) (S.X₂.map (g ≫ f).op x) := by
    have h₁ := ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality J S.f) (op U)) z₀
    have h₂ := NatTrans.naturality_apply (toSheafify J S.X₂) (g ≫ f).op x
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h₁
    rw [h₁, hz₀, NatTrans.naturality_apply, NatTrans.naturality_apply (toSheafify J S.X₂),
      show (sheafifyMap J S.f).app (op W) z' = _ from hz', op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply]
    rfl
  refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J (toSheafify J S.X₂) _ _ heq)
  intro U' h hh
  refine ⟨S.X₁.map h.op z₀, ?_⟩
  change S.X₂.map h.op _ = S.X₂.map h.op _ at hh
  rw [NatTrans.naturality_apply, hh, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp only [op_comp, Category.assoc]

end LocalExactness

section Flat

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]

variable (J) in
/-- A presheaf of `R`-modules *has locally trivial relations* if every finite family of sections
`y : Fin s → P(V)` satisfying `R`-linear relations `∑ⱼ eₗⱼ yⱼ = 0` is, locally on `V`, an
`R`-linear combination `yⱼ = ∑ₘ bⱼₘ zₘ` of sections with `e * b = 0`. This is the local form of
the equational criterion for flatness. -/
def Presheaf.HasLocallyTrivialRelations (P : Cᵒᵖ ⥤ ModuleCat.{u + 1} R) : Prop :=
  ∀ ⦃V : C⦄ {s q : ℕ} (y : Fin s → P.obj (op V)) (e : Matrix (Fin q) (Fin s) R),
    (∀ l, ∑ j, e l j • y j = 0) → ∃ T ∈ J V, ∀ ⦃W : C⦄ (f : W ⟶ V), T f →
      ∃ (t : ℕ) (b : Matrix (Fin s) (Fin t) R) (z : Fin t → P.obj (op W)),
        e * b = 0 ∧ ∀ j, P.map f.op (y j) = ∑ m, b j m • z m

omit [EssentiallySmall.{u + 1} C] in
/-- Locally trivial relations, for families and relations indexed by arbitrary finite types. -/
lemma Presheaf.HasLocallyTrivialRelations.exists_of_fintype {P : Cᵒᵖ ⥤ ModuleCat.{u + 1} R}
    (hP : Presheaf.HasLocallyTrivialRelations J P) {V : C} {ι κ : Type} [Fintype ι] [Finite κ]
    (y : ι → P.obj (op V)) (e : Matrix κ ι R) (he : ∀ l, ∑ j, e l j • y j = 0) :
    ∃ T ∈ J V, ∀ ⦃W : C⦄ (f : W ⟶ V), T f →
      ∃ (t : ℕ) (b : Matrix ι (Fin t) R) (z : Fin t → P.obj (op W)),
        e * b = 0 ∧ ∀ j, P.map f.op (y j) = ∑ m, b j m • z m := by
  have := Fintype.ofFinite κ
  let eι := Fintype.equivFin ι
  let eκ := Fintype.equivFin κ
  obtain ⟨T, hT, hfac⟩ := hP (y ∘ eι.symm) (fun l n ↦ e (eκ.symm l) (eι.symm n)) (fun l ↦ by
    rw [← he (eκ.symm l)]
    exact Fintype.sum_equiv eι.symm _ _ fun _ ↦ rfl)
  refine ⟨T, hT, fun W f hf ↦ ?_⟩
  obtain ⟨t, b, z, heb, hyz⟩ := hfac f hf
  refine ⟨t, fun j m ↦ b (eι j) m, z, ?_, fun j ↦ ?_⟩
  · ext l m
    have := congrFun (congrFun heb (eκ l)) m
    simp only [Matrix.mul_apply, Equiv.symm_apply_apply, Matrix.zero_apply] at this ⊢
    rw [← this]
    exact Fintype.sum_equiv eι _ _ fun _ ↦ by simp
  · simpa using hyz (eι j)

omit [EssentiallySmall.{u + 1} C] in
/-- **Tensoring with a presheaf with locally trivial relations is locally injective.** If `P`
has locally trivial relations and `M ⟶ N` is an injection of presheaves of modules, a section
of `P ⊗ M` killed in `P ⊗ N` vanishes locally. -/
theorem Presheaf.equalizerSieve_whiskerLeft_mem {P : Cᵒᵖ ⥤ ModuleCat.{u + 1} R}
    (hP : Presheaf.HasLocallyTrivialRelations J P)
    {M N : Cᵒᵖ ⥤ ModuleCat.{u + 1} R} (g : M ⟶ N) (hg : ∀ U, Function.Injective (g.app U))
    {U : C} (t : (P ⊗ M).obj (op U)) (ht : (P ◁ g).app (op U) t = 0) :
    Presheaf.equalizerSieve t 0 ∈ J U := by
  classical
  -- `t = ∑ₖ mₖ ⊗ g'ₖ`, and its image `∑ₖ mₖ ⊗ g(g'ₖ)` vanishes through finitely many relations
  obtain ⟨n, m, g', htm⟩ :=
    TensorProduct.exists_sum_tmul_eq (t : P.obj (op U) ⊗[R] M.obj (op U))
  have ht₀ : ∑ k, m k ⊗ₜ[R] g.app (op U) (g' k) = 0 := by
    have : (LinearMap.lTensor _ (g.app (op U)).hom) (t : P.obj (op U) ⊗[R] M.obj (op U)) = 0 :=
      ht
    rw [htm] at this
    simpa [map_sum] using this
  obtain ⟨s, q, y, a, e, hma, hey, hab⟩ :=
    TensorProduct.exists_relations_of_sum_tmul_eq_zero m (fun k ↦ g.app (op U) (g' k)) ht₀
  -- rewrite `t = ∑ⱼ yⱼ ⊗ g''ⱼ`; every solution of the relations `e` kills `g''`
  let g'' : Fin s → M.obj (op U) := fun j ↦ ∑ k, a k j • g' k
  have ht' : (t : P.obj (op U) ⊗[R] M.obj (op U)) = ∑ j, y j ⊗ₜ[R] g'' j := by
    rw [htm]
    simp only [g'', hma, TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
    exact Finset.sum_comm
  have hg'' (c : Fin s → R) (hc : ∀ l, ∑ j, e l j * c j = 0) : ∑ j, c j • g'' j = 0 := by
    refine hg (op U) ?_
    rw [map_zero, ← hab c hc]
    simp only [g'', map_sum, map_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  -- locally the relations `e` between the `yⱼ` are trivial, and then `t` vanishes
  obtain ⟨T, hT, hfac⟩ := hP y e hey
  refine J.superset_covering ?_ hT
  intro U' h hh
  obtain ⟨t', b, z, heb, hyz⟩ := hfac h hh
  change (P ⊗ M).map h.op t = (P ⊗ M).map h.op 0
  rw [map_zero]
  change (TensorProduct.map (P.map h.op).hom (M.map h.op).hom)
    (t : P.obj (op U) ⊗[R] M.obj (op U)) = 0
  rw [ht']
  simp only [map_sum, TensorProduct.map_tmul]
  simp_rw [hyz, TensorProduct.sum_tmul, TensorProduct.smul_tmul]
  rw [Finset.sum_comm]
  simp_rw [← TensorProduct.tmul_sum, ← map_smul, ← map_sum]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [hg'' (fun j ↦ b j m) (fun l ↦ by simpa [Matrix.mul_apply] using congrFun (congrFun heb l) m),
    map_zero, TensorProduct.tmul_zero]

omit [EssentiallySmall.{u + 1} C] in
/-- **Tensoring with a presheaf with locally trivial relations is locally injective.** -/
theorem Presheaf.isLocallyInjective_whiskerLeft {P : Cᵒᵖ ⥤ ModuleCat.{u + 1} R}
    (hP : Presheaf.HasLocallyTrivialRelations J P)
    {M N : Cᵒᵖ ⥤ ModuleCat.{u + 1} R} (g : M ⟶ N) (hg : ∀ U, Function.Injective (g.app U)) :
    Presheaf.IsLocallyInjective J (P ◁ g) where
  equalizerSieve_mem {U} x y hxy := by
    have h := Presheaf.equalizerSieve_whiskerLeft_mem hP g hg (U := U.unop) (x - y)
      (by rw [map_sub, hxy, sub_self])
    refine J.superset_covering ?_ h
    intro U' f hf
    change _ = _ at hf
    rw [map_sub, map_zero, sub_eq_zero] at hf
    exact hf

variable [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]

/-- **Relation criterion for flatness.** The sheafification of a presheaf of modules with locally
trivial relations is flat: tensoring with it is the sheafification of tensoring with the
presheaf, which turns injections into locally injective maps
(`CategoryTheory.Presheaf.isLocallyInjective_whiskerLeft`), and sheafification turns these into
monomorphisms. -/
theorem Presheaf.flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations
    {P : Cᵒᵖ ⥤ ModuleCat.{u + 1} R} (hP : Presheaf.HasLocallyTrivialRelations J P) :
    ObjectProperty.flat ((presheafToSheaf J _).obj P) := by
  rw [ObjectProperty.flat_iff_preservesFiniteLimits,
    Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  refine ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, ?_⟩
  have := hS.mono_f
  let g := S.f
  -- `g` is injective on sections
  have hg : ∀ U, Function.Injective (g.hom.app U) := fun U ↦ by
    have : Mono g.hom := (sheafToPresheaf J _).map_mono g
    rw [← ModuleCat.mono_iff_injective]
    infer_instance
  -- `P^# ◁ g` is, up to isomorphism, the sheafification of `P ◁ g`
  have : Presheaf.IsLocallyInjective J (P ◁ g.hom) :=
    Presheaf.isLocallyInjective_whiskerLeft hP g.hom hg
  have : Sheaf.IsLocallyInjective ((presheafToSheaf J _).map (P ◁ g.hom)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J (P ◁ g.hom)).2 this
  have : Mono ((presheafToSheaf J _).map (P ◁ g.hom)) := Sheaf.mono_of_isLocallyInjective _
  let μ := Sheaf.presheafToSheafCompTensorLeftIso (J := J) (A := ModuleCat.{u + 1} R) P
  have h₁ : (presheafToSheaf J _).obj P ◁ (presheafToSheaf J _).map g.hom =
      μ.hom.app _ ≫ (presheafToSheaf J _).map (P ◁ g.hom) ≫ μ.inv.app _ := by
    have hn := μ.hom.naturality g.hom
    change _ ◁ _ ≫ _ = _ ≫ (presheafToSheaf J _).map (P ◁ g.hom) at hn
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  let ε := (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit
  have h₂ : g = inv (ε.app S.X₁) ≫ (presheafToSheaf J _).map g.hom ≫ ε.app S.X₂ := by
    rw [IsIso.eq_inv_comp]
    exact (ε.naturality g).symm
  change Mono ((presheafToSheaf J _).obj P ◁ g)
  rw [h₂, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp, h₁]
  infer_instance

variable [IsNoetherianRing R]

/-- **Linear relations between sections of a flat sheaf are locally trivial.** Let `F` be a
flat sheaf of modules over a Noetherian commutative ring `R`, and let `y : Fin s → F(V)` satisfy
the relations `∑ⱼ eₗⱼ yⱼ = 0`. Then locally on `V` there are a matrix `b` with `e * b = 0` and
sections `z` with `yⱼ = ∑ₘ bⱼₘ zₘ`.

This is the sheaf version of the equational criterion for flatness
(`Module.Flat.iff_forall_exists_factorization`). -/
theorem Sheaf.hasLocallyTrivialRelations_of_flat {F : Sheaf J (ModuleCat.{u + 1} R)}
    (hF : ObjectProperty.flat F) : Presheaf.HasLocallyTrivialRelations J F.obj := by
  intro V s q y e he
  classical
  -- the exact sequence `R^t ⟶ R^s ⟶ R^q`, with `R^t ⟶ R^s` generating the kernel of `e`
  let φ := e.mulVecLin
  obtain ⟨t, gens, hgens⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (LinearMap.ker φ))
  let b : Matrix (Fin s) (Fin t) R := Matrix.of fun j m ↦ gens m j
  have hb : LinearMap.range b.mulVecLin = LinearMap.ker φ := by
    rw [Matrix.range_mulVecLin, ← hgens]
    rfl
  have heb : e * b = 0 := by
    ext l m
    have : gens m ∈ LinearMap.ker φ := hgens ▸ Submodule.subset_span ⟨m, rfl⟩
    have := congrFun (LinearMap.mem_ker.1 this) l
    simpa [φ, b, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  let S₀ := ShortComplex.moduleCatMkOfKerLERange (ModuleCat.ofHom b.mulVecLin)
    (ModuleCat.ofHom φ) (by rw [ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, hb])
  have hS₀ : S₀.Exact := ShortComplex.Exact.moduleCat_of_range_eq_ker _ _ hb
  -- tensoring with `F` keeps it exact, and computes the sheafification of `F(-) ⊗ R^n`
  have : PreservesFiniteLimits (tensorLeft F) := hF.tensorLeft.1
  have : PreservesFiniteColimits (tensorLeft F) := hF.tensorLeft.2
  let Φ : ModuleCat.{u + 1} R ⥤ Sheaf J (ModuleCat.{u + 1} R) :=
    Functor.const Cᵒᵖ ⋙ tensorLeft F.obj ⋙ presheafToSheaf J _
  let eΦ : constantSheaf J (ModuleCat.{u + 1} R) ⋙ tensorLeft F ≅ Φ :=
    Functor.isoWhiskerLeft _ ((curriedTensor _).mapIso
        (asIso ((sheafificationAdjunction J _).counit.app F)).symm) ≪≫
      Functor.isoWhiskerLeft (Functor.const Cᵒᵖ)
        (Sheaf.presheafToSheafCompTensorLeftIso F.obj)
  have : PreservesFiniteLimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
    comp_preservesFiniteColimits _ _
  have hS : (S₀.map Φ).Exact :=
    (ShortComplex.exact_iff_of_iso (S₀.mapNatIso eΦ)).1
      ((hS₀.map (constantSheaf J _)).map (tensorLeft F))
  let Sp := S₀.map (Functor.const Cᵒᵖ ⋙ tensorLeft F.obj)
  -- the section `∑ⱼ yⱼ ⊗ eⱼ` of `F(V) ⊗ R^s` is killed by `e`
  let x : Sp.X₂.obj (op V) := ∑ j, y j ⊗ₜ[R] (Pi.single j 1 : Fin s → R)
  have hx : Sp.g.app (op V) x = 0 := by
    refine (TensorProduct.piScalarRight R R _ (Fin q)).injective ?_
    ext l
    change TensorProduct.piScalarRight R R _ (Fin q) (φ.lTensor _ x) l = 0
    rw [TensorProduct.piScalarRight_lTensor_mulVecLin, TensorProduct.piScalarRight_sum_tmul_single]
    simpa using he l
  refine ⟨_, Presheaf.imageSieve_mem_of_exact_map_presheafToSheaf hS x hx, ?_⟩
  rintro W f ⟨z₀, hz₀⟩
  refine ⟨t, b, TensorProduct.piScalarRight R R _ (Fin t) z₀, heb, fun j ↦ ?_⟩
  have hz := congrArg (fun w ↦ TensorProduct.piScalarRight R R _ (Fin s) w j) hz₀
  change TensorProduct.piScalarRight R R _ (Fin s) (b.mulVecLin.lTensor _ z₀) j =
    TensorProduct.piScalarRight R R _ (Fin s)
      (TensorProduct.map (F.obj.map f.op).hom LinearMap.id x) j at hz
  rw [TensorProduct.piScalarRight_lTensor_mulVecLin] at hz
  rw [hz]
  simp [x, map_sum, Pi.single_apply]

/-- **Relation criterion for flatness of sheaves of modules.** A sheaf of modules over a
Noetherian commutative ring is flat if and only if linear relations between its sections are
locally trivial. -/
theorem Sheaf.flat_iff_hasLocallyTrivialRelations (F : Sheaf J (ModuleCat.{u + 1} R)) :
    ObjectProperty.flat F ↔ Presheaf.HasLocallyTrivialRelations J F.obj :=
  ⟨Sheaf.hasLocallyTrivialRelations_of_flat, fun h ↦ ObjectProperty.prop_of_iso _
    (asIso ((sheafificationAdjunction J _).counit.app F))
    (Presheaf.flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations h)⟩

end Flat

end CategoryTheory
