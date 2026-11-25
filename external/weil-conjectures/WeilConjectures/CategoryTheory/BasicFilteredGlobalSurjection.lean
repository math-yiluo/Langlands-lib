/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! The explicit basic complex `P₀` and its map `f₀` of Stacks Tag 0H7X.
Global and filtered cocycles index a free zero-differential complex, with the filtration
spanned by the filtered generators whose step index is at least the filtration index.
(blueprint: lem-pur-kunneth-basic-filtered-surjection-global)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open Module
namespace CategoryTheory

abbrev P0Cycle (R : Type u) [CommRing R]
    (K : WeilFilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (n : ℤ) :=
  {z : K.obj.X n // K.obj.d n (n + 1) z = 0}

abbrev P0StepCycle (R : Type u) [CommRing R]
    (K : WeilFilteredObject (CochainComplex (ModuleCat.{u} R) ℤ))
    (j n : ℤ) :=
  {z : K.obj.X n // (∃ x : (K.filtration.step j : CochainComplex (ModuleCat.{u} R) ℤ).X n,
      (K.filtration.step j).arrow.f n x = z) ∧ K.obj.d n (n + 1) z = 0}

abbrev P0Index (R : Type u) [CommRing R]
    (K : WeilFilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (n : ℤ) :=
  P0Cycle R K n ⊕ (Σ j : ℤ, P0StepCycle R K j n)

noncomputable def P0Index.map (R : Type u) [CommRing R]
    (K : WeilFilteredObject (CochainComplex (ModuleCat.{u} R) ℤ))
    (n : ℤ) : P0Index R K n → K.obj.X n := fun z =>
  match z with
  | Sum.inl z => z.1
  | Sum.inr z => z.2.1

/-- The cochain complex which is free on `ι n` in degree `n`, with zero differential.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, construction of `P₀` (blueprint: lem-pur-kunneth-basic-filtered-surjection-global). -/
noncomputable def freeZeroComplex (R : Type u) [CommRing R] (ι : ℤ → Type u) :
    CochainComplex (ModuleCat.{u} R) ℤ where
  X n := ModuleCat.of R (ι n →₀ R)
  d _ _ := 0

@[simp]
lemma freeZeroComplex_d (R : Type u) [CommRing R] (ι : ℤ → Type u) (n m : ℤ) :
    (freeZeroComplex R ι).d n m = 0 :=
  rfl

instance (R : Type u) [CommRing R] (ι : ℤ → Type u) (n : ℤ) :
    Module.Free R ((freeZeroComplex R ι).X n) :=
  inferInstanceAs (Module.Free R (ι n →₀ R))

/-- The map of free zero-differential complexes induced by maps of the generators.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, construction of `P₀` (blueprint: lem-pur-kunneth-basic-filtered-surjection-global). -/
noncomputable def freeZeroComplexMap (R : Type u) [CommRing R] {ι ι' : ℤ → Type u}
    (g : ∀ n, ι n → ι' n) : freeZeroComplex R ι ⟶ freeZeroComplex R ι' where
  f n := ModuleCat.ofHom (Finsupp.lmapDomain R R (g n))

@[simp]
lemma freeZeroComplexMap_f_apply (R : Type u) [CommRing R] {ι ι' : ℤ → Type u}
    (g : ∀ n, ι n → ι' n) (n : ℤ) (x : ι n →₀ R) :
    (freeZeroComplexMap R g).f n x = Finsupp.mapDomain (g n) x :=
  rfl

lemma freeZeroComplexMap_comp (R : Type u) [CommRing R] {ι ι' ι'' : ℤ → Type u}
    (g : ∀ n, ι n → ι' n) (g' : ∀ n, ι' n → ι'' n) :
    freeZeroComplexMap R g ≫ freeZeroComplexMap R g' =
      freeZeroComplexMap R (fun n ↦ g' n ∘ g n) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [HomologicalComplex.comp_f]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  exact (Finsupp.mapDomain_comp).symm

lemma mono_freeZeroComplexMap (R : Type u) [CommRing R] {ι ι' : ℤ → Type u}
    (g : ∀ n, ι n → ι' n) (hg : ∀ n, Function.Injective (g n)) :
    Mono (freeZeroComplexMap R g) :=
  HomologicalComplex.mono_of_mono_f _ fun n ↦
    (ModuleCat.mono_iff_injective _).2 (Finsupp.mapDomain_injective (hg n))

/-- A chain map into a complex `M` whose components factor through a monomorphism `L ⟶ M`
factors through `L` as a chain map.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, filtration of `P₀` (blueprint: lem-pur-kunneth-basic-filtered-surjection-global). -/
theorem HomologicalComplex.exists_lift_of_degreewise_lift {V : Type*} [Category* V]
    [Abelian V] {ι : Type*} {c : ComplexShape ι} {A L M : HomologicalComplex V c}
    (i : L ⟶ M) [Mono i] (φ : A ⟶ M) (h : ∀ n, A.X n ⟶ L.X n)
    (hh : ∀ n, h n ≫ i.f n = φ.f n) : ∃ ψ : A ⟶ L, ψ ≫ i = φ := by
  refine ⟨{ f := h, comm' := fun p q _ ↦ ?_ }, ?_⟩
  · rw [← cancel_mono (i.f q), Category.assoc, Category.assoc, hh, ← i.comm,
      ← Category.assoc, hh]
    exact φ.comm p q
  · ext n : 1
    exact hh n

/-- A cocycle of a cochain complex of modules lifts to the cycles object.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, surjectivity of `f₀` on cohomology
(blueprint: lem-pur-kunneth-basic-filtered-surjection-global). -/
theorem CochainComplex.exists_iCycles_eq_of_d_eq_zero {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (x : L.X n)
    (hx : L.d n (n + 1) x = 0) : ∃ z : L.cycles n, L.iCycles n z = x := by
  have hx' : (L.sc n).g x = 0 := by
    refine (fun (j : ℤ) (hj : (ComplexShape.up ℤ).next n = j) (hx : L.d n j x = 0) ↦ ?_) _
      (CochainComplex.next ℤ n) hx
    subst hj
    exact hx
  exact ⟨(L.sc n).moduleCatCyclesIso.inv ⟨x, hx'⟩,
    ConcreteCategory.congr_hom (L.sc n).moduleCatCyclesIso_inv_iCycles ⟨x, hx'⟩⟩

/-- A chain map of cochain complexes of modules is surjective on `Hⁿ` as soon as every
`n`-cocycle of the target is the image of an `n`-cocycle of the source.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, surjectivity of `f₀` on cohomology
(blueprint: lem-pur-kunneth-basic-filtered-surjection-global). -/
theorem CochainComplex.epi_homologyMap_of_forall_cocycle {R : Type u} [CommRing R]
    {L M : CochainComplex (ModuleCat.{u} R) ℤ} (φ : L ⟶ M) (n : ℤ)
    (h : ∀ x : M.X n, M.d n (n + 1) x = 0 →
      ∃ y : L.X n, L.d n (n + 1) y = 0 ∧ φ.f n y = x) :
    Epi (HomologicalComplex.homologyMap φ n) := by
  rw [ModuleCat.epi_iff_surjective]
  intro a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (M.homologyπ n)).mp inferInstance a
  have hz : M.d n (n + 1) (M.iCycles n z) = 0 := by
    rw [← ModuleCat.comp_apply]
    simp
  obtain ⟨y, hy, hyx⟩ := h _ hz
  obtain ⟨c, hc⟩ := exists_iCycles_eq_of_d_eq_zero L n y hy
  have hcmap : HomologicalComplex.cyclesMap φ n c = z := by
    apply (ModuleCat.mono_iff_injective (M.iCycles n)).mp inferInstance
    have hw := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ n) c
    simpa only [ModuleCat.comp_apply, hc, hyx] using hw
  refine ⟨L.homologyπ n c, ?_⟩
  have hw := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ n) c
  simpa only [ModuleCat.comp_apply, hcmap] using hw

lemma Subobject.ofLE_arrow_f_apply {R : Type u} [CommRing R]
    {L : CochainComplex (ModuleCat.{u} R) ℤ} {X Y : Subobject L} (h : X ≤ Y) (n : ℤ)
    (x : (X : CochainComplex (ModuleCat.{u} R) ℤ).X n) :
    Y.arrow.f n ((Subobject.ofLE X Y h).f n x) = X.arrow.f n x := by
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]

variable (R : Type u) [CommRing R] (K : WeilFilteredObject (CochainComplex (ModuleCat.{u} R) ℤ))

/-- The generators of `F^i P₀` in degree `n`: the filtered cocycles of `F^j K` with `j ≥ i`.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, construction of `P₀` (blueprint: lem-pur-kunneth-basic-filtered-surjection-global). -/
abbrev P0StepIndex (i n : ℤ) :=
  {z : Σ j : ℤ, P0StepCycle R K j n // i ≤ z.1}

/-- The basic complex `P₀`: free on all global and filtered cocycles of `K`, with zero
differential.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, construction of `P₀` (blueprint: lem-pur-kunneth-basic-filtered-surjection-global). -/
noncomputable abbrev P0Complex : CochainComplex (ModuleCat.{u} R) ℤ :=
  freeZeroComplex R (P0Index R K)

/-- The model of `F^i P₀`, free on the generators of `P0StepIndex`.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, construction of `P₀` (blueprint: lem-pur-kunneth-basic-filtered-surjection-global). -/
noncomputable abbrev P0StepComplex (i : ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  freeZeroComplex R (P0StepIndex R K i)

/-- The inclusion of the model of `F^i P₀` into `P₀`. -/
noncomputable abbrev P0StepComplex.ι (i : ℤ) : P0StepComplex R K i ⟶ P0Complex R K :=
  freeZeroComplexMap R fun _ z ↦ Sum.inr z.1

instance (i : ℤ) : Mono (P0StepComplex.ι R K i) :=
  mono_freeZeroComplexMap R _ fun _ ↦ Sum.inr_injective.comp Subtype.val_injective

/-- The inclusion of the model of `F^{i'} P₀` into the model of `F^i P₀` for `i ≤ i'`. -/
noncomputable abbrev P0StepComplex.ofLE {i i' : ℤ} (h : i ≤ i') :
    P0StepComplex R K i' ⟶ P0StepComplex R K i :=
  freeZeroComplexMap R fun _ z ↦ ⟨z.1, h.trans z.2⟩

instance {i i' : ℤ} (h : i ≤ i') : Mono (P0StepComplex.ofLE R K h) :=
  mono_freeZeroComplexMap R _ fun _ _ _ hzz ↦ Subtype.ext (Subtype.mk.inj hzz)

lemma P0StepComplex.ofLE_ι {i i' : ℤ} (h : i ≤ i') :
    P0StepComplex.ofLE R K h ≫ P0StepComplex.ι R K i = P0StepComplex.ι R K i' := by
  rw [freeZeroComplexMap_comp]
  rfl

/-- The filtration of `P₀`: `F^i P₀` is the span of the generators of `P0StepIndex`. -/
noncomputable def P0Filtration : DecreasingFiltration (P0Complex R K) where
  F i := Subobject.mk (P0StepComplex.ι R K i)
  F_succ_le i := Subobject.mk_le_mk_of_comm (P0StepComplex.ofLE R K (show i ≤ i + 1 by omega))
    (P0StepComplex.ofLE_ι R K _)

/-- The filtered basic complex `P₀`. -/
noncomputable def P0Filtered : WeilFilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) where
  obj := P0Complex R K
  filtration := P0Filtration R K

/-- The map `f₀ : P₀ ⟶ K`, sending each generator to the cocycle that indexes it.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof (blueprint: lem-pur-kunneth-basic-filtered-surjection-global). -/
noncomputable def P0Map : P0Complex R K ⟶ K.obj where
  f n := ModuleCat.ofHom (Finsupp.linearCombination R (P0Index.map R K n))
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    have h : ModuleCat.ofHom (Finsupp.linearCombination R (P0Index.map R K p)) ≫
        K.obj.d p (p + 1) = 0 := by
      refine ModuleCat.hom_ext (Finsupp.lhom_ext fun z a => ?_)
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        Finsupp.linearCombination_single]
      cases z with
      | inl z =>
        simp only [P0Index.map, map_smul]
        exact (congrArg (a • ·) z.2).trans (smul_zero a)
      | inr z =>
        simp only [P0Index.map, map_smul]
        exact (congrArg (a • ·) z.2.2.2).trans (smul_zero a)
    refine h.trans ?_
    rw [freeZeroComplex_d]
    exact zero_comp.symm

lemma P0Map_f_single (n : ℤ) (z : P0Index R K n) :
    (P0Map R K).f n (Finsupp.single z 1) = P0Index.map R K n z := by
  exact (Finsupp.linearCombination_single R 1 z).trans (one_smul R _)

/-- `f₀` is a morphism of filtered complexes. -/
theorem P0Map_preserves (i : ℤ) : ∃ lift : ((P0Filtered R K).filtration.F i :
    CochainComplex (ModuleCat.{u} R) ℤ) ⟶ 
    (K.filtration.F i : CochainComplex (ModuleCat.{u} R) ℤ),
    lift ≫ (K.filtration.F i).arrow = ((P0Filtered R K).filtration.F i).arrow ≫ P0Map R K := by
  obtain ⟨ψ, hψ⟩ := HomologicalComplex.exists_lift_of_degreewise_lift
    (K.filtration.F i).arrow (P0StepComplex.ι R K i ≫ P0Map R K)
    (fun n ↦ ModuleCat.ofHom (Finsupp.linearCombination R fun z : P0StepIndex R K i n ↦
      (Subobject.ofLE (K.filtration.F z.1.1) (K.filtration.F i)
        (K.filtration.antitone z.2)).f n z.1.2.2.1.choose))
    (fun n ↦ ModuleCat.hom_ext (Finsupp.lhom_ext fun z a ↦ by
      obtain ⟨⟨j, v, hv, hd⟩, hij⟩ := z
      have h := Subobject.ofLE_arrow_f_apply (K.filtration.antitone hij) n hv.choose
      have e0 : (ModuleCat.ofHom (Finsupp.linearCombination R fun z : P0StepIndex R K i n ↦
          (Subobject.ofLE (K.filtration.F z.1.1) (K.filtration.F i)
            (K.filtration.antitone z.2)).f n z.1.2.2.1.choose) ≫ (K.filtration.F i).arrow.f n)
          (Finsupp.single ⟨⟨j, v, hv, hd⟩, hij⟩ a) = a • v := by
        erw [ModuleCat.comp_apply, ModuleCat.ofHom_apply, Finsupp.linearCombination_single,
          map_smul]
        exact congrArg (a • ·) (h.trans hv.choose_spec)
      have e1 : (P0StepComplex.ι R K i ≫ P0Map R K).f n
          (Finsupp.single ⟨⟨j, v, hv, hd⟩, hij⟩ a) = a • v := by
        erw [HomologicalComplex.comp_f, ModuleCat.comp_apply, freeZeroComplexMap_f_apply,
          Finsupp.mapDomain_single]
        exact Finsupp.linearCombination_single R a _
      exact e0.trans e1.symm))
  refine ⟨(Subobject.underlyingIso (P0StepComplex.ι R K i)).hom ≫ ψ,
    (Category.assoc _ _ _).trans ?_⟩
  rw [hψ]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ P0Map R K) (Subobject.underlyingIso_hom_comp_eq_mk _))

/-- `f₀` is surjective on cohomology in every degree.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof (blueprint: lem-pur-kunneth-basic-filtered-surjection-global). -/
theorem epi_homologyMap_P0Map (n : ℤ) : Epi (HomologicalComplex.homologyMap (P0Map R K) n) := by
  refine CochainComplex.epi_homologyMap_of_forall_cocycle _ n fun x hx => ?_
  refine ⟨Finsupp.single (Sum.inl ⟨x, hx⟩) 1, rfl, ?_⟩
  exact P0Map_f_single R K n (Sum.inl ⟨x, hx⟩)

end CategoryTheory
