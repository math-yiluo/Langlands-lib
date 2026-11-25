/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ZigzagModule
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The canonical map from zig-zags to row-cokernel homology

Source: Stacks Project, Algebra, Tag 00M1, proof and functoriality paragraph
(blueprint: lem-weil-pbc-double-complex-zigzag-to-row-cokernel-map).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace HomologicalComplex₂

private noncomputable abbrev endpoint
    {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :=
  DirectSum.component R (ZigzagIndex n)
    (fun i : ZigzagIndex n ↦ (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩

private lemma endpoint_cycle {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) (a : zigzagCycles A n) :
    (A.opcycles 0).d n (n - 1) ((A.pOpcycles 0).f n (endpoint A n a.val)) = 0 := by
  classical
  cases n with
  | zero => simp [HomologicalComplex.shape]
  | succ n =>
    have ha := a.property 0 n (by omega)
    have he : ((A.d 1 0).f n)
        (DirectSum.component R (ZigzagIndex (n + 1))
          (fun i : ZigzagIndex (n + 1) ↦ (A.X i.1.1).X i.1.2)
          ⟨(1, n), by omega⟩ a.val) =
        ((A.X 0).d (n + 1) n) (endpoint A (n + 1) a.val) := by
      exact sub_eq_zero.mp ha
    have hc := ConcreteCategory.congr_hom ((A.pOpcycles 0).comm (n + 1) n)
      (endpoint A (n + 1) a.val)
    have hz := HomologicalComplex.congr_hom (A.d_pOpcycles 1 0) n
    have hzero := ConcreteCategory.congr_hom hz
      (DirectSum.component R (ZigzagIndex (n + 1))
        (fun i : ZigzagIndex (n + 1) ↦ (A.X i.1.1).X i.1.2)
        ⟨(1, n), by omega⟩ a.val)
    dsimp at hc hzero
    rw [he] at hzero
    simpa using hc.trans hzero

private lemma row_projection_exact {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (q : ℕ) :
    Function.Surjective ((A.pOpcycles 0).f q) ∧
      LinearMap.ker ((A.pOpcycles 0).f q).hom =
        LinearMap.range ((A.d 1 0).f q).hom := by
  let S := CategoryTheory.ShortComplex.mk (A.d 1 0) (A.pOpcycles 0)
    (A.d_pOpcycles 1 0)
  have hS : S.Exact := S.exact_of_g_is_cokernel (A.opcyclesIsCokernel 1 0 (by simp))
  have he := hS.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) q)
  refine ⟨(ModuleCat.epi_iff_surjective _).mp inferInstance, ?_⟩
  exact he.moduleCat_range_eq_ker.symm

private lemma zigzagIndex_eq_iff {n : ℕ} (i j : ZigzagIndex n) :
    i = j ↔ i.val = j.val := Subtype.ext_iff

private lemma endpoint_boundary {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) (b : zigzagTotal A (n + 1)) :
    (A.pOpcycles 0).f n (endpoint A n (zigzagBoundary A n b)) =
      (A.opcycles 0).d (n + 1) n
        ((A.pOpcycles 0).f (n + 1) (endpoint A (n + 1) b)) := by
  classical
  suffices h : ((A.pOpcycles 0).f n).hom.comp
      ((endpoint A n).comp (zigzagBoundary A n)) =
      ((A.opcycles 0).d (n + 1) n).hom.comp
        (((A.pOpcycles 0).f (n + 1)).hom.comp (endpoint A (n + 1))) by
    exact LinearMap.congr_fun h b
  apply DirectSum.linearMap_ext
  rintro ⟨⟨p, q⟩, hi⟩
  ext x
  cases p with
  | zero =>
    have hq : q = n + 1 := by omega
    subst q
    simp only [endpoint, zigzagBoundary, LinearMap.comp_apply, DirectSum.toModule_lof,
      zigzagBoundaryComponent, lt_self_iff_false, ↓reduceDIte, lt_add_iff_pos_left,
      Order.lt_add_one_iff, zero_le, Nat.add_one_sub_one, zero_add,
      DirectSum.component.lof_self]
    exact (ConcreteCategory.congr_hom ((A.pOpcycles 0).comm (n + 1) n) x).symm
  | succ p =>
    cases p with
    | zero =>
      have hq : q = n := by omega
      subst q
      have hz := HomologicalComplex.congr_hom (A.d_pOpcycles 1 0) n
      have hx := ConcreteCategory.congr_hom hz x
      dsimp at hx
      cases n <;>
        simpa [LinearMap.comp_apply, zigzagBoundary, zigzagBoundaryComponent, endpoint,
          DirectSum.component.of, zigzagIndex_eq_iff] using hx
    | succ p =>
      cases q <;>
        simp [LinearMap.comp_apply, zigzagBoundary, zigzagBoundaryComponent, endpoint,
          DirectSum.component.of, zigzagIndex_eq_iff]

private lemma endpoint_map {R : Type u} [CommRing R]
    {A B : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (Φ : A ⟶ B) (n : ℕ) (a : zigzagTotal A n) :
    endpoint B n (zigzagTotalMap Φ n a) = (Φ.f 0).f n (endpoint A n a) := by
  classical
  suffices h : (endpoint B n).comp (zigzagTotalMap Φ n) =
      ((Φ.f 0).f n).hom.comp (endpoint A n) by
    exact LinearMap.congr_fun h a
  apply DirectSum.linearMap_ext
  intro i
  ext x
  by_cases hi : i = ⟨(0, n), by simp⟩
  · subst i
    simp [LinearMap.comp_apply, zigzagTotalMap, endpoint]
  · simp [LinearMap.comp_apply, zigzagTotalMap, endpoint, DirectSum.component.of, hi]

private lemma endpoint_boundary_class_zero {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) (a : zigzagCycles A n)
    (ha : a.val ∈ zigzagBoundaries A n) (c : (A.opcycles 0).cycles n)
    (hc : (A.opcycles 0).iCycles n c =
      (A.pOpcycles 0).f n (endpoint A n a.val)) :
    (A.opcycles 0).homologyπ n c = 0 := by
  obtain ⟨b, hb⟩ := ha
  let K := A.opcycles 0
  let x := (A.pOpcycles 0).f (n + 1) (endpoint A (n + 1) b)
  have he : c = K.toCycles (n + 1) n x := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    rw [hc, ← hb, endpoint_boundary]
    exact (ConcreteCategory.congr_hom (K.toCycles_i (n + 1) n) x).symm
  rw [he]
  exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ (n + 1) n) x

open Classical in
/-- The endpoint of a zig-zag induces a natural linear map to row-cokernel homology.
Source: Stacks Project, Algebra, Tag 00M1, proof, canonical homomorphisms and the
right-hand square of the functoriality diagram
(blueprint: lem-weil-pbc-double-complex-zigzag-to-row-cokernel-map).

Here `C A = A.opcycles 0` is formed in the abelian category of chain complexes:
its degree `q` is the cokernel of `d : A₁,ᵩ → A₀,ᵩ`. The projection `π A` is a
chain map, and `opcyclesMap Φ 0` is the induced row-cokernel chain map.
The first three clauses record the cokernel and its differential and morphism formulas.
The fourth clause is (a); the fifth is (b); the last two specify the induced map
on representatives and its naturality (c). No exactness is assumed.

Proof: (1) Commuting squares make `δ` descend through each horizontal cokernel;
`δ² = 0` makes these cokernels a complex. Commutation of `Φ` with `d` makes it
descend, and commutation with `δ` makes the descended maps a chain map. The
projections are surjective with kernel the horizontal image.
(2) For a zig-zag of positive degree, its last equation is
`δ a₀,ₙ = d a₁,ₙ₋₁`; the cokernel projection kills the right side. At degree zero
the outgoing differential vanishes. This uses the relations of
`def-weil-pbc-double-complex-zigzag-module`.
(3) For a trivial zig-zag `D b`, the endpoint is `d b₁,ₙ + δ b₀,ₙ₊₁`;
its projection is the boundary `δʳᵗ π b₀,ₙ₊₁`. Thus its homology class is zero,
using `def-weil-pbc-module-chain-complex-homology`.
(4) The endpoint projection followed by the homology class map is linear on
zig-zags, and kills their intersection with trivial zig-zags by (3). The quotient
universal property gives the unique linear map `ρ`, with the stated formula.
(5) On a representative `a`, both composites in the naturality square give the
class of `π Φ₀,ₙ a₀,ₙ`, by the projection formula in (1). Representatives generate
the quotient, so the linear maps agree. No row or column exactness is used. -/
theorem exists_zigzagToRowCokernel
    {R : Type u} [CommRing R] (n : ℕ) :
    let C := fun A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) => A.opcycles 0
    let π := fun A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) => A.pOpcycles 0
    let e := fun A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) =>
      DirectSum.component R (ZigzagIndex n)
        (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩
    ∃ ρ : ∀ A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ), zigzagModule A n →ₗ[R] (C A).homology n,
      (∀ A q, Function.Surjective ((π A).f q) ∧
        LinearMap.ker ((π A).f q).hom = LinearMap.range ((A.d 1 0).f q).hom) ∧
      (∀ A q, (A.X 0).d (q + 1) q ≫ (π A).f q =
        (π A).f (q + 1) ≫ (C A).d (q + 1) q) ∧
      (∀ A B (Φ : A ⟶ B) q,
        (π A).f q ≫ (HomologicalComplex.opcyclesMap Φ 0).f q =
          (Φ.f 0).f q ≫ (π B).f q) ∧
      (∀ A (a : zigzagCycles A n),
        (C A).d n (n - 1) ((π A).f n (e A a.val)) = 0 ∧
        ∃ c : (C A).cycles n, (C A).iCycles n c = (π A).f n (e A a.val)) ∧
      (∀ A (a : zigzagCycles A n), a.val ∈ zigzagBoundaries A n →
        ∀ c : (C A).cycles n, (C A).iCycles n c = (π A).f n (e A a.val) →
          (C A).homologyπ n c = 0) ∧
      (∀ A (a : zigzagCycles A n) (c : (C A).cycles n),
        (C A).iCycles n c = (π A).f n (e A a.val) →
          ρ A (((zigzagBoundaries A n).comap (zigzagCycles A n).subtype).mkQ a) =
            (C A).homologyπ n c) ∧
      (∀ A B (Φ : A ⟶ B),
        (ModuleCat.Hom.hom
          (HomologicalComplex.homologyMap (HomologicalComplex.opcyclesMap Φ 0) n)).comp (ρ A) =
          (ρ B).comp (zigzagMap Φ n)) := by
  classical
  dsimp only
  let l := fun A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) ↦
    (A.opcycles 0).liftCycles
      (ModuleCat.ofHom (((A.pOpcycles 0).f n).hom.comp
        ((endpoint A n).comp (zigzagCycles A n).subtype))) (n - 1)
      (by cases n <;> simp [ChainComplex.next_nat_zero, ChainComplex.next_nat_succ])
      (by ext a; exact endpoint_cycle A n a)
  have hl : ∀ A (a : zigzagCycles A n), (A.opcycles 0).iCycles n (l A a) =
      (A.pOpcycles 0).f n (endpoint A n a.val) := by
    intro A a
    have he : l A ≫ (A.opcycles 0).iCycles n =
        ModuleCat.ofHom (((A.pOpcycles 0).f n).hom.comp
          ((endpoint A n).comp (zigzagCycles A n).subtype)) :=
      HomologicalComplex.liftCycles_i (A.opcycles 0) _ _ _ _
    exact ConcreteCategory.congr_hom he a
  let f := fun A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) ↦ ((A.opcycles 0).homologyπ n).hom.comp (l A).hom
  have hf : ∀ A, ((zigzagBoundaries A n).comap (zigzagCycles A n).subtype) ≤
      LinearMap.ker (f A) := by
    intro A a ha
    exact endpoint_boundary_class_zero A n a ha (l A a) (hl A a)
  let ρ := fun A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) ↦
    ((zigzagBoundaries A n).comap (zigzagCycles A n).subtype).liftQ (f A) (hf A)
  have hρ : ∀ A (a : zigzagCycles A n) (c : (A.opcycles 0).cycles n),
      (A.opcycles 0).iCycles n c = (A.pOpcycles 0).f n (endpoint A n a.val) →
      ρ A (((zigzagBoundaries A n).comap (zigzagCycles A n).subtype).mkQ a) =
        (A.opcycles 0).homologyπ n c := by
    intro A a c hc
    have he : l A a = c :=
      (ModuleCat.mono_iff_injective ((A.opcycles 0).iCycles n)).mp inferInstance
        ((hl A a).trans hc.symm)
    change (A.opcycles 0).homologyπ n (l A a) = _
    rw [he]
  refine ⟨ρ, row_projection_exact, ?_, ?_, ?_, ?_, hρ, ?_⟩
  · intro A q
    exact ((A.pOpcycles 0).comm (q + 1) q).symm
  · intro A B Φ q
    exact HomologicalComplex.congr_hom (HomologicalComplex.p_opcyclesMap Φ 0) q
  · intro A a
    exact ⟨endpoint_cycle A n a, l A a, hl A a⟩
  · intro A a ha c hc
    exact endpoint_boundary_class_zero A n a ha c hc
  · intro A B Φ
    apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ :=
      ((zigzagBoundaries A n).comap (zigzagCycles A n).subtype).mkQ_surjective z
    let b : zigzagCycles B n := ⟨zigzagTotalMap Φ n a.val,
      (zigzagTotalMap_preserves Φ n).1 (Submodule.mem_map_of_mem a.property)⟩
    let ψ := HomologicalComplex.opcyclesMap Φ 0
    have he : HomologicalComplex.cyclesMap ψ n (l A a) = l B b := by
      apply (ModuleCat.mono_iff_injective ((B.opcycles 0).iCycles n)).mp inferInstance
      calc
        (B.opcycles 0).iCycles n (HomologicalComplex.cyclesMap ψ n (l A a)) =
            ψ.f n ((A.opcycles 0).iCycles n (l A a)) :=
          ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ n) (l A a)
        _ = ψ.f n ((A.pOpcycles 0).f n (endpoint A n a.val)) := by rw [hl]
        _ = (B.pOpcycles 0).f n ((Φ.f 0).f n (endpoint A n a.val)) :=
          ConcreteCategory.congr_hom
            (HomologicalComplex.congr_hom (HomologicalComplex.p_opcyclesMap Φ 0) n)
            (endpoint A n a.val)
        _ = (B.pOpcycles 0).f n (endpoint B n b.val) := by rw [← endpoint_map Φ n]
        _ = (B.opcycles 0).iCycles n (l B b) := (hl B b).symm
    change HomologicalComplex.homologyMap ψ n
        ((A.opcycles 0).homologyπ n (l A a)) =
      (B.opcycles 0).homologyπ n (l B b)
    calc
      _ = (B.opcycles 0).homologyπ n (HomologicalComplex.cyclesMap ψ n (l A a)) :=
        ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality ψ n) (l A a)
      _ = _ := by rw [he]

end HomologicalComplex₂
