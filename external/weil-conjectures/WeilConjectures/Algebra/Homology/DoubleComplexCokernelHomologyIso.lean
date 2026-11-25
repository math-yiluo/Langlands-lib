/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Algebra.Homology.RowCycleLiftsToZigzag
import WeilConjectures.Algebra.Homology.ZigzagToRowCokernel
import WeilConjectures.Algebra.Homology.ZigzagTrivialIfRowBoundary

/-!
# Homology of cokernel complexes of an exact double complex

Source: Stacks Project, Algebra, Lemma Tag 00M1 (lemma-no-spectral-sequence),
including its preceding cokernel-complex construction and functoriality paragraph
(blueprint: lem-weil-pbc-double-complex-cokernel-homology-iso).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace HomologicalComplex₂

private abbrev ExactRows {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :=
  ∀ (p q : ℕ), 0 < p →
    (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
      (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
        HomologicalComplex.zero_f])).Exact

private def indexSwap (n : ℕ) : ZigzagIndex n ≃ ZigzagIndex n where
  toFun i := ⟨(i.val.2, i.val.1), by have := i.property; omega⟩
  invFun i := ⟨(i.val.2, i.val.1), by have := i.property; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def totalSwap {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) : zigzagTotal A.flip n ≃ₗ[R] zigzagTotal A n :=
  DirectSum.lequivCongrLeft R (indexSwap n)

private theorem totalSwap_cycles {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) (a : zigzagTotal A.flip n) :
    totalSwap A n a ∈ zigzagCycles A n ↔ a ∈ zigzagCycles A.flip n := by
  change (∀ p q h, zigzagRelation A n p q h (totalSwap A n a) = 0) ↔
    ∀ p q h, zigzagRelation A.flip n p q h a = 0
  constructor
  · intro ha p q h
    have hh := ha q p (by omega)
    simp only [zigzagRelation, LinearMap.sub_apply, LinearMap.comp_apply,
      DirectSum.component, totalSwap, indexSwap,
      flip_d_f, flip_X_d, sub_eq_zero] at hh ⊢
    exact hh.symm
  · intro ha p q h
    have hh := ha q p (by omega)
    simp only [zigzagRelation, LinearMap.sub_apply, LinearMap.comp_apply,
      DirectSum.component, totalSwap, indexSwap,
      flip_d_f, flip_X_d, sub_eq_zero] at hh ⊢
    exact hh.symm

open Classical in
private theorem totalSwap_lof {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) (i : ZigzagIndex n) (x : (A.flip.X i.val.1).X i.val.2) :
    totalSwap A n (DirectSum.lof R (ZigzagIndex n)
      (fun j : ZigzagIndex n ↦ (A.flip.X j.val.1).X j.val.2) i x) =
      DirectSum.lof R (ZigzagIndex n)
        (fun j : ZigzagIndex n ↦ (A.X j.val.1).X j.val.2) (indexSwap n i) x := by
  classical
  exact DirectSum.lequivCongrLeft_lof R (e := indexSwap n)
    (M := fun j : ZigzagIndex n ↦ (A.flip.X j.val.1).X j.val.2)
    (i := i) (k := indexSwap n i) rfl x x (by simp)

set_option backward.isDefEq.respectTransparency false in
private theorem totalSwap_boundary {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    (totalSwap A n).toLinearMap.comp (zigzagBoundary A.flip n) =
      (zigzagBoundary A n).comp (totalSwap A (n + 1)).toLinearMap := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, zigzagBoundary, DirectSum.toModule_lof,
    LinearEquiv.coe_coe]
  rw [totalSwap_lof, DirectSum.toModule_lof]
  simp only [zigzagBoundaryComponent, LinearMap.add_apply]
  dsimp only [indexSwap, Equiv.coe_fn_mk]
  rw [map_add]
  split_ifs <;> simp only [LinearMap.comp_apply, LinearMap.zero_apply,
    map_zero, indexSwap, Equiv.coe_fn_mk, flip_d_f, flip_X_d,
    add_zero, zero_add]
  all_goals
    repeat rw [totalSwap_lof]
    first | rfl | exact add_comm _ _

private theorem totalSwap_boundaries {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) (a : zigzagTotal A.flip n) :
    totalSwap A n a ∈ zigzagBoundaries A n ↔ a ∈ zigzagBoundaries A.flip n := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨c, rfl⟩ := (totalSwap A (n + 1)).surjective b
    refine ⟨c, (totalSwap A n).injective ?_⟩
    rw [← hb]
    exact LinearMap.congr_fun (totalSwap_boundary A n) c
  · rintro ⟨b, rfl⟩
    exact ⟨totalSwap A (n + 1) b, (LinearMap.congr_fun (totalSwap_boundary A n) b).symm⟩

private noncomputable def cyclesSwap {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) : zigzagCycles A.flip n ≃ₗ[R] zigzagCycles A n :=
  (totalSwap A n).ofSubmodules _ _ (by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (totalSwap_cycles A n b).mpr hb
    · intro ha
      obtain ⟨b, rfl⟩ := (totalSwap A n).surjective a
      exact ⟨b, (totalSwap_cycles A n b).mp ha, rfl⟩)

private noncomputable def moduleSwap {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) : zigzagModule A.flip n ≃ₗ[R] zigzagModule A n :=
  Submodule.Quotient.equiv _ _ (cyclesSwap A n) (by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (totalSwap_boundaries A n b.val).mpr hb
    · intro ha
      obtain ⟨b, rfl⟩ := (cyclesSwap A n).surjective a
      exact ⟨b, (totalSwap_boundaries A n b.val).mp ha, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem totalSwap_naturality {R : Type u} [CommRing R]
    {A B : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (Φ : A ⟶ B) (n : ℕ) :
    (zigzagTotalMap Φ n).comp (totalSwap A n).toLinearMap =
      (totalSwap B n).toLinearMap.comp (zigzagTotalMap
        ((flipFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)).map Φ) n) := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [totalSwap_lof]
  dsimp only [zigzagTotalMap, flipFunctor]
  rw [DirectSum.toModule_lof, DirectSum.toModule_lof]
  simp only [LinearMap.comp_apply]
  rw [totalSwap_lof]
  rfl

private theorem exists_flipZigzagIso (R : Type u) [CommRing R] (n : ℕ) :
    ∃ σ : ∀ A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ),
        ModuleCat.of R (zigzagModule A.flip n) ≅ ModuleCat.of R (zigzagModule A n),
      ∀ A B (Φ : A ⟶ B),
        (σ A).hom ≫ ModuleCat.ofHom (zigzagMap Φ n) =
          ModuleCat.ofHom (zigzagMap
            ((flipFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ)
              (ComplexShape.down ℕ)).map Φ) n) ≫ (σ B).hom := by
  classical
  refine ⟨fun A ↦ (moduleSwap A n).toModuleIso, ?_⟩
  intro A B Φ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    ((zigzagBoundaries A.flip n).comap (zigzagCycles A.flip n).subtype) z
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  dsimp only [moduleSwap, LinearEquiv.toModuleIso, ModuleCat.hom_ofHom,
    Submodule.Quotient.equiv, zigzagMap]
  simp only [Submodule.mkQ_apply]
  dsimp only [flipFunctor]
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.mapQ_apply,
    Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (totalSwap_naturality Φ n) a.val

private theorem zigzagToRow_bijective
    {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (hrow : ∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact)
    (n : ℕ) (ρ : zigzagModule A n →ₗ[R] (A.opcycles 0).homology n)
    (hπ : Function.Surjective ((A.pOpcycles 0).f n))
    (hcycle : ∀ a : zigzagCycles A n, ∃ c : (A.opcycles 0).cycles n,
      (A.opcycles 0).iCycles n c = (A.pOpcycles 0).f n
        (DirectSum.component R (ZigzagIndex n)
          (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩ a.val))
    (hformula : ∀ (a : zigzagCycles A n) (c : (A.opcycles 0).cycles n),
      (A.opcycles 0).iCycles n c = (A.pOpcycles 0).f n
        (DirectSum.component R (ZigzagIndex n)
          (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩ a.val) →
      ρ (((zigzagBoundaries A n).comap (zigzagCycles A n).subtype).mkQ a) =
        (A.opcycles 0).homologyπ n c) : Function.Bijective ρ := by
  classical
  let K := A.opcycles 0
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro z hz
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
      ((zigzagBoundaries A n).comap (zigzagCycles A n).subtype) z
    obtain ⟨c, hc⟩ := hcycle a
    have hzero : K.homologyπ n c = 0 := by
      rw [← hformula a c hc]
      exact hz
    have hex := (ShortComplex.mk (K.toCycles (n + 1) n) (K.homologyπ n)
      (K.toCycles_comp_homologyπ (n + 1) n)).exact_of_g_is_cokernel
        (K.homologyIsCokernel (n + 1) n (by simp))
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex c hzero
    have hb : a.val ∈ zigzagBoundaries A n := by
      apply zigzag_trivial_if_row_boundary A hrow n a.val a.property
      refine ⟨y, ?_⟩
      rw [← hc, ← hy]
      exact (congrArg (fun f : K.X (n + 1) ⟶ K.X n ↦ f y)
        (K.toCycles_i (n + 1) n)).symm
    exact (Submodule.Quotient.mk_eq_zero _).mpr hb
  · intro z
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance z
    obtain ⟨x, hx⟩ := hπ (K.iCycles n c)
    obtain ⟨a, ha, he⟩ := row_cycle_lifts_to_zigzag A hrow n x ⟨c, hx.symm⟩
    refine ⟨((zigzagBoundaries A n).comap (zigzagCycles A n).subtype).mkQ ⟨a, ha⟩, ?_⟩
    rw [hformula ⟨a, ha⟩ c (by simpa only [he] using hx.symm)]
    exact hc

/-- For a first-quadrant homological double complex with commuting squares and rows
and columns exact in positive degrees, the homology of the column-cokernel complex
is naturally isomorphic to that of the row-cokernel complex.

As in the landed zig-zag modules, the row-cokernel complex `Aʳᵗ` is `A.opcycles 0`,
formed in the abelian category of chain complexes: its degree `q` is the cokernel of
`d₁,ᵩ : A₁,ᵩ → A₀,ᵩ`, with differential induced by `δ`, and a bicomplex morphism `Φ`
induces `opcyclesMap Φ 0`. The column-cokernel complex `Aᵘᵖ` is the same construction
applied to `A.flip` (no signs: `flip` only exchanges the indices): its degree `p` is
the cokernel of `δ_{p,1} : A_{p,1} → A_{p,0}` with differential induced by `d`, and `Φ`
induces `opcyclesMap (flip.map Φ) 0`. Row exactness is `ShortComplex.Exact` of
`d_{p+1,q}, d_{p,q}` for `p > 0`; column exactness the same for `δ` and `q > 0`.
The single family `θ` is chosen before quantifying over morphisms, and its homs
satisfy the naturality square `H_n(Φʳᵗ) ∘ θ^A = θ^B ∘ H_n(Φᵘᵖ)`.

Source: Stacks Project, Algebra, Tag 00M1 (lemma-no-spectral-sequence), setup and proof
(blueprint: lem-weil-pbc-double-complex-cokernel-homology-iso).

Proof: (1) Transpose the bicomplex. Its row-cokernel complex is the original
column-cokernel complex, and its zig-zag module is the same, by exchanging coordinates
(`def-weil-pbc-double-complex-zigzag-module`). (2) The endpoint map from zig-zag homology
to row-cokernel homology (`lem-weil-pbc-double-complex-zigzag-to-row-cokernel-map`)
is surjective by lifting a cycle through the exact rows
(`lem-weil-pbc-double-complex-row-cycle-lifts-to-zigzag`), and injective by eliminating
a zig-zag whose endpoint is a boundary
(`lem-weil-pbc-double-complex-zigzag-trivial-if-row-boundary`). Thus it is an isomorphism
`ρ`. (3) Apply (2) to the transpose to obtain the column-side isomorphism `λ`.
(4) Set `θ = λ⁻¹ ≫ ρ`. (5) A bicomplex morphism acts on zig-zags coordinatewise
(`lem-weil-pbc-double-complex-zigzag-module-functorial`), and the endpoint maps commute
with it by the naturality clause of the endpoint-map lemma. Composing the two
commutative squares with `λ⁻¹` gives the displayed naturality equation. Homology and
exactness throughout are `def-weil-pbc-module-chain-complex-homology` and
`def-weil-pbc-exact-sequence`. -/
theorem doubleComplexCokernelHomologyIso (R : Type u) [CommRing R] :
    let D := HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)
    let E := fun A : D =>
      (∀ (p q : ℕ), 0 < p →
        (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
          (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
            HomologicalComplex.zero_f])).Exact) ∧
      (∀ (p q : ℕ), 0 < q →
        (ShortComplex.mk ((A.X p).d (q + 1) q) ((A.X p).d q (q - 1))
          (by simp)).Exact)
    let flip := flipFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    ∃ θ : ∀ (A : D), E A → ∀ n : ℕ,
        (A.flip.opcycles 0).homology n ≅ (A.opcycles 0).homology n,
      ∀ (A B : D) (hA : E A) (hB : E B) (Φ : A ⟶ B) (n : ℕ),
        (θ A hA n).hom ≫
            HomologicalComplex.homologyMap (HomologicalComplex.opcyclesMap Φ 0) n =
          HomologicalComplex.homologyMap
              (HomologicalComplex.opcyclesMap (flip.map Φ) 0) n ≫ (θ B hB n).hom := by
  classical
  dsimp only
  let ρ := fun n ↦ (exists_zigzagToRowCokernel.{u, v} (R := R) n).choose
  have hρ n := (exists_zigzagToRowCokernel.{u, v} (R := R) n).choose_spec
  let σ := fun n ↦ (exists_flipZigzagIso.{u, v} R n).choose
  have hσ n := (exists_flipZigzagIso.{u, v} R n).choose_spec
  have hbij (A) (hrow : ExactRows A) (n) : Function.Bijective (ρ n A) := by
    rcases hρ n with ⟨hπ, _, _, hc, _, hf, _⟩
    exact zigzagToRow_bijective A hrow n (ρ n A) (hπ A n).1
      (fun a ↦ (hc A a).2) (hf A)
  let e := fun A hrow n ↦ (LinearEquiv.ofBijective (ρ n A) (hbij A hrow n)).toModuleIso
  have he A B hA hB (Φ : A ⟶ B) n :
      (e A hA n).hom ≫
          HomologicalComplex.homologyMap (HomologicalComplex.opcyclesMap Φ 0) n =
        ModuleCat.ofHom (zigzagMap Φ n) ≫ (e B hB n).hom := by
    apply ModuleCat.hom_ext
    exact (hρ n).2.2.2.2.2.2 A B Φ
  refine ⟨fun A hA n ↦ (e A.flip (fun p q hp ↦ hA.2 q p hp) n).symm ≪≫
    σ n A ≪≫ e A hA.1 n, ?_⟩
  intro A B hA hB Φ n
  let ellA := e A.flip (fun p q hp ↦ hA.2 q p hp) n
  let ellB := e B.flip (fun p q hp ↦ hB.2 q p hp) n
  let Φt := (flipFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)).map Φ
  have hflip : ellA.hom ≫
      HomologicalComplex.homologyMap (HomologicalComplex.opcyclesMap Φt 0) n =
      ModuleCat.ofHom (zigzagMap Φt n) ≫ ellB.hom :=
    he A.flip B.flip (fun p q hp ↦ hA.2 q p hp)
      (fun p q hp ↦ hB.2 q p hp) Φt n
  have hflipInv : ellA.inv ≫ ModuleCat.ofHom (zigzagMap Φt n) =
      HomologicalComplex.homologyMap (HomologicalComplex.opcyclesMap Φt 0) n ≫ ellB.inv := by
    apply (cancel_epi ellA.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hflip]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change ellA.inv ≫ (σ n A).hom ≫ (e A hA.1 n).hom ≫
      HomologicalComplex.homologyMap (HomologicalComplex.opcyclesMap Φ 0) n =
    HomologicalComplex.homologyMap (HomologicalComplex.opcyclesMap Φt 0) n ≫
      ellB.inv ≫ (σ n B).hom ≫ (e B hB.1 n).hom
  rw [he A B hA.1 hB.1 Φ n]
  rw [← Category.assoc (σ n A).hom, hσ n A B Φ]
  simp only [Category.assoc]
  rw [← Category.assoc ellA.inv (ModuleCat.ofHom (zigzagMap Φt n)), hflipInv]
  simp only [Category.assoc]
  rfl

end HomologicalComplex₂
