/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # The two edges of the resolution Hom double complex

Source: Stacks Project, Tag 0954, proof of Lemma 47.8.2.
(blueprint: lem-sbc-ext-projective-edge-quasi-iso).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory Limits Opposite HomologicalComplex

namespace ModuleCat

variable {R : Type u} [CommRing R]

local instance : (linearCoyoneda R (ModuleCat.{u} R)).PreservesZeroMorphisms where
  map_zero := by
    intros
    ext X f
    change (0 : _ ⟶ _) ≫ f = 0
    simp

/-- Reverse a nonnegative chain complex in the opposite category.
Source: Stacks Project, Tag 0954, the contravariance of the Hom complex.
(blueprint: lem-sbc-ext-projective-edge-quasi-iso). -/
def resolutionHomOpposite (P : ChainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R)ᵒᵖ ℕ where
  X n := op (P.X n)
  d n m := (P.d m n).op
  shape n m h := by
    rw [P.shape m n h, op_zero]
  d_comp_d' n m k _ _ := by
    rw [← op_comp, P.d_comp_d, op_zero]

/-- The first-quadrant total complex of `Hom(P,E)`.
Source: Stacks Project, Tag 0954, injective-resolution computation of Ext.
(blueprint: lem-sbc-ext-projective-edge-quasi-iso). -/
noncomputable abbrev resolutionHomTotal
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (E : CochainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  mapBifunctor (resolutionHomOpposite P) E (linearCoyoneda R (ModuleCat.{u} R)) (ComplexShape.up ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- The vertical augmentation from `Hom(P,M)` to `Tot Hom(P,E)`.
Source: Stacks Project, Tag 0954, injective-resolution computation of Ext.
(blueprint: lem-sbc-ext-projective-edge-quasi-iso). -/
noncomputable def resolutionHomProjectiveEdge
    {X M : ModuleCat.{u} R} (P : ProjectiveResolution X) (E : InjectiveResolution M) :
    P.complex.linearYonedaObj R M ⟶ resolutionHomTotal P.complex E.cocomplex where
  f n := ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (P.complex.X n))).map
      (E.ι.f 0) ≫
    ιMapBifunctor (resolutionHomOpposite P.complex) E.cocomplex (linearCoyoneda R (ModuleCat.{u} R))
      (ComplexShape.up ℕ) n 0 n (by simp [ComplexShape.π])
  comm' n m h := by
    obtain rfl : m = n + 1 := h.symm
    simp only [resolutionHomTotal, mapBifunctor.d_eq, Category.assoc,
      Preadditive.comp_add]
    rw [mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
    rw [mapBifunctor.d₁_eq _ _ _ _ (i₁ := n) (i₁' := n + 1) (by rfl)
      0 (n + 1) (by simp),
      mapBifunctor.d₂_eq _ _ _ _ n (i₂ := 0) (i₂' := 1) (by rfl)
        (n + 1) (by simp)]
    have hε : ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (n, 0) = 1 := rfl
    simp only [hε, one_smul, Linear.comp_units_smul]
    have hz : ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (P.complex.X n))).map
        (E.ι.f 0) ≫
        ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (P.complex.X n))).map
          (E.cocomplex.d 0 1) = 0 := by
      rw [← Functor.map_comp, E.ι_f_zero_comp_complex_d, Functor.map_zero]
    simp only [← Category.assoc]
    dsimp only [resolutionHomOpposite]
    rw [hz, zero_comp, smul_zero, add_zero]
    congr 1

/-- The horizontal augmentation from `Hom(X,E)` to `Tot Hom(P,E)`.
Source: Stacks Project, Tag 0954, injective-resolution computation of Ext.
(blueprint: lem-sbc-ext-projective-edge-quasi-iso). -/
noncomputable def resolutionHomInjectiveEdge
    {X M : ModuleCat.{u} R} (P : ProjectiveResolution X) (E : InjectiveResolution M) :
    (((linearCoyoneda R (ModuleCat.{u} R)).obj (op X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.cocomplex ⟶
      resolutionHomTotal P.complex E.cocomplex where
  f n := ((linearCoyoneda R (ModuleCat.{u} R)).map (P.π.f 0).op).app
      (E.cocomplex.X n) ≫
    ιMapBifunctor (resolutionHomOpposite P.complex) E.cocomplex
      (linearCoyoneda R (ModuleCat.{u} R)) (ComplexShape.up ℕ)
      0 n n (by simp [ComplexShape.π])
  comm' n m h := by
    obtain rfl : m = n + 1 := h.symm
    simp only [resolutionHomTotal, mapBifunctor.d_eq, Category.assoc,
      Preadditive.comp_add]
    rw [mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
    rw [mapBifunctor.d₁_eq _ _ _ _ (i₁ := 0) (i₁' := 1) (by rfl)
      n (n + 1) (by simp [Nat.add_comm]),
      mapBifunctor.d₂_eq _ _ _ _ 0 (i₂ := n) (i₂' := n + 1) (by rfl)
        (n + 1) (by simp)]
    have hε₁ : ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (0, n) = 1 := rfl
    have hε₂ : ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (0, n) = 1 := rfl
    simp only [hε₁, hε₂, one_smul]
    have hz : ((linearCoyoneda R (ModuleCat.{u} R)).map (P.π.f 0).op).app
        (E.cocomplex.X n) ≫
        ((linearCoyoneda R (ModuleCat.{u} R)).map (P.complex.d 1 0).op).app
          (E.cocomplex.X n) = 0 := by
      rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp,
        P.complex_d_comp_π_f_zero, op_zero, Functor.map_zero, zero_app]
    dsimp only [resolutionHomOpposite]
    simp only [← Category.assoc]
    rw [hz, zero_comp, zero_add]
    congr 1

private theorem coyoneda_preservesHomology (X : ModuleCat.{u} R) [Projective X] :
    ((linearCoyoneda R (ModuleCat.{u} R)).obj (op X)).PreservesHomology := by
  let F := (linearCoyoneda R (ModuleCat.{u} R)).obj (op X)
  have : PreservesLimits (F ⋙ forget (ModuleCat.{u} R)) := by
    change PreservesLimits (coyoneda.obj (op X))
    infer_instance
  have : PreservesLimits F := preservesLimits_of_reflects_of_preserves
    F (forget (ModuleCat.{u} R))
  have : (F ⋙ forget (ModuleCat.{u} R)).PreservesEpimorphisms := by
    exact (Projective.projective_iff_preservesEpimorphisms_coyoneda_obj X).mp
      inferInstance
  have : F.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_preserves_of_reflects
    F (forget (ModuleCat.{u} R))
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

/-- Precomposition on the projective Hom complex.
Source: Stacks Project, Tag 0954, naturality of the resolution computation.
(blueprint: lem-sbc-ext-projective-edge-quasi-iso). -/
def resolutionHomPrecomp {P P' : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : P' ⟶ P) (M : ModuleCat.{u} R) :
    P.linearYonedaObj R M ⟶ P'.linearYonedaObj R M where
  f n := ModuleCat.ofHom (Linear.leftComp R M (f.f n))
  comm' n m h := by
    obtain rfl : m = n + 1 := h.symm
    ext g
    change P'.d (n + 1) n ≫ f.f n ≫ g =
      f.f (n + 1) ≫ P.d (n + 1) n ≫ g
    rw [← Category.assoc, ← f.comm, Category.assoc]

/-- Precomposition on the total resolution Hom complex.
Source: Stacks Project, Tag 0954, naturality of the resolution computation.
(blueprint: lem-sbc-ext-projective-edge-quasi-iso). -/
noncomputable def resolutionHomTotalPrecomp
    {P P' : ChainComplex (ModuleCat.{u} R) ℕ} (f : P' ⟶ P)
    (E : CochainComplex (ModuleCat.{u} R) ℕ) :
    resolutionHomTotal P E ⟶ resolutionHomTotal P' E :=
  mapBifunctorMap
    (show resolutionHomOpposite P ⟶ resolutionHomOpposite P' from
      { f n := (f.f n).op
        comm' n m _ := by simp only [resolutionHomOpposite, ← op_comp, f.comm] })
    (𝟙 E) (linearCoyoneda R (ModuleCat.{u} R)) (ComplexShape.up ℕ)

/-- Precomposition commutes with the projective edge.
Source: Stacks Project, Tag 0954, naturality of the Ext computation.
(blueprint: lem-sbc-ext-projective-edge-quasi-iso). -/
theorem projectiveEdge_naturality
    {X X' M : ModuleCat.{u} R} (P : ProjectiveResolution X)
    (P' : ProjectiveResolution X') (E : InjectiveResolution M) (f : P'.complex ⟶ P.complex) :
    resolutionHomProjectiveEdge P E ≫ resolutionHomTotalPrecomp f E.cocomplex =
      resolutionHomPrecomp f M ≫ resolutionHomProjectiveEdge P' E := by
  ext n : 1
  simp only [resolutionHomProjectiveEdge, resolutionHomTotalPrecomp,
    HomologicalComplex.comp_f, Category.assoc, ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f]
  dsimp only [Functor.mapHomologicalComplex, linearCoyoneda]
  ext a
  rfl

/-- A chain map compatible with the augmentation commutes with the injective edge.
Source: Stacks Project, Tag 0954, naturality of the Ext computation.
(blueprint: lem-sbc-ext-projective-edge-quasi-iso). -/
theorem injectiveEdge_naturality
    {X X' M : ModuleCat.{u} R} (g : X' ⟶ X) (P : ProjectiveResolution X)
    (P' : ProjectiveResolution X') (E : InjectiveResolution M)
    (f : P'.complex ⟶ P.complex) (hf : f.f 0 ≫ P.π.f 0 = P'.π.f 0 ≫ g) :
    resolutionHomInjectiveEdge P E ≫ resolutionHomTotalPrecomp f E.cocomplex =
      (NatTrans.mapHomologicalComplex
        ((linearCoyoneda R (ModuleCat.{u} R)).map g.op) (ComplexShape.up ℕ)).app
          E.cocomplex ≫ resolutionHomInjectiveEdge P' E := by
  ext n : 1
  simp only [resolutionHomInjectiveEdge, resolutionHomTotalPrecomp,
    HomologicalComplex.comp_f, Category.assoc, ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f]
  dsimp only [Functor.mapHomologicalComplex, linearCoyoneda]
  ext a
  change (ιMapBifunctor (resolutionHomOpposite P'.complex) E.cocomplex
    (linearCoyoneda R (ModuleCat.{u} R)) (ComplexShape.up ℕ) 0 n n (by simp)).hom
      (f.f 0 ≫ P.π.f 0 ≫ a) =
    (ιMapBifunctor (resolutionHomOpposite P'.complex) E.cocomplex
    (linearCoyoneda R (ModuleCat.{u} R)) (ComplexShape.up ℕ) 0 n n (by simp)).hom
      (P'.π.f 0 ≫ g ≫ a)
  rw [← Category.assoc, hf, Category.assoc]

@[instance_reducible]
private def resolutionHomTotalSymmetry :
    TotalComplexShapeSymmetry (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p _ rfl q
    change (-1 : ℤˣ) ^ (p * q) * 1 =
      (-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ ((p + 1) * q)
    rw [mul_one, Nat.add_mul, one_mul, pow_add]
    calc
      _ = (-1 : ℤˣ) ^ (p * q) *
          ((-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ q) := by rw [Int.units_mul_self, mul_one]
      _ = _ := mul_left_comm _ _ _
  σ_ε₂ := by
    rintro p q _ rfl
    change (-1 : ℤˣ) ^ (p * q) * (-1 : ℤˣ) ^ p =
      1 * (-1 : ℤˣ) ^ (p * (q + 1))
    rw [one_mul, Nat.mul_add, Nat.mul_one, pow_add]

/-- The projective edge is a quasi-isomorphism.
Source: Stacks Project, Tag 0954, injective-resolution computation of Ext.
(blueprint: lem-sbc-ext-projective-edge-quasi-iso).

Proof: each vertical augmented column is Hom(P^i,M) → Hom(P^i,E).
Projectivity of P^i makes Hom(P^i,-) exact, so this augmentation is a
quasi-isomorphism. The first-quadrant total comparison then makes the edge
map a quasi-isomorphism. Each diagonal is finite; the component elimination
argument starts at its leftmost component and moves right while lowering
vertical degree, terminating at the injective augmentation in degree -1.
The edge component is exactly postcomposition with E.ι followed by the
(n,0) summand inclusion. In degree zero this gives the kernel comparison;
zero modules and an unbounded resolution satisfy the same finite diagonal
argument. -/
theorem resolutionHomProjectiveEdge_quasiIso
    {X M : ModuleCat.{u} R} (P : ProjectiveResolution X) (E : InjectiveResolution M) :
    QuasiIso (resolutionHomProjectiveEdge P E) := by
  let : TotalComplexShapeSymmetry (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) := resolutionHomTotalSymmetry
  let K := (((linearCoyoneda R (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℕ) (ComplexShape.up ℕ)).obj
      (resolutionHomOpposite P.complex)).obj E.cocomplex
  let A := P.complex.linearYonedaObj R M
  let a : A ⟶ K.flip.X 0 :=
    { f n := ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (P.complex.X n))).map
        (E.ι.f 0)
      comm' n m _ := by ext g; rfl }
  have ha : a ≫ K.flip.d 0 1 = 0 := by
    ext n g
    change g ≫ E.ι.f 0 ≫ E.cocomplex.d 0 1 = 0
    rw [E.ι_f_zero_comp_complex_d, comp_zero]
  let b := resolutionHomProjectiveEdge P E ≫ (K.totalFlipIso (ComplexShape.up ℕ)).inv
  have hb : ∀ n, b.f n = a.f n ≫
      K.flip.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) := by
    intro n
    simp only [b, HomologicalComplex.comp_f, resolutionHomProjectiveEdge,
      Category.assoc]
    rw [HomologicalComplex₂.ιTotal_totalFlipIso_f_inv]
    have hσ : ComplexShape.σ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) n 0 = 1 := by
      change (-1 : ℤˣ) ^ (n * 0) = 1
      simp
    simp only [hσ, one_smul]
    rfl
  have hcol (n : ℕ) : QuasiIso
      ((CochainComplex.fromSingle₀Equiv (K.flip.flip.X n) (A.X n)).symm
        ⟨a.f n, by simpa using congrArg (fun f => f.f n) ha⟩) := by
    let F := (linearCoyoneda R (ModuleCat.{u} R)).obj (op (P.complex.X n))
    have : F.PreservesHomology := coyoneda_preservesHomology (P.complex.X n)
    let T := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀ (ModuleCat.{u} R)).obj M)
    let t : (CochainComplex.single₀ (ModuleCat.{u} R)).obj (A.X n) ⟶ T :=
      (CochainComplex.fromSingle₀Equiv T (A.X n)).symm ⟨𝟙 _, by
        change (𝟙 _) ≫ F.map (((CochainComplex.single₀ (ModuleCat.{u} R)).obj M).d 0 1) = 0
        simp only [HomologicalComplex.single_obj_d, Functor.map_zero, comp_zero]⟩
    have ht (i : ℕ) : IsIso (t.f i) := by
      cases i with
      | zero =>
          change IsIso (𝟙 (A.X n))
          infer_instance
      | succ i =>
          apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
            (A.X n) (i + 1) (by omega)).isIso
          exact F.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
            M (i + 1) (by omega))
    have : IsIso t := HomologicalComplex.Hom.isIso_of_components t
    let φ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map E.ι
    have : QuasiIso φ := by dsimp only [φ]; infer_instance
    have hcomp : t ≫ φ = (CochainComplex.fromSingle₀Equiv (K.flip.flip.X n) (A.X n)).symm
        ⟨a.f n, by simpa using congrArg (fun f => f.f n) ha⟩ := by
      apply HomologicalComplex.from_single_hom_ext
      simp only [HomologicalComplex.comp_f, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
      change (𝟙 _) ≫ F.map (E.ι.f 0) = _
      rfl
    rw [← hcomp]
    infer_instance
  have : QuasiIso b := HomologicalComplex₂.quasiIso_of_column_augmentation
    K.flip A a ha b hb hcol
  exact (quasiIso_iff_comp_right (resolutionHomProjectiveEdge P E)
    (K.totalFlipIso (ComplexShape.up ℕ)).inv).mp this

end ModuleCat
