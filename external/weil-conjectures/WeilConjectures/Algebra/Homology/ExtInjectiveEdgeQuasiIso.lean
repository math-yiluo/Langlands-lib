/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ExtResolutionDoubleComplex
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation

/-! # The injective edge of the resolution Hom double complex

Source: Stacks Project, Tag 0954, proof of Lemma 47.8.2.
(blueprint: lem-sbc-ext-injective-edge-quasi-iso).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory Limits Opposite HomologicalComplex

namespace ModuleCat

private theorem yoneda_preservesHomology {R : Type u} [CommRing R]
    (J : ModuleCat.{u} R) [Injective J] :
    ((linearYoneda R (ModuleCat.{u} R)).obj J).PreservesHomology := by
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  have : PreservesLimits (F ⋙ forget (ModuleCat.{u} R)) := by
    change PreservesLimits (yoneda.obj J)
    infer_instance
  have : PreservesLimits F := preservesLimits_of_reflects_of_preserves
    F (forget (ModuleCat.{u} R))
  have : (F ⋙ forget (ModuleCat.{u} R)).PreservesEpimorphisms :=
    (Injective.injective_iff_preservesEpimorphisms_yoneda_obj J).mp inferInstance
  have : F.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_preserves_of_reflects
    F (forget (ModuleCat.{u} R))
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

/-- The injective edge is a quasi-isomorphism.
Source: Stacks Project, Tag 0954, injective-resolution computation of Ext.
(blueprint: lem-sbc-ext-injective-edge-quasi-iso).

Proof: the horizontal augmented complex in vertical degree j is
Hom(X,E^j) → Hom(P,E^j). Injectivity of E^j makes Hom(-,E^j) exact,
so this augmentation is a quasi-isomorphism. Apply first-quadrant total
comparison to these augmentations. Explicitly, in the augmented total
complex a cocycle has finitely many components. Remove the component
with smallest vertical degree using horizontal exactness and subtract
the signed total boundary of a lift. Its replacement has higher vertical
degree and lower horizontal degree. At horizontal degree -1 the monic
augmentation forces the last component to vanish. Thus the cone is acyclic
and the edge is a quasi-isomorphism. Its component is precomposition with
P.π followed by the (0,n) summand inclusion, so it is precisely the
constructed map. Degree zero and zero modules require no exception. -/
theorem resolutionHomInjectiveEdge_quasiIso
    {R : Type u} [CommRing R] {X M : ModuleCat.{u} R}
    (P : ProjectiveResolution X) (E : InjectiveResolution M) :
    QuasiIso (resolutionHomInjectiveEdge P E) := by
  let K := (((linearCoyoneda R (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℕ) (ComplexShape.up ℕ)).obj
      (resolutionHomOpposite P.complex)).obj E.cocomplex
  let A := (((linearCoyoneda R (ModuleCat.{u} R)).obj (op X)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj E.cocomplex
  let a : A ⟶ K.X 0 := (NatTrans.mapHomologicalComplex
    ((linearCoyoneda R (ModuleCat.{u} R)).map (P.π.f 0).op)
      (ComplexShape.up ℕ)).app E.cocomplex
  have ha : a ≫ K.d 0 1 = 0 := by
    ext n g
    change P.complex.d 1 0 ≫ P.π.f 0 ≫ g = 0
    rw [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]
  apply HomologicalComplex₂.quasiIso_of_column_augmentation K A a ha
    (resolutionHomInjectiveEdge P E) (fun _ => rfl)
  intro n
  let F := (linearYoneda R (ModuleCat.{u} R)).obj (E.cocomplex.X n)
  have : F.PreservesHomology := yoneda_preservesHomology (E.cocomplex.X n)
  let T := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((ChainComplex.single₀ (ModuleCat.{u} R)).obj X).op
  let t : (CochainComplex.single₀ (ModuleCat.{u} R)).obj (A.X n) ⟶ T :=
    (CochainComplex.fromSingle₀Equiv T (A.X n)).symm ⟨𝟙 _, by
      change (𝟙 _) ≫ F.map (((ChainComplex.single₀ (ModuleCat.{u} R)).obj X).d 1 0).op = 0
      simp only [HomologicalComplex.single_obj_d, op_zero, Functor.map_zero,
        comp_zero]⟩
  have ht (i : ℕ) : IsIso (t.f i) := by
    cases i with
    | zero =>
        change IsIso (𝟙 (A.X n))
        infer_instance
    | succ i =>
        apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
          (A.X n) (i + 1) (by omega)).isIso
        apply F.map_isZero
        exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
          X (i + 1) (by omega)).op
  have : IsIso t := HomologicalComplex.Hom.isIso_of_components t
  let φ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
    ((HomologicalComplex.opFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ)).map P.π.op)
  have : QuasiIso φ := by
    dsimp only [φ]
    infer_instance
  have hcomp : t ≫ φ = (CochainComplex.fromSingle₀Equiv (K.flip.X n) (A.X n)).symm
      ⟨a.f n, by simpa using congrArg (fun f => f.f n) ha⟩ := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    change (𝟙 _) ≫ F.map (P.π.f 0).op = _
    rfl
  rw [← hcomp]
  infer_instance

end ModuleCat
