/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.Algebra.Homology.TorIndependentTensorAugmentation
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # The scalar extension of resolutions under Tor independence

Source: Stacks Project, More on Algebra, Section 06Y5 and Tag 06Y6;
Tag 08IB, the Tor-independent affine calculation.
(blueprint: lem-pc-tor-independent-kflat-resolution-tensor).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace ModuleCat

open MonoidalCategory in
open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorScalarIso
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] :
    tensorRight ((restrictScalars (algebraMap R B)).obj (of B B)) ≅
      extendScalars (algebraMap R B) ⋙ restrictScalars (algebraMap R B) := by
  letI := (algebraMap R B).toAlgebra
  exact NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    (show (tensorRight ((restrictScalars (algebraMap R B)).obj (of B B))).obj M ≃ₗ[R]
        (restrictScalars (algebraMap R B)).obj
          ((extendScalars (algebraMap R B)).obj M) from
      { (TensorProduct.comm R M ((restrictScalars (algebraMap R B)).obj (of B B))).toAddEquiv
          with
        map_smul' := by
          intro r x
          induction x using TensorProduct.inductionOn with
          | tmul m b =>
            change B at b
            change b ⊗ₜ[R, algebraMap R B] (r • m) =
              (algebraMap R B r * b) ⊗ₜ[R, algebraMap R B] m
            rw [TensorProduct.tmul_smul]
            rfl
          | add x y hx hy => simp_all })) (by
      intro M N g
      ext : 1
      apply TensorProduct.ext'
      intro m b
      rfl)

/-- A K-flat resolution over R of the restriction of an A-K-flat complex
still computes ordinary extension to B if A and B are Tor independent over R.
Source: Stacks Project, Tags 06Y5, 06Y6 and 08IB.
(blueprint: lem-pc-tor-independent-kflat-resolution-tensor).

Proof: Resolve B[0] over R by a bounded-above projective complex F with
augmentation f. The complex A tensor_R F has cohomology E = A tensor_R B in
degree zero and Tor_i^R(A,B) in degree -i; it has zero positive cohomology.
Balancedness follows by resolving both A and B and comparing the two
filtrations of the double tensor complex, with finite diagonals in each degree.
Thus Tor vanishing makes A tensor_R f a quasi-isomorphism of A-complexes.
Its cone is acyclic. Tensoring this cone with Q over A preserves acyclicity by
hK. The signed tensor-cone identification and mixed tensor associativity show
that Q tensor_R F -> Q tensor_R B is a quasi-isomorphism after restriction to R.
The same augmentation for P is a quasi-isomorphism by its R-K-flatness.
Tensoring s with F is a quasi-isomorphism because F is bounded above with
projective, hence flat, terms and therefore R-K-flat. The commuting tensor
square, with three sides now quasi-isomorphisms, makes s tensor_R B a
quasi-isomorphism. Tensor symmetry identifies this with restriction of the
termwise scalar extension of s to B. Exact restriction reflects homology
isomorphisms, giving the asserted B-linear quasi-isomorphism. No boundedness
of Q or P is used. The argument also applies to zero complexes and rings. -/
theorem scalarExtension_quasiIso_of_torIndependent_kFlat
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} R) i).obj (ModuleCat.of R A)).obj
        (ModuleCat.of R B)))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L Q (MonoidalCategory.curriedTensor _)).Acyclic)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
    (s : P ⟶ (((restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj Q))
    (hs : QuasiIso s) :
    QuasiIso (((extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).map s) := by
  let G := ModuleCat.of R (Shrink.{u} R)
  have hG : ObjectProperty.flat G :=
    ObjectProperty.prop_of_iso _ (Shrink.linearEquiv.{u, u, u} R R).toModuleIso.symm
      (ObjectProperty.prop_unit _)
  have : Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R) :=
    ⟨{ F := ObjectProperty.lift _ (coyoneda.obj (Opposite.op G) ⋙ sigmaConst.obj G)
          (fun _ ↦ ObjectProperty.flat_coproduct _ (fun _ ↦ hG))
       π := (sigmaConstAdj G).counit
       epi_π_app X := (isSeparator_iff_epi G).1 (ModuleCat.isSeparator R) X }⟩
  have (N : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).obj N) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorLeft N))
  have (N : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).flip.obj N) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℤ)).symm
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)
  let E := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj
    ((restrictScalars (algebraMap R B)).obj (of B B))
  let X := ((restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj Q
  let r : W.localizerMorphismKFlat.LeftResolution E := Classical.arbitrary _
  let F := r.X₁.obj
  let f : F ⟶ E := r.w
  have hF : W.kFlat F := r.X₁.property
  have hf : QuasiIso f := r.hw
  have hPf : QuasiIso (MonoidalCategory.whiskerLeft P f) := hP.whiskerLeft hf
  have hXf : QuasiIso (MonoidalCategory.whiskerLeft X f) :=
    tensorAugmentation_quasiIso_of_torIndependent hTor Q hK F hF f hf
  have hsF : QuasiIso (MonoidalCategory.whiskerRight s F) := hF.whiskerRight hs
  have hbottom : QuasiIso (MonoidalCategory.whiskerRight s E) := by
    apply (quasiIso_iff_comp_left (MonoidalCategory.whiskerLeft P f)
      (MonoidalCategory.whiskerRight s E)).1
    rw [MonoidalCategory.whisker_exchange s f]
    infer_instance
  let e : MonoidalCategory.tensorRight E ≅
      (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ) ⋙
        (restrictScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ) :=
    CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      ((restrictScalars (algebraMap R B)).obj (of B B)) ≪≫
        NatIso.mapHomologicalComplex (tensorScalarIso (R := R) (B := B)) (.up ℤ)
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (((extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).map s)
    (restrictScalars (algebraMap R B))).1
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app P) (e.app X) (e.hom.naturality s).symm)).1 hbottom

end ModuleCat
