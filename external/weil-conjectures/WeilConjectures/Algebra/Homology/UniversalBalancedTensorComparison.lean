/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Universal scalar extension computed by a fixed second-factor resolution

Source: Stacks Project, Tags 064L and 06Y6.
(blueprint: new-lem-pc-universal-balanced-tensor-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings


namespace RingTensorCohomology

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def extensionTensorIso
    {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B) (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars f).obj ((ModuleCat.extendScalars f).obj M) ≅
      MonoidalCategory.tensorObj M
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) := by
  let := f.toAlgebra
  let : Module R ((ModuleCat.extendScalars f).obj M) :=
    ((ModuleCat.restrictScalars f).obj ((ModuleCat.extendScalars f).obj M)).isModule
  let e := TensorProduct.comm R B M
  exact LinearEquiv.toModuleIso
    { e.toAddEquiv with
      map_smul' := by
        intro r x
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp_all
        | tmul b m =>
          change B at b
          change m ⊗ₜ[R] (f r * b) = r • (m ⊗ₜ[R] b)
          change m ⊗ₜ[R] (r • b) = r • (m ⊗ₜ[R] b)
          exact TensorProduct.tmul_smul r m b }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def extensionTensorNatIso
    {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B) :
    ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f ≅
      MonoidalCategory.tensorRight ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) :=
  NatIso.ofComponents (extensionTensorIso f) (by
    intro M N g
    ext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp_all
    | tmul b m => rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def coefficientRingIso
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B B) ≅
      ModuleCat.of R B :=
  { hom := ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B B))
      (Y := ModuleCat.of R B)
      { toFun := fun b ↦ b
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro r b
          change B at b
          exact (Algebra.smul_def r b).symm }
    inv := ModuleCat.ofHom
      (X := ModuleCat.of R B)
      (Y := (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B B))
      { toFun := fun b ↦ b
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro r b
          change B at b
          exact Algebra.smul_def r b }
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def extensionTensorComplexIso
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    extend R B ⋙ (ModuleCat.restrictScalars (algebraMap R B)).mapHomologicalComplex
      (.up ℤ) ≅
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.flip.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R B)) := by
  let G := MonoidalCategory.curriedTensor (ModuleCat.{u} R)
  let t := Functor.mapIso G.flip (coefficientRingIso R B)
  exact Functor.mapHomologicalComplexCompIso
    (extensionTensorNatIso (algebraMap R B) ≪≫ t) (.up ℤ) ≪≫
      (CochainComplex.map₂HomologicalComplexFlipObjSingleIso G (ModuleCat.of R B)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def homologyRestrictionIso
    {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B) (i : ℤ) :
    HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i ⋙
      ModuleCat.restrictScalars f ≅
    (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i :=
  NatIso.ofComponents (fun K ↦ ((K.sc i).mapHomologyIso (ModuleCat.restrictScalars f)).symm)
    (fun g ↦ ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ i).map g) (ModuleCat.restrictScalars f))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The resolved scalar-extension model and tensor with a K-flat second factor
have naturally isomorphic additive homology functors.
Source: Stacks Project, Tags 064L and 06Y6.
(blueprint: new-lem-pc-universal-balanced-tensor-comparison).

Proof: Write P(X) for the functorial K-flat resolution of X, and s_X for its
augmentation. Form the natural span P(X) tensor F -> X tensor F and
P(X) tensor F -> P(X) tensor B[0]. The first arrow is tensor of s_X with F,
and is a quasi-isomorphism by K-flatness of F. The second arrow is tensor
of P(X) with f and is a quasi-isomorphism by K-flatness of P(X).
The single-factor total tensor isomorphism identifies P(X) tensor B[0]
with termwise P(X) tensor B. Tensor symmetry identifies this with the
restriction of extendScalars(R -> B)(P(X)); on generators it sends x tensor b
to b tensor x. Restriction of scalars is exact, so commutes naturally with
homology. Forget to additive groups and compose these identifications with
the homology map of the first span arrow and the inverse of the second.
Functoriality of the resolution, tensor and homology gives a natural
isomorphism. This works in every degree for unbounded complexes and arbitrary
R-algebras B, including zero rings and zero complexes. -/
private theorem exists_resolutionBalancedTensorIso
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (i : ℤ) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj
      (ModuleCat.of R B)) (hf : QuasiIso f)
    (hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F) :
    Nonempty ((resolution R ⋙ extend R B ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i ⋙
        forget₂ (ModuleCat.{u} B) AddCommGrpCat) ≅
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.flip.obj F ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i ⋙
          forget₂ (ModuleCat.{u} R) AddCommGrpCat)) := by
  classical
  let T := (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex
  let J := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i ⋙
    forget₂ (ModuleCat.{u} R) AddCommGrpCat
  let TF := T.flip.obj F
  let a := Functor.whiskerRight (Functor.whiskerRight (augmentation R) TF) J
  have : IsIso a := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro X
    have hs : QuasiIso ((augmentation R).app X) := by
      dsimp [augmentation]
      infer_instance
    have ht : QuasiIso (TF.map ((augmentation R).app X)) := hF.whiskerRight hs
    change IsIso (J.map (TF.map ((augmentation R).app X)))
    change IsIso ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).map
      (HomologicalComplex.homologyMap _ i))
    infer_instance
  let c := Functor.whiskerRight
    (Functor.whiskerLeft (resolution R) (T.flip.map f)) J
  have : IsIso c := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro X
    have hP := (flatResolution R).kFlat_resolutionFunctor_obj
      ObjectProperty.flat.essImage_ι_le X
    have ht : QuasiIso ((T.flip.map f).app ((resolution R).obj X)) := hP.whiskerLeft hf
    change IsIso (J.map ((T.flip.map f).app ((resolution R).obj X)))
    change IsIso ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).map
      (HomologicalComplex.homologyMap _ i))
    infer_instance
  let U := forget₂ (ModuleCat.{u} R) AddCommGrpCat
  let d := Functor.isoWhiskerLeft (resolution R ⋙ extend R B)
    (Functor.isoWhiskerRight (homologyRestrictionIso (algebraMap R B) i) U)
  let e := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (resolution R) (extensionTensorComplexIso R B)) J
  exact ⟨d ≪≫ e ≪≫ (asIso c).symm ≪≫ asIso a⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolution_kFlat (R : Type u) [CommRing R]
    (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
      ((resolution R).obj X) :=
  (flatResolution R).kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le X

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolution_counit_isIso
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (ε.app ((HomotopyCategory.quotient _ _).obj ((resolution R).obj X))) := by
  apply ModuleCat.scalarExtensionCounit_isIso_of_kFlat (algebraMap R B) _ _ L ε hL
  intro N hN
  have ht := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 (resolution_kFlat R X))
    ((HomotopyCategory.quotient _ _).obj N)
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N).2 hN)
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 ht.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def resolutionDerivedIso
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ L ≅
      resolution R ⋙ extend R B ⋙
        HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙ DerivedCategory.Qh := by
  let V := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
  let s := Functor.whiskerRight (augmentation R) (V ⋙ L)
  have : IsIso s := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro X
    have : QuasiIso ((augmentation R).app X) := by
      dsimp [augmentation]
      infer_instance
    have : IsIso (V.map ((augmentation R).app X)) :=
      (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)) _).2
        (inferInstanceAs (IsIso (DerivedCategory.Q.map ((augmentation R).app X))))
    change IsIso (L.map (V.map ((augmentation R).app X)))
    infer_instance
  let c := Functor.whiskerLeft
    (resolution R ⋙ HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)) ε
  have : IsIso c := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro X
    exact resolution_counit_isIso L ε hL X
  exact (asIso s).symm ≪≫ asIso c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Natural additive comparisons for universal scalar extension and a fixed K-flat
second factor. Source: Stacks Project, Tags 064L and 06Y6.
(blueprint: new-lem-pc-universal-balanced-tensor-comparison).

Proof: use the functorial R-K-flat resolution P(X) -> X. Tensoring its augmentation
with F is a quasi-isomorphism because F is K-flat. Tensoring F -> B[0] with P(X)
is a quasi-isomorphism because P(X) is K-flat. Identify P(X) tensor B[0] with
restriction of the ordinary extension of P(X) to B, on pure tensors by
x tensor b -> b tensor x. The universal scalar-extension counit at P(X) is
invertible by scalarExtensionCounit_isIso_of_kFlat. Its composite with the inverse
of the derived image of P(X) -> X therefore compares the given universal functor
with this span. Take homology and forget to additive groups to obtain e.
Naturality of the resolution augmentation, tensoring, the counit and the homology
comparison proves the first equation. The defining counit equation for the unique
isomorphism between two universal left derived functors proves the second equation
at P(X); naturality for P(X) -> X then proves it at X. The two quasi-isomorphism
inverses cancel in both equations. There are no boundedness or flatness assumptions
on B or X; zero complexes and zero rings are included. -/
theorem exists_universalBalancedTensorComparison
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (i : ℤ) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj
      (ModuleCat.of R B)) (hf : QuasiIso f)
    (hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F) :
    let V := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    let T := (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex
    let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)
    ∃ e : ∀ (L : DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} B))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      L.IsLeftDerivedFunctor ε W → ∀ X : CochainComplex (ModuleCat.{u} R) ℤ,
        H.obj (L.obj (V.obj X)) ≃+ (((T.obj X).obj F).homology i),
      (∀ L ε hL X Y (g : X ⟶ Y) x,
        e L ε hL Y (H.map (L.map (V.map g)) x) =
          HomologicalComplex.homologyMap ((T.map g).app F) i (e L ε hL X x)) ∧
      (∀ (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
        (ε : DerivedCategory.Qh ⋙ L ⟶
          (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh) (hL : L.IsLeftDerivedFunctor ε W)
        (K : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
        (δ : DerivedCategory.Qh ⋙ K ⟶
          (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh) (hK : K.IsLeftDerivedFunctor δ W) X x,
        letI := hL
        letI := hK
        let ζ := Functor.leftDerivedNatIso L K ε δ W (Iso.refl _)
        e K δ hK X (H.map (ζ.hom.app (V.obj X)) x) = e L ε hL X x) := by
  classical
  dsimp only
  let V := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let U := forget₂ (ModuleCat.{u} B) AddCommGrpCat
  let C := resolution R ⋙ extend R B
  let β : (HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙
      DerivedCategory.Qh) ⋙ H ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i :=
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)) H ≪≫
      DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i
  obtain ⟨b⟩ := exists_resolutionBalancedTensorIso R B i F f hf hF
  let a := fun L ε hL ↦
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (resolutionDerivedIso L ε hL) H ≪≫
        Functor.isoWhiskerLeft C β) U ≪≫ b
  refine ⟨fun L ε hL X ↦ ((a L ε hL).app X).addCommGroupIsoToAddEquiv, ?_, ?_⟩
  · intro L ε hL X Y g x
    exact congrArg (fun t : (V ⋙ L ⋙ H ⋙ U).obj X ⟶ _ ↦ t x)
      ((a L ε hL).hom.naturality g)
  · intro L ε hL K δ hK X x
    let := hL
    let := hK
    let ζ := Functor.leftDerivedNatIso L K ε δ
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
    have hz : ζ.hom.app (V.obj X) ≫ (resolutionDerivedIso K δ hK).hom.app X =
        (resolutionDerivedIso L ε hL).hom.app X := by
      let s := V.map ((augmentation R).app X)
      have : QuasiIso ((augmentation R).app X) := by
        dsimp [augmentation]
        infer_instance
      have : IsIso s :=
        (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)) _).2
          (inferInstanceAs (IsIso (DerivedCategory.Q.map ((augmentation R).app X))))
      apply (cancel_epi (L.map s)).1
      simp only [resolutionDerivedIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
        asIso_inv, NatTrans.comp_app, NatIso.isIso_inv_app]
      change L.map s ≫ (ζ.hom.app (V.obj X) ≫
        (inv (K.map s) ≫ δ.app ((HomotopyCategory.quotient _ _).obj
          ((resolution R).obj X)))) =
        L.map s ≫ (inv (L.map s) ≫ ε.app ((HomotopyCategory.quotient _ _).obj
          ((resolution R).obj X)))
      have hn : L.map s ≫ ζ.hom.app (V.obj X) =
          ζ.hom.app (V.obj ((resolution R).obj X)) ≫ K.map s := ζ.hom.naturality s
      rw [← Category.assoc, hn]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      have hz' := Functor.leftDerivedNatTrans_app L K ε δ
        (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))
        (𝟙 _) ((HomotopyCategory.quotient _ _).obj ((resolution R).obj X))
      rw [NatTrans.id_app, Category.comp_id] at hz'
      exact hz'
    have he : U.map (H.map (ζ.hom.app (V.obj X))) ≫ (a K δ hK).hom.app X =
        (a L ε hL).hom.app X := by
      dsimp [a]
      rw [← U.map_comp_assoc, ← H.map_comp_assoc, hz]
    exact congrArg (fun t : (V ⋙ L ⋙ H ⋙ U).obj X ⟶ _ ↦ t x) he

end RingTensorCohomology
