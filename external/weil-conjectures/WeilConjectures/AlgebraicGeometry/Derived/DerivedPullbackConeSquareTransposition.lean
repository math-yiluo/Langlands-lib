/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.KFlatClosure
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.Algebra.Homology.Picard.AdditiveAdjunctionConeSquare
import WeilConjectures.AlgebraicGeometry.Picard.KFlatPullbackAdjunctionComparison

/-! # Derived transposition of a specified cone square -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem replacement (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (A B : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (t : A ⟶ B) :
    ∃ (P Q : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
      (p : P ⟶ Q) (x : P ⟶ A) (y : Q ⟶ B) (_h : p ≫ y = x ≫ t),
      P.IsAcyclicTensorKFlat ∧ Q.IsAcyclicTensorKFlat ∧ QuasiIso x ∧ QuasiIso y := by
  classical
  let E := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let := SheafOfModules.monoidalCategory S.sheaf
  let := SheafOfModules.symmetricCategory S.sheaf
  have : MonoidalPreadditive E := Classical.choice (SheafOfModules.tensorClosed S.sheaf).1
  let : MonoidalClosed E := Classical.choice (SheafOfModules.tensorClosed S.sheaf).2.1
  have : IsGrothendieckAbelian.{u} E := SheafOfModules.isGrothendieckAbelian _
  have : HasColimitsOfSize.{0, 0} E := hasColimitsOfSizeShrink.{0, 0, u, u} E
  have := schemeModule_hasFunctorialFlatResolution S
  have (M : E) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor E).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := MonoidalCategory.tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [MonoidalCategory.curriedTensor]))
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution E).some.reduced
  let R := Λ.kFlatResolutionFunctor ObjectProperty.flat.essImage_ι_le
  let ε := Λ.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le
  have toLean (K : CochainComplex.KFlat E) :
      CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) K.obj := by
    have h := (HomotopyCategory.kFlat_quotient_obj_iff K.obj).2 K.property
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic] at h
    intro N hN
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      ((h ((HomotopyCategory.quotient E (.up ℤ)).obj N)
        ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N).2 hN)).2)
  refine ⟨(R.obj A).obj, (R.obj B).obj, (R.map t).hom, ε.app A, ε.app B,
    ε.naturality t, toLean _, toLean _, ?_, ?_⟩
  · infer_instance
  · infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem cone_precompose
    {E : Type*} [Category E] [Preadditive E] [HasBinaryBiproducts E]
    {P Q A B A' B' : CochainComplex E ℤ}
    (p : P ⟶ Q) (t : A ⟶ B) (t' : A' ⟶ B')
    (x : P ⟶ A) (y : Q ⟶ B) (h : p ≫ y = x ≫ t)
    (α : A ⟶ A') (β : B ⟶ B') (H : Homotopy (t ≫ β) (α ≫ t')) :
    ∃ H₀ : Homotopy (p ≫ (y ≫ β)) ((x ≫ α) ≫ t'),
      CochainComplex.mappingCone.mapOfHomotopy H₀ =
        CochainComplex.mappingCone.map p t x y h ≫
          CochainComplex.mappingCone.mapOfHomotopy H := by
  let H₀ : Homotopy (p ≫ (y ≫ β)) ((x ≫ α) ≫ t') :=
    (Homotopy.ofEq (by rw [← Category.assoc, h, Category.assoc])).trans
      ((H.compLeft x).trans (Homotopy.ofEq (Category.assoc x α t').symm))
  refine ⟨H₀, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext n
  apply (CochainComplex.mappingCone.ext_from_iff p (n + 1) n rfl _ _).2
  constructor
  · simp [CochainComplex.mappingCone.mapOfHomotopy, CochainComplex.mappingCone.map,
      CochainComplex.HomComplex.Cochain.equivHomotopy, H₀, Homotopy.trans,
      Homotopy.ofEq, Homotopy.compLeft, Category.assoc,
      CochainComplex.HomComplex.Cochain.ofHomotopy]
  · simp [CochainComplex.mappingCone.mapOfHomotopy, CochainComplex.mappingCone.map,
      Category.assoc]

private theorem mappingCone_map_isIso
    {E : Type*} [Category E] [Abelian E] [HasDerivedCategory.{w} E]
    {P Q A B : CochainComplex E ℤ}
    (p : P ⟶ Q) (t : A ⟶ B) (x : P ⟶ A) (y : Q ⟶ B)
    (h : p ≫ y = x ≫ t) [IsIso (DerivedCategory.Q.map x)]
    [IsIso (DerivedCategory.Q.map y)] :
    IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.map p t x y h)) := by
  let m := DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap p t x y h)
  have h₁ : IsIso m.hom₁ := inferInstanceAs (IsIso (DerivedCategory.Q.map x))
  have h₂ : IsIso m.hom₂ := inferInstanceAs (IsIso (DerivedCategory.Q.map y))
  exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ m
    (DerivedCategory.mappingCone_triangle_distinguished p)
    (DerivedCategory.mappingCone_triangle_distinguished t) h₁ h₂

private theorem map_transpose_of_composite
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (Q : C ⥤ C') (Q' : D ⥤ D')
    {Ld : C' ⥤ D'} {Rd : D' ⥤ C'} (adj' : Ld ⊣ Rd)
    {P A : C} {I Z : D} (c : P ⟶ A) (b : P ⟶ R.obj I) (α : A ⟶ R.obj I)
    (k : Z ⟶ L.obj P) (a : Z ⟶ I)
    (e : Q'.obj (L.obj P) ⟶ Ld.obj (Q.obj P))
    (η : Q.obj (R.obj I) ⟶ Rd.obj (Q'.obj I))
    (ha : a = k ≫ (adj.homEquiv _ _).symm b) (hb : b = c ≫ α)
    (he : Q'.map ((adj.homEquiv _ _).symm b) =
      e ≫ (adj'.homEquiv _ _).symm (Q.map b ≫ η)) :
    Q'.map a = (Q'.map k ≫ e ≫ Ld.map (Q.map c)) ≫
      (adj'.homEquiv _ _).symm (Q.map α ≫ η) := by
  rw [ha, Functor.map_comp, he, hb, Functor.map_comp, Category.assoc,
    Adjunction.homEquiv_naturality_left_symm]
  simp only [Category.assoc]

-- Perform the cone construction with abstract functors, so its proof does not
-- repeatedly unfold the chosen tensor pullback and derived sheaf adjunction.
private theorem localized_cone_square_transposition
    {E E' : Type*} [Category E] [Category E'] [Abelian E] [Abelian E']
    [HasDerivedCategory.{w} E] [HasDerivedCategory.{w} E']
    {L : E ⥤ E'} {R : E' ⥤ E} [L.Additive] [R.Additive] (adj₀ : L ⊣ R)
    {Ld : DerivedCategory E ⥤ DerivedCategory E'}
    {Rd : DerivedCategory E' ⥤ DerivedCategory E} (adj : Ld ⊣ Rd)
    (η : R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rd)
    (K : CochainComplex E ℤ → Prop)
    (e : ∀ P (_ : K P), DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P) ≅
      Ld.obj (DerivedCategory.Q.obj P))
    (he : ∀ P (hP : K P) I (α : P ⟶ (R.mapHomologicalComplex (.up ℤ)).obj I),
      DerivedCategory.Q.map (((adj₀.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm α) =
        (e P hP).hom ≫ (adj.homEquiv _ _).symm (DerivedCategory.Q.map α ≫ η.app I))
    {P Q A B : CochainComplex E ℤ} {A' B' : CochainComplex E' ℤ}
    (p : P ⟶ Q) (t : A ⟶ B) (t' : A' ⟶ B')
    (x : P ⟶ A) (y : Q ⟶ B) (hc : p ≫ y = x ≫ t)
    (hP : K P) (hQ : K Q) (hconeP : K (CochainComplex.mappingCone p))
    (hx : QuasiIso x) (hy : QuasiIso y)
    (α : A ⟶ (R.mapHomologicalComplex (.up ℤ)).obj A')
    (β : B ⟶ (R.mapHomologicalComplex (.up ℤ)).obj B')
    (H : Homotopy (t ≫ β) (α ≫ (R.mapHomologicalComplex (.up ℤ)).map t')) :
    ∃ (C D : CochainComplex E' ℤ) (s : C ⟶ D) (a : C ⟶ A') (b : D ⟶ B')
      (H' : Homotopy (s ≫ b) (a ≫ t'))
      (d₁ : DerivedCategory.Q.obj C ≅ Ld.obj (DerivedCategory.Q.obj A))
      (d₂ : DerivedCategory.Q.obj D ≅ Ld.obj (DerivedCategory.Q.obj B))
      (d₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone s) ≅
        Ld.obj (DerivedCategory.Q.obj (CochainComplex.mappingCone t))),
      DerivedCategory.Q.map a =
        d₁.hom ≫ (adj.homEquiv _ _).symm (DerivedCategory.Q.map α ≫ η.app A') ∧
      DerivedCategory.Q.map b =
        d₂.hom ≫ (adj.homEquiv _ _).symm (DerivedCategory.Q.map β ≫ η.app B') ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H') =
        d₃.hom ≫ (adj.homEquiv _ _).symm
          (DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H ≫
            (CochainComplex.mappingCone.mapHomologicalComplexIso t' R).inv) ≫
              η.app (CochainComplex.mappingCone t')) := by
  let lc := L.mapHomologicalComplex (.up ℤ)
  let ac := adj₀.mapHomologicalComplex (.up ℤ)
  obtain ⟨H₀, hcone⟩ := cone_precompose p t _ x y hc α β H
  obtain ⟨H', htrans⟩ := CochainComplex.additiveAdjunction_cone_square
    adj₀ p t' (x ≫ α) (y ≫ β) H₀
  let c := CochainComplex.mappingCone.map p t x y hc
  have : IsIso (DerivedCategory.Q.map x) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ x).2 hx
  have : IsIso (DerivedCategory.Q.map y) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ y).2 hy
  have : IsIso (DerivedCategory.Q.map c) := mappingCone_map_isIso p t x y hc
  refine ⟨lc.obj P, lc.obj Q, lc.map p, (ac.homEquiv _ _).symm (x ≫ α),
    (ac.homEquiv _ _).symm (y ≫ β), H',
    e P hP ≪≫ Ld.mapIso (asIso (DerivedCategory.Q.map x)),
    e Q hQ ≪≫ Ld.mapIso (asIso (DerivedCategory.Q.map y)),
    DerivedCategory.Q.mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso p L).symm ≪≫
      e _ hconeP ≪≫ Ld.mapIso (asIso (DerivedCategory.Q.map c)), ?_, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Functor.map_comp,
      Adjunction.homEquiv_naturality_left_symm, Category.assoc] using he P hP A' (x ≫ α)
  · simpa only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Functor.map_comp,
      Adjunction.homEquiv_naturality_left_symm, Category.assoc] using he Q hQ B' (y ≫ β)
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
    apply map_transpose_of_composite ac DerivedCategory.Q DerivedCategory.Q adj
      c _ _ (CochainComplex.mappingCone.mapHomologicalComplexIso p L).inv _
      (e _ hconeP).hom _ htrans
    · exact (congrArg (fun k ↦ k ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso t' R).inv) hcone).trans
          (Category.assoc _ _ _)
    · exact he _ hconeP _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
/-- Transpose a specified cone-square through derived pullback/direct image.
This is independent of open covers and of base-change comparison maps.
Source: Stacks Project, Cohomology, Tags 06YI and 06YJ (K-flat computations),
079W (derived adjunction), and Derived Categories, Tag 014P (cone formulas).
(blueprint: lem-pc-derived-pullback-cone-square-transposition).

Proof: Choose a K-flat resolution Q -> B. Represent the composite of Q(t)
with the inverse localized resolution by a right fraction out of A. Refine
its denominator until the resulting square commutes in the homotopy category,
then replace its source by a K-flat resolution P. This yields a homotopy
square from P -> Q to A -> B whose vertical maps are quasi-isomorphisms.
Its specified cone comparison is a quasi-isomorphism by the cone triangle.
The two replacement vertices and their cone are K-flat. Precompose alpha and
beta with the replacement and compose its square homotopy with H. Use the
underived tensor-pullback/direct-image adjunction to transpose these two chain
maps and the degree-minus-one cochain of H. The adjunction is additive and commutes with
differentials, so its
transpose is a homotopy H' for the resulting square. Termwise tensor pullback
commutes with mapping cones. Hence transposing the two-component formula for
mapOfHomotopy H gives exactly mapOfHomotopy H', including its sign. The K-flat
counit identifies the localized two source complexes and cone with Lg* Q(A),
Lg* Q(B) and Lg* Q(Cone t), giving d1,d2,d3. The canonical derived adjunction
is obtained from this underived adjunction and the left-derived counit and
right-derived unit. Its homEquiv therefore identifies each localized chain
transpose with the displayed transpose of Q(alpha) eta, Q(beta) eta, and the
specified cone map followed by eta. The cone comparison for the additive
direct-image functor accounts for its inverse in the third formula. Comparing
with relativeMVAdj uses uniqueness with those pinned units and counits.
The construction permits arbitrary complexes and homotopies, without bounds,
flatness of g or K-injectivity of A',B'. Zero complexes and the zero homotopy
are covered by the same additive construction. -/
theorem derivedPullback_cone_square_transposition
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (A B : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (A' B' : CochainComplex (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
    (t : A ⟶ B) (t' : A' ⟶ B') :
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    ∀ (α : A ⟶ F.obj A') (β : B ⟶ F.obj B')
      (H : Homotopy (t ≫ β) (α ≫ F.map t')),
    ∃ (C D : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (s : C ⟶ D) (a : C ⟶ A') (b : D ⟶ B')
      (H' : Homotopy (s ≫ b) (a ≫ t'))
      (d₁ : DerivedCategory.Q.obj C ≅ (derivedPullback g).obj (DerivedCategory.Q.obj A))
      (d₂ : DerivedCategory.Q.obj D ≅ (derivedPullback g).obj (DerivedCategory.Q.obj B))
      (d₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone s) ≅
        (derivedPullback g).obj (DerivedCategory.Q.obj (CochainComplex.mappingCone t))),
      DerivedCategory.Q.map a =
        d₁.hom ≫ (adj.homEquiv _ _).symm (DerivedCategory.Q.map α ≫ η.app A') ∧
      DerivedCategory.Q.map b =
        d₂.hom ≫ (adj.homEquiv _ _).symm (DerivedCategory.Q.map β ≫ η.app B') ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H') =
        d₃.hom ≫ (adj.homEquiv _ _).symm
          (DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H ≫
            (CochainComplex.mappingCone.mapHomologicalComplexIso t' G).inv) ≫
              η.app (CochainComplex.mappingCone t')) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf, moduleRings] at *
  intro α β H
  obtain ⟨hL, e, he⟩ := kFlat_pullback_adjunction_comparison g
  obtain ⟨P, Q, p, x, y, hc, hP, hQ, hx, hy⟩ := replacement S A B t
  exact localized_cone_square_transposition
    (E := SheafOfModules.{u} (moduleRings S.toRingedSpace))
    (E' := SheafOfModules.{u} (moduleRings S'.toRingedSpace))
    (L := Scheme.Modules.tensorPullback g)
    (R := RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g))
    (relativeMVAdj g) (schemeMVDirectImageLocalization g)
    (CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf)) e he
    p t t' x y hc hP hQ (CochainComplex.isKFlat_mappingCone p hP hQ) hx hy α β H

end AlgebraicGeometry
