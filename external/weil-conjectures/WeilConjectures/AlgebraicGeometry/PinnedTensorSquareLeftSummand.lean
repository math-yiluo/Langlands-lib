/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.AlgebraicGeometry.PinnedStalkTensor
import WeilConjectures.AlgebraicGeometry.ModulePinnedTensorStalkSquare
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk

/-! # Stalk compatibility of a specified tensor pullback chain map

Source: Stacks Project, perfect.tex, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-pinned-tensor-square-left-summand).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry

@[instance_reducible] local instance pinnedTensorSquareLeftSummandInstance1 (Y : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  SheafOfModules.monoidalCategory Y.sheaf

local instance pinnedTensorSquareLeftSummandInstance2 (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  modulePreadditive Y

local instance pinnedTensorSquareLeftSummandInstance3
    (Y : Scheme.{u}) : (curriedTensor Y.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf

local instance pinnedTensorSquareLeftSummandInstance4 (Y : Scheme.{u}) (M : Y.Modules) :
    ((curriedTensor Y.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Y.sheaf M

-- Keep the categorical chase independent of the stalk and total-complex definitions.
private theorem summand_chase {C : Type*} [Category C]
    {A B C₀ D E F K B₀ D₀ E₀ F₀ H I J : C}
    (s : A ⟶ B) (t : B ⟶ C₀) (u : C₀ ⟶ D) (v : D ⟶ E) (w : E ⟶ F)
    (e : F ≅ K) (s₀ : A ⟶ B₀) (t₀ : B₀ ⟶ C₀) (u₀ : B₀ ⟶ D₀)
    (v₀ : D₀ ⟶ D) (c₀ : D₀ ⟶ E₀) (j₀ : E₀ ⟶ E) (a₀ : E₀ ⟶ F₀)
    (j₁ : F₀ ⟶ F) (tx₁ : F₀ ⟶ J) (tx₀ : E₀ ⟶ I) (l : I ⟶ J)
    (j : J ⟶ K) (q : A ⟶ H) (r : H ⟶ I)
    (hs : s ≫ t = s₀ ≫ t₀) (hn : t₀ ≫ u = u₀ ≫ v₀)
    (hc : v₀ ≫ v = c₀ ≫ j₀) (hj : j₀ ≫ w = a₀ ≫ j₁)
    (ht : j₁ ≫ e.hom = tx₁ ≫ j) (ha : a₀ ≫ tx₁ = tx₀ ≫ l)
    (hm : s₀ ≫ u₀ ≫ c₀ ≫ tx₀ = q ≫ r) :
    s ≫ t ≫ u ≫ v ≫ w = q ≫ r ≫ l ≫ j ≫ e.inv := by
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc s t, hs]
  simp only [Category.assoc]
  rw [← Category.assoc t₀ u, hn]
  simp only [Category.assoc]
  rw [← Category.assoc v₀ v, hc]
  simp only [Category.assoc]
  rw [← Category.assoc j₀ w, hj]
  simp only [Category.assoc, ht]
  rw [← Category.assoc a₀ tx₁, ha]
  simp only [Category.assoc]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ l ≫ j) hm

private theorem pinnedSummand_inverse {C : Type*} [Category C]
    {A B D E : C} (e : B ≅ E) (t : A ≅ D) (j : A ⟶ B) (i : D ⟶ E)
    (h : j ≫ e.hom = t.hom ≫ i) : i ≫ e.inv = t.inv ≫ j := by
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, h, Iso.inv_hom_id_assoc]

private theorem pinnedTensorStalk_transport_naturality {X X' : Scheme.{u}}
    (g' : X' ⟶ X) (z : X')
    (a : X.presheaf.stalk (g' z) →+* X'.presheaf.stalk z)
    (ha : a = (g'.stalkMap z).hom) {M N : X.Modules} (u : M ⟶ N) :
    let T := RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)
    let D := RingedSpace.moduleStalkFunctor X'.toRingedSpace z
    let H := Scheme.Modules.tensorPullback g'
    let k := fun L : X.Modules ↦
      eqToHom (congrArg (fun a ↦ (ModuleCat.extendScalars a).obj (T.obj L)) ha) ≫
        (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.app L
    (ModuleCat.extendScalars a).map (T.map u) ≫ k N = k M ≫ D.map (H.map u) := by
  subst a
  dsimp only
  simp only [eqToHom_refl, Category.id_comp]
  exact (Classical.choose
    (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.naturality u

-- Prove transport of the module square before introducing complexes and tensor totals.
private theorem pinnedTensorStalkSquare_transport {X X' : Scheme.{u}}
    (g' : X' ⟶ X) (z : X')
    (a : X.presheaf.stalk (g' z) →+* X'.presheaf.stalk z)
    (ha : a = (g'.stalkMap z).hom) (M N : X.Modules) :
    let T := RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)
    let D := RingedSpace.moduleStalkFunctor X'.toRingedSpace z
    let H := Scheme.Modules.tensorPullback g'
    let ty := Classical.choose (SheafOfModules.stalkTensorIso X.toRingedSpace (g' z))
    let tx := Classical.choose (SheafOfModules.stalkTensorIso X'.toRingedSpace z)
    let c := Classical.choose (Scheme.Modules.module_pullback_tensor g')
    let k := fun L : X.Modules ↦
      eqToHom (congrArg (fun a ↦ (ModuleCat.extendScalars a).obj (T.obj L)) ha) ≫
        (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.app L
    (ModuleCat.extendScalars a).map (ty M N).inv ≫ k (M ⊗ N) ≫
        D.map (c M N).hom ≫ (tx (H.obj M) (H.obj N)).hom =
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars a) (T.obj M) (T.obj N) ≫
        (k M ⊗ₘ k N) := by
  subst a
  dsimp only
  simp only [eqToHom_refl, Category.id_comp]
  apply (cancel_epi (Functor.Monoidal.μIso
    (ModuleCat.extendScalars (g'.stalkMap z).hom)
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).obj M)
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).obj N)).hom).1
  have h := Scheme.Modules.module_pinned_tensor_stalk_square g' z M N
  simpa only [Category.assoc, Functor.Monoidal.μIso_hom,
    Functor.Monoidal.μ_δ_assoc] using h

/-- Pullback route on one tensor summand, in explicit stalk coordinates.

Proof: invert the pinned source injection equation by cancelling its degree-n hom.
Map this equation under scalar extension. Rewrite the degree-n pullback-stalk
comparison using its specified component. Its naturality moves the sheaf tensor
summand injection through this comparison; the restriction equation for the actual
ring map identifies scalar extension with extension along g'.stalkMap z. Map hχ under
the target stalk functor. The bifunctor-map summand equation moves identity tensor a
to identity tensor a.f q. The target module tensor-stalk naturality equation then
moves this map to identity tensor S(a)_q. The target pinned injection equation
identifies its injection followed by e'.hom_n. The module tensor pullback/stalk
square on P.X p and Q.X q gives δ_G followed by κ_P,p tensor κ_Q,q: represent the two
stalk vectors by sections on a common neighborhood, use the canonical tensor-stalk
and pullback tensor generator formulas, and check the scalar-extension tensorator
on one tensor a pure tensor. Extension-of-scalars extensionality and tensor induction
extend this equality to every element of this single summand. A categorical diagram
chase combines the six equations after postcomposition with e'.hom_n, and cancels
e'.inv_n followed by e'.hom_n to obtain the displayed formula. No coproduct
extensionality or chain-map
extensionality occurs here. Zero stalk rings, zero modules, and unbounded complexes
are allowed, since the calculation is in the two modules in degrees p and q.
Source: Stacks Project, perfect.tex, Tag 0DJA(1), using Tag 0BYJ; Modules, Tags 01CD
and 01CB; Sheaves, Tag 0098.
(blueprint: lem-pc-pinned-tensor-square-left-summand). -/
theorem pinned_tensor_square_left_summand
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ)
    (a : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q ⟶ N)
    (χ : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P Q) ≅
      pullbackTensorTotal X'
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q))
    (hχ : ∀ (p q n : ℤ) (h : p + q = n),
      (Scheme.Modules.tensorPullback g').map
          (HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q n h) ≫
        χ.hom.f n =
      ((Classical.choose (Scheme.Modules.module_pullback_tensor g')) (P.X p) (Q.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q)
          (curriedTensor _) (.up ℤ) p q n h) (z : X') (n p q : ℤ) (h : p + q = n) :
    letI := SingleComplexBaseChange.leftAlgebra f g' z
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
    let R := SingleComplexBaseChange.R f g' z
    let A := SingleComplexBaseChange.A g' z
    let B := SingleComplexBaseChange.B f' z
    let C := SingleComplexBaseChange.C z
    let F := (ModuleCat.extendScalars.{u, u, u}
      ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))).mapHomologicalComplex (.up ℤ)
    let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
      (.up ℤ)
    let U := SingleComplexBaseChange.stalkComplex g' z P
    let V := SingleComplexBaseChange.stalkComplex g' z Q
    let H := (Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)
    let e := Classical.choose (exists_pinned_stalk_tensor X (g' z))
    let e' := Classical.choose (exists_pinned_stalk_tensor X' z)
    let σ : U ⊗ V ≅ SingleComplexBaseChange.stalkComplex g' z
      (pullbackTensorTotal X P Q) := (e P Q).symm
    let G := ModuleCat.extendScalars.{u, u, u}
      ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))
    let ι := G.map (HomologicalComplex.ιMapBifunctor U V
      (curriedTensor _) (.up ℤ) p q n h)
    ι ≫ (F.map σ.hom ≫
          (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z
            (pullbackTensorTotal X P Q)).hom ≫
          S.map (χ.hom ≫
            HomologicalComplex.mapBifunctorMap (𝟙 _) a (curriedTensor _) (.up ℤ))).f n =
      Functor.OplaxMonoidal.δ G (U.X p) (V.X q) ≫
      ((SingleComplexBaseChange.tensorStalkIso f f' g g' sq z P).hom.f p ⊗ₘ
        (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z Q).hom.f q) ≫
      (𝟙 _ ⊗ₘ (S.map a).f q) ≫
      HomologicalComplex.ιMapBifunctor (S.obj (H.obj P)) (S.obj N)
        (curriedTensor _) (.up ℤ) p q n h ≫ (e' (H.obj P) N).inv.f n := by
  classical
  extract_lets _ _ _ _ _ S₀ _ _ H₀ e₀ e₀'
  let := SingleComplexBaseChange.leftAlgebra f g' z
  let := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
  let := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
  let : (curriedTensor X'.Modules).PreservesZeroMorphisms :=
    pinnedTensorSquareLeftSummandInstance3 X'
  let : ∀ M : X'.Modules, ((curriedTensor X'.Modules).obj M).PreservesZeroMorphisms :=
    pinnedTensorSquareLeftSummandInstance4 X'
  let : ∀ (P Q : CochainComplex X.Modules ℤ),
      HomologicalComplex.HasMapBifunctor P Q (curriedTensor X.Modules) (.up ℤ) :=
    fun P Q ↦ inferInstance
  let : ∀ (P Q : CochainComplex X'.Modules ℤ),
      HomologicalComplex.HasMapBifunctor P Q (curriedTensor X'.Modules) (.up ℤ) :=
    fun P Q ↦ inferInstance
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)
  let D := RingedSpace.moduleStalkFunctor X'.toRingedSpace z
  let H := Scheme.Modules.tensorPullback g'
  let HC := H₀
  let DC := S₀
  let b := (SingleComplexBaseChange.tensorMap f f' g g' sq z).comp
    (algebraMap (SingleComplexBaseChange.A g' z)
      (TensorProduct (SingleComplexBaseChange.R f g' z)
        (SingleComplexBaseChange.A g' z) (SingleComplexBaseChange.B f' z)))
  let G := ModuleCat.extendScalars.{u, u, u} b
  let e := e₀
  let e' := e₀'
  let ty := Classical.choose (SheafOfModules.stalkTensorIso X.toRingedSpace (g' z))
  let tx := Classical.choose (SheafOfModules.stalkTensorIso X'.toRingedSpace z)
  let c := Classical.choose (Scheme.Modules.module_pullback_tensor g')
  let k (L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) (i : ℤ) :
      G.obj (T.obj (L.X i)) ⟶ D.obj (H.obj (L.X i)) :=
    (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z L).hom.f i
  let iPQ : P.X p ⊗ Q.X q ⟶ (pullbackTensorTotal X P Q).X n :=
    HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q n h
  have hs := Classical.choose_spec (exists_pinned_stalk_tensor X (g' z)) P Q p q n h
  have hs' : HomologicalComplex.ιMapBifunctor
      (SingleComplexBaseChange.stalkComplex g' z P)
      (SingleComplexBaseChange.stalkComplex g' z Q)
      (curriedTensor _) (.up ℤ) p q n h ≫ (e P Q).inv.f n =
      (ty (P.X p) (Q.X q)).inv ≫ T.map iPQ := by
    exact pinnedSummand_inverse ((HomologicalComplex.eval _ _ n).mapIso (e P Q))
      (ty (P.X p) (Q.X q)) _ _ hs
  have hk (L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (i : ℤ) : k L i =
      eqToHom (congrArg (fun a : SingleComplexBaseChange.A g' z →+*
          SingleComplexBaseChange.C z ↦ (ModuleCat.extendScalars a).obj
            (T.obj (L.X i)))
        (Classical.choose_spec
          (SingleComplexBaseChange.exists_tensorMap f f' g g' sq z)).1) ≫
      (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.app
        (L.X i) :=
    Classical.choose_spec (SingleComplexBaseChange.exists_tensorStalkIso
      f f' g g' sq z L) i
  have hn : G.map (T.map iPQ) ≫ k (pullbackTensorTotal X P Q) n =
      (eqToHom (congrArg (fun a : SingleComplexBaseChange.A g' z →+*
          SingleComplexBaseChange.C z ↦ (ModuleCat.extendScalars a).obj
            (T.obj (P.X p ⊗ Q.X q)))
        (Classical.choose_spec
          (SingleComplexBaseChange.exists_tensorMap f f' g g' sq z)).1) ≫
        (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.app
          (P.X p ⊗ Q.X q)) ≫ D.map (H.map iPQ) := by
    rw [hk]
    exact pinnedTensorStalk_transport_naturality g' z b
      (Classical.choose_spec (SingleComplexBaseChange.exists_tensorMap f f' g g' sq z)).1 iPQ
  have hm : G.map (ty (P.X p) (Q.X q)).inv ≫
      (eqToHom (congrArg (fun a : SingleComplexBaseChange.A g' z →+*
          SingleComplexBaseChange.C z ↦ (ModuleCat.extendScalars a).obj
            (T.obj (P.X p ⊗ Q.X q)))
        (Classical.choose_spec
          (SingleComplexBaseChange.exists_tensorMap f f' g g' sq z)).1) ≫
        (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.app
          (P.X p ⊗ Q.X q)) ≫ D.map (c (P.X p) (Q.X q)).hom ≫
        (tx (H.obj (P.X p)) (H.obj (Q.X q))).hom =
      Functor.OplaxMonoidal.δ G (T.obj (P.X p)) (T.obj (Q.X q)) ≫
        (k P p ⊗ₘ k Q q) := by
    rw [hk, hk]
    exact pinnedTensorStalkSquare_transport g' z b
      (Classical.choose_spec (SingleComplexBaseChange.exists_tensorMap f f' g g' sq z)).1
      (P.X p) (Q.X q)
  have hj :
      HomologicalComplex.ιMapBifunctor
          ((HC.obj P))
          ((HC.obj Q))
          (curriedTensor _) (.up ℤ) p q n h ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 _) a (curriedTensor _) (.up ℤ)).f n =
      (𝟙 _ ⊗ₘ a.f q) ≫
        HomologicalComplex.ιMapBifunctor
          ((HC.obj P)) N
          (curriedTensor _) (.up ℤ) p q n h := by
    erw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f]
    rfl
  have ht := Classical.choose_spec (exists_pinned_stalk_tensor X' z)
    (HC.obj P) N p q n h
  have ha := (Classical.choose_spec
    (SheafOfModules.stalkTensorIso X'.toRingedSpace z)).2
    (H.obj (P.X p)) (H.obj (Q.X q)) (H.obj (P.X p)) (N.X q) (𝟙 _) (a.f q)
  change G.map (HomologicalComplex.ιMapBifunctor
      (SingleComplexBaseChange.stalkComplex g' z P)
      (SingleComplexBaseChange.stalkComplex g' z Q)
      (curriedTensor _) (.up ℤ) p q n h) ≫
    G.map ((e P Q).inv.f n) ≫ k (pullbackTensorTotal X P Q) n ≫
      D.map (χ.hom.f n ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 _) a (curriedTensor _) (.up ℤ)).f n) =
    Functor.OplaxMonoidal.δ G (T.obj (P.X p)) (T.obj (Q.X q)) ≫
      (k P p ⊗ₘ k Q q) ≫ (𝟙 _ ⊗ₘ D.map (a.f q)) ≫
        HomologicalComplex.ιMapBifunctor
          (DC.obj (HC.obj P))
          (DC.obj N)
          (curriedTensor _) (.up ℤ) p q n h ≫
            (e' (HC.obj P) N).inv.f n
  rw [D.map_comp]
  have hgs := congrArg G.map hs'
  simp only [G.map_comp] at hgs
  have hc := congrArg D.map (hχ p q n h)
  simp only [D.map_comp] at hc
  have hja := congrArg D.map hj
  simp only [D.map_comp] at hja
  conv at ha =>
    rhs
    arg 2
    arg 1
    rw [D.map_id]
  exact summand_chase _ _ _ _ _
    ((HomologicalComplex.eval _ _ n).mapIso
      (e' (HC.obj P) N))
    _ _ _ _ _ _ _ _ _ (tx (H.obj (P.X p)) (H.obj (Q.X q))).hom
    _ _ _ _ hgs hn hc hja ht ha hm

end AlgebraicGeometry
