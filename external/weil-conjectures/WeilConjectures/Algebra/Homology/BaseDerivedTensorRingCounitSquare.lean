/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Ordinary comparison square from a transported counit square

Source: Stacks Project, Tag 06Y6, independence of choices.
(blueprint: lem-pc-base-derived-tensor-ring-counit-square). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

private theorem forgetHomologyIso_comp
    {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    (K : ShortComplex (ModuleCat.{u} T)) :
    let G := restrictScalars.{u} f
    let F := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
    let F' := forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u}
    ((K.map G).mapHomologyIso F).hom ≫
        F.map (K.mapHomologyIso G).hom =
      (K.mapHomologyIso F').hom := by
  dsimp only
  let h := K.homologyData.left
  rw [(h.map (restrictScalars.{u} f)).mapHomologyIso_eq,
    h.mapHomologyIso_eq, h.mapHomologyIso_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_assoc]
  let γ : ShortComplex.LeftHomologyMapData
      (𝟙 (K.map (forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u})))
      ((h.map (restrictScalars.{u} f)).map
        (forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}))
      (h.map (forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u})) :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by ext x; rfl
      commπ := by ext x; rfl }
  have hh := γ.homologyMap_comm
  simp only [γ, ShortComplex.homologyMap_id, Category.id_comp, Category.comp_id] at hh
  rw [← hh]
  rfl

private theorem forgetHomologyMap
    {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    (K : CochainComplex (ModuleCat.{u} S) ℤ)
    (L : CochainComplex (ModuleCat.{u} T) ℤ)
    (φ : K ⟶ ((restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).obj L)
    (i : ℤ) :
    let F := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
    let F' := forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u}
    F.map (HomologicalComplex.homologyMap φ i) ≫
        F.map ((L.sc i).mapHomologyIso (restrictScalars.{u} f)).hom =
      ((K.sc i).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ) i ≫
        ((L.sc i).mapHomologyIso F').hom := by
  dsimp only
  let F := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
  let F' := forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u}
  let G := restrictScalars.{u} f
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ i).map φ) F
  change HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ) i ≫
      (((L.sc i).map G).mapHomologyIso F).hom =
    ((K.sc i).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap φ i) at hn
  rw [← forgetHomologyIso_comp f (L.sc i)]
  rw [reassoc_of% hn]
  simp only [F, Iso.inv_hom_id_assoc]


/-- A square for the raw derived counits gives the ordinary model comparison square.

Proof: substitute comparison_eq for M and N. The identity hk cancels the
cohomology identifications, and hf replaces the transported N counit by the
M counit followed by homology(v). The two routes from ordinary R0-to-B0
extension to the restriction of the ordinary tensor-algebra complex agree:
on b tensor x, ordinaryIso_tmul, hv, and hs give respectively
(1 tensor eB(b)) tensor q(x). The equality heE at 1 tensor b identifies the
coefficient maps. Tensor induction proves equality in every degree; hence the
chain maps and their maps on homology agree. Restriction along includeRight
and then eB equals restriction along eE and includeRight, by heE on 1 tensor b.
Use the identity-on-elements restriction-composition isomorphism to compare
these functors. Naturality of exact-restriction homology isomorphisms and their
compatibility with composition identify the two homology maps in the square.
Cancel the invertible restriction homology maps and evaluate the equality of
B0-linear morphisms at x. This proves the displayed equality of underlying
elements. No universality, invertibility of f or k, scalar-action identity,
flatness, or properties of the maps to C0 and C are needed. This is just the
ordinary-complex and exact-homology part of the coefficient transport argument;
it also applies to zero maps, zero rings, and zero complexes.
Source: Stacks Project, Tag 06Y6, Lemma 15.61.1; exact-restriction homology
naturality as in Tag 05RR.
(blueprint: lem-pc-base-derived-tensor-ring-counit-square). -/
theorem baseDerivedTensor_ring_counit_square
    {R₀ A₀ B₀ C₀ R A B C : Type u}
    [CommRing R₀] [CommRing A₀] [CommRing B₀] [CommRing C₀]
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R₀ A₀] [Algebra R₀ B₀] [Algebra (A₀ ⊗[R₀] B₀) C₀]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (Q₀ : CochainComplex (ModuleCat.{u} A₀) ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : BaseDerivedTensorCohomologyModel R₀ A₀ B₀ Q₀ C₀)
    (N : BaseDerivedTensorCohomologyModel R A B Q C)
    (eA : A₀ ≃+* A) (eB : B₀ ≃+* B)
    (q : Q₀ ≅ ((restrictScalars.{u} eA.toRingHom).mapHomologicalComplex (.up ℤ)).obj Q)
    (eE : (A₀ ⊗[R₀] B₀) ≃+* (A ⊗[R] B))
    (heE : ∀ (a : A₀) (b : B₀), eE (a ⊗ₜ[R₀] b) = eA a ⊗ₜ[R] eB b)
    (s : ((extendScalars (algebraMap A₀ (A₀ ⊗[R₀] B₀))).mapHomologicalComplex
        (.up ℤ)).obj Q₀ ≅
      ((restrictScalars.{u} eE.toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
          (.up ℤ)).obj Q))
    (hs : ∀ (j : ℤ) (r : A₀ ⊗[R₀] B₀) (x : Q₀.X j),
      s.hom.f j (r ⊗ₜ[A₀,algebraMap A₀ (A₀ ⊗[R₀] B₀)] x) =
        eE r ⊗ₜ[A,algebraMap A (A ⊗[R] B)] (show Q.X j from q.hom.f j x))
    (i : ℤ) :
    let π₀ := HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ)
    let π := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
    let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) i
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    let P₀ := π₀ ⋙ DerivedCategory.Qh ⋙ M.derived ⋙ H₀
    let P := π ⋙ DerivedCategory.Qh ⋙ N.derived ⋙ H
    let U := restrictScalars.{u} eB.toRingHom
    let T₀ := (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ)
    let T := (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)
    let c₀ := fun K : CochainComplex (ModuleCat.{u} R₀) ℤ ↦
      H₀.map (M.counit.app (π₀.obj K)) ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B₀) i).hom.app
          ((HomotopyCategory.quotient _ _).obj (T₀.obj K)) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B₀) (.up ℤ) i).hom.app
          (T₀.obj K)
    let c := fun K : CochainComplex (ModuleCat.{u} R) ℤ ↦
      H.map (N.counit.app (π.obj K)) ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
          ((HomotopyCategory.quotient _ _).obj (T.obj K)) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app
          (T.obj K)
    let K₀ := ((restrictScalars.{u} (algebraMap R₀ A₀)).mapHomologicalComplex
      (.up ℤ)).obj Q₀
    let K := ((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj Q
    let S₀ := restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B₀ →ₐ[R₀] A₀ ⊗[R₀] B₀).toRingHom
    let S := restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
    let E := ((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    ∀ (v : T₀.obj K₀ ≅ (U.mapHomologicalComplex (.up ℤ)).obj (T.obj K))
      (_hv : ∀ (j : ℤ) (b : B₀) (x : Q₀.X j),
        v.hom.f j (b ⊗ₜ[R₀,algebraMap R₀ B₀] (show K₀.X j from x)) =
          eB b ⊗ₜ[R,algebraMap R B] (show K.X j from q.hom.f j x))
      (f : P₀.obj K₀ ⟶ U.obj (P.obj K))
      (_hf : f ≫ U.map (c K) = c₀ K₀ ≫ HomologicalComplex.homologyMap v.hom i ≫
        ((T.obj K).sc i |>.mapHomologyIso U).hom)
      (k : S₀.obj (M.cohomology i) ⟶ U.obj (S.obj (N.cohomology i)))
      (_hk : k ≫ U.map (N.cohomologyIso i).hom = (M.cohomologyIso i).hom ≫ f),
      ∀ x : M.cohomology i,
        ((E.sc i).mapHomologyIso (restrictScalars.{u} eE.toRingHom)).inv
            (N.comparison i (show N.cohomology i from k x)) =
          HomologicalComplex.homologyMap s.hom i (M.comparison i x) := by
  intro π₀ π H₀ H P₀ P U T₀ T c₀ c K₀ K S₀ S E v hv f hf k hk
  let Z₀ := forget₂ (ModuleCat.{u} B₀) AddCommGrpCat.{u}
  let Z := forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}
  let F₀ := forget₂ (ModuleCat.{u} (A₀ ⊗[R₀] B₀)) AddCommGrpCat.{u}
  let F := forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u}
  let O₀ := ((extendScalars (algebraMap A₀ (A₀ ⊗[R₀] B₀))).mapHomologicalComplex
    (.up ℤ)).obj Q₀
  let HA := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i
  let z₀ := ((T₀.obj K₀).sc i).mapHomologyIso Z₀
  let z := ((T.obj K).sc i).mapHomologyIso Z
  let o₀ := (O₀.sc i).mapHomologyIso F₀
  let o := (E.sc i).mapHomologyIso F
  let a₀ := (Z₀.mapHomologicalComplex (.up ℤ)).map M.ordinaryIso.hom
  let a := (Z.mapHomologicalComplex (.up ℤ)).map N.ordinaryIso.hom
  let b := (Z₀.mapHomologicalComplex (.up ℤ)).map v.hom
  let r := (F₀.mapHomologicalComplex (.up ℤ)).map s.hom
  have hm : F₀.map (M.comparison i) =
      Z₀.map (M.cohomologyIso i).hom ≫ Z₀.map (c₀ K₀) ≫
        z₀.inv ≫ HA.map a₀ ≫ o₀.hom := by
    have hM : S₀.map (M.comparison i) ≫ ((O₀.sc i).mapHomologyIso S₀).inv =
        (M.cohomologyIso i).hom ≫ c₀ K₀ ≫
          HomologicalComplex.homologyMap M.ordinaryIso.hom i := M.comparison_eq i
    have hh := congrArg
      (fun m ↦ Z₀.map (m ≫ ((O₀.sc i).mapHomologyIso S₀).hom)) hM
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp] at hh
    change F₀.map (M.comparison i) = Z₀.map (M.cohomologyIso i).hom ≫
      Z₀.map (c₀ K₀) ≫ Z₀.map (HomologicalComplex.homologyMap M.ordinaryIso.hom i) ≫
        Z₀.map ((O₀.sc i).mapHomologyIso S₀).hom at hh
    exact hh.trans (congrArg (fun m ↦ Z₀.map (M.cohomologyIso i).hom ≫
      Z₀.map (c₀ K₀) ≫ m) (forgetHomologyMap
        (Algebra.TensorProduct.includeRight : B₀ →ₐ[R₀] A₀ ⊗[R₀] B₀).toRingHom
        (T₀.obj K₀) O₀ M.ordinaryIso.hom i))
  have hn : F.map (N.comparison i) =
      Z.map (N.cohomologyIso i).hom ≫ Z.map (c K) ≫
        z.inv ≫ HA.map a ≫ o.hom := by
    have hN : S.map (N.comparison i) ≫ ((E.sc i).mapHomologyIso S).inv =
        (N.cohomologyIso i).hom ≫ c K ≫
          HomologicalComplex.homologyMap N.ordinaryIso.hom i := N.comparison_eq i
    have hh := congrArg
      (fun m ↦ Z.map (m ≫ ((E.sc i).mapHomologyIso S).hom)) hN
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp] at hh
    change F.map (N.comparison i) = Z.map (N.cohomologyIso i).hom ≫
      Z.map (c K) ≫ Z.map (HomologicalComplex.homologyMap N.ordinaryIso.hom i) ≫
        Z.map ((E.sc i).mapHomologyIso S).hom at hh
    exact hh.trans (congrArg (fun m ↦ Z.map (N.cohomologyIso i).hom ≫
      Z.map (c K) ≫ m) (forgetHomologyMap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
        (T.obj K) E N.ordinaryIso.hom i))
  have hk' : Z₀.map k ≫ Z.map (N.cohomologyIso i).hom =
      Z₀.map (M.cohomologyIso i).hom ≫ Z₀.map f := by
    exact (Z₀.map_comp _ _).symm.trans ((congrArg Z₀.map hk).trans (Z₀.map_comp _ _))
  have hf' : Z₀.map f ≫ Z.map (c K) =
      Z₀.map (c₀ K₀) ≫ z₀.inv ≫ HA.map b ≫ z.hom := by
    have hh := congrArg Z₀.map hf
    simp only [Functor.map_comp] at hh
    change Z₀.map f ≫ Z.map (c K) = Z₀.map (c₀ K₀) ≫
      Z₀.map (HomologicalComplex.homologyMap v.hom i) ≫
        Z₀.map ((T.obj K).sc i |>.mapHomologyIso U).hom at hh
    exact hh.trans (congrArg (fun m ↦ Z₀.map (c₀ K₀) ≫ m)
      (forgetHomologyMap eB.toRingHom (T₀.obj K₀) (T.obj K) v.hom i))
  have hchain : a₀ ≫ r = b ≫ a := by
    apply HomologicalComplex.hom_ext
    intro j
    ext x
    change s.hom.f j (M.ordinaryIso.hom.f j x) =
      N.ordinaryIso.hom.f j (v.hom.f j x)
    induction x using TensorProduct.inductionOn with
    | tmul b x =>
      rw [M.ordinaryIso_tmul, hv, N.ordinaryIso_tmul, hs]
      congr 1
      simpa [Algebra.TensorProduct.includeRight] using heE 1 b
    | add x y hx hy => simp only [map_add, hx, hy]
  have hfinal : Z₀.map k ≫ F.map (N.comparison i) =
      F₀.map (M.comparison i) ≫ o₀.inv ≫ HA.map r ≫ o.hom := by
    rw [hn, hm]
    simp only [Category.assoc]
    rw [← Category.assoc (Z₀.map k), hk']
    simp only [Category.assoc]
    rw [← Category.assoc (Z₀.map f), hf']
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hh := congrArg HA.map hchain
    simp only [Functor.map_comp] at hh
    exact congrArg (fun m ↦ Z₀.map (M.cohomologyIso i).hom ≫ Z₀.map (c₀ K₀) ≫
      z₀.inv ≫ m ≫ o.hom) hh.symm
  have hT := forgetHomologyMap eE.toRingHom O₀ E s.hom i
  change F₀.map (HomologicalComplex.homologyMap s.hom i) ≫
      F₀.map ((E.sc i).mapHomologyIso (restrictScalars.{u} eE.toRingHom)).hom =
    o₀.inv ≫ HA.map r ≫ o.hom at hT
  rw [← hT] at hfinal
  have hx := ConcreteCategory.congr_hom hfinal
  intro x
  have h := hx x
  change N.comparison i (show N.cohomology i from k x) =
    ((E.sc i).mapHomologyIso (restrictScalars.{u} eE.toRingHom)).hom
      (HomologicalComplex.homologyMap s.hom i (M.comparison i x)) at h
  rw [h]
  exact ConcreteCategory.congr_hom
    ((E.sc i).mapHomologyIso (restrictScalars.{u} eE.toRingHom)).hom_inv_id _

end ModuleCat
