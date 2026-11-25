/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedTensorOrdinaryRingComparison
import WeilConjectures.Algebra.Homology.SemilinearScalarExtensionHomologySquare

/-! # Change of all coefficient rings in the localized tensor comparison

Source: Stacks Project, Tags 06Y6 and 08IB, derived tensor functoriality.
(blueprint: lem-pc-base-derived-tensor-ring-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

-- Lift the given additive isomorphism; its inverse comes from the component isomorphisms.
private noncomputable def semilinearComplexIso
    {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T)
    (K : CochainComplex (ModuleCat.{u} S) ℤ)
    (L : CochainComplex (ModuleCat.{u} T) ℤ)
    (a : ((forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj K ≅
      ((forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj L)
    (ha : ∀ (i : ℤ) (s : S) (x : K.X i),
      a.hom.f i (s • x) = e s • (show L.X i from a.hom.f i x)) :
    K ≅ ((restrictScalars.{u} e.toRingHom).mapHomologicalComplex (.up ℤ)).obj L := by
  let b := fun i ↦ (HomologicalComplex.Hom.isoApp a i).addCommGroupIsoToAddEquiv
  let c : ∀ i, K.X i ≃ₗ[S] (restrictScalars.{u} e.toRingHom).obj (L.X i) :=
    fun i ↦ { __ := b i, map_smul' := ha i }
  refine HomologicalComplex.Hom.isoOfComponents (fun i ↦ (c i).toModuleIso) ?_
  intro i j hij
  ext x
  exact ConcreteCategory.congr_hom (a.hom.comm i j) x

-- Canonical homology factors compose, independently of the chosen homology data.
private theorem forgetHomologyIso_restrict
    {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T)
    (K : ShortComplex (ModuleCat.{u} T)) :
    let G := restrictScalars.{u} e.toRingHom
    let F := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
    let F' := forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u}
    ((K.map G).mapHomologyIso F).hom ≫
        F.map (K.mapHomologyIso G).hom =
      (K.mapHomologyIso F').hom := by
  dsimp only
  let h := K.homologyData.left
  rw [(h.map (restrictScalars.{u} e.toRingHom)).mapHomologyIso_eq,
    h.mapHomologyIso_eq, h.mapHomologyIso_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_assoc]
  let γ : ShortComplex.LeftHomologyMapData
      (𝟙 (K.map (forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u})))
      ((h.map (restrictScalars.{u} e.toRingHom)).map
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

/-- The localized comparison is natural under compatible coefficient-ring
isomorphisms and a semilinear isomorphism of its input complex.

Proof: restriction along eR and eB gives exact inverse equivalences on module
categories and on their homotopy and derived categories. The two equations on
R identify extension R0 to B0 with extension R to B under these equivalences:
on generators the comparison sends b0 tensor q to eB(b0) tensor alpha(q).
Transport the universal left-derived functor and its counit through these
exact equivalences. Uniqueness of left-derived functors identifies this functor
with N.derived, compatibly with the counits. Applying homology and the two
cohomologyIso maps gives a semilinear isomorphism on base-tensor cohomology.
For a0 in A0, naturality of alpha for multiplication and cohomologyIso_smul
show that it intertwines a0 tensor 1 and eA(a0) tensor 1. Its B0-linearity
intertwines 1 tensor b0 and 1 tensor eB(b0). Tensor induction gives semilinearity
for the tensor of eA and eB over eR. The equations on C identify the two
extensions of these cohomology modules to C0 and C; extending the semilinear
isomorphism yields the additive isomorphism l. The equations comparison_eq
identify the unlocalized comparison with the transported counit. Use localized_eq
and the scalar-extension adjunction to identify the localized maps. The specified
generator formula for tau identifies the resulting ordinary-complex map with
its given tau, by tensor induction. Finally the exact forgetful homology
isomorphisms yield the displayed equality. The comparisons need not be
invertible, the inputs need not be K-flat, and all rings may be zero rings.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change, and Tag 08IB,
lemma-compare-base-change; the coefficient equivalences are exact.
(blueprint: lem-pc-base-derived-tensor-ring-transport). -/
theorem exists_baseDerivedTensor_ring_transport
    {R₀ A₀ B₀ C₀ R A B C : Type u}
    [CommRing R₀] [CommRing A₀] [CommRing B₀] [CommRing C₀]
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R₀ A₀] [Algebra R₀ B₀] [Algebra (A₀ ⊗[R₀] B₀) C₀]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R₀)] [HasDerivedCategory (ModuleCat.{u} B₀)]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    (Q₀ : CochainComplex (ModuleCat.{u} A₀) ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : BaseDerivedTensorCohomologyModel R₀ A₀ B₀ Q₀ C₀)
    (N : BaseDerivedTensorCohomologyModel R A B Q C)
    (eR : R₀ ≃+* R) (eA : A₀ ≃+* A) (eB : B₀ ≃+* B) (eC : C₀ ≃+* C)
    (hRA : eA.toRingHom.comp (algebraMap R₀ A₀) =
      (algebraMap R A).comp eR.toRingHom)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom)
    (hCA : eC.toRingHom.comp
        ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp (algebraMap A₀ (A₀ ⊗[R₀] B₀))) =
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B))).comp eA.toRingHom)
    (hCB : eC.toRingHom.comp ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
        Algebra.TensorProduct.includeRight.toRingHom) =
      ((algebraMap (A ⊗[R] B) C).comp
        Algebra.TensorProduct.includeRight.toRingHom).comp eB.toRingHom)
    (α : ((forget₂ (ModuleCat.{u} A₀) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj Q₀ ≅
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj Q)
    (hα : ∀ (i : ℤ) (a : A₀) (q : Q₀.X i),
      α.hom.f i (a • q) = eA a • (show Q.X i from α.hom.f i q))
    (τ :
      ((forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
          (algebraMap A₀ (A₀ ⊗[R₀] B₀)))).mapHomologicalComplex (.up ℤ)).obj Q₀) ≅
      ((forget₂ (ModuleCat.{u} C) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars ((algebraMap (A ⊗[R] B) C).comp
          (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q))
    (hτ : ∀ (i : ℤ) (c : C₀) (q : Q₀.X i),
      τ.hom.f i (c ⊗ₜ[A₀,(algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
          (algebraMap A₀ (A₀ ⊗[R₀] B₀))] q) =
        eC c ⊗ₜ[A,(algebraMap (A ⊗[R] B) C).comp
          (algebraMap A (A ⊗[R] B))] (show Q.X i from α.hom.f i q))
    (i : ℤ) :
    let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} C) AddCommGrpCat.{u}
    let T₀ := ((extendScalars ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
      (algebraMap A₀ (A₀ ⊗[R₀] B₀)))).mapHomologicalComplex (.up ℤ)).obj Q₀
    let T := ((extendScalars ((algebraMap (A ⊗[R] B) C).comp
      (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q
    ∃ l : F₀.obj ((extendScalars (algebraMap (A₀ ⊗[R₀] B₀) C₀)).obj (M.cohomology i)) ≅
        F.obj ((extendScalars (algebraMap (A ⊗[R] B) C)).obj (N.cohomology i)),
      F₀.map (M.localizedComparison i) ≫ ((T₀.sc i).mapHomologyIso F₀).inv ≫
        HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom =
      l.hom ≫ F.map (N.localizedComparison i) := by
  rename_i hR₀ hB₀ hR hB
  let q := semilinearComplexIso eA Q₀ Q α hα
  let T₀ := ((extendScalars ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
    (algebraMap A₀ (A₀ ⊗[R₀] B₀)))).mapHomologicalComplex (.up ℤ)).obj Q₀
  let T := ((extendScalars ((algebraMap (A ⊗[R] B) C).comp
    (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q
  have hτlinear : ∀ (j : ℤ) (c : C₀) (z : T₀.X j),
      τ.hom.f j (c • z) = eC c • (show T.X j from τ.hom.f j z) := by
    intro j c z
    induction z using TensorProduct.inductionOn with
    | tmul d x =>
      rw [ExtendScalars.smul_tmul, hτ, hτ, ExtendScalars.smul_tmul, map_mul]
    | add z w hz hw =>
      rw [smul_add, map_add, hz, hw, map_add, smul_add]
  let t := semilinearComplexIso eC T₀ T τ hτlinear
  have hD : ∀ (a : A₀) (b : B₀),
      eC (algebraMap (A₀ ⊗[R₀] B₀) C₀ (a ⊗ₜ[R₀] b)) =
        algebraMap (A ⊗[R] B) C (eA a ⊗ₜ[R] eB b) := by
    intro a b
    have hA := RingHom.congr_fun hCA a
    have hB := RingHom.congr_fun hCB b
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom] at hA hB
    change eC (algebraMap (A₀ ⊗[R₀] B₀) C₀ (Algebra.TensorProduct.includeRight b)) =
      algebraMap (A ⊗[R] B) C (Algebra.TensorProduct.includeRight (eB b)) at hB
    have hprod : ∀ (a : A₀) (b : B₀),
        (a ⊗ₜ[R₀] b) = algebraMap A₀ (A₀ ⊗[R₀] B₀) a *
          Algebra.TensorProduct.includeRight b := by
      intro a b
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [hprod, map_mul, map_mul, hA, hB, ← map_mul]
    congr 1
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  obtain ⟨eE, heE, v, k, hv, hk⟩ :=
    exists_baseDerivedTensor_ordinary_ring_comparison Q₀ Q M N eR eA eB hRA hRB q i
  have hC : eC.toRingHom.comp (algebraMap (A₀ ⊗[R₀] B₀) C₀) =
      (algebraMap (A ⊗[R] B) C).comp eE.toRingHom := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b => simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, heE] using hD a b
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  have hδ :
      ((forget₂ (ModuleCat.{u} (A₀ ⊗[R₀] B₀)) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℤ)).map M.ordinaryToLocalized ≫
        ((forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℤ)).map t.hom =
      ((forget₂ (ModuleCat.{u} (A₀ ⊗[R₀] B₀)) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℤ)).map v.hom ≫
        ((forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℤ)).map N.ordinaryToLocalized := by
    apply HomologicalComplex.Hom.ext
    funext j
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
      change τ.hom.f j (M.ordinaryToLocalized.f j
        (r ⊗ₜ[A₀, algebraMap A₀ (A₀ ⊗[R₀] B₀)] x)) =
          N.ordinaryToLocalized.f j (v.hom.f j
            (r ⊗ₜ[A₀, algebraMap A₀ (A₀ ⊗[R₀] B₀)] x))
      rw [M.ordinaryToLocalized_tmul, hτ, hv, N.ordinaryToLocalized_tmul]
      exact congrArg (fun c : C ↦ c ⊗ₜ[A, (algebraMap (A ⊗[R] B) C).comp
        (algebraMap A (A ⊗[R] B))] (show Q.X j from q.hom.f j x))
          (RingHom.congr_fun hC r)
    | add z w hz hw => simp only [map_add] at hz hw ⊢; rw [hz, hw]
  obtain ⟨l, hl⟩ := exists_scalarExtension_homology_square
    (algebraMap (A₀ ⊗[R₀] B₀) C₀) (algebraMap (A ⊗[R] B) C) eE eC hC
    (M.cohomology i) (N.cohomology i) _ _ T₀ T v t k
    M.ordinaryToLocalized N.ordinaryToLocalized hδ i
    (M.comparison i) (N.comparison i) hk
    (M.localizedComparison i) (N.localizedComparison i) (M.localized_eq i) (N.localized_eq i)
  let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
  let F := forget₂ (ModuleCat.{u} C) AddCommGrpCat.{u}
  let G := restrictScalars.{u} eC.toRingHom
  refine ⟨l, ?_⟩
  let n : F.obj ((extendScalars (algebraMap (A ⊗[R] B) C)).obj (N.cohomology i)) ⟶
      F.obj (T.sc i).homology := F.map (N.localizedComparison i)
  have ht : (F₀.mapHomologicalComplex (.up ℤ)).map t.hom = τ.hom := by
    ext j x
    rfl
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ i).map t.hom) F₀
  change HomologicalComplex.homologyMap
      ((F₀.mapHomologicalComplex (.up ℤ)).map t.hom) i ≫
      (((T.sc i).map G).mapHomologyIso F₀).hom =
    ((T₀.sc i).mapHomologyIso F₀).hom ≫
      F₀.map (HomologicalComplex.homologyMap t.hom i) at hn
  rw [ht] at hn
  have hc := forgetHomologyIso_restrict eC (T.sc i)
  change F₀.map (M.localizedComparison i) ≫ ((T₀.sc i).mapHomologyIso F₀).inv ≫
      HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom =
    l.hom ≫ n
  rw [← hc]
  rw [reassoc_of% hn]
  simp only [Iso.inv_hom_id_assoc]
  change l.hom ≫ n ≫
      F₀.map ((T.sc i).mapHomologyIso G).inv =
    F₀.map (M.localizedComparison i) ≫ F₀.map (HomologicalComplex.homologyMap t.hom i) at hl
  have hh := congrArg
    (fun f ↦ f ≫ F₀.map ((T.sc i).mapHomologyIso G).hom) hl
  simp only [Category.assoc] at hh
  rw [← F₀.map_comp, Iso.inv_hom_id, F₀.map_id] at hh
  change l.hom ≫ n ≫ 𝟙 (F.obj (T.sc i).homology) =
    F₀.map (M.localizedComparison i) ≫ F₀.map (HomologicalComplex.homologyMap t.hom i) ≫
      F₀.map ((T.sc i).mapHomologyIso G).hom at hh
  rw [Category.comp_id] at hh
  exact hh.symm

end ModuleCat
