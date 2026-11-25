/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorMonodromyHom

/-!
# Naturality of `H¹(Y_ét, M) ≃ Hom_cont(π₁(Y, s), M)` in the coefficients

Let `φ : M →+ M'` be a homomorphism of finite abelian groups. If `P` is an `M`-torsor and `P'`
an `M'`-torsor with a `φ`-equivariant morphism `P ⟶ P'` over `Y`, then the class of `P'` in
`H¹(Y_ét, M')` is the image of the class of `P` under the map induced by `φ` on the constant
sheaves (`AlgebraicGeometry.Scheme.EtaleTorsor.classH1_eq_map_of_hom`). Consequently the
identification `H¹(Y_ét, M) ≃ Hom_cont(π₁(Y, s), M)` of blueprint
`lemma-invariant-additive-characters` turns the map induced by `φ` into the composition with `φ`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PreGaloisCategory

namespace AlgebraicGeometry.Scheme

section ContinuousMapSheaf

variable (X : Scheme.{u}) {A B : Type (u + 1)} [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A] [DiscreteTopology A] [TopologicalSpace B] [AddCommGroup B]
  [IsTopologicalAddGroup B]

/-- Composition with `φ : A →+ B` on the sheaves of locally constant functions. -/
noncomputable def Etale.continuousMapSheafMap (φ : A →+ B) :
    Etale.continuousMapSheaf X A ⟶ Etale.continuousMapSheaf X B :=
  ⟨{ app U := AddCommGrpCat.ofHom
        { toFun f := (⟨φ, continuous_of_discreteTopology⟩ : C(A, B)).comp f
          map_zero' := by ext; simp
          map_add' f g := by ext; simp }
     naturality U V h := rfl }⟩

lemma Etale.continuousMapSheafMap_app_apply (φ : A →+ B) (U : X.Etaleᵒᵖ)
    (f : (Etale.continuousMapSheaf X A).obj.obj U) :
    (Etale.continuousMapSheafMap X φ).hom.app U f =
      (⟨φ, continuous_of_discreteTopology⟩ : C(A, B)).comp f :=
  rfl


/-- The identification of the constant sheaf with the sheaf of locally constant functions is
natural in the coefficients. -/
lemma Etale.constantSheafToContinuousMapSheaf_naturality (φ : A →+ B) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map (AddCommGrpCat.ofHom φ) ≫
        Etale.constantSheafToContinuousMapSheaf X B =
      Etale.constantSheafToContinuousMapSheaf X A ≫ Etale.continuousMapSheafMap X φ := by
  apply ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _
    _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    ← Category.assoc, ← Category.assoc]
  change (toSheafify X.smallEtaleTopology _ ≫ ((constantSheaf X.smallEtaleTopology
      AddCommGrpCat.{u + 1}).map (AddCommGrpCat.ofHom φ)).hom) ≫
      (Etale.constantSheafToContinuousMapSheaf X B).hom =
    (toSheafify X.smallEtaleTopology _ ≫ (Etale.constantSheafToContinuousMapSheaf X A).hom) ≫
      (Etale.continuousMapSheafMap X φ).hom
  rw [Etale.toSheafify_constantSheafToContinuousMapSheaf,
    show toSheafify X.smallEtaleTopology _ ≫ ((constantSheaf X.smallEtaleTopology
      AddCommGrpCat.{u + 1}).map (AddCommGrpCat.ofHom φ)).hom =
      (Functor.const _).map (AddCommGrpCat.ofHom φ) ≫ toSheafify X.smallEtaleTopology _ from
      (toSheafify_naturality _ _).symm,
    Category.assoc, Etale.toSheafify_constantSheafToContinuousMapSheaf]
  rfl

end ContinuousMapSheaf

namespace EtaleTorsor

variable {M M' : Type (u + 1)} [AddCommGroup M] [Finite M] [AddCommGroup M'] [Finite M']
  {Y : Scheme.{u}}

/-- The action of locally constant functions is compatible with `φ`-equivariant morphisms of
torsors. -/
lemma smulHom_comp_of_addMonoidHom [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M']
    [DiscreteTopology M'] (φ : M →+ M') (t : EtaleTorsor M Y) (t' : EtaleTorsor M' Y)
    {U : Y.Etale} (f : C(U.left, M)) (ψ : U ⟶ t.toEtale) (Φ : t.toEtale ⟶ t'.toEtale)
    (hΦ : ∀ m : M, t.vadd m ≫ Φ.left = Φ.left ≫ t'.vadd (φ m)) :
    t.smulHom f ψ ≫ Φ =
      t'.smulHom ((⟨φ, continuous_of_discreteTopology⟩ : C(M, M')).comp f) (ψ ≫ Φ) := by
  refine etaleHom_ext ?_
  refine U.left.hom_ext_fiberOpens f fun m ↦ ?_
  have hle : U.left.fiberOpens f m ≤ U.left.fiberOpens
      ((⟨φ, continuous_of_discreteTopology⟩ : C(M, M')).comp f) (φ m) := fun x hx ↦ by
    change φ (f x) = φ m
    rw [show f x = m from hx]
  rw [MorphismProperty.Comma.comp_left, ← Category.assoc, ι_smulHom_left_of_le t f ψ le_rfl,
    ι_smulHom_left_of_le t' _ _ hle, MorphismProperty.Comma.comp_left]
  simp only [Category.assoc, hΦ]

/-- **Change of coefficients.** Let `φ : M →+ M'`, let `t` be an `M`-torsor and `t'` an
`M'`-torsor with a `φ`-equivariant morphism `Φ : P ⟶ P'` over `Y`. Then the class of `t'` in
`H¹(Y_ét, M')` is the image of the class of `t` under the map induced by `φ`. -/
theorem classH1_eq_map_of_hom (φ : M →+ M') (t : EtaleTorsor M Y) (t' : EtaleTorsor M' Y)
    (Φ : t.P ⟶ t'.P) (hΦ : Φ ≫ t'.π = t.π) (hv : ∀ a, t.vadd a ≫ Φ = Φ ≫ t'.vadd (φ a)) :
    classH1 M' Y ⟦t'⟧ = Sheaf.H.map ((constantSheaf Y.smallEtaleTopology
      AddCommGrpCat.{u + 1}).map (AddCommGrpCat.ofHom φ)) 1 (classH1 M Y ⟦t⟧) := by
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  let _ : TopologicalSpace M' := ⊥
  have : DiscreteTopology M' := ⟨rfl⟩
  let Φ' : t.toEtale ⟶ t'.toEtale := MorphismProperty.Over.homMk Φ hΦ
  rw [classH1_mk, classH1_mk]
  refine Sheaf.Torsor.classH1_eq_map_of_equivariant _ _ _ _ (fun U x ↦ ⟨x.down ≫ Φ'⟩)
    (fun U V f x ↦ ULift.ext (by
      change f.unop ≫ x.down ≫ Φ' = (f.unop ≫ x.down) ≫ Φ'
      exact (Category.assoc _ _ _).symm)) (fun U a x ↦ ?_)
  have hnat : (Etale.constantSheafToContinuousMapSheaf Y M').hom.app U
      (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (AddCommGrpCat.ofHom φ)).hom.app U a) =
      (Etale.continuousMapSheafMap Y φ).hom.app U
        ((Etale.constantSheafToContinuousMapSheaf Y M).hom.app U a) :=
    ConcreteCategory.congr_hom (congrArg (fun α ↦ α.hom.app U)
      (Etale.constantSheafToContinuousMapSheaf_naturality Y φ)) a
  apply ULift.ext
  change t.smulHom ((Etale.constantSheafToContinuousMapSheaf Y M).hom.app U a) x.down ≫ Φ' =
    t'.smulHom ((Etale.constantSheafToContinuousMapSheaf Y M').hom.app U
      (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (AddCommGrpCat.ofHom φ)).hom.app U a)) (x.down ≫ Φ')
  rw [hnat, smulHom_comp_of_addMonoidHom φ t t' _ x.down Φ' hv]
  rfl

section Monodromy

open FiniteEtale

variable [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
  [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- Blueprint `lemma-invariant-additive-characters`: Abelian case: torsors, characters and H^1,
naturality in the coefficients.

Under the identification `H¹(Y_ét, M) ≃ Hom_cont(π₁(Y, s), M)`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom`), the map induced by a
homomorphism `φ : M →+ M'` on the constant sheaves is the composition with `φ`. -/
theorem sheafHEquivContinuousMonoidHom_map (φ : M →+ M')
    (x : Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1) (g : G) :
    (sheafHEquivContinuousMonoidHom M' s G (Sheaf.H.map ((constantSheaf Y.smallEtaleTopology
      AddCommGrpCat.{u + 1}).map (AddCommGrpCat.ofHom φ)) 1 x) g).toAdd =
      φ (sheafHEquivContinuousMonoidHom M s G x g).toAdd := by
  obtain ⟨T, rfl⟩ := (bijective_classH1 (M := M) (Y := Y)).2 x
  induction T using Quotient.inductionOn with | h t => ?_
  let χ : G →ₜ* Multiplicative M' :=
    (⟨φ.toMultiplicative, continuous_of_discreteTopology⟩ :
      Multiplicative M →ₜ* Multiplicative M').comp (t.monodromy s G)
  obtain ⟨t', ht'⟩ := exists_monodromy_eq s G χ
  obtain ⟨Φ, hΦ, hv⟩ := exists_hom_of_monodromy s G φ t t' fun g ↦ by rw [ht']; rfl
  rw [← classH1_eq_map_of_hom φ t t' Φ hΦ hv, sheafHEquivContinuousMonoidHom_classH1,
    sheafHEquivContinuousMonoidHom_classH1, ht']
  rfl

variable (M) in
/-- Blueprint `lemma-invariant-additive-characters`: Finite constant torsors and the etale
fundamental group, additivity.

The identification `H¹(Y_ét, M) ≃ Hom_cont(π₁(Y, s), M)` turns the sum of classes into the
pointwise sum of characters. Writing the pair `(e x, e y)` of characters as the image of a class
`z ∈ H¹(Y_ét, M × M)`, the classes `x` and `y` are the images of `z` under the projections, by
naturality in the coefficients (`sheafHEquivContinuousMonoidHom_map`), so `x + y` is the image of
`z` under the sum map `M × M → M`, as `H¹` and the constant sheaf functor are additive. -/
theorem sheafHEquivContinuousMonoidHom_add
    (x y : Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1) :
    sheafHEquivContinuousMonoidHom M s G (x + y) =
      sheafHEquivContinuousMonoidHom M s G x * sheafHEquivContinuousMonoidHom M s G y := by
  set e := sheafHEquivContinuousMonoidHom M s G
  let ψ : G →ₜ* Multiplicative (M × M) :=
    { toFun g := Multiplicative.ofAdd ((e x g).toAdd, (e y g).toAdd)
      map_one' := by simp
      map_mul' a b := by
        simp
        rfl
      continuous_toFun := continuous_of_discreteTopology.comp
        ((continuous_toAdd.comp (e x).continuous).prodMk (continuous_toAdd.comp (e y).continuous)) }
  let z := (sheafHEquivContinuousMonoidHom (M × M) s G).symm ψ
  let c (φ : M × M →+ M) := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    (AddCommGrpCat.ofHom φ)
  have hz (φ : M × M →+ M) (g : G) : (e (Sheaf.H.map (c φ) 1 z) g).toAdd = φ (ψ g).toAdd := by
    rw [sheafHEquivContinuousMonoidHom_map, Equiv.apply_symm_apply]
  have hx : Sheaf.H.map (c (AddMonoidHom.fst M M)) 1 z = x :=
    e.injective (ContinuousMonoidHom.ext fun g ↦ Multiplicative.toAdd.injective (hz _ g))
  have hy : Sheaf.H.map (c (AddMonoidHom.snd M M)) 1 z = y :=
    e.injective (ContinuousMonoidHom.ext fun g ↦ Multiplicative.toAdd.injective (hz _ g))
  have hc : c (AddMonoidHom.fst M M + AddMonoidHom.snd M M) =
      c (AddMonoidHom.fst M M) + c (AddMonoidHom.snd M M) :=
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map_add
  rw [← hx, ← hy, ← Sheaf.H.map_add_apply, ← hc]
  refine ContinuousMonoidHom.ext fun g ↦ Multiplicative.toAdd.injective ?_
  rw [ContinuousMonoidHom.mul_apply, toAdd_mul, hz, hz, hz]
  rfl

variable (M) in
/-- Blueprint `lemma-invariant-additive-characters`: Finite constant torsors and the etale
fundamental group.

The group isomorphism `H¹(Y_ét, M) ≃+ Hom_cont(π₁(Y, s), M)` underlying the bijection
`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom`: the class of a torsor is
sent to its monodromy character, and sums of classes to products of characters
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom_add`). -/
noncomputable def sheafHAddEquivContinuousMonoidHom :
    Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1 ≃+ Additive (G →ₜ* Multiplicative M) where
  toEquiv := (sheafHEquivContinuousMonoidHom M s G).trans Additive.ofMul
  map_add' x y := congrArg Additive.ofMul (sheafHEquivContinuousMonoidHom_add M s G x y)

@[simp]
lemma toMul_sheafHAddEquivContinuousMonoidHom_apply
    (x : Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1) :
    (sheafHAddEquivContinuousMonoidHom M s G x).toMul = sheafHEquivContinuousMonoidHom M s G x :=
  rfl

end Monodromy

end EtaleTorsor

end AlgebraicGeometry.Scheme
