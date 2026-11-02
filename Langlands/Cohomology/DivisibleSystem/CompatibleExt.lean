import Langlands.Cohomology.DivisibleSystem.TowerComplex
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Levelwise evaluation of Ext groups and derived morphisms of inverse systems

Let `C` be an abelian category and `ℕᵒᵖ ⥤ C` the abelian category of inverse systems in `C`.
Evaluation at a level `m` is an exact functor `(ℕᵒᵖ ⥤ C) ⥤ C`, so it maps Ext groups and
morphisms in the derived category of inverse systems to the corresponding objects at level `m`.
This module records these levelwise images and their compatibility with the transition maps.

* `extEval X Y n m` is the additive map `Ext^n(X, Y) → Ext^n(X m, Y m)` induced by evaluation at
  `m`, Ext groups of inverse systems being computed in `ℕᵒᵖ ⥤ C`.
* `compatibleExt X Y n` is the subgroup of families `(e m)_m` of classes
  `e m ∈ Ext^n(X m, Y m)` such that, for `m' ≤ m`, the images of `e m` and `e m'` in
  `Ext^n(X m, Y m')` (by composition with the transition morphisms of `Y` and of `X`) agree.
  `extToCompatible X Y n` maps an Ext class of inverse systems to the family of its levelwise
  images. In degree `0` it is bijective (`extToCompatible_bijective_zero`,
  `compatibleExtZeroAddEquiv`): a morphism of inverse systems is a compatible family of levelwise
  morphisms. In positive degrees it is not claimed to be injective or surjective.
* `derivedEval`, `compatibleDerived` and `derivedToCompatible` are the analogues for morphisms
  `K ⟶ L⟦n⟧` in the derived category of inverse systems, `K` and `L` being cochain complexes in
  `ℕᵒᵖ ⥤ C` with level `m` complexes `evalComplex K m` and `evalComplex L m`.
  `towerDerivedEval` specializes `derivedEval` to the complexes `towerComplex T` of
  `ℓ`-divisible systems of complexes, whose level `m` complex is `T m`
  (`evalComplex_towerComplex`).

This is a step towards relating integral Ext groups to their finite levels, as in the proof of
Harris's integral statement (4.10.4) (Harris 1999, end of the proof of Proposition 4.10, printed
p.312), which passes from Hom complexes at the finite levels `m` to the limit by a
Mittag-Leffler argument. Harris's level `m` groups are taken over the coefficients `𝒪/ℓ^m 𝒪`;
here all levels lie in the fixed category `C`.
-/

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategory

universe w' w t' t v u

section Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasExt.{w'} (ℕᵒᵖ ⥤ C)]

/-- The transition morphism `X m ⟶ X m'` of an inverse system `X`, for `m' ≤ m`. -/
abbrev systemTransition (X : ℕᵒᵖ ⥤ C) {m' m : ℕ} (h : m' ≤ m) : X.obj (op m) ⟶ X.obj (op m') :=
  X.map (homOfLE h).op

/-- The image of an Ext class between inverse systems under the exact evaluation functor at
level `m`. -/
noncomputable def extEval (X Y : ℕᵒᵖ ⥤ C) (n m : ℕ) :
    Abelian.Ext.{w'} X Y n →+ Abelian.Ext.{w} (X.obj (op m)) (Y.obj (op m)) n :=
  ((evaluation ℕᵒᵖ C).obj (op m)).mapExtAddHom X Y n

lemma extEval_apply (X Y : ℕᵒᵖ ⥤ C) (n m : ℕ) (α : Abelian.Ext.{w'} X Y n) :
    extEval X Y n m α = α.mapExactFunctor ((evaluation ℕᵒᵖ C).obj (op m)) :=
  rfl

lemma extEval_mk₀ (X Y : ℕᵒᵖ ⥤ C) (m : ℕ) (f : X ⟶ Y) :
    extEval.{w'} X Y 0 m (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ (f.app (op m)) :=
  Abelian.Ext.mapExactFunctor_mk₀ _ f

/-- The levelwise Ext classes of an Ext class between inverse systems are compatible with the
transition morphisms. -/
lemma extEval_comp_mk₀ (X Y : ℕᵒᵖ ⥤ C) {n : ℕ} (α : Abelian.Ext.{w'} X Y n) {m' m : ℕ}
    (h : m' ≤ m) :
    (extEval X Y n m α).comp (Abelian.Ext.mk₀ (systemTransition Y h)) (add_zero n) =
      (Abelian.Ext.mk₀ (systemTransition X h)).comp (extEval X Y n m' α) (zero_add n) :=
  α.mapExactFunctor_comp_mk₀_natTransApp ((evaluation ℕᵒᵖ C).map (homOfLE h).op)

variable (X Y : ℕᵒᵖ ⥤ C) (n : ℕ)

/-- The compatible families of levelwise Ext classes. -/
def compatibleExt : AddSubgroup (∀ m : ℕ, Abelian.Ext.{w} (X.obj (op m)) (Y.obj (op m)) n) where
  carrier := {e | ∀ (m' m : ℕ) (h : m' ≤ m),
    (e m).comp (Abelian.Ext.mk₀ (systemTransition Y h)) (add_zero n) =
      (Abelian.Ext.mk₀ (systemTransition X h)).comp (e m') (zero_add n)}
  add_mem' {a b} ha hb := fun m' m h => by
    simp only [Pi.add_apply, Abelian.Ext.add_comp, Abelian.Ext.comp_add, ha m' m h, hb m' m h]
  zero_mem' := fun m' m h => by simp
  neg_mem' {a} ha := fun m' m h => by
    simp only [Pi.neg_apply, Abelian.Ext.neg_comp, Abelian.Ext.comp_neg, ha m' m h]

omit [HasExt.{w'} (ℕᵒᵖ ⥤ C)] in
variable {X Y n} in
lemma mem_compatibleExt_iff (e : ∀ m : ℕ, Abelian.Ext.{w} (X.obj (op m)) (Y.obj (op m)) n) :
    e ∈ compatibleExt X Y n ↔ ∀ (m' m : ℕ) (h : m' ≤ m),
      (e m).comp (Abelian.Ext.mk₀ (systemTransition Y h)) (add_zero n) =
        (Abelian.Ext.mk₀ (systemTransition X h)).comp (e m') (zero_add n) :=
  Iff.rfl

/-- The map from Ext groups of inverse systems to compatible families of levelwise Ext
classes. -/
noncomputable def extToCompatible :
    Abelian.Ext.{w'} X Y n →+ compatibleExt.{w} X Y n where
  toFun α := ⟨fun m => extEval X Y n m α, fun _ _ h => extEval_comp_mk₀ X Y α h⟩
  map_zero' := by ext m : 2; simp
  map_add' α β := by ext m : 2; simp

@[simp]
lemma extToCompatible_apply_coe (α : Abelian.Ext.{w'} X Y n) (m : ℕ) :
    (extToCompatible X Y n α).1 m = extEval X Y n m α :=
  rfl

/-- In degree `0` the map from Ext groups of inverse systems to compatible families of levelwise
Ext classes is bijective. -/
lemma extToCompatible_bijective_zero :
    Function.Bijective (extToCompatible.{w', w} X Y 0) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro α hα
    obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective X Y).2 α
    have : f = 0 := by
      ext m : 2
      have h := congrArg (fun e : compatibleExt.{w} X Y 0 => e.1 m.unop) hα
      simp only [extToCompatible_apply_coe, extEval_mk₀, ZeroMemClass.coe_zero, Pi.zero_apply,
        Abelian.Ext.mk₀_eq_zero_iff] at h
      simpa using h
    rw [this, Abelian.Ext.mk₀_zero]
  · intro e
    let f : X ⟶ Y :=
      { app := fun m => Abelian.Ext.homEquiv₀ (e.1 m.unop)
        naturality := fun m m' φ => by
          have h := e.2 m'.unop m.unop (leOfHom φ.unop)
          rw [← Abelian.Ext.mk₀_homEquiv₀_apply (e.1 m.unop),
            ← Abelian.Ext.mk₀_homEquiv₀_apply (e.1 m'.unop),
            Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀] at h
          have h' := (Abelian.Ext.mk₀_bijective _ _).1 h
          have hφ : φ = (homOfLE (leOfHom φ.unop)).op := rfl
          rw [hφ]
          exact h'.symm }
    refine ⟨Abelian.Ext.mk₀ f, ?_⟩
    ext m : 2
    simp [extEval_mk₀, f]

/-- In degree `0`, morphisms of inverse systems are the compatible families of levelwise Ext
classes. -/
noncomputable def compatibleExtZeroAddEquiv : (X ⟶ Y) ≃+ compatibleExt.{w} X Y 0 :=
  Abelian.Ext.addEquiv₀.symm.trans
    (AddEquiv.ofBijective (extToCompatible.{w', w} X Y 0) (extToCompatible_bijective_zero X Y))

end Ext

section Level

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The complex of level `m` objects of a complex of inverse systems. -/
abbrev evalComplex (K : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (m : ℕ) : CochainComplex C ℤ :=
  (((evaluation ℕᵒᵖ C).obj (op m)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The transition chain map `K m ⟶ K m'` of a complex of inverse systems, for `m' ≤ m`. -/
abbrev evalComplexTransition (K : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) {m' m : ℕ} (h : m' ≤ m) :
    evalComplex K m ⟶ evalComplex K m' :=
  (NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ C).map (homOfLE h).op)
    (ComplexShape.up ℤ)).app K

/-- The level `m` complex of `towerComplex T` is the complex `T m`. -/
lemma evalComplex_towerComplex {ℓ : ℕ} (T : DivisibleSystem (CochainComplex C ℤ) ℓ) (m : ℕ) :
    evalComplex (towerComplex T) m = T.obj m :=
  rfl

end Level

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{t} C]
  [HasDerivedCategory.{t'} (ℕᵒᵖ ⥤ C)]

/-- The image of a morphism `K ⟶ L⟦n⟧` in the derived category of inverse systems under the
functor induced by the exact evaluation functor at level `m`. -/
noncomputable def derivedEval (K L : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (n : ℤ) (m : ℕ) :
    (Q.obj K ⟶ (Q.obj L)⟦n⟧) →+ (Q.obj (evalComplex K m) ⟶ (Q.obj (evalComplex L m))⟦n⟧) where
  toFun f := (((evaluation ℕᵒᵖ C).obj (op m)).mapDerivedCategoryFactors.inv.app K) ≫
    ((evaluation ℕᵒᵖ C).obj (op m)).mapDerivedCategory.map f ≫
    (((evaluation ℕᵒᵖ C).obj (op m)).mapDerivedCategory.commShiftIso n).hom.app (Q.obj L) ≫
    ((((evaluation ℕᵒᵖ C).obj (op m)).mapDerivedCategoryFactors.hom.app L)⟦n⟧')
  map_zero' := by simp
  map_add' f g := by simp

/-- The levelwise images of a derived morphism of complexes of inverse systems are compatible
with the transition chain maps. -/
lemma derivedEval_comp (K L : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (n : ℤ)
    (f : Q.obj K ⟶ (Q.obj L)⟦n⟧) {m' m : ℕ} (h : m' ≤ m) :
    derivedEval K L n m f ≫ (Q.map (evalComplexTransition L h))⟦n⟧' =
      Q.map (evalComplexTransition K h) ≫ derivedEval K L n m' f := by
  set F := (evaluation ℕᵒᵖ C).obj (op m)
  set G := (evaluation ℕᵒᵖ C).obj (op m')
  set τ : F ⟶ G := (evaluation ℕᵒᵖ C).map (homOfLE h).op
  have hK := NatTrans.mapDerivedCategory_app_Q_obj τ K
  have hL := NatTrans.mapDerivedCategory_app_Q_obj τ L
  have hshift := NatTrans.shift_app_comm (NatTrans.mapDerivedCategory τ) n (Q.obj L)
  have hnat := (NatTrans.mapDerivedCategory τ).naturality f
  have hL' : F.mapDerivedCategoryFactors.hom.app L ≫ Q.map (evalComplexTransition L h) =
      (NatTrans.mapDerivedCategory τ).app (Q.obj L) ≫ G.mapDerivedCategoryFactors.hom.app L := by
    rw [hL]; simp [evalComplexTransition, τ]
  have hK' : F.mapDerivedCategoryFactors.inv.app K ≫
      (NatTrans.mapDerivedCategory τ).app (Q.obj K) =
      Q.map (evalComplexTransition K h) ≫ G.mapDerivedCategoryFactors.inv.app K := by
    rw [hK]; simp [evalComplexTransition, τ]
  simp only [derivedEval, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.assoc]
  rw [← Functor.map_comp, hL', Functor.map_comp, reassoc_of% hshift, reassoc_of% hnat,
    reassoc_of% hK']

variable (K L : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (n : ℤ)

/-- The compatible families of levelwise derived morphisms `K m ⟶ L m⟦n⟧`. -/
def compatibleDerived :
    AddSubgroup (∀ m : ℕ, Q.obj (evalComplex K m) ⟶ (Q.obj (evalComplex L m))⟦n⟧) where
  carrier := {e | ∀ (m' m : ℕ) (h : m' ≤ m),
    e m ≫ (Q.map (evalComplexTransition L h))⟦n⟧' = Q.map (evalComplexTransition K h) ≫ e m'}
  add_mem' {a b} ha hb := fun m' m h => by
    simp only [Pi.add_apply, Preadditive.add_comp, Preadditive.comp_add, ha m' m h, hb m' m h]
  zero_mem' := fun m' m h => by simp
  neg_mem' {a} ha := fun m' m h => by
    simp only [Pi.neg_apply, Preadditive.neg_comp, Preadditive.comp_neg, ha m' m h]

omit [HasDerivedCategory.{t'} (ℕᵒᵖ ⥤ C)] in
variable {K L n} in
lemma mem_compatibleDerived_iff
    (e : ∀ m : ℕ, Q.obj (evalComplex K m) ⟶ (Q.obj (evalComplex L m))⟦n⟧) :
    e ∈ compatibleDerived K L n ↔ ∀ (m' m : ℕ) (h : m' ≤ m),
      e m ≫ (Q.map (evalComplexTransition L h))⟦n⟧' = Q.map (evalComplexTransition K h) ≫ e m' :=
  Iff.rfl

/-- The map from derived morphisms `K ⟶ L⟦n⟧` of complexes of inverse systems to compatible
families of levelwise derived morphisms. -/
noncomputable def derivedToCompatible :
    (Q.obj K ⟶ (Q.obj L)⟦n⟧) →+ compatibleDerived K L n where
  toFun f := ⟨fun m => derivedEval K L n m f, fun _ _ h => derivedEval_comp K L n f h⟩
  map_zero' := by ext m : 2; simp
  map_add' f g := by ext m : 2; simp

@[simp]
lemma derivedToCompatible_apply_coe (f : Q.obj K ⟶ (Q.obj L)⟦n⟧) (m : ℕ) :
    (derivedToCompatible K L n f).1 m = derivedEval K L n m f :=
  rfl

end Derived

section Tower

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{t} C]
  [HasDerivedCategory.{t'} (ℕᵒᵖ ⥤ C)] {ℓ : ℕ}

/-- The levelwise images of a derived morphism `towerComplex T ⟶ (towerComplex W)⟦n⟧`. -/
noncomputable def towerDerivedEval (T W : DivisibleSystem (CochainComplex C ℤ) ℓ) (n : ℤ)
    (m : ℕ) :
    (Q.obj (towerComplex T) ⟶ (Q.obj (towerComplex W))⟦n⟧) →+
      (Q.obj (T.obj m) ⟶ (Q.obj (W.obj m))⟦n⟧) :=
  derivedEval (towerComplex T) (towerComplex W) n m

end Tower

end Langlands.Cohomology.DivisibleSystem
