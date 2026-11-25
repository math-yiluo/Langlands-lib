/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.AlgebraicGeometry.ModuleLocalConstancyOfFiniteUnderlying
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Lisse sheaves of finite modules and module objects

Source: literature/stacks-project/etale-cohomology.tex, Lemma 0DV5, proof of (1)--(3),
with sites-modules Lemma 093S (1)
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Sheaves of left `Λ`-modules on `Y_et` are `Sheaf Y.smallEtaleTopology (ModuleCat.{u+1} Λ)`
with `Λ : Type (u + 1)` (STATE: the encoding of the six-functor and constructible chapters).
`FLC(Y)` is `IsFiniteLocallyConstantSheafOfTypes` (def-weil-pbc-etale-sheaves).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]

/-- A sheaf of left `Λ`-modules on `Y_et` is *lisse* when there are an etale covering
`{U_i → Y}` and finite left `Λ`-modules `M_i` with `F|_{U_i}` isomorphic, as a sheaf of
`Λ`-modules, to the constant sheaf (the sheafified constant presheaf) of `M_i`.
Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
def IsLisseModuleSheaf (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ 𝒰 : Cover.{u} etalePrecoverage Y, ∀ i : 𝒰.I₀,
    ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
      Nonempty (F.over (𝒰.etalePrecoverageToEtale i) ≅
        (constantSheaf (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} Λ)).obj M)

/-- A `Λ`-module structure on a sheaf of sets `A` in the sense of commutative diagrams:
morphisms `+ : A × A → A`, `0 : * → A` from the final object, `- : A → A` and `λ · : A → A`
for every `λ ∈ Λ`, satisfying the axioms of a left `Λ`-module as equalities of morphisms
(products are those of all sheaves of sets). Source: Stacks Project, Lemma 0DV5, proof of
(2)--(3) (blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
structure ModuleObjectStruct (Λ : Type (u + 1)) [Ring Λ]
    (A : Sheaf Y.smallEtaleTopology (Type (u + 1))) where
  /-- Addition. -/
  add : A ⨯ A ⟶ A
  /-- Zero, from the final object. -/
  zero : ⊤_ (Sheaf Y.smallEtaleTopology (Type (u + 1))) ⟶ A
  /-- Negation. -/
  neg : A ⟶ A
  /-- Scalar multiplication by each element of `Λ`. -/
  smul : Λ → (A ⟶ A)
  add_assoc : prod.map add (𝟙 A) ≫ add =
    (prod.associator A A A).hom ≫ prod.map (𝟙 A) add ≫ add
  add_comm : (prod.braiding A A).hom ≫ add = add
  zero_add : prod.lift (terminal.from A ≫ zero) (𝟙 A) ≫ add = 𝟙 A
  neg_add_cancel : prod.lift neg (𝟙 A) ≫ add = terminal.from A ≫ zero
  one_smul : smul 1 = 𝟙 A
  mul_smul (r s : Λ) : smul (r * s) = smul s ≫ smul r
  smul_add (r : Λ) : add ≫ smul r = prod.map (smul r) (smul r) ≫ add
  add_smul (r s : Λ) : smul (r + s) = prod.lift (smul r) (smul s) ≫ add
  smul_zero (r : Λ) : zero ≫ smul r = zero
  zero_smul : smul 0 = terminal.from A ≫ zero

variable (Y Λ) in
/-- A `Λ`-module object of `FLC(Y)`: a finite locally constant sheaf of sets with a
`Λ`-module structure in the sense of commutative diagrams. Source: Stacks Project,
Lemma 0DV5 (blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
structure LambdaModuleObject where
  /-- The underlying sheaf of sets. -/
  sheaf : Sheaf Y.smallEtaleTopology (Type (u + 1))
  isFLC : IsFiniteLocallyConstantSheafOfTypes sheaf
  /-- The module operations. -/
  str : ModuleObjectStruct Λ sheaf

namespace LambdaModuleObject

/-- A morphism of `Λ`-module objects: a morphism of `FLC(Y)` commuting with addition, zero,
negation and every scalar multiplication. Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
@[ext]
structure Hom (A B : LambdaModuleObject Y Λ) where
  /-- The underlying morphism of sheaves of sets. -/
  hom : A.sheaf ⟶ B.sheaf
  add : A.str.add ≫ hom = prod.map hom hom ≫ B.str.add
  zero : A.str.zero ≫ hom = B.str.zero
  neg : A.str.neg ≫ hom = hom ≫ B.str.neg
  smul (r : Λ) : A.str.smul r ≫ hom = hom ≫ B.str.smul r

/-- The category of `Λ`-module objects of `FLC(Y)`. Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
instance : Category (LambdaModuleObject Y Λ) where
  Hom := Hom
  id A := ⟨𝟙 _, by simp, by simp, by simp, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [← Category.assoc, f.add, Category.assoc, g.add,
      ← Category.assoc, prod.map_map], by rw [← Category.assoc, f.zero, g.zero],
    by rw [← Category.assoc, f.neg, Category.assoc, g.neg, Category.assoc],
    fun r => by rw [← Category.assoc, f.smul, Category.assoc, g.smul, Category.assoc]⟩

end LambdaModuleObject

variable (Y Λ) in
/-- The category of lisse sheaves of left `Λ`-modules, with `Λ`-linear maps of sheaves.
Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
abbrev LisseModuleSheafCategory : Type (u + 2) :=
  ObjectProperty.FullSubcategory
    (IsLisseModuleSheaf (Y := Y) (Λ := Λ))

/-- A module-object structure on the underlying sheaf of sets of a sheaf of `Λ`-modules `F`
is the one of `F` when, on the sections over every `U`, its addition, zero, negation and
scalar multiplications are those of the `Λ`-module `F(U)`. Source: Stacks Project,
Lemma 0DV5, proof of (2)--(3)
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
def ModuleObjectStruct.IsUnderlying (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (S : ModuleObjectStruct Λ ((sheafForget Y.smallEtaleTopology).obj F)) : Prop :=
  (∀ U x, S.add.hom.app U x =
      @id (F.obj.obj U) ((prod.fst : _ ⨯ _ ⟶ (sheafForget _).obj F).hom.app U x) +
        @id (F.obj.obj U) ((prod.snd : _ ⨯ _ ⟶ (sheafForget _).obj F).hom.app U x)) ∧
    (∀ U x, S.zero.hom.app U x = (0 : F.obj.obj U)) ∧
    (∀ U (x : F.obj.obj U), S.neg.hom.app U x = -x) ∧
    ∀ (r : Λ) U (x : F.obj.obj U), (S.smul r).hom.app U x = r • x

private theorem sheafType_ext
    {A B : Sheaf Y.smallEtaleTopology (Type (u + 1))} {f g : A ⟶ B}
    (h : ∀ U x, f.hom.app U x = g.hom.app U x) : f = g := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact ConcreteCategory.hom_ext _ _ (h U)

@[simp] private theorem sheafType_comp_apply
    {A B C : Sheaf Y.smallEtaleTopology (Type (u + 1))} (f : A ⟶ B) (g : B ⟶ C)
    (U : Y.Etaleᵒᵖ) (x : A.obj.obj U) :
    (f ≫ g).hom.app U x = g.hom.app U (f.hom.app U x) := rfl

@[simp] private theorem sheafType_id_apply
    (A : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U : Y.Etaleᵒᵖ)
    (x : A.obj.obj U) : (𝟙 A : A ⟶ A).hom.app U x = x := rfl

private theorem sheafType_congr
    {A B : Sheaf Y.smallEtaleTopology (Type (u + 1))} {f g : A ⟶ B}
    (h : f = g) (U : Y.Etaleᵒᵖ) (x : A.obj.obj U) :
    f.hom.app U x = g.hom.app U x := congrArg (fun k ↦ k.hom.app U x) h

private theorem moduleObjectStruct_ext
    {A : Sheaf Y.smallEtaleTopology (Type (u + 1))} {S T : ModuleObjectStruct Λ A}
    (ha : S.add = T.add) (hz : S.zero = T.zero) (hn : S.neg = T.neg)
    (hm : S.smul = T.smul) : S = T := by
  cases S
  cases T
  cases ha
  cases hz
  cases hn
  cases hm
  rfl

@[simp] private theorem sheafType_map_fst_apply
    {A B C D : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (f : A ⟶ C) (g : B ⟶ D) (U : Y.Etaleᵒᵖ) (x : (A ⨯ B).obj.obj U) :
    (prod.fst : C ⨯ D ⟶ C).hom.app U ((prod.map f g).hom.app U x) =
      f.hom.app U ((prod.fst : A ⨯ B ⟶ A).hom.app U x) := by
  exact sheafType_congr (prod.map_fst f g) U x

@[simp] private theorem sheafType_map_snd_apply
    {A B C D : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (f : A ⟶ C) (g : B ⟶ D) (U : Y.Etaleᵒᵖ) (x : (A ⨯ B).obj.obj U) :
    (prod.snd : C ⨯ D ⟶ D).hom.app U ((prod.map f g).hom.app U x) =
      g.hom.app U ((prod.snd : A ⨯ B ⟶ B).hom.app U x) := by
  exact sheafType_congr (prod.map_snd f g) U x

@[simp] private theorem sheafType_lift_fst_apply
    {A B C : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (f : A ⟶ B) (g : A ⟶ C) (U : Y.Etaleᵒᵖ) (x : A.obj.obj U) :
    (prod.fst : B ⨯ C ⟶ B).hom.app U ((prod.lift f g).hom.app U x) =
      f.hom.app U x := by
  exact sheafType_congr (prod.lift_fst f g) U x

@[simp] private theorem sheafType_lift_snd_apply
    {A B C : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (f : A ⟶ B) (g : A ⟶ C) (U : Y.Etaleᵒᵖ) (x : A.obj.obj U) :
    (prod.snd : B ⨯ C ⟶ C).hom.app U ((prod.lift f g).hom.app U x) =
      g.hom.app U x := by
  exact sheafType_congr (prod.lift_snd f g) U x

private instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @Etale))

private noncomputable def moduleUnderlyingStalkIso
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    ((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj
      ((sheafForget Y.smallEtaleTopology).obj F) ≅
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)).obj
        (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact ((pointSmallEtale s).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F

private noncomputable def moduleConstantValueStalkIso
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : Y.Etale) (M : ModuleCat.{u + 1} Λ)
    (e : F.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj M)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    ((pointSmallEtale (s ≫ U.hom)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F ≅ M := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let eU : (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
    (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) U F).symm ≪≫
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)).functor.mapIso e ≪≫
      ((Etale.overEquiv U).constantSheafSheafCongrIso
        (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
        (ModuleCat.{u + 1} Λ) CategoryTheory.Over.mkIdTerminal).app M
  exact ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.hom s).app F).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso eU ≪≫
      (pointSmallEtale s).sheafFiberConstantSheafIso M

private theorem finiteModuleConstantModel_over
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale)
    (hc : (F.over U).IsConstant (Y.smallEtaleTopology.over U))
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj
        ((sheafForget Y.smallEtaleTopology).obj F))) :
    ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
      Nonempty (F.over U ≅
        (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  by_cases hU : IsEmpty U.left
  · let := hU
    let E := (Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)).functor
    have hF : IsZero (E.obj (F.over U)) := Etale.isZero_sheaf_of_isEmpty _
    have hM : IsZero (E.obj
        ((constantSheaf (Y.smallEtaleTopology.over U)
          (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ PUnit))) :=
      Etale.isZero_sheaf_of_isEmpty _
    exact ⟨ModuleCat.of Λ PUnit, inferInstance, ⟨E.preimageIso (hF.iso hM)⟩⟩
  · have : Nonempty U.left := not_isEmpty_iff.mp hU
    let x : U.left := Classical.choice inferInstance
    let Ω := AlgebraicClosure (U.left.residueField x)
    let s : Spec (.of Ω) ⟶ U.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)) ≫
        U.left.fromSpecResidueField x
    let := hc
    obtain ⟨M, ⟨e⟩⟩ := (F.over U).mem_essImage_of_isConstant
    have : Finite (((pointSmallEtale (s ≫ U.hom)).sheafFiber
        (A := Type (u + 1))).obj ((sheafForget Y.smallEtaleTopology).obj F)) :=
      hf Ω (s ≫ U.hom)
    let eM := moduleUnderlyingStalkIso F (s ≫ U.hom) ≪≫
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)).mapIso
        (moduleConstantValueStalkIso F U M e.symm s)
    exact ⟨M, Finite.of_equiv _ eM.toEquiv, ⟨e.symm⟩⟩

/-- Clause (1): a sheaf of left modules over a finite ring `Λ` is lisse if and only if its
underlying sheaf of sets lies in `FLC(Y)`. Source: Stacks Project, Lemma 0DV5 (1), using
Lemma 093S (1) (blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Proof: if `F` is lisse, choose an etale covering on which it is isomorphic, as a sheaf of
`Λ`-modules, to the constant sheaf of a finite left `Λ`-module `M_i`; forgetting the module
structure gives an isomorphism of sheaves of sets with the constant finite sheaf underlying
`M_i`, so the underlying sheaf lies in `FLC(Y)`. Conversely, trivialize the underlying sheaf
on an etale cover, and also the finite products that occur as sources of the operations.
Each operation sends every element of its finite constant source to a section of the finite
constant target, which after an etale refinement is a constant section; refining over the
finite source makes the operation a map of finite constant sets. As `Λ` is finite there are
finitely many operations, so one common refinement makes all of them constant. The module
axioms hold as equalities of sheaf maps, so the local constant finite set is a finite left
`Λ`-module and the local identification is an isomorphism of sheaves of `Λ`-modules. -/
theorem lisseModuleSheaf_iff_underlying_finiteLocallyConstant [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsLisseModuleSheaf F ↔
      IsFiniteLocallyConstantSheafOfTypes ((sheafForget Y.smallEtaleTopology).obj F) := by
  constructor
  · rintro ⟨𝒰, h𝒰⟩
    constructor
    · refine ⟨𝒰, fun i ↦ ?_⟩
      obtain ⟨M, _, ⟨e⟩⟩ := h𝒰 i
      have : (F.over (𝒰.etalePrecoverageToEtale i)).IsConstant
          (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)) :=
        Sheaf.isConstant_of_iso _ e
      change ((sheafCompose (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
        (F.over (𝒰.etalePrecoverageToEtale i))).IsConstant _
      infer_instance
    · refine ⟨fun Ω _ _ s ↦ (ConcreteCategory.isFinitelyGenerated_iff_finite _).mpr ?_⟩
      obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (s default)
      have : Etale (𝒰.f i) := 𝒰.map_prop i
      obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s x hx
      obtain ⟨M, hM, ⟨e⟩⟩ := h𝒰 i
      let := hM
      let es := moduleUnderlyingStalkIso F s
      have em := moduleConstantValueStalkIso F (𝒰.etalePrecoverageToEtale i) M e t
      change ((pointSmallEtale (t ≫ 𝒰.f i)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F ≅ M at em
      rw [ht] at em
      exact Finite.of_equiv M
        (es ≪≫ (CategoryTheory.forget (ModuleCat.{u + 1} Λ)).mapIso em).toEquiv.symm
  · intro hF
    let := module_localConstancy_of_finite_underlying F hF
    obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
    exact ⟨d.cover, fun i ↦ finiteModuleConstantModel_over F
      (d.cover.etalePrecoverageToEtale i) (d.isConstant i)
      (fun Ω _ _ s ↦ hF.finite_sheafFiber Ω s)⟩

/-- The underlying sheaf of sets of a sheaf of `Λ`-modules carries exactly one module-object
structure given on sections by the operations of the modules `F(U)`. Source: Stacks Project,
Lemma 0DV5, proof of (2)--(3)
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Proof: products of sheaves of sets are computed on sections, and the operations of the
modules `F(U)` commute with the restriction maps, so they are morphisms of sheaves; the
module axioms hold on sections. A morphism of sheaves is determined by its sections. -/
theorem existsUnique_moduleObjectStruct_isUnderlying
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃! S : ModuleObjectStruct Λ ((sheafForget Y.smallEtaleTopology).obj F), S.IsUnderlying F := by
  let A := (sheafForget Y.smallEtaleTopology).obj F
  let a : A ⨯ A ⟶ A := ObjectProperty.homMk
    { app := fun U ↦ ↾(fun x =>
        @id (F.obj.obj U) ((prod.fst : A ⨯ A ⟶ A).hom.app U x) +
          @id (F.obj.obj U) ((prod.snd : A ⨯ A ⟶ A).hom.app U x))
      naturality := fun U V f ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        have hf := ConcreteCategory.congr_hom ((prod.fst : A ⨯ A ⟶ A).hom.naturality f) x
        have hs := ConcreteCategory.congr_hom ((prod.snd : A ⨯ A ⟶ A).hom.naturality f) x
        change _ = F.obj.map f (_ + _)
        rw [map_add]
        exact congrArg₂ (fun (x y : F.obj.obj V) ↦ x + y) hf hs }
  let z : ⊤_ (Sheaf Y.smallEtaleTopology (Type (u + 1))) ⟶ A := ObjectProperty.homMk
    { app := fun U ↦ ↾(fun _ ↦ (0 : F.obj.obj U))
      naturality := fun U V f ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        exact (map_zero (F.obj.map f).hom).symm }
  let n : A ⟶ A := ObjectProperty.homMk
    { app := fun U ↦ ↾(fun x : F.obj.obj U ↦ -x)
      naturality := fun U V f ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        exact (map_neg (F.obj.map f).hom (@id (F.obj.obj U) x)).symm }
  let m : Λ → (A ⟶ A) := fun r ↦ ObjectProperty.homMk
    { app := fun U ↦ ↾(fun x : F.obj.obj U ↦ r • x)
      naturality := fun U V f ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        exact (map_smul (F.obj.map f).hom r (@id (F.obj.obj U) x)).symm }
  have ha : ∀ U x, a.hom.app U x =
      @id (F.obj.obj U) ((prod.fst : A ⨯ A ⟶ A).hom.app U x) +
        @id (F.obj.obj U) ((prod.snd : A ⨯ A ⟶ A).hom.app U x) := fun _ _ ↦ rfl
  have hz : ∀ U x, z.hom.app U x = (0 : F.obj.obj U) := fun _ _ ↦ rfl
  have hn : ∀ U (x : F.obj.obj U), n.hom.app U x = -x := fun _ _ ↦ rfl
  have hm : ∀ r U (x : F.obj.obj U), (m r).hom.app U x = r • x := fun _ _ _ ↦ rfl
  let S : ModuleObjectStruct Λ A :=
    { add := a
      zero := z
      neg := n
      smul := m
      add_assoc := by
        apply sheafType_ext
        intro U x
        simp only [sheafType_comp_apply, ha, sheafType_map_fst_apply,
          sheafType_map_snd_apply, sheafType_id_apply, prod.associator_hom,
          sheafType_lift_fst_apply, sheafType_lift_snd_apply]
        exact @add_assoc (F.obj.obj U) _ _ _ _
      add_comm := by
        apply sheafType_ext
        intro U x
        simp only [sheafType_comp_apply, ha, prod.braiding_hom,
          sheafType_lift_fst_apply, sheafType_lift_snd_apply]
        exact @add_comm (F.obj.obj U) _ _ _
      zero_add := by
        apply sheafType_ext
        intro U x
        simp [ha, hz]
      neg_add_cancel := by
        apply sheafType_ext
        intro U x
        simp [ha, hz, hn]
      one_smul := by
        apply sheafType_ext
        intro U x
        simp [hm]
      mul_smul := fun r s ↦ by
        apply sheafType_ext
        intro U x
        simp [hm, mul_smul]
      smul_add := fun r ↦ by
        apply sheafType_ext
        intro U x
        simp [ha, hm, smul_add]
      add_smul := fun r s ↦ by
        apply sheafType_ext
        intro U x
        simp [ha, hm, add_smul]
      smul_zero := fun r ↦ by
        apply sheafType_ext
        intro U x
        simp [hz, hm]
      zero_smul := by
        apply sheafType_ext
        intro U x
        simp [hz, hm] }
  refine ⟨S, ⟨ha, hz, hn, hm⟩, ?_⟩
  intro T hT
  have ea : T.add = S.add := sheafType_ext (fun U x ↦ (hT.1 U x).trans (ha U x).symm)
  have ez : T.zero = S.zero :=
    sheafType_ext (fun U x ↦ (hT.2.1 U x).trans (hz U x).symm)
  have en : T.neg = S.neg :=
    sheafType_ext (fun U x ↦ (hT.2.2.1 U x).trans (hn U x).symm)
  have em : T.smul = S.smul := funext fun r =>
    sheafType_ext (fun U x ↦ (hT.2.2.2 r U x).trans (hm r U x).symm)
  exact moduleObjectStruct_ext ea ez en em

/-- The module-object structure of the underlying sheaf of sets of a sheaf of `Λ`-modules:
its addition, zero, negation and scalar multiplications. Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
noncomputable def underlyingModuleObjectStruct
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ModuleObjectStruct Λ ((sheafForget Y.smallEtaleTopology).obj F) :=
  (existsUnique_moduleObjectStruct_isUnderlying F).exists.choose

/-- A `Λ`-linear map of sheaves commutes with the underlying addition, zero, negation and
scalar multiplications. Source: Stacks Project, Lemma 0DV5, proof of (2)--(3)
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Proof: on sections over every `U` the map is `Λ`-linear, and morphisms of sheaves of sets
are determined by their sections. -/
theorem underlyingModuleObjectStruct_map
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ G) :
    let φ := (sheafForget Y.smallEtaleTopology).map f
    (underlyingModuleObjectStruct F).add ≫ φ =
        prod.map φ φ ≫ (underlyingModuleObjectStruct G).add ∧
      (underlyingModuleObjectStruct F).zero ≫ φ = (underlyingModuleObjectStruct G).zero ∧
      (underlyingModuleObjectStruct F).neg ≫ φ = φ ≫ (underlyingModuleObjectStruct G).neg ∧
      ∀ r : Λ, (underlyingModuleObjectStruct F).smul r ≫ φ =
        φ ≫ (underlyingModuleObjectStruct G).smul r := by
  have hF := (existsUnique_moduleObjectStruct_isUnderlying F).exists.choose_spec
  have hG := (existsUnique_moduleObjectStruct_isUnderlying G).exists.choose_spec
  change (underlyingModuleObjectStruct F).IsUnderlying F at hF
  change (underlyingModuleObjectStruct G).IsUnderlying G at hG
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    change f.hom.app U ((underlyingModuleObjectStruct F).add.hom.app U x) =
      (underlyingModuleObjectStruct G).add.hom.app U
        ((prod.map ((sheafForget Y.smallEtaleTopology).map f)
          ((sheafForget Y.smallEtaleTopology).map f)).hom.app U x)
    rw [hF.1, map_add, hG.1]
    have hf := congrArg (fun k ↦ k.hom.app U x)
      (prod.map_fst ((sheafForget Y.smallEtaleTopology).map f)
        ((sheafForget Y.smallEtaleTopology).map f))
    have hs := congrArg (fun k ↦ k.hom.app U x)
      (prod.map_snd ((sheafForget Y.smallEtaleTopology).map f)
        ((sheafForget Y.smallEtaleTopology).map f))
    exact congrArg₂ (· + ·) hf.symm hs.symm
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    change f.hom.app U ((underlyingModuleObjectStruct F).zero.hom.app U x) =
      (underlyingModuleObjectStruct G).zero.hom.app U x
    rw [hF.2.1, hG.2.1, map_zero]
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    change f.hom.app U ((underlyingModuleObjectStruct F).neg.hom.app U x) =
      (underlyingModuleObjectStruct G).neg.hom.app U (f.hom.app U x)
    rw [hF.2.2.1, hG.2.2.1, map_neg]
  · intro r
    apply sheafType_ext
    intro U x
    change f.hom.app U (((underlyingModuleObjectStruct F).smul r).hom.app U x) =
      ((underlyingModuleObjectStruct G).smul r).hom.app U (f.hom.app U x)
    rw [hF.2.2.2, hG.2.2.2, map_smul]

variable (Y Λ) in
/-- The functor of clause (2): a lisse sheaf `F` goes to its underlying sheaf of sets (in
`FLC(Y)` by clause (1)) with the addition, zero, negation and scalar multiplications of `F`;
a `Λ`-linear map goes to its underlying map of sheaves of sets. Source: Stacks Project,
Lemma 0DV5 (blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
noncomputable def lisseToModuleObject [Finite Λ] :
    LisseModuleSheafCategory Y Λ ⥤ LambdaModuleObject Y Λ where
  obj F := ⟨(sheafForget Y.smallEtaleTopology).obj F.obj,
    (lisseModuleSheaf_iff_underlying_finiteLocallyConstant F.obj).mp F.property,
    underlyingModuleObjectStruct F.obj⟩
  map f := ⟨(sheafForget Y.smallEtaleTopology).map f.hom,
    (underlyingModuleObjectStruct_map f.hom).1, (underlyingModuleObjectStruct_map f.hom).2.1,
    (underlyingModuleObjectStruct_map f.hom).2.2.1, (underlyingModuleObjectStruct_map f.hom).2.2.2⟩
  map_id F := LambdaModuleObject.Hom.ext ((sheafForget Y.smallEtaleTopology).map_id F.obj)
  map_comp f g := LambdaModuleObject.Hom.ext
    ((sheafForget Y.smallEtaleTopology).map_comp f.hom g.hom)

private abbrev sectionFunctor (U : Y.Etaleᵒᵖ) :
    Sheaf Y.smallEtaleTopology (Type (u + 1)) ⥤ Type (u + 1) :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj U

private noncomputable def sectionPair
    (A B : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U : Y.Etaleᵒᵖ)
    (x : A.obj.obj U) (y : B.obj.obj U) : (A ⨯ B).obj.obj U :=
  ((PreservesLimitPair.iso (sectionFunctor U) A B) ≪≫
    Types.binaryProductIso _ _).inv (x, y)

@[simp] private theorem sectionPair_fst
    (A B : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U : Y.Etaleᵒᵖ)
    (x : A.obj.obj U) (y : B.obj.obj U) :
    (prod.fst : A ⨯ B ⟶ A).hom.app U (sectionPair A B U x y) = x := by
  have h := PreservesLimitPair.iso_inv_fst (sectionFunctor U) A B
  have h' := congrArg (fun k ↦ (Types.binaryProductIso _ _).inv ≫ k) h
  simp only [Types.binaryProductIso_inv_comp_fst] at h'
  exact congrArg (fun k ↦ k (x, y)) h'

@[simp] private theorem sectionPair_snd
    (A B : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U : Y.Etaleᵒᵖ)
    (x : A.obj.obj U) (y : B.obj.obj U) :
    (prod.snd : A ⨯ B ⟶ B).hom.app U (sectionPair A B U x y) = y := by
  have h := PreservesLimitPair.iso_inv_snd (sectionFunctor U) A B
  have h' := congrArg (fun k ↦ (Types.binaryProductIso _ _).inv ≫ k) h
  simp only [Types.binaryProductIso_inv_comp_snd] at h'
  exact congrArg (fun k ↦ k (x, y)) h'

private theorem sectionPair_ext
    {A B : Sheaf Y.smallEtaleTopology (Type (u + 1))} {U : Y.Etaleᵒᵖ}
    {x y : (A ⨯ B).obj.obj U}
    (hf : (prod.fst : A ⨯ B ⟶ A).hom.app U x =
      (prod.fst : A ⨯ B ⟶ A).hom.app U y)
    (hs : (prod.snd : A ⨯ B ⟶ B).hom.app U x =
      (prod.snd : A ⨯ B ⟶ B).hom.app U y) : x = y := by
  apply ((PreservesLimitPair.iso (sectionFunctor U) A B) ≪≫
    Types.binaryProductIso _ _).toEquiv.injective
  apply Prod.ext
  · have h : ((PreservesLimitPair.iso (sectionFunctor U) A B) ≪≫
        Types.binaryProductIso _ _).hom ≫ ↾Prod.fst =
        (sectionFunctor U).map (prod.fst : A ⨯ B ⟶ A) := by
      simp only [Iso.trans_hom, Category.assoc, Types.binaryProductIso_hom_comp_fst,
        PreservesLimitPair.iso_hom]
      exact prodComparison_fst _ _ _
    exact (congrArg (fun k ↦ k x) h).trans (hf.trans (congrArg (fun k ↦ k y) h).symm)
  · have h : ((PreservesLimitPair.iso (sectionFunctor U) A B) ≪≫
        Types.binaryProductIso _ _).hom ≫ ↾Prod.snd =
        (sectionFunctor U).map (prod.snd : A ⨯ B ⟶ B) := by
      simp only [Iso.trans_hom, Category.assoc, Types.binaryProductIso_hom_comp_snd,
        PreservesLimitPair.iso_hom]
      exact prodComparison_snd _ _ _
    exact (congrArg (fun k ↦ k x) h).trans (hs.trans (congrArg (fun k ↦ k y) h).symm)

@[simp] private theorem sectionPair_eta
    {A B : Sheaf Y.smallEtaleTopology (Type (u + 1))} {U : Y.Etaleᵒᵖ}
    (x : (A ⨯ B).obj.obj U) :
    sectionPair A B U ((prod.fst : A ⨯ B ⟶ A).hom.app U x)
      ((prod.snd : A ⨯ B ⟶ B).hom.app U x) = x := by
  apply sectionPair_ext <;> simp

@[simp] private theorem sectionPair_map
    {A B C D : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (f : A ⟶ C) (g : B ⟶ D) (U : Y.Etaleᵒᵖ)
    (x : A.obj.obj U) (y : B.obj.obj U) :
    (prod.map f g).hom.app U (sectionPair A B U x y) =
      sectionPair C D U (f.hom.app U x) (g.hom.app U y) := by
  apply sectionPair_ext <;> simp

@[simp] private theorem sectionPair_lift
    {A B C : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (f : A ⟶ B) (g : A ⟶ C) (U : Y.Etaleᵒᵖ) (x : A.obj.obj U) :
    (prod.lift f g).hom.app U x =
      sectionPair B C U (f.hom.app U x) (g.hom.app U x) := by
  apply sectionPair_ext <;> simp

@[simp] private theorem sectionPair_restrict
    (A B : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    {U V : Y.Etaleᵒᵖ} (g : U ⟶ V) (x : A.obj.obj U) (y : B.obj.obj U) :
    (A ⨯ B).obj.map g (sectionPair A B U x y) =
      sectionPair A B V (A.obj.map g x) (B.obj.map g y) := by
  apply sectionPair_ext
  · have h := ConcreteCategory.congr_hom ((prod.fst : A ⨯ B ⟶ A).hom.naturality g)
      (sectionPair A B U x y)
    simpa only [types_comp_apply, sectionPair_fst] using h
  · have h := ConcreteCategory.congr_hom ((prod.snd : A ⨯ B ⟶ B).hom.naturality g)
      (sectionPair A B U x y)
    simpa only [types_comp_apply, sectionPair_snd] using h

private noncomputable def sectionPoint (U : Y.Etaleᵒᵖ) :
    (⊤_ (Sheaf Y.smallEtaleTopology (Type (u + 1)))).obj.obj U :=
  ((PreservesTerminal.iso (sectionFunctor U)) ≪≫ Types.terminalIso).inv PUnit.unit

private theorem sectionPoint_unique (U : Y.Etaleᵒᵖ)
    (x : (⊤_ (Sheaf Y.smallEtaleTopology (Type (u + 1)))).obj.obj U) :
    x = sectionPoint U := by
  apply ((PreservesTerminal.iso (sectionFunctor U)) ≪≫ Types.terminalIso).toEquiv.injective
  exact Subsingleton.elim _ _

@[simp] private theorem sectionPoint_from
    (A : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U : Y.Etaleᵒᵖ)
    (x : A.obj.obj U) : (terminal.from A).hom.app U x = sectionPoint U :=
  sectionPoint_unique _ _

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible] private noncomputable def moduleSectionAddCommGroup
    (A : Sheaf Y.smallEtaleTopology (Type (u + 1))) (S : ModuleObjectStruct Λ A)
    (U : Y.Etaleᵒᵖ) : AddCommGroup (A.obj.obj U) := by
  letI : Add (A.obj.obj U) := ⟨fun x y ↦ S.add.hom.app U (sectionPair A A U x y)⟩
  letI : Zero (A.obj.obj U) := ⟨S.zero.hom.app U (sectionPoint U)⟩
  letI : Neg (A.obj.obj U) := ⟨fun x ↦ S.neg.hom.app U x⟩
  exact {
    add := fun x y ↦ S.add.hom.app U (sectionPair A A U x y)
    zero := S.zero.hom.app U (sectionPoint U)
    neg := fun x ↦ S.neg.hom.app U x
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc x y z := by
      change S.add.hom.app U (sectionPair A A U
        (S.add.hom.app U (sectionPair A A U x y)) z) =
        S.add.hom.app U (sectionPair A A U x (S.add.hom.app U (sectionPair A A U y z)))
      have h := sheafType_congr S.add_assoc U
        (sectionPair (A ⨯ A) A U (sectionPair A A U x y) z)
      simpa only [sheafType_comp_apply, sectionPair_map, sheafType_id_apply,
        prod.associator_hom, sectionPair_lift, sectionPair_fst, sectionPair_snd] using h
    add_comm x y := by
      change S.add.hom.app U (sectionPair A A U x y) =
        S.add.hom.app U (sectionPair A A U y x)
      have h := sheafType_congr S.add_comm U (sectionPair A A U x y)
      simpa only [sheafType_comp_apply, prod.braiding_hom, sectionPair_lift,
        sectionPair_fst, sectionPair_snd] using h.symm
    zero_add x := by
      change S.add.hom.app U
        (sectionPair A A U (S.zero.hom.app U (sectionPoint U)) x) = x
      have h := sheafType_congr S.zero_add U x
      simpa only [sheafType_comp_apply, sectionPair_lift, sectionPoint_from,
        sheafType_id_apply] using h
    add_zero x := by
      have h := sheafType_congr S.zero_add U x
      have hc := sheafType_congr S.add_comm U
        (sectionPair A A U x (S.zero.hom.app U (sectionPoint U)))
      simp only [sheafType_comp_apply, prod.braiding_hom, sectionPair_lift,
        sectionPair_fst, sectionPair_snd] at hc
      exact hc.symm.trans (by
        simpa only [sheafType_comp_apply, sectionPair_lift, sectionPoint_from,
          sheafType_id_apply] using h)
    neg_add_cancel x := by
      change S.add.hom.app U (sectionPair A A U (S.neg.hom.app U x) x) =
        S.zero.hom.app U (sectionPoint U)
      have h := sheafType_congr S.neg_add_cancel U x
      simpa only [sheafType_comp_apply, sectionPair_lift, sectionPoint_from,
        sheafType_id_apply] using h }

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible] private noncomputable def moduleSectionModule
    (A : Sheaf Y.smallEtaleTopology (Type (u + 1))) (S : ModuleObjectStruct Λ A)
    (U : Y.Etaleᵒᵖ) :
    letI := moduleSectionAddCommGroup A S U
    Module Λ (A.obj.obj U) := by
  letI := moduleSectionAddCommGroup A S U
  letI : SMul Λ (A.obj.obj U) := ⟨fun r x ↦ (S.smul r).hom.app U x⟩
  exact
    { smul := fun r x ↦ (S.smul r).hom.app U x
      one_smul := fun x ↦ sheafType_congr S.one_smul U x
      mul_smul := fun r s x ↦ sheafType_congr (S.mul_smul r s) U x
      smul_add := fun r x y ↦ by
        change (S.smul r).hom.app U (S.add.hom.app U (sectionPair A A U x y)) =
          S.add.hom.app U
            (sectionPair A A U ((S.smul r).hom.app U x) ((S.smul r).hom.app U y))
        have h := sheafType_congr (S.smul_add r) U (sectionPair A A U x y)
        simpa only [sheafType_comp_apply, sectionPair_map] using h
      add_smul := fun r s x ↦ by
        change (S.smul (r + s)).hom.app U x = S.add.hom.app U
          (sectionPair A A U ((S.smul r).hom.app U x) ((S.smul s).hom.app U x))
        have h := sheafType_congr (S.add_smul r s) U x
        simpa only [sheafType_comp_apply, sectionPair_lift] using h
      smul_zero := fun r ↦ sheafType_congr (S.smul_zero r) U (sectionPoint U)
      zero_smul := fun x ↦ by
        change (S.smul 0).hom.app U x = S.zero.hom.app U (sectionPoint U)
        have h := sheafType_congr S.zero_smul U x
        simpa only [sheafType_comp_apply, sectionPoint_from] using h }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def recoveredModulePresheaf
    (A : Sheaf Y.smallEtaleTopology (Type (u + 1))) (S : ModuleObjectStruct Λ A) :
    Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ := by
  letI (U : Y.Etaleᵒᵖ) := moduleSectionAddCommGroup A S U
  letI (U : Y.Etaleᵒᵖ) := moduleSectionModule A S U
  exact
    { obj := fun U ↦ ModuleCat.of Λ (A.obj.obj U)
      map := fun {U V} g ↦ ModuleCat.ofHom
        { toFun := A.obj.map g
          map_add' := fun x y ↦ by
            change A.obj.map g (S.add.hom.app U (sectionPair A A U x y)) =
              S.add.hom.app V (sectionPair A A V (A.obj.map g x) (A.obj.map g y))
            have h := ConcreteCategory.congr_hom (S.add.hom.naturality g)
              (sectionPair A A U x y)
            simpa only [types_comp_apply, sectionPair_restrict] using h.symm
          map_smul' := fun r x ↦ by
            have h := ConcreteCategory.congr_hom ((S.smul r).hom.naturality g) x
            exact h.symm }
      map_id := fun U ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        exact ConcreteCategory.congr_hom (A.obj.map_id U) x
      map_comp := fun g h ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        exact ConcreteCategory.congr_hom (A.obj.map_comp g h) x }

private noncomputable def recoveredModuleSheaf
    (A : Sheaf Y.smallEtaleTopology (Type (u + 1))) (S : ModuleObjectStruct Λ A) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  ⟨recoveredModulePresheaf A S,
    (Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).mpr A.property⟩

private theorem recoveredModuleSheaf_str
    (A : Sheaf Y.smallEtaleTopology (Type (u + 1))) (S : ModuleObjectStruct Λ A) :
    underlyingModuleObjectStruct (recoveredModuleSheaf A S) = S := by
  have hS : S.IsUnderlying (recoveredModuleSheaf A S) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro U x
      change S.add.hom.app U x = S.add.hom.app U
        (sectionPair A A U ((prod.fst : A ⨯ A ⟶ A).hom.app U x)
          ((prod.snd : A ⨯ A ⟶ A).hom.app U x))
      rw [sectionPair_eta]
    · intro U x
      change S.zero.hom.app U x = S.zero.hom.app U (sectionPoint U)
      rw [sectionPoint_unique U x]
    · intro U x
      rfl
    · intro r U x
      rfl
  exact (existsUnique_moduleObjectStruct_isUnderlying (recoveredModuleSheaf A S)).unique
    (existsUnique_moduleObjectStruct_isUnderlying (recoveredModuleSheaf A S)).exists.choose_spec hS

private theorem lisseToModuleObject_surjective [Finite Λ] :
    Function.Surjective (lisseToModuleObject Y Λ).obj := by
  intro A
  let F := recoveredModuleSheaf A.sheaf A.str
  have hF : IsLisseModuleSheaf F :=
    (lisseModuleSheaf_iff_underlying_finiteLocallyConstant F).mpr A.isFLC
  refine ⟨⟨F, hF⟩, ?_⟩
  have h := recoveredModuleSheaf_str A.sheaf A.str
  cases A
  dsimp only [lisseToModuleObject, F] at h ⊢
  congr 1

private theorem moduleCat_ext_operations {M N : ModuleCat.{u + 1} Λ}
    (hc : (M : Type (u + 1)) = N)
    (ha : HEq M.isAddCommGroup.add N.isAddCommGroup.add)
    (hm : HEq M.isModule.smul N.isModule.smul) : M = N := by
  cases M
  cases N
  rename_i M mA mM N nA nM
  change M = N at hc
  cases hc
  have hA : mA = nA := AddCommGroup.ext (eq_of_heq ha)
  cases hA
  have hM : mM = nM := Module.ext' _ _
    (fun r x ↦ congrFun (congrFun (eq_of_heq hm) r) x)
  cases hM
  rfl

private theorem recoveredModuleSheaf_obj
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etaleᵒᵖ) :
    (recoveredModuleSheaf ((sheafForget _).obj F)
      (underlyingModuleObjectStruct F)).obj.obj U = F.obj.obj U := by
  have hF := (existsUnique_moduleObjectStruct_isUnderlying F).exists.choose_spec
  change (underlyingModuleObjectStruct F).IsUnderlying F at hF
  refine moduleCat_ext_operations
    (M := (recoveredModuleSheaf ((sheafForget _).obj F)
      (underlyingModuleObjectStruct F)).obj.obj U) (N := F.obj.obj U) rfl ?_ ?_
  · change HEq (fun x y : F.obj.obj U ↦ (underlyingModuleObjectStruct F).add.hom.app U
      (sectionPair ((sheafForget _).obj F) ((sheafForget _).obj F) U x y))
      (fun x y : F.obj.obj U ↦ x + y)
    apply heq_of_eq
    funext x y
    rw [hF.1, sectionPair_fst, sectionPair_snd]
    rfl
  · change HEq (fun r (x : F.obj.obj U) ↦
      ((underlyingModuleObjectStruct F).smul r).hom.app U x)
      (fun r (x : F.obj.obj U) ↦ r • x)
    apply heq_of_eq
    funext r x
    exact hF.2.2.2 r U x

private theorem moduleCat_hom_hext
    {M N P Q : ModuleCat.{u + 1} Λ} (f : M ⟶ N) (g : P ⟶ Q)
    (hM : M = P) (hN : N = Q)
    (h : HEq (fun x ↦ f x) (fun x ↦ g x)) : HEq f g := by
  cases hM
  cases hN
  apply heq_of_eq
  apply ConcreteCategory.hom_ext
  exact congrFun (eq_of_heq h)

private theorem recoveredModuleSheaf_eq
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    recoveredModuleSheaf ((sheafForget _).obj F) (underlyingModuleObjectStruct F) = F := by
  apply ObjectProperty.FullSubcategory.ext
  apply CategoryTheory.Functor.hext
  · exact recoveredModuleSheaf_obj F
  · intro U V f
    apply moduleCat_hom_hext _ _ (recoveredModuleSheaf_obj F U)
      (recoveredModuleSheaf_obj F V)
    rfl

private theorem lisseToModuleObject_injective [Finite Λ] :
    Function.Injective (lisseToModuleObject Y Λ).obj := by
  intro F G h
  apply ObjectProperty.FullSubcategory.ext
  have hS := congrArg (fun A ↦ recoveredModuleSheaf A.sheaf A.str) h
  simpa only [lisseToModuleObject, recoveredModuleSheaf_eq] using hS

private theorem lisseToModuleObject_faithful [Finite Λ] :
    (lisseToModuleObject Y Λ).Faithful where
  map_injective := by
    intro F G f g h
    apply ObjectProperty.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun k ↦ k.hom.hom.app U x) h

private theorem lisseToModuleObject_full [Finite Λ] :
    (lisseToModuleObject Y Λ).Full where
  map_surjective := by
    intro F G f
    have hF := (existsUnique_moduleObjectStruct_isUnderlying F.obj).exists.choose_spec
    have hG := (existsUnique_moduleObjectStruct_isUnderlying G.obj).exists.choose_spec
    change (underlyingModuleObjectStruct F.obj).IsUnderlying F.obj at hF
    change (underlyingModuleObjectStruct G.obj).IsUnderlying G.obj at hG
    let φ : F.obj ⟶ G.obj := ObjectProperty.homMk
      { app := fun U ↦ ModuleCat.ofHom
          { toFun := f.hom.hom.app U
            map_add' := fun x y ↦ by
              have h := sheafType_congr f.add U
                (sectionPair ((sheafForget _).obj F.obj) ((sheafForget _).obj F.obj) U x y)
              dsimp only [lisseToModuleObject] at h
              simp only [sheafType_comp_apply, hF.1, hG.1,
                sheafType_map_fst_apply, sheafType_map_snd_apply, sectionPair_fst,
                sectionPair_snd] at h
              exact h
            map_smul' := fun r x ↦ by
              have h := sheafType_congr (f.smul r) U x
              dsimp only [lisseToModuleObject] at h
              simp only [sheafType_comp_apply] at h
              rw [hF.2.2.2, hG.2.2.2] at h
              exact h }
        naturality := fun U V g ↦ by
          apply ConcreteCategory.hom_ext
          intro x
          exact ConcreteCategory.congr_hom (f.hom.hom.naturality g) x }
    refine ⟨ObjectProperty.homMk φ, ?_⟩
    apply LambdaModuleObject.Hom.ext
    rfl

/-- Clause (2): the functor sending a lisse sheaf of left `Λ`-modules to its underlying sheaf
of sets with its addition, zero, negation and scalar multiplications is an isomorphism of
categories (an equivalence that is bijective on objects) onto the `Λ`-module objects of
`FLC(Y)`. Source: Stacks Project, Lemma 0DV5 (2)--(3)
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Proof: by clause (1) the functor lands in `FLC(Y)`. Conversely a module object of `FLC(Y)`
gives on every `U` a `Λ`-module structure on its sections, compatible with restriction, so a
sheaf of `Λ`-modules, lisse by clause (1). Forgetting and restoring the operations leaves
every operation unchanged, and a module object already has exactly the corresponding
sheaf-of-modules structure. A map is preserved and recovered precisely when it commutes with
addition, zero, negation and scalar multiplication. So the functor is bijective on objects and
on morphisms: an isomorphism of categories, hence an equivalence. -/
theorem lisseToModuleObject_isIso_of_categories [Finite Λ] :
    (lisseToModuleObject Y Λ).IsEquivalence ∧
      Function.Bijective (lisseToModuleObject Y Λ).obj := by
  let : (lisseToModuleObject Y Λ).EssSurj := ⟨fun A ↦ by
    obtain ⟨F, hF⟩ := lisseToModuleObject_surjective (Y := Y) (Λ := Λ) A
    exact ⟨F, ⟨eqToIso hF⟩⟩⟩
  let : (lisseToModuleObject Y Λ).Faithful := lisseToModuleObject_faithful
  let : (lisseToModuleObject Y Λ).Full := lisseToModuleObject_full
  exact ⟨Functor.IsEquivalence.mk, lisseToModuleObject_injective,
    lisseToModuleObject_surjective⟩


end AlgebraicGeometry.Scheme
