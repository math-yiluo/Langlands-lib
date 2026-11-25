/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Grp.LeftExactFunctor
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Exact inverse image for constant left-module sheaves

Source: Stacks Project, Sites, Proposition 00YV (2), (5), (6), its fixed-ring
scalar-endomorphism proof, and Section 00XZ; Derived Categories, Tag 015F
(auxiliary; not a blueprint node).

The lift is characterized by its underlying-set comparison, addition and scalar
endomorphisms, and the original geometric adjunction unit. Comparisons have a
normalization equation and uniqueness; arbitrary unrelated functors are never compared.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
namespace ConstantLeftModuleInverseImage

/-- Constant-coefficient module sheaves, using the recorded general-site category.
Source: Stacks, 00YV (6) (auxiliary; not a blueprint node). -/
abbrev Modules {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :=
  ringedSiteModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Forget constant scalars, retaining the abelian sheaf.
Source: Stacks, 00YV (6) (auxiliary; not a blueprint node). -/
abbrev V {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :
    Modules J Λ ⥤ Sheaf J AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Forget the abelian group structure.
Source: Stacks, 00YV (2) (auxiliary; not a blueprint node). -/
abbrev U {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J (Type u) :=
  sheafCompose J (forget AddCommGrpCat.{u})

/-- The underlying-set functor on constant-coefficient modules.
Source: Stacks, 00YV (6) (auxiliary; not a blueprint node). -/
abbrev W {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :
    Modules J Λ ⥤ Sheaf J (Type u) := V J Λ ⋙ U J

/-- Characterization of a sheaf's addition map by its values on sections.
The projections allow arbitrary choices of categorical products.
Source: Stacks, discussion preceding 00YV
(auxiliary; not a blueprint node). -/
def IsAddition {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Sheaf J AddCommGrpCat.{u})
    (a : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A) : Prop :=
  ∀ (T : Cᵒᵖ) (x : ((U J).obj A ⨯ (U J).obj A).obj.obj T),
    a.hom.app T x =
      @id (A.obj.obj T)
        ((prod.fst : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A).hom.app T x) +
      @id (A.obj.obj T)
        ((prod.snd : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A).hom.app T x)

/-- A constant scalar endomorphism of the underlying abelian sheaf. This is
not required to be a module morphism when the ring is noncommutative.
Source: Stacks, fixed-ring paragraph in the proof of 00YV
(auxiliary; not a blueprint node). -/
def IsScalar {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (M : Modules J Λ) (r : Λ) (a : (V J Λ).obj M ⟶ (V J Λ).obj M) : Prop :=
  ∀ (T : Cᵒᵖ) (x : M.val.obj T),
    a.hom.app T x =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T r) • x

/-- The underlying set sheaf of the sheafified constant ring `Λ_C`.
Source: Stacks, 00YV (2) and 0H7J (auxiliary; not a blueprint node). -/
abbrev CoeffSet {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] : Sheaf J (Type u) :=
  (sheafCompose J (forget RingCat.{u})).obj ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Characterization of the addition map of the constant ring sheaf by its values
on sections. Source: Stacks, ring paragraph of the proof of 00YV
(auxiliary; not a blueprint node). -/
def IsRingAdd {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) : Prop :=
  ∀ (T : Cᵒᵖ) (x : (CoeffSet J Λ ⨯ CoeffSet J Λ).obj.obj T),
    m.hom.app T x =
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x) +
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x)

/-- Characterization of the multiplication map of the constant ring sheaf by its
values on sections, in the given order (no commutativity). Source: Stacks, ring
paragraph of the proof of 00YV (auxiliary; not a blueprint node). -/
def IsRingMul {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) : Prop :=
  ∀ (T : Cᵒᵖ) (x : (CoeffSet J Λ ⨯ CoeffSet J Λ).obj.obj T),
    m.hom.app T x =
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x) *
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x)

end ConstantLeftModuleInverseImage
open ConstantLeftModuleInverseImage

/-- A normalized lift of the given geometric morphism. The set comparisons and
unit equations connect both adjunctions to `L ⊣ R`; addition and scalar equations
specify the transported operations. Zero and negation are determined by addition.
The ring comparison is normalized on every scalar summand of the constant sheaf
(these summands determine it uniquely) and carries the addition and multiplication
transported by `L` to those of the target constant ring.
Source: Stacks, 00YV (2), (5), (6), 0H7J, and the node's proof steps 1--6
(auxiliary; not a blueprint node). -/
structure ConstantLeftModuleInverseImageLift
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L) where
  /-- The comparison `f⁻¹|Λ_C| ≅ |Λ_D|`, written on `L` of the constant set sheaf. -/
  ringUnderlying :
    L.obj ((constantSheaf J (Type u)).obj Λ) ≅
      (sheafCompose K (forget RingCat.{u})).obj
        ((constantSheaf K RingCat.{u}).obj (RingCat.of Λ))
  /-- The comparison carries the addition `L(+) ∘ p⁻¹` transported by `L` to the
  addition of `Λ_D`. -/
  ring_add : ∀ (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ)
    (m' : CoeffSet K Λ ⨯ CoeffSet K Λ ⟶ CoeffSet K Λ),
    IsRingAdd J Λ m → IsRingAdd K Λ m' →
      inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
          L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          ringUnderlying.hom =
        prod.map
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom)
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom) ≫ m'
  /-- The comparison carries the multiplication `L(μ) ∘ p⁻¹` transported by `L`
  to the multiplication of `Λ_D`. With `ring_add`, the bijectivity of the
  comparison and `constant_scalar` at `0` and `1`, it is a ring-sheaf isomorphism
  from the transported ring structure on `f⁻¹Λ_C` to `Λ_D`. -/
  ring_mul : ∀ (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ)
    (m' : CoeffSet K Λ ⨯ CoeffSet K Λ ⟶ CoeffSet K Λ),
    IsRingMul J Λ m → IsRingMul K Λ m' →
      inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
          L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          ringUnderlying.hom =
        prod.map
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom)
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom) ≫ m'
  pointIso : L.obj ((constantSheaf J (Type u)).obj PUnit.{u+1}) ≅
    (constantSheaf K (Type u)).obj PUnit.{u+1}
  constant_scalar : ∀ r : Λ,
    L.map ((constantSheaf J (Type u)).map
      (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))) ≫ ringUnderlying.hom ≫
      (constantCommuteCompose K (forget RingCat.{u})).hom.app (RingCat.of Λ) =
      pointIso.hom ≫ (constantSheaf K (Type u)).map
        (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))
  moduleFunctor : Modules J Λ ⥤ Modules K Λ
  moduleDirect : Modules K Λ ⥤ Modules J Λ
  moduleAdj : moduleFunctor ⊣ moduleDirect
  additive : moduleFunctor.Additive
  preservesFiniteLimits : PreservesFiniteLimits moduleFunctor
  preservesFiniteColimits : PreservesFiniteColimits moduleFunctor
  abelianInverse : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}
  abelianDirect : Sheaf K AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}
  abelianAdj : abelianInverse ⊣ abelianDirect
  abelianSetIso : abelianInverse ⋙ U K ≅ U J ⋙ L
  abelianDirectSetIso : abelianDirect ⋙ U J ≅ U K ⋙ R
  abelian_addition : ∀ (A : Sheaf J AddCommGrpCat.{u})
    (a : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A)
    (b : (U K).obj (abelianInverse.obj A) ⨯ (U K).obj (abelianInverse.obj A) ⟶
      (U K).obj (abelianInverse.obj A)),
    IsAddition J A a → IsAddition K (abelianInverse.obj A) b →
      b ≫ abelianSetIso.hom.app A =
        prod.map (abelianSetIso.hom.app A) (abelianSetIso.hom.app A) ≫
          inv (prodComparison L ((U J).obj A) ((U J).obj A)) ≫ L.map a
  abelian_unit : ∀ A : Sheaf J AddCommGrpCat.{u},
    (U J).map (abelianAdj.unit.app A) ≫
      abelianDirectSetIso.hom.app (abelianInverse.obj A) ≫
      R.map (abelianSetIso.hom.app A) = adj.unit.app ((U J).obj A)
  underlyingIso : moduleFunctor ⋙ V K Λ ≅ V J Λ ⋙ abelianInverse
  directUnderlyingIso : moduleDirect ⋙ V J Λ ≅ V K Λ ⋙ abelianDirect
  moduleSetIso : moduleFunctor ⋙ W K Λ ≅ W J Λ ⋙ L
  moduleSetIso_compatibility : ∀ M : Modules J Λ,
    (U K).map (underlyingIso.hom.app M) ≫ abelianSetIso.hom.app ((V J Λ).obj M) =
      moduleSetIso.hom.app M
  scalar_compatibility : ∀ (M : Modules J Λ) (r : Λ)
    (a : (V J Λ).obj M ⟶ (V J Λ).obj M)
    (b : (V K Λ).obj (moduleFunctor.obj M) ⟶ (V K Λ).obj (moduleFunctor.obj M)),
    IsScalar J Λ M r a → IsScalar K Λ (moduleFunctor.obj M) r b →
      b ≫ underlyingIso.hom.app M = underlyingIso.hom.app M ≫ abelianInverse.map a
  unit_compatibility : ∀ M : Modules J Λ,
    (V J Λ).map (moduleAdj.unit.app M) ≫
      directUnderlyingIso.hom.app (moduleFunctor.obj M) ≫
      abelianDirect.map (underlyingIso.hom.app M) = abelianAdj.unit.app ((V J Λ).obj M)

/-! The coefficient comparison is natural in the constant type. Binary operations
are compared after the isomorphism from the constant sheaf on pairs. -/
section CoefficientConstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
variable (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
variable (adj : L ⊣ R) [PreservesFiniteLimits L]
private def pointTerminal : IsTerminal ((constantSheaf J (Type u)).obj PUnit.{u+1}) := by
  exact (Types.isTerminalPUnit.isTerminalObj (Functor.const Cᵒᵖ) _).isTerminalObj
    (presheafToSheaf J (Type u)) _
private def pointComparison :
    L.obj ((constantSheaf J (Type u)).obj PUnit.{u+1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u+1} :=
  ((pointTerminal J).isTerminalObj L _).uniqueUpToIso (pointTerminal K)
private def globalComparison : R ⋙ Sheaf.Γ J (Type u) ≅ Sheaf.Γ K (Type u) := by
  exact Functor.isoWhiskerLeft R (Sheaf.ΓNatIsoCoyoneda J PUnit.{u+1}) ≪≫
    (adj.compCoyonedaIso.app (op ((constantSheaf J (Type u)).obj PUnit.{u+1}))).symm ≪≫
    coyoneda.mapIso (pointComparison J K L).symm.op ≪≫
    (Sheaf.ΓNatIsoCoyoneda K PUnit.{u+1}).symm
private def constantComparison :
    constantSheaf J (Type u) ⋙ L ≅ constantSheaf K (Type u) :=
  (((constantSheafΓAdj J (Type u)).comp adj).ofNatIsoRight
    (globalComparison J K L R adj)).leftAdjointUniq (constantSheafΓAdj K (Type u))

variable (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}]

omit [HasWeakSheafify J RingCat.{u}] in
private theorem constantMap_unit (X Y : Type u) (f : X → Y) (T : Cᵒᵖ) (x : X) :
    ((constantSheaf J (Type u)).map (TypeCat.ofHom f)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app T x) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj Y)).app T (f x) := by
  exact (congrArg (fun g ↦ g.app T x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map (TypeCat.ofHom f)))).symm

open ConstantLeftModuleInverseImage
end CoefficientConstruction

/-! Lift left exact functors to abelian sheaves sectionwise, transport the constant
scalar endomorphisms, and extend them along ring sheafification. -/
section TransportConstruction
set_option linter.unusedSimpArgs false
open ConstantLeftModuleInverseImage
attribute [local instance] comp_preservesFiniteLimits

variable {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
  {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
  (F : A ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]

private def sectionAb (T : Dᵒᵖ) : A ⥤ AddCommGrpCat.{u} :=
  ((AddCommGrpCat.leftExactFunctorForgetEquivalence A).inverse.obj
    (LeftExactFunctor.of (F ⋙ sheafToPresheaf K (Type u) ⋙
      (evaluation Dᵒᵖ (Type u)).obj T))).obj

private instance constantLeftModuleTransportInst1
    (T : Dᵒᵖ) : PreservesFiniteLimits (sectionAb K F T) :=
  ((AddCommGrpCat.leftExactFunctorForgetEquivalence A).inverse.obj
    (LeftExactFunctor.of (F ⋙ sheafToPresheaf K (Type u) ⋙
      (evaluation Dᵒᵖ (Type u)).obj T))).property

section AbelianAdjunction
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
private instance forgetAbLimits : PreservesFiniteLimits (U J) := by
  have : PreservesFiniteLimits (U J ⋙ sheafToPresheaf J (Type u)) := by
    change PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} (Type u)).obj
        (forget AddCommGrpCat.{u}))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type u))

private instance abBiproducts : HasFiniteBiproducts (Sheaf J AddCommGrpCat.{u}) :=
  .of_hasFiniteProducts

variable (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  [PreservesFiniteLimits L] [PreservesFiniteLimits R]
  (adj : L ⊣ R)

end AbelianAdjunction

section ModuleAction
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]

variable (B : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}) [B.Additive]

variable [HasWeakSheafify K RingCat.{u}]
  (B' : Sheaf K AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}) [B'.Additive]
  (a : B ⊣ B')

end ModuleAction
section Assembly
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}]
  (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  (adj : L ⊣ R) (hL : PreservesFiniteLimits L)

end Assembly

end TransportConstruction

end CategoryTheory
