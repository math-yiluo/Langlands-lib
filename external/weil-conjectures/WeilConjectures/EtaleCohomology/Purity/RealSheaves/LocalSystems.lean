/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant
public import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.ConstructibleSheaf.Biproduct
public import WeilConjectures.ConstructibleSheaf.OfForget
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Continuous.Basic
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.RepresentationTheory.IntegralModel

/-!
# Local systems: the Galois correspondence and the lisse sheaf–representation dictionary

This file states the four steps that turn sheaf-theoretic statements about lisse sheaves on
a curve over a finite field into statements about representations of its Weil group:

- the Galois correspondence between finite locally constant sheaves of `Λ`-modules on a
  connected scheme and finite `Λ`-modules with a continuous action of the étale fundamental
  group;
- the resulting equivalence between lisse Weil sheaves and lisse Weil representations,
  matching short exact sequences and hence subobjects, quotients and subquotients;
- the existence of a Frobenius-stable integral model (an `𝒪_E`-lattice) of a lisse Weil
  representation;
- the identification of the ordinary étale `H⁰` with the invariants of the geometric
  fundamental group, equivariantly for the residual Frobenius.

## Implementation notes

Lisse `ℚ̄_ℓ`-sheaves do not exist in Mathlib. The renderings chosen here are therefore the
following.

- The étale fundamental group `π₁(Y, s)` is named as a fundamental group
  (`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`) of the fibre functor
  `AlgebraicGeometry.Scheme.FiniteEtale.fiber s` on finite étale `Y`-schemes.
  `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup`
  states the Galois correspondence for any such group `G`, and
  `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf` deduces the
  version with `G` existentially quantified as a bundled profinite group (`ProfiniteGrp`).
  The target category is the full subcategory of `Rep Λ G` cut out by
  `Rep.IsFiniteContinuous`. Compatibility with the geometric stalk is the requested clause; it
  is an isomorphism of underlying `Λ`-modules only, not tied to the action of `G` on geometric
  fibres. Exactness is `AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_shortExact_iff`
  (in `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystemsExact`). Compatibility
  with `⊗_Λ` is *not* a formal consequence of the equivalence (an equivalence of abelian
  categories need not be monoidal); it is proved in
  `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystemsTensor`, see
  `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_tensor`. The
  compatibility with base change along a map `Λ → Λ'` of
  finite rings is not restated either; with `G` fixed as in the `_of_isFundamentalGroup`
  version it could now be written down, but it is not part of the statement here.

- `AlgebraicGeometry.WeilGroup.isLisseRep` is a full subcategory of `Rep ℚ̄_ℓ W(C₀)`, and the
  content of the lisse sheaf–representation equivalence used by the rest of the block is
  recorded by the closure properties
  `AlgebraicGeometry.WeilGroup.isLisseRep.isClosedUnderKernels` and its companions together
  with `AlgebraicGeometry.WeilGroup.isLisseRep_shortExact_iff`. The equivalence itself, from lisse
  Weil sheaves, is `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`; its exactness is
  `AlgebraicGeometry.WeilGroup.isLisse_shortExact_iff`.
  Closure under extensions is *not* recorded: inside `Rep ℚ̄_ℓ W(C₀)` it fails, since a
  discontinuous additive character `c` of `π₁(C)` (for instance of a quotient `ℤ_ℓ`) gives the
  non-lisse extension `g ↦ !![1, c g; 0, 1]` of the trivial line by itself. An extension of
  lisse sheaves is lisse, but its representation is continuous for a reason — it comes from a
  sheaf — that is invisible on the representation side.

- In `AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice` the finite extension `E/ℚ_ℓ` is
  existentially quantified as a finite-dimensional `IntermediateField ℚ_[l] (PadicAlgCl l)`,
  which is what makes "after replacing `E` by a finite extension" a true statement; the
  `𝒪_E`-module structure on `V` is the restriction of scalars along
  `𝒪_E → E → ℚ̄_ℓ`, introduced by `letI` inside the statement.

- `AlgebraicGeometry.WeilGroup.globalSections_eq_invariants` is the representation-theoretic
  step of the proof sketch: the `π₁(U)`-equivariant maps from the trivial line
  (`AlgebraicGeometry.WeilGroup.globalSections`) are the invariants. The statement about the
  étale global sections `H⁰(Ū, F|_U)` of a lisse Weil sheaf is
  `AlgebraicGeometry.WeilGroup.exists_globalSections_upperStar_linearEquiv_invariants`.

The open subcurve `U₀ ⊆ C₀`, its Weil group `W(U₀)` and the restriction homomorphism
`W(U₀) → W(C₀)` enter through `AlgebraicGeometry.WeilGroup.Restriction`, which is also what
`AlgebraicGeometry.BoundaryDatum` extends.

## Main definitions

- `AlgebraicGeometry.WeilGroup.isLisseRep`
- `AlgebraicGeometry.WeilGroup.globalSections`

## Main statements

- `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf`
- `AlgebraicGeometry.WeilGroup.isLisseRep_shortExact_iff`
- `AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice`
- `AlgebraicGeometry.WeilGroup.globalSections_eq_invariants`
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

open Limits

/-- A functor to types preserving a binary product sends it to the cartesian product. -/
lemma Functor.bijective_map_prod_fst_snd {C : Type*} [Category* C] (H : C ⥤ Type _)
    (A B : C) [HasBinaryProduct A B] [PreservesLimit (pair A B) H] :
    Function.Bijective (fun z : H.obj (A ⨯ B) ↦ (H.map prod.fst z, H.map prod.snd z)) := by
  have : (fun z : H.obj (A ⨯ B) ↦ (H.map prod.fst z, H.map prod.snd z)) =
      ((PreservesLimitPair.iso H A B).hom ≫ (Types.binaryProductIso _ _).hom) := by
    funext z
    ext
    · rw [ConcreteCategory.comp_apply, Types.binaryProductIso_hom_comp_fst_apply,
        ← ConcreteCategory.comp_apply, PreservesLimitPair.iso_hom, prodComparison_fst]
    · rw [ConcreteCategory.comp_apply, Types.binaryProductIso_hom_comp_snd_apply,
        ← ConcreteCategory.comp_apply, PreservesLimitPair.iso_hom, prodComparison_snd]
  rw [this]
  exact (isIso_iff_bijective _).mp inferInstance

section PairAux

variable {C : Type*} [Category* C] (H : C ⥤ Type _)

/-- The bijection `H(A ⨯ B) ≃ H(A) × H(B)` for a functor to types preserving the product. -/
noncomputable def Functor.prodEquiv (A B : C) [HasBinaryProduct A B] [PreservesLimit (pair A B) H] :
    H.obj (A ⨯ B) ≃ H.obj A × H.obj B :=
  Equiv.ofBijective _ (H.bijective_map_prod_fst_snd A B)

variable {H} {A B : C} [HasBinaryProduct A B] [PreservesLimit (pair A B) H]

@[simp]
lemma Functor.map_fst_prodEquiv_symm (u : H.obj A) (v : H.obj B) :
    H.map prod.fst ((H.prodEquiv A B).symm (u, v)) = u :=
  congrArg _root_.Prod.fst ((H.prodEquiv A B).apply_symm_apply (u, v))

@[simp]
lemma Functor.map_snd_prodEquiv_symm (u : H.obj A) (v : H.obj B) :
    H.map prod.snd ((H.prodEquiv A B).symm (u, v)) = v :=
  congrArg _root_.Prod.snd ((H.prodEquiv A B).apply_symm_apply (u, v))

@[simp]
lemma Functor.map_prod_lift {X : C} (f : X ⟶ A) (g : X ⟶ B) (t : H.obj X) :
    H.map (prod.lift f g) t = (H.prodEquiv A B).symm (H.map f t, H.map g t) := by
  apply (H.prodEquiv A B).injective
  rw [Equiv.apply_symm_apply]
  change (H.map prod.fst (H.map (prod.lift f g) t), H.map prod.snd (H.map (prod.lift f g) t)) = _
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, prod.lift_fst,
    prod.lift_snd]

lemma Functor.subsingleton_obj_terminal [HasTerminal C] [PreservesLimit (Functor.empty.{0} C) H] :
    Subsingleton (H.obj (⊤_ C)) :=
  (PreservesTerminal.iso H ≪≫ Types.terminalIso).toEquiv.subsingleton

end PairAux

end CategoryTheory

namespace AlgebraicGeometry

/-- The functor sending a finite étale `Y`-scheme `P` to the étale sheaf of sets `Hom_Y(-, P)` it
represents. This is the first half of the step *sheaves and covers* of
`AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup`:
finite locally constant sheaves of sets are the sheaves in its essential image. -/
noncomputable def Scheme.FiniteEtale.toSheaf (Y : Scheme.{u}) :
    Y.FiniteEtale ⥤ Sheaf Y.smallEtaleTopology (Type u) :=
  ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.yoneda

/-- A finite étale `Y`-scheme is determined by the étale sheaf of sets it represents: the small
étale topology is subcanonical, so `AlgebraicGeometry.Scheme.FiniteEtale.toSheaf` is fully
faithful. -/
noncomputable def Scheme.FiniteEtale.fullyFaithfulToSheaf (Y : Scheme.{u}) :
    (Scheme.FiniteEtale.toSheaf Y).FullyFaithful :=
  (ObjectProperty.fullyFaithfulι _).comp Y.smallEtaleTopology.yonedaFullyFaithful

/-- The stalk at a geometric point `s` of the sheaf represented by a finite étale `Y`-scheme `P`
is the geometric fibre of `P` at `s`. This is the compatibility of
`AlgebraicGeometry.Scheme.FiniteEtale.toSheaf` with the stalk functor, which makes the triangle
of `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup`
commute on represented sheaves. -/
noncomputable def Scheme.FiniteEtale.toSheafCompSheafFiberIso {Y : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    Scheme.FiniteEtale.toSheaf Y ⋙ (Scheme.pointSmallEtale s).sheafFiber ≅
      ObjectProperty.ι _ ⋙ (Scheme.pointSmallEtale s).fiber :=
  Functor.isoWhiskerLeft (ObjectProperty.ι _)
    (Functor.isoWhiskerRight (Y.smallEtaleTopology.yonedaCompSheafToPresheaf)
        (Scheme.pointSmallEtale s).presheafFiber ≪≫
      Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm
        (Scheme.pointSmallEtale s).presheafFiber ≪≫
      (Scheme.pointSmallEtale s).shrinkYonedaCompPresheafFiberIso)

/-- The functor sending a finite étale `Y`-scheme `P` to the étale sheaf of sets
`Hom_Y(-, P)`, with values in `Type (u + 1)`, as a finite locally constant sheaf of sets
(`AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`). -/
noncomputable def Scheme.FiniteEtale.toFiniteLocallyConstant (Y : Scheme.{u}) :
    Y.FiniteEtale ⥤ Y.FiniteLocallyConstant :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{u + 1})
    fun P ↦ by
      have : IsFinite P.obj.hom := P.property
      have : Etale P.obj.hom := P.obj.prop
      obtain ⟨_, h⟩ := (Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso Y).1 _ P.obj.hom
      exact h

/-- `AlgebraicGeometry.Scheme.FiniteEtale.toFiniteLocallyConstant` is fully faithful: the small
étale topology is subcanonical. -/
noncomputable def Scheme.FiniteEtale.fullyFaithfulToFiniteLocallyConstant (Y : Scheme.{u}) :
    (Scheme.FiniteEtale.toFiniteLocallyConstant Y).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    (((ObjectProperty.fullyFaithfulι _).comp
      Y.smallEtaleTopology.fullyFaithfulUliftYoneda.{u + 1}) :
      (ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{u + 1}).FullyFaithful)

instance (Y : Scheme.{u}) : (Scheme.FiniteEtale.toFiniteLocallyConstant Y).Full :=
  (Scheme.FiniteEtale.fullyFaithfulToFiniteLocallyConstant Y).full

instance (Y : Scheme.{u}) : (Scheme.FiniteEtale.toFiniteLocallyConstant Y).Faithful :=
  (Scheme.FiniteEtale.fullyFaithfulToFiniteLocallyConstant Y).faithful

/-- Every finite locally constant sheaf of sets is represented by a finite étale `Y`-scheme
(`AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`). -/
instance (Y : Scheme.{u}) : (Scheme.FiniteEtale.toFiniteLocallyConstant Y).EssSurj where
  mem_essImage E := by
    obtain ⟨P, π, _, _, ⟨e⟩⟩ := (Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso Y).2 E.obj
      E.property
    exact ⟨⟨Scheme.Etale.mk π, ‹IsFinite π›⟩, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
      ((fullyFaithfulSheafToPresheaf _ _).preimageIso e.symm)⟩⟩

instance (Y : Scheme.{u}) : (Scheme.FiniteEtale.toFiniteLocallyConstant Y).IsEquivalence where

/-- **Sheaves and covers** (the first step of `proposition-lattices-representations-normal-scheme`):
finite étale `Y`-schemes are equivalent to finite locally constant étale sheaves of sets, by
`P ↦ Hom_Y(-, P)`.
-/
noncomputable def Scheme.FiniteEtale.equivalenceFiniteLocallyConstant (Y : Scheme.{u}) :
    Y.FiniteEtale ≌ Y.FiniteLocallyConstant :=
  (Scheme.FiniteEtale.toFiniteLocallyConstant Y).asEquivalence

/-- **The sheaf of sets underlying a finite locally constant sheaf of `Λ`-modules**, for a
finite ring `Λ`, is finite locally constant: it is constant on the members of the same étale
cover, the forgetful functor preserving sheafification, and its stalks are the underlying sets
of the stalks of `F`, finitely generated modules over a finite ring. This is the first step of
the *linear structure* part of
`AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup`:
a finite locally constant sheaf of `Λ`-modules is a finite locally constant sheaf of sets with a
`Λ`-module structure. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.isFiniteLocallyConstantSheafOfTypes
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {Y : Scheme.{u}}
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : IsFiniteLocallyConstantSheaf F) :
    IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F) := by
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := hF.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · have := h𝒰 i
    exact inferInstanceAs (((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
      (F.over _)).IsConstant _)
  · have hfg := hF.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s
    have : Finite (ToType ((pointSmallEtale s).sheafFiber.obj F)) :=
      ConcreteCategory.FiniteOfIsFinitelyGenerated.finite_of_isFinitelyGenerated
        (C := ModuleCat.{u + 1} Λ) _ hfg
    let e := ((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    exact @Finite.of_equiv _ _ this e.symm.toEquiv


section BiprodAux

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasBinaryBiproducts C]
  {R : Type*} [Ring R] (H : C ⥤ ModuleCat R) [H.Additive] {X X' : C}

lemma _root_.CategoryTheory.Functor.map_biprod_fst_inl_add_inr (a : H.obj X) (b : H.obj X') :
    H.map Limits.biprod.fst (H.map Limits.biprod.inl a + H.map Limits.biprod.inr b) = a := by
  simp [← ConcreteCategory.comp_apply, ← H.map_comp]

lemma _root_.CategoryTheory.Functor.map_biprod_snd_inl_add_inr (a : H.obj X) (b : H.obj X') :
    H.map Limits.biprod.snd (H.map Limits.biprod.inl a + H.map Limits.biprod.inr b) = b := by
  simp [← ConcreteCategory.comp_apply, ← H.map_comp]

lemma _root_.CategoryTheory.Functor.map_biprod_desc_id_id (w : H.obj (X ⊞ X)) :
    H.map (Limits.biprod.desc (𝟙 X) (𝟙 X)) w =
      H.map Limits.biprod.fst w + H.map Limits.biprod.snd w := by
  have : Limits.biprod.desc (𝟙 X) (𝟙 X) = Limits.biprod.fst + Limits.biprod.snd := by
    apply Limits.biprod.hom_ext' <;> simp
  rw [this, H.map_add]
  rfl

end BiprodAux

section GaloisAction

/-! ### The Galois action on stalks of finite locally constant sheaves -/

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- The stalk at `s` of the sheaf `Hom_Y(-, P)` (with values in `Type (u + 1)`) represented by a
finite étale `Y`-scheme `P` is the geometric fibre of `P`. -/
noncomputable def Scheme.FiniteEtale.toFiniteLocallyConstantCompSheafFiberIso :
    Scheme.FiniteEtale.toFiniteLocallyConstant Y ⋙ ObjectProperty.ι _ ⋙
        (Scheme.pointSmallEtale s).sheafFiber ≅
      ObjectProperty.ι _ ⋙ (Scheme.pointSmallEtale s).fiber ⋙ uliftFunctor.{u + 1} :=
  have : Y.smallEtaleTopology.HasSheafCompose uliftFunctor.{u + 1, u} := inferInstance
  have : Limits.PreservesFilteredColimitsOfSize.{u, u} uliftFunctor.{u + 1, u} := inferInstance
  Functor.isoWhiskerLeft (Scheme.FiniteEtale.toSheaf Y)
      ((Scheme.pointSmallEtale s).sheafFiberCompIso uliftFunctor.{u + 1}) ≪≫
    Functor.isoWhiskerRight (Scheme.FiniteEtale.toSheafCompSheafFiberIso s) uliftFunctor.{u + 1}


/-- The stalk of a finite locally constant sheaf of sets `S` at `s` is the geometric fibre of the
finite étale `Y`-scheme representing `S`. -/
noncomputable def Scheme.FiniteLocallyConstant.stalkEquiv (S : Y.FiniteLocallyConstant) :
    (Scheme.pointSmallEtale s).sheafFiber.obj S.obj ≃
      ULift.{u + 1} ((Scheme.pointSmallEtale s).fiber.obj
        ((Scheme.FiniteEtale.equivalenceFiniteLocallyConstant Y).inverse.obj S).obj) :=
  ((Scheme.pointSmallEtale s).sheafFiber.mapIso ((ObjectProperty.ι _).mapIso
      ((Scheme.FiniteEtale.equivalenceFiniteLocallyConstant Y).counitIso.app S))).symm.toEquiv.trans
    ((Scheme.FiniteEtale.toFiniteLocallyConstantCompSheafFiberIso s).app
      ((Scheme.FiniteEtale.equivalenceFiniteLocallyConstant Y).inverse.obj S)).toEquiv

lemma Scheme.FiniteLocallyConstant.stalkEquiv_naturality {S S' : Y.FiniteLocallyConstant}
    (f : S ⟶ S') (x : (Scheme.pointSmallEtale s).sheafFiber.obj S.obj) :
    stalkEquiv s S' ((Scheme.pointSmallEtale s).sheafFiber.map f.hom x) =
      ULift.up ((Scheme.FiniteEtale.fiber s).map
        ((Scheme.FiniteEtale.equivalenceFiniteLocallyConstant Y).inverse.map f)
          (stalkEquiv s S x).down) := by
  set E := Scheme.FiniteEtale.equivalenceFiniteLocallyConstant Y
  have h₁ := congrArg (fun φ ↦ (Scheme.pointSmallEtale s).sheafFiber.map φ.hom)
    (E.counitIso.inv.naturality f)
  have h₂ := (Scheme.FiniteEtale.toFiniteLocallyConstantCompSheafFiberIso s).hom.naturality
    (E.inverse.map f)
  have k₁ := ConcreteCategory.congr_hom h₁ x
  have k₂ := ConcreteCategory.congr_hom h₂
    ((Scheme.pointSmallEtale s).sheafFiber.map (E.counitIso.inv.app S).hom x)
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
    ConcreteCategory.comp_apply] at k₁ k₂
  simp only [stalkEquiv, Equiv.trans_apply, Iso.toEquiv_fun, Iso.symm_hom, Functor.mapIso_inv,
    ObjectProperty.ι_map, Iso.app_inv]
  erw [k₁]
  exact k₂


variable (G : Type u) [Group G] [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]

/-- The action of `G` on the stalk at `s` of a finite locally constant sheaf of sets, through
the geometric fibre of the representing finite étale `Y`-scheme. -/
noncomputable def Scheme.FiniteLocallyConstant.galoisSMul (g : G) (S : Y.FiniteLocallyConstant)
    (x : (Scheme.pointSmallEtale s).sheafFiber.obj S.obj) :
    (Scheme.pointSmallEtale s).sheafFiber.obj S.obj :=
  (stalkEquiv s S).symm ⟨(g • (show (Scheme.FiniteEtale.fiber s).obj
    ((Scheme.FiniteEtale.equivalenceFiniteLocallyConstant Y).inverse.obj S) from
      (stalkEquiv s S x).down) : (Scheme.FiniteEtale.fiber s).obj _)⟩

lemma Scheme.FiniteLocallyConstant.galoisSMul_naturality
    [PreGaloisCategory.IsNaturalSMul (Scheme.FiniteEtale.fiber s) G] (g : G)
    {S S' : Y.FiniteLocallyConstant} (f : S ⟶ S')
    (x : (Scheme.pointSmallEtale s).sheafFiber.obj S.obj) :
    (Scheme.pointSmallEtale s).sheafFiber.map f.hom (galoisSMul s G g S x) =
      galoisSMul s G g S' ((Scheme.pointSmallEtale s).sheafFiber.map f.hom x) := by
  apply (stalkEquiv s S').injective
  rw [stalkEquiv_naturality]
  simp only [galoisSMul, Equiv.apply_symm_apply, stalkEquiv_naturality]
  exact congrArg ULift.up (PreGaloisCategory.IsNaturalSMul.naturality g _ _)

lemma Scheme.FiniteLocallyConstant.galoisSMul_one (S : Y.FiniteLocallyConstant)
    (x : (Scheme.pointSmallEtale s).sheafFiber.obj S.obj) : galoisSMul s G 1 S x = x := by
  simp only [galoisSMul, one_smul]
  exact (stalkEquiv s S).symm_apply_apply x

lemma Scheme.FiniteLocallyConstant.galoisSMul_mul (g h : G) (S : Y.FiniteLocallyConstant)
    (x : (Scheme.pointSmallEtale s).sheafFiber.obj S.obj) :
    galoisSMul s G (g * h) S x = galoisSMul s G g S (galoisSMul s G h S x) := by
  simp [galoisSMul, mul_smul]


section Linear

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- The finite locally constant sheaf of sets underlying a finite locally constant sheaf of
`Λ`-modules. -/
noncomputable abbrev Scheme.IsFiniteLocallyConstantSheaf.toFLC
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F) :
    Y.FiniteLocallyConstant :=
  ⟨(sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F,
    Scheme.IsFiniteLocallyConstantSheaf.isFiniteLocallyConstantSheafOfTypes F hF⟩

instance : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : ((Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : Limits.PreservesBinaryBiproducts
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _


omit [Finite Λ] in
lemma Scheme.sheafFiber_map_smul_id (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (c : Λ)
    (w : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map (c • 𝟙 F) w = c • w := by
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨V, v, σ, rfl⟩ := (Scheme.pointSmallEtale s).toPresheafFiber_jointly_surjective w
  change ((Scheme.pointSmallEtale s).toPresheafFiber V v F.obj ≫
    (Scheme.pointSmallEtale s).presheafFiber.map (c • 𝟙 F).hom) σ = _
  rw [(Scheme.pointSmallEtale s).toPresheafFiber_naturality, ConcreteCategory.comp_apply]
  exact map_smul _ c σ

/-- The stalk of a finite locally constant sheaf of `Λ`-modules is that of its underlying sheaf
of sets. -/
noncomputable def Scheme.IsFiniteLocallyConstantSheaf.stalkEquiv
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F) :
    (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F : Type (u + 1)) ≃
      (Scheme.pointSmallEtale s).sheafFiber.obj hF.toFLC.obj :=
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  (((Scheme.pointSmallEtale s).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F).symm.toEquiv

lemma Scheme.IsFiniteLocallyConstantSheaf.stalkEquiv_symm_naturality
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F)
    (hF' : IsFiniteLocallyConstantSheaf F') (f : F ⟶ F')
    (z : (Scheme.pointSmallEtale s).sheafFiber.obj hF.toFLC.obj) :
    ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map f
        ((hF.stalkEquiv s).symm z) =
      (hF'.stalkEquiv s).symm ((Scheme.pointSmallEtale s).sheafFiber.map
        ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map f) z) := by
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact (ConcreteCategory.congr_hom (((Scheme.pointSmallEtale s).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).hom.naturality f) z).symm

/-- The action of `g ∈ G` on the stalk of a finite locally constant sheaf of `Λ`-modules. -/
noncomputable def Scheme.IsFiniteLocallyConstantSheaf.galoisAct (g : G)
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F)
    (x : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F :=
  (hF.stalkEquiv s).symm
    (Scheme.FiniteLocallyConstant.galoisSMul s G g hF.toFLC (hF.stalkEquiv s x))

lemma Scheme.IsFiniteLocallyConstantSheaf.galoisAct_naturality
    [PreGaloisCategory.IsNaturalSMul (Scheme.FiniteEtale.fiber s) G] (g : G)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F)
    (hF' : IsFiniteLocallyConstantSheaf F') (f : F ⟶ F')
    (x : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map f
        (hF.galoisAct s G g x) =
      hF'.galoisAct s G g
        (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map f x) := by
  let f' : hF.toFLC ⟶ hF'.toFLC :=
    ObjectProperty.homMk ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map f)
  have h := stalkEquiv_symm_naturality s hF hF' f (hF.stalkEquiv s x)
  rw [Equiv.symm_apply_apply] at h
  simp only [galoisAct, stalkEquiv_symm_naturality s hF hF' f, h, Equiv.apply_symm_apply]
  exact congrArg _ (Scheme.FiniteLocallyConstant.galoisSMul_naturality s G g f' _)


lemma Scheme.IsFiniteLocallyConstantSheaf.galoisAct_add
    [PreGaloisCategory.IsNaturalSMul (Scheme.FiniteEtale.fiber s) G] (g : G)
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F)
    (x y : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    hF.galoisAct s G g (x + y) = hF.galoisAct s G g x + hF.galoisAct s G g y := by
  have := hF
  have hB : IsFiniteLocallyConstantSheaf (F ⊞ F) :=
    Scheme.IsFiniteLocallyConstantSheaf.biprod F F
  let St := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  let z := St.map Limits.biprod.inl x + St.map Limits.biprod.inr y
  have hdesc := St.map_biprod_desc_id_id (X := F)
  have hfst : St.map Limits.biprod.fst z = x := St.map_biprod_fst_inl_add_inr x y
  have hsnd : St.map Limits.biprod.snd z = y := St.map_biprod_snd_inl_add_inr x y
  have h₁ : St.map (Limits.biprod.desc (𝟙 F) (𝟙 F)) z = x + y := by rw [hdesc, hfst, hsnd]
  have n₁ := galoisAct_naturality s G g hB hF (Limits.biprod.desc (𝟙 F) (𝟙 F)) z
  have n₂ := galoisAct_naturality s G g hB hF Limits.biprod.fst z
  have n₃ := galoisAct_naturality s G g hB hF Limits.biprod.snd z
  rw [h₁] at n₁
  rw [hfst] at n₂
  rw [hsnd] at n₃
  rw [← n₁, ← n₂, ← n₃]
  exact hdesc _

lemma Scheme.IsFiniteLocallyConstantSheaf.galoisAct_smul
    [PreGaloisCategory.IsNaturalSMul (Scheme.FiniteEtale.fiber s) G] (g : G)
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F)
    (c : Λ) (x : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    hF.galoisAct s G g (c • x) = c • hF.galoisAct s G g x := by
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let St := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hc (w : St.obj F) : St.map (c • 𝟙 F) w = c • w := by
    obtain ⟨V, v, σ, rfl⟩ := (Scheme.pointSmallEtale s).toPresheafFiber_jointly_surjective w
    change ((Scheme.pointSmallEtale s).toPresheafFiber V v F.obj ≫
      (Scheme.pointSmallEtale s).presheafFiber.map (c • 𝟙 F).hom) σ = _
    rw [(Scheme.pointSmallEtale s).toPresheafFiber_naturality, ConcreteCategory.comp_apply]
    exact map_smul _ c σ
  have n := galoisAct_naturality s G g hF hF (c • 𝟙 F) x
  rw [hc, hc] at n
  exact n.symm

/-- The representation of `G` on the stalk at `s` of a finite locally constant sheaf of
`Λ`-modules. -/
noncomputable def Scheme.IsFiniteLocallyConstantSheaf.galoisRep
    [PreGaloisCategory.IsNaturalSMul (Scheme.FiniteEtale.fiber s) G]
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F) :
    Representation Λ G
      (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) where
  toFun g :=
    { toFun := hF.galoisAct s G g
      map_add' := hF.galoisAct_add s G g
      map_smul' := hF.galoisAct_smul s G g }
  map_one' := by
    ext x
    simp [galoisAct, Scheme.FiniteLocallyConstant.galoisSMul_one]
  map_mul' g h := by
    ext x
    simp [galoisAct, Scheme.FiniteLocallyConstant.galoisSMul_mul]



/-- **The geometric stalk as a representation of `G`**, on finite locally constant sheaves of
`Λ`-modules. -/
noncomputable def Scheme.galoisRepFunctor
    [PreGaloisCategory.IsNaturalSMul (Scheme.FiniteEtale.fiber s) G] :
    ObjectProperty.FullSubcategory
        (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          IsFiniteLocallyConstantSheaf F) ⥤ Rep.{u + 1} Λ G where
  obj F := Rep.of (F.property.galoisRep s G)
  map {F F'} f := Rep.ofHom
    { toLinearMap :=
        (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map f.hom).hom
      isIntertwining' g := LinearMap.ext fun v ↦
        Scheme.IsFiniteLocallyConstantSheaf.galoisAct_naturality s G g F.2 F'.2 f.hom v }
  map_id F := by
    ext v
    simp
  map_comp f f' := by
    ext v
    simp

/-- The underlying `Λ`-module of `AlgebraicGeometry.Scheme.galoisRepFunctor` is the stalk. -/
noncomputable def Scheme.galoisRepFunctorCompForget₂Iso
    [PreGaloisCategory.IsNaturalSMul (Scheme.FiniteEtale.fiber s) G] :
    Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ) ⋙
        forget₂ (Rep.{u + 1} Λ G) (ModuleCat.{u + 1} Λ) ≅
      ObjectProperty.ι _ ⋙ (Scheme.pointSmallEtale s).sheafFiber :=
  NatIso.ofComponents (fun F ↦ Iso.refl _) fun f ↦ by
    ext v
    rfl


/-- On a connected scheme, morphisms of finite locally constant sheaves of sets are determined
by their stalks at a geometric point. -/
lemma Scheme.FiniteLocallyConstant.hom_ext_of_sheafFiber [ConnectedSpace Y]
    {S S' : Y.FiniteLocallyConstant} {φ ψ : S ⟶ S'}
    (h : ∀ x, (Scheme.pointSmallEtale s).sheafFiber.map φ.hom x =
      (Scheme.pointSmallEtale s).sheafFiber.map ψ.hom x) : φ = ψ := by
  apply (Scheme.FiniteEtale.equivalenceFiniteLocallyConstant Y).inverse.map_injective
  apply (Scheme.FiniteEtale.fiber s).map_injective
  ext a
  obtain ⟨x, hx⟩ := (stalkEquiv s S).surjective ⟨a⟩
  have h₁ := stalkEquiv_naturality s φ x
  have h₂ := stalkEquiv_naturality s ψ x
  rw [hx, h x] at h₁
  rw [hx] at h₂
  exact congrArg ULift.down (h₁.symm.trans h₂)

instance [ConnectedSpace Y] [PreGaloisCategory.IsNaturalSMul (Scheme.FiniteEtale.fiber s) G] :
    (Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).Faithful where
  map_injective {F F'} f g h := by
    have hfg (x) : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map f.hom x =
        ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map g.hom x :=
      congr(($h).hom x)
    let f' : F.property.toFLC ⟶ F'.property.toFLC :=
      ObjectProperty.homMk
        ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map f.hom)
    let g' : F.property.toFLC ⟶ F'.property.toFLC :=
      ObjectProperty.homMk
        ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map g.hom)
    have h' : f' = g' := Scheme.FiniteLocallyConstant.hom_ext_of_sheafFiber s fun z ↦ by
      apply (F'.property.stalkEquiv s).symm.injective
      have e₁ := Scheme.IsFiniteLocallyConstantSheaf.stalkEquiv_symm_naturality s F.2 F'.2 f.hom z
      have e₂ := Scheme.IsFiniteLocallyConstantSheaf.stalkEquiv_symm_naturality s F.2 F'.2 g.hom z
      exact e₁.symm.trans ((hfg _).trans e₂)
    ext V v
    exact congr(($h').hom.hom.app V v)


/-- **Equivariant maps of stalks come from morphisms of sheaves.** On a connected scheme, a
`G`-equivariant map between the stalks of finite locally constant sheaves of sets is the stalk of
a morphism of sheaves. -/
lemma Scheme.FiniteLocallyConstant.exists_hom_of_equivariant [ConnectedSpace Y]
    [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]
    [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G]
    {S S' : Y.FiniteLocallyConstant}
    (φ : (Scheme.pointSmallEtale s).sheafFiber.obj S.obj →
      (Scheme.pointSmallEtale s).sheafFiber.obj S'.obj)
    (hφ : ∀ g x, φ (galoisSMul s G g S x) = galoisSMul s G g S' (φ x)) :
    ∃ ψ : S ⟶ S', ∀ x, (Scheme.pointSmallEtale s).sheafFiber.map ψ.hom x = φ x := by
  set E := Scheme.FiniteEtale.equivalenceFiniteLocallyConstant Y
  let φ' : (Scheme.FiniteEtale.fiber s).obj (E.inverse.obj S) →
      (Scheme.FiniteEtale.fiber s).obj (E.inverse.obj S') :=
    fun a ↦ (stalkEquiv s S' (φ ((stalkEquiv s S).symm ⟨a⟩))).down
  have hφ' (g : G) (a) : φ' (g • a) = g • φ' a := by
    have := hφ g ((stalkEquiv s S).symm ⟨a⟩)
    simp only [galoisSMul, Equiv.apply_symm_apply] at this
    simp only [φ', this, Equiv.apply_symm_apply]
  let A := Scheme.FiniteEtale.equivalenceContAction s G
  let m : A.functor.obj (E.inverse.obj S) ⟶ A.functor.obj (E.inverse.obj S') :=
    ObjectProperty.homMk ⟨FintypeCat.homMk φ', fun g ↦ by
      apply FintypeCat.hom_ext
      intro a
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, FintypeCat.homMk_apply,
        FintypeCat.homMk_apply]
      exact hφ' g a⟩
  have hh : (Scheme.FiniteEtale.fiber s).map (A.functor.preimage m) = FintypeCat.homMk φ' :=
    congrArg (fun k ↦ k.hom.hom) (A.functor.map_preimage m)
  refine ⟨E.inverse.preimage (A.functor.preimage m), fun x ↦ (stalkEquiv s S').injective ?_⟩
  rw [stalkEquiv_naturality, E.inverse.map_preimage, hh, FintypeCat.homMk_apply]
  simp only [φ']
  rw [show (⟨(stalkEquiv s S x).down⟩ : ULift _) = stalkEquiv s S x from rfl,
    Equiv.symm_apply_apply]
  rfl


lemma Scheme.IsFiniteLocallyConstantSheaf.sheafFiber_map_stalkEquiv
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F)
    (hF' : IsFiniteLocallyConstantSheaf F') (f : F ⟶ F')
    (x : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    (Scheme.pointSmallEtale s).sheafFiber.map
        ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map f) (hF.stalkEquiv s x) =
      hF'.stalkEquiv s
        (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map f x) := by
  have h := stalkEquiv_symm_naturality s hF hF' f (hF.stalkEquiv s x)
  rw [Equiv.symm_apply_apply] at h
  rw [h, Equiv.apply_symm_apply]

lemma Scheme.IsFiniteLocallyConstantSheaf.galoisAct_eq
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F)
    (g : G) (z : (Scheme.pointSmallEtale s).sheafFiber.obj hF.toFLC.obj) :
    hF.galoisAct s G g ((hF.stalkEquiv s).symm z) =
      (hF.stalkEquiv s).symm (Scheme.FiniteLocallyConstant.galoisSMul s G g hF.toFLC z) := by
  simp [galoisAct]

/-- An equivariant linear map of stalks is the stalk of a morphism of the underlying sheaves of
sets. -/
lemma Scheme.IsFiniteLocallyConstantSheaf.exists_hom_of_equivariant [ConnectedSpace Y]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G]
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F)
    (hF' : IsFiniteLocallyConstantSheaf F')
    (φ : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F →
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F')
    (hφ : ∀ g x, φ (hF.galoisAct s G g x) = hF'.galoisAct s G g (φ x)) :
    ∃ ψ : hF.toFLC ⟶ hF'.toFLC, ∀ x, (Scheme.pointSmallEtale s).sheafFiber.map ψ.hom
      (hF.stalkEquiv s x) = hF'.stalkEquiv s (φ x) := by
  obtain ⟨ψ, hψ⟩ := Scheme.FiniteLocallyConstant.exists_hom_of_equivariant s G
    (fun z ↦ hF'.stalkEquiv s (φ ((hF.stalkEquiv s).symm z))) fun g z ↦ by
      rw [← galoisAct_eq s G hF g z, hφ]
      simp only [galoisAct, Equiv.apply_symm_apply]
  exact ⟨ψ, fun x ↦ by rw [hψ, Equiv.symm_apply_apply]⟩

instance [ConnectedSpace Y] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G] :
    (Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).Full where
  map_surjective {F F'} φ := by
    let St := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
    let fl {A B : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
        (hA : Scheme.IsFiniteLocallyConstantSheaf A) (hB : Scheme.IsFiniteLocallyConstantSheaf B)
        (f : A ⟶ B) :
        hA.toFLC ⟶ hB.toFLC :=
      ObjectProperty.homMk ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map f)
    let φ0 : St.obj F.obj → St.obj F'.obj := fun v ↦ φ.hom v
    have hφ0 (g : G) (x) : φ0 (F.2.galoisAct s G g x) = F'.2.galoisAct s G g (φ0 x) :=
      LinearMap.congr_fun (φ.hom.isIntertwining' g) x
    have hadd (x y) : φ0 (x + y) = φ0 x + φ0 y := map_add φ.hom x y
    have hsmul (c : Λ) (x) : φ0 (c • x) = c • φ0 x := map_smul φ.hom c x
    obtain ⟨ψ, hψ⟩ := F.2.exists_hom_of_equivariant s G F'.2 φ0 hφ0
    have := F.2
    have := F'.2
    have hB : Scheme.IsFiniteLocallyConstantSheaf (F.obj ⊞ F.obj) :=
      Scheme.IsFiniteLocallyConstantSheaf.biprod _ _
    have hB' : Scheme.IsFiniteLocallyConstantSheaf (F'.obj ⊞ F'.obj) :=
      Scheme.IsFiniteLocallyConstantSheaf.biprod _ _
    let μ : St.obj (F.obj ⊞ F.obj) → St.obj (F'.obj ⊞ F'.obj) := fun w ↦
      St.map Limits.biprod.inl (φ0 (St.map Limits.biprod.fst w)) +
        St.map Limits.biprod.inr (φ0 (St.map Limits.biprod.snd w))
    have hμ (g : G) (w) : μ (hB.galoisAct s G g w) = hB'.galoisAct s G g (μ w) := by
      simp only [μ]
      rw [Scheme.IsFiniteLocallyConstantSheaf.galoisAct_add,
        ← Scheme.IsFiniteLocallyConstantSheaf.galoisAct_naturality s G g F'.2 hB',
        ← Scheme.IsFiniteLocallyConstantSheaf.galoisAct_naturality s G g F'.2 hB', ← hφ0, ← hφ0,
        Scheme.IsFiniteLocallyConstantSheaf.galoisAct_naturality s G g hB F.2,
        Scheme.IsFiniteLocallyConstantSheaf.galoisAct_naturality s G g hB F.2]
    obtain ⟨Ψ, hΨ⟩ := hB.exists_hom_of_equivariant s G hB' μ hμ
    -- identities of morphisms of sheaves of sets, checked on stalks
    have key {A B A' B' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
        (hA : Scheme.IsFiniteLocallyConstantSheaf A) (hB : Scheme.IsFiniteLocallyConstantSheaf B)
        (hA' : Scheme.IsFiniteLocallyConstantSheaf A')
        (hB' : Scheme.IsFiniteLocallyConstantSheaf B') (α : hA.toFLC ⟶ hA'.toFLC)
        (β : hB.toFLC ⟶ hB'.toFLC) (a : A ⟶ B) (a' : A' ⟶ B')
        (αs : St.obj A → St.obj A') (βs : St.obj B → St.obj B')
        (hα : ∀ x, (Scheme.pointSmallEtale s).sheafFiber.map α.hom (hA.stalkEquiv s x) =
          hA'.stalkEquiv s (αs x))
        (hβ : ∀ x, (Scheme.pointSmallEtale s).sheafFiber.map β.hom (hB.stalkEquiv s x) =
          hB'.stalkEquiv s (βs x))
        (h : ∀ x, St.map a' (αs x) = βs (St.map a x)) :
        α ≫ fl hA' hB' a' = fl hA hB a ≫ β :=
      Scheme.FiniteLocallyConstant.hom_ext_of_sheafFiber s fun z ↦ by
        obtain ⟨x, rfl⟩ := (hA.stalkEquiv s).surjective z
        simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
          ConcreteCategory.comp_apply]
        rw [hα]
        erw [Scheme.IsFiniteLocallyConstantSheaf.sheafFiber_map_stalkEquiv s hA' hB',
          Scheme.IsFiniteLocallyConstantSheaf.sheafFiber_map_stalkEquiv s hA hB]
        rw [hβ, h]
    have i₁ := key hB F.2 hB' F'.2 Ψ ψ Limits.biprod.fst Limits.biprod.fst μ φ0 hΨ hψ
      fun w ↦ St.map_biprod_fst_inl_add_inr _ _
    have i₂ := key hB F.2 hB' F'.2 Ψ ψ Limits.biprod.snd Limits.biprod.snd μ φ0 hΨ hψ
      fun w ↦ St.map_biprod_snd_inl_add_inr _ _
    have i₃ := key hB F.2 hB' F'.2 Ψ ψ (Limits.biprod.desc (𝟙 _) (𝟙 _))
      (Limits.biprod.desc (𝟙 _) (𝟙 _)) μ φ0 hΨ hψ fun w ↦ by
        rw [St.map_biprod_desc_id_id, St.map_biprod_desc_id_id, St.map_biprod_fst_inl_add_inr,
          St.map_biprod_snd_inl_add_inr, hadd]
    have i₄ (c : Λ) := key F.2 F.2 F'.2 F'.2 ψ ψ (c • 𝟙 _) (c • 𝟙 _) φ0 φ0 hψ hψ fun x ↦ by
      rw [Scheme.sheafFiber_map_smul_id, Scheme.sheafFiber_map_smul_id, hsmul]
    -- `ψ` is linear on sections
    let ψV (V : Y.Etale) : F.obj.obj.obj (Opposite.op V) → F'.obj.obj.obj (Opposite.op V) :=
      fun a ↦ ψ.hom.hom.app (Opposite.op V) a
    have happ (V : Y.Etale) (a b : F.obj.obj.obj (Opposite.op V)) :
        ψV V (a + b) = ψV V a + ψV V b := by
      let Sec := sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (evaluation _ _).obj (Opposite.op V)
      let c := Sec.map Limits.biprod.inl a + Sec.map Limits.biprod.inr b
      have k₁ := congr($(i₁).hom.hom.app (Opposite.op V) c)
      have k₂ := congr($(i₂).hom.hom.app (Opposite.op V) c)
      have k₃ := congr($(i₃).hom.hom.app (Opposite.op V) c)
      change Sec.map Limits.biprod.fst (Ψ.hom.hom.app (Opposite.op V) c) =
        ψ.hom.hom.app (Opposite.op V) (Sec.map Limits.biprod.fst c) at k₁
      change Sec.map Limits.biprod.snd (Ψ.hom.hom.app (Opposite.op V) c) =
        ψ.hom.hom.app (Opposite.op V) (Sec.map Limits.biprod.snd c) at k₂
      change Sec.map (Limits.biprod.desc (𝟙 _) (𝟙 _)) (Ψ.hom.hom.app (Opposite.op V) c) =
        ψ.hom.hom.app (Opposite.op V) (Sec.map (Limits.biprod.desc (𝟙 _) (𝟙 _)) c) at k₃
      rw [Sec.map_biprod_fst_inl_add_inr] at k₁
      rw [Sec.map_biprod_snd_inl_add_inr] at k₂
      rw [Sec.map_biprod_desc_id_id, Sec.map_biprod_desc_id_id, Sec.map_biprod_fst_inl_add_inr,
        Sec.map_biprod_snd_inl_add_inr, k₁, k₂] at k₃
      exact k₃.symm
    have hsm (V : Y.Etale) (c : Λ) (a : F.obj.obj.obj (Opposite.op V)) :
        ψV V (c • a) = c • ψV V a := by
      have k := congr($(i₄ c).hom.hom.app (Opposite.op V) a)
      exact k.symm
    let f : F.obj ⟶ F'.obj :=
      ⟨{ app V := ModuleCat.ofHom
          { toFun := ψV V.unop
            map_add' := happ V.unop
            map_smul' := hsm V.unop }
         naturality V W h := by
          ext a
          exact ConcreteCategory.congr_hom (ψ.hom.hom.naturality h) a }⟩
    refine ⟨ObjectProperty.homMk f, ?_⟩
    ext v
    change St.map f v = φ0 v
    apply (F'.2.stalkEquiv s).injective
    rw [← Scheme.IsFiniteLocallyConstantSheaf.sheafFiber_map_stalkEquiv s F.2 F'.2 f v, ← hψ]
    rfl


open scoped PreGaloisCategory in
/-- The stalk of a finite locally constant sheaf is a finite continuous representation. -/
lemma Scheme.galoisRepFunctor_obj_isFiniteContinuous [ConnectedSpace Y] [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G] [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G]
    (F : ObjectProperty.FullSubcategory
      (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦ IsFiniteLocallyConstantSheaf F)) :
    Rep.IsFiniteContinuous ((Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).obj F) := by
  refine ⟨?_, fun x ↦ ?_⟩
  · have hfg := F.2.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s
    exact ConcreteCategory.FiniteOfIsFinitelyGenerated.finite_of_isFinitelyGenerated
      (C := ModuleCat.{u + 1} Λ) _ hfg
  · let a : (Scheme.FiniteEtale.fiber s).obj
        ((Scheme.FiniteEtale.equivalenceFiniteLocallyConstant Y).inverse.obj F.2.toFLC) :=
      (Scheme.FiniteLocallyConstant.stalkEquiv s F.2.toFLC (F.2.stalkEquiv s x)).down
    have : {g : G | ((Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).obj F).ρ g x = x} =
        {g : G | g • a = a} := by
      ext g
      change F.2.galoisAct s G g x = x ↔ _
      simp only [Scheme.IsFiniteLocallyConstantSheaf.galoisAct,
        Scheme.FiniteLocallyConstant.galoisSMul, Equiv.symm_apply_eq]
      constructor
      · intro h
        exact congrArg ULift.down h
      · intro h
        exact ULift.ext h
    rw [this]
    exact (isOpen_discrete {a}).preimage (continuous_id.smul continuous_const)

end Linear

end GaloisAction

section EssSurjAux

open Limits

variable {Y : Scheme.{u}}


/-- Products of sheaves of sets trivialised over `U` are trivialised over `U`. -/
lemma Scheme.isConstant_over_prod (U : Y.Etale) {S T : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    [(S.over U).IsConstant (Y.smallEtaleTopology.over U)]
    [(T.over U).IsConstant (Y.smallEtaleTopology.over U)] :
    ((S ⨯ T).over U).IsConstant (Y.smallEtaleTopology.over U) := by
  obtain ⟨X, ⟨eX⟩⟩ := Sheaf.mem_essImage_of_isConstant _ (S.over U)
  obtain ⟨X', ⟨eX'⟩⟩ := Sheaf.mem_essImage_of_isConstant _ (T.over U)
  exact Sheaf.isConstant_of_iso _
    (PreservesLimitPair.iso (Y.smallEtaleTopology.overPullback (Type (u + 1)) U) S T ≪≫
      prod.mapIso eX.symm eX'.symm ≪≫
      (PreservesLimitPair.iso (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1)))
        X X').symm)

/-- The terminal sheaf of sets is trivialised over every `U`. -/
lemma Scheme.isConstant_over_terminal (U : Y.Etale) :
    ((⊤_ Sheaf Y.smallEtaleTopology (Type (u + 1))).over U).IsConstant
      (Y.smallEtaleTopology.over U) :=
  Sheaf.isConstant_of_iso _
    (PreservesTerminal.iso (Y.smallEtaleTopology.overPullback (Type (u + 1)) U) ≪≫
      (PreservesTerminal.iso (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1)))).symm)

/-- A finite discrete `G`-set with open stabilisers has a continuous action. -/
lemma continuousSMul_of_isOpen_stabilizer (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {X : Type*} [TopologicalSpace X] [DiscreteTopology X] [MulAction G X]
    (h : ∀ x : X, IsOpen {g : G | g • x = x}) : ContinuousSMul G X := by
  refine ⟨continuous_discrete_rng.mpr fun y ↦ ?_⟩
  have : (fun p : G × X ↦ p.1 • p.2) ⁻¹' {y} = ⋃ x : X, {g : G | g • x = y} ×ˢ {x} := by
    ext ⟨g, x⟩
    simp
  rw [this]
  refine isOpen_iUnion fun x ↦ (?_ : IsOpen _).prod (isOpen_discrete _)
  by_cases hx : ∃ g₀ : G, g₀ • x = y
  · obtain ⟨g₀, rfl⟩ := hx
    have : {g : G | g • x = g₀ • x} = (fun g ↦ g₀⁻¹ * g) ⁻¹' {g | g • x = x} := by
      ext g
      simp [mul_smul, inv_smul_eq_iff]
    rw [this]
    exact (h x).preimage (continuous_const_mul _)
  · push Not at hx
    convert isOpen_empty
    ext g
    simpa using hx g

section EssSurj

variable [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
  [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G]

open scoped FintypeCatDiscrete

/-- **Finite continuous `G`-sets are stalks.** Every finite set with a continuous action of the
fundamental group `G` is, equivariantly, the stalk at `s` of a finite locally constant sheaf of
sets. -/
lemma Scheme.FiniteLocallyConstant.exists_stalkEquiv {X : Type (u + 1)} [Finite X]
    [MulAction G X] (hX : ∀ x : X, IsOpen {g : G | g • x = x}) :
    ∃ (S : Y.FiniteLocallyConstant) (e : (Scheme.pointSmallEtale s).sheafFiber.obj S.obj ≃ X),
      ∀ g x, e (Scheme.FiniteLocallyConstant.galoisSMul s G g S x) = g • e x := by
  classical
  let eq2 : X ≃ ULift.{u} (Fin (Nat.card X)) := (Finite.equivFin X).trans Equiv.ulift.symm
  let : MulAction G (ULift.{u} (Fin (Nat.card X))) := eq2.symm.mulAction G
  have heq (g : G) (y : ULift.{u} (Fin (Nat.card X))) : eq2.symm (g • y) = g • eq2.symm y := by
    change eq2.symm (eq2 (g • eq2.symm y)) = _
    rw [Equiv.symm_apply_apply]
  let X0 : FintypeCat.{u} := FintypeCat.of (ULift.{u} (Fin (Nat.card X)))
  let XA : Action FintypeCat.{u} G := Action.FintypeCat.ofMulAction G X0
  have hcont : XA.IsContinuous := by
    let : DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj XA) := ⟨rfl⟩
    refine continuousSMul_of_isOpen_stabilizer G fun y ↦ ?_
    convert hX (eq2.symm (show ULift.{u} (Fin (Nat.card X)) from y)) using 1
    ext g
    change g • (show ULift.{u} (Fin (Nat.card X)) from y) = y ↔
      g • eq2.symm (show ULift.{u} (Fin (Nat.card X)) from y) = eq2.symm y
    rw [← heq, eq2.symm.injective.eq_iff]
  let XC : ContAction FintypeCat.{u} G := ⟨XA, hcont⟩
  let A := Scheme.FiniteEtale.equivalenceContAction s G
  let E := Scheme.FiniteEtale.equivalenceFiniteLocallyConstant Y
  let P := A.inverse.obj XC
  let S := E.functor.obj P
  let iP : A.functor.obj P ≅ XC := A.counitIso.app XC
  let jP : E.inverse.obj S ≅ P := (E.unitIso.app P).symm
  let f1 : (Scheme.FiniteEtale.fiber s).obj (E.inverse.obj S) ≃
      (Scheme.FiniteEtale.fiber s).obj P :=
    FintypeCat.equivEquivIso.symm ((Scheme.FiniteEtale.fiber s).mapIso jP)
  let f2 : (Scheme.FiniteEtale.fiber s).obj P ≃ X0 :=
    FintypeCat.equivEquivIso.symm ((ObjectProperty.ι _ ⋙ Action.forget _ _).mapIso iP)
  refine ⟨S, (stalkEquiv s S).trans (Equiv.ulift.trans (f1.trans (f2.trans eq2.symm))),
    fun g x ↦ ?_⟩
  simp only [Equiv.trans_apply, galoisSMul, Equiv.apply_symm_apply]
  rw [← heq]
  congr 1
  let a : (Scheme.FiniteEtale.fiber s).obj (E.inverse.obj S) := (stalkEquiv s S x).down
  have h1 : f1 (g • a) = g • f1 a := PreGaloisCategory.IsNaturalSMul.naturality g jP.hom a
  have h2 : f2 (g • f1 a) = g • f2 (f1 a) :=
    ConcreteCategory.congr_hom (iP.hom.hom.comm g) (f1 a)
  exact (congrArg f2 h1).trans h2

section Construction

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

omit [ConnectedSpace Y] in
/-- A product of finite sheaves of sets is finite. -/
lemma Scheme.isFiniteSheaf_prod {S T : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (hS : Scheme.IsFiniteSheaf S) (hT : Scheme.IsFiniteSheaf T) :
    Scheme.IsFiniteSheaf (S ⨯ T) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    have hS' := hS.isFinitelyGenerated_sheafFiber Ω s
    have hT' := hT.isFinitelyGenerated_sheafFiber Ω s
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite] at hS' hT' ⊢
    have : AB5OfSize.{u, u} (Type (u + 1)) := AB5OfSize_shrink.{u, u, u + 1, u + 1} _
    exact Finite.of_injective _ ((pointSmallEtale s).sheafFiber.bijective_map_prod_fst_snd S T).1

omit [ConnectedSpace Y] in
/-- The terminal sheaf of sets is finite. -/
lemma Scheme.isFiniteSheaf_terminal :
    Scheme.IsFiniteSheaf (⊤_ Sheaf Y.smallEtaleTopology (Type (u + 1))) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    have : AB5OfSize.{u, u} (Type (u + 1)) := AB5OfSize_shrink.{u, u, u + 1, u + 1} _
    exact Finite.of_equiv _
      (PreservesTerminal.iso (pointSmallEtale s).sheafFiber ≪≫ Types.terminalIso).toEquiv.symm

/-- **Finite continuous representations are stalks.** -/
theorem Scheme.exists_galoisRepFunctor_obj_iso (M : Rep.{u + 1} Λ G)
    (hM : Rep.IsFiniteContinuous M) :
    ∃ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : IsFiniteLocallyConstantSheaf F),
      Nonempty ((Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).obj ⟨F, hF⟩ ≅ M) := by
  classical
  have : Finite M.V := hM.1
  let : MulAction G M.V :=
    { smul g x := M.ρ g x
      one_smul x := by
        change M.ρ 1 x = x
        simp
      mul_smul g h x := by
        change M.ρ (g * h) x = M.ρ g (M.ρ h x)
        simp [map_mul] }
  obtain ⟨S, e, he⟩ := Scheme.FiniteLocallyConstant.exists_stalkEquiv s G (X := M.V) hM.2
  let 𝒮 := S.obj
  obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := S.property
  have triv2 : ∀ i, ((𝒮 ⨯ 𝒮).over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)) := fun i ↦ by
    have := h𝒰 i
    exact Scheme.isConstant_over_prod _
  have triv3 : ∀ i, ((𝒮 ⨯ (𝒮 ⨯ 𝒮)).over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)) := fun i ↦ by
    have := h𝒰 i
    have := triv2 i
    exact Scheme.isConstant_over_prod _
  let S2 : Y.FiniteLocallyConstant := ⟨𝒮 ⨯ 𝒮, ⟨𝒰, triv2⟩, Scheme.isFiniteSheaf_prod hfin hfin⟩
  let S3 : Y.FiniteLocallyConstant :=
    ⟨𝒮 ⨯ (𝒮 ⨯ 𝒮), ⟨𝒰, triv3⟩, Scheme.isFiniteSheaf_prod hfin (Scheme.isFiniteSheaf_prod hfin hfin)⟩
  let S0 : Y.FiniteLocallyConstant :=
    ⟨⊤_ _, ⟨𝒰, fun i ↦ Scheme.isConstant_over_terminal _⟩, Scheme.isFiniteSheaf_terminal⟩
  have : AB5OfSize.{u, u} (Type (u + 1)) := AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  let St := (Scheme.pointSmallEtale s).sheafFiber (A := Type (u + 1))
  have he' (g : G) (x : M.V) :
      Scheme.FiniteLocallyConstant.galoisSMul s G g S (e.symm x) = e.symm (M.ρ g x) := by
    apply e.injective
    rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  have hfst (g : G) (w : St.obj (𝒮 ⨯ 𝒮)) :
      St.map prod.fst (Scheme.FiniteLocallyConstant.galoisSMul s G g S2 w) =
        Scheme.FiniteLocallyConstant.galoisSMul s G g S (St.map prod.fst w) :=
    Scheme.FiniteLocallyConstant.galoisSMul_naturality s G g (S := S2) (S' := S)
      (ObjectProperty.homMk prod.fst) w
  have hsnd (g : G) (w : St.obj (𝒮 ⨯ 𝒮)) :
      St.map prod.snd (Scheme.FiniteLocallyConstant.galoisSMul s G g S2 w) =
        Scheme.FiniteLocallyConstant.galoisSMul s G g S (St.map prod.snd w) :=
    Scheme.FiniteLocallyConstant.galoisSMul_naturality s G g (S := S2) (S' := S)
      (ObjectProperty.homMk prod.snd) w
  -- the addition, scalar multiplications and zero of `𝒮`, from those of the stalk `M`
  obtain ⟨ψa, hψa⟩ := Scheme.FiniteLocallyConstant.exists_hom_of_equivariant s G (S := S2)
    (S' := S) (fun w ↦ e.symm (e (St.map prod.fst w) + e (St.map prod.snd w))) fun g w ↦ by
      erw [hfst g w, hsnd g w, he, he, he', LinearMap.map_add]
      rfl
  have hm : ∀ c : Λ, ∃ ψ : S ⟶ S, ∀ w, St.map ψ.hom w = e.symm (c • e w) := fun c ↦
    Scheme.FiniteLocallyConstant.exists_hom_of_equivariant s G (fun w ↦ e.symm (c • e w))
      fun g w ↦ by
        simp only [he, he', map_smul]
        rfl
  choose ψm hψm using hm
  obtain ⟨ψz, hψz⟩ := Scheme.FiniteLocallyConstant.exists_hom_of_equivariant s G (S := S0)
    (S' := S) (fun _ ↦ e.symm 0) fun g w ↦ by rw [he', LinearMap.map_zero]
  let a : 𝒮 ⨯ 𝒮 ⟶ 𝒮 := ψa.hom
  let m (c : Λ) : 𝒮 ⟶ 𝒮 := (ψm c).hom
  let z : ⊤_ _ ⟶ 𝒮 := ψz.hom
  have ha (u : St.obj (𝒮 ⨯ 𝒮)) :
      e (St.map a u) = e (St.map prod.fst u) + e (St.map prod.snd u) := by
    rw [hψa]
    exact e.apply_symm_apply _
  have hmc (c : Λ) (x : St.obj 𝒮) : e (St.map (m c) x) = c • e x := by
    rw [hψm]
    simp
  have hz (x : St.obj (⊤_ _)) : e (St.map z x) = 0 := by
    rw [hψz]
    simp
  have hA {A : Sheaf Y.smallEtaleTopology (Type (u + 1))} (χ : A ⟶ 𝒮 ⨯ 𝒮) (w : St.obj A) :
      e (St.map (χ ≫ a) w) = e (St.map (χ ≫ prod.fst) w) + e (St.map (χ ≫ prod.snd) w) := by
    rw [Functor.map_comp_apply, ha, Functor.map_comp_apply, Functor.map_comp_apply]
  have hSm {A : Sheaf Y.smallEtaleTopology (Type (u + 1))} (χ : A ⟶ 𝒮) (c : Λ) (w : St.obj A) :
      e (St.map (χ ≫ m c) w) = c • e (St.map χ w) := by
    rw [Functor.map_comp_apply, hmc]
  have hZ {A : Sheaf Y.smallEtaleTopology (Type (u + 1))} (χ : A ⟶ ⊤_ _) (w : St.obj A) :
      e (St.map (χ ≫ z) w) = 0 := by
    rw [Functor.map_comp_apply, hz]
  have ext3 {A : Y.FiniteLocallyConstant} (φ ψ : A.obj ⟶ 𝒮)
      (h : ∀ w, e (St.map φ w) = e (St.map ψ w)) : φ = ψ :=
    congrArg (·.hom) (Scheme.FiniteLocallyConstant.hom_ext_of_sheafFiber s
      (φ := (ObjectProperty.homMk φ : A ⟶ S)) (ψ := ObjectProperty.homMk ψ)
      fun w ↦ e.injective (h w))
  -- the module laws, as identities of morphisms of sheaves
  have L_assoc : (prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ a)
      (prod.snd ≫ prod.snd) ≫ a : 𝒮 ⨯ (𝒮 ⨯ 𝒮) ⟶ 𝒮) = prod.lift prod.fst (prod.snd ≫ a) ≫ a :=
    ext3 (A := S3) _ _ fun w ↦ by
      simp only [hA, prod.lift_fst, prod.lift_snd, add_assoc]
  have L_zero_add : prod.lift (terminal.from 𝒮 ≫ z) (𝟙 𝒮) ≫ a = 𝟙 𝒮 :=
    ext3 (A := S) _ _ fun w ↦ by
      simp only [hA, hZ, prod.lift_fst, prod.lift_snd, zero_add]
  have L_add_comm : prod.lift prod.snd prod.fst ≫ a = a :=
    ext3 (A := S2) _ _ fun w ↦ by
      rw [hA, ha, prod.lift_fst, prod.lift_snd, add_comm]
  have L_neg : prod.lift (m (-1)) (𝟙 𝒮) ≫ a = terminal.from 𝒮 ≫ z :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [hA, hZ, prod.lift_fst, prod.lift_snd, ← Category.id_comp (m (-1)), hSm,
        neg_one_smul, neg_add_cancel]
  have L_one : m 1 = 𝟙 𝒮 :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [← Category.id_comp (m 1), hSm, one_smul]
  have L_mul (c d : Λ) : m (c * d) = m d ≫ m c :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [← Category.id_comp (m (c * d)), hSm, hSm, ← Category.id_comp (m d), hSm, mul_smul]
  have L_smul_add (c : Λ) : a ≫ m c = prod.lift (prod.fst ≫ m c) (prod.snd ≫ m c) ≫ a :=
    ext3 (A := S2) _ _ fun w ↦ by
      rw [hSm, ha, hA, prod.lift_fst, prod.lift_snd, hSm, hSm, smul_add]
  have L_add_smul (c d : Λ) : m (c + d) = prod.lift (m c) (m d) ≫ a :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [hA, prod.lift_fst, prod.lift_snd, ← Category.id_comp (m (c + d)), hSm,
        ← Category.id_comp (m c), hSm, ← Category.id_comp (m d), hSm, add_smul]
  have L_smul_zero (c : Λ) : z ≫ m c = z :=
    ext3 (A := S0) _ _ fun w ↦ by
      rw [hSm, ← Category.id_comp z, hZ, smul_zero]
  have L_zero_smul : m 0 = terminal.from 𝒮 ≫ z :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [hZ, ← Category.id_comp (m 0), hSm, zero_smul]
  -- the module structure on the sections of `𝒮`
  let Hv (V : (Y.Etale)ᵒᵖ) : Sheaf Y.smallEtaleTopology (Type (u + 1)) ⥤ Type (u + 1) :=
    sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj V
  let unitV (V : (Y.Etale)ᵒᵖ) : (Hv V).obj (⊤_ _) :=
    (PreservesTerminal.iso (Hv V) ≪≫ Types.terminalIso).inv PUnit.unit
  have hunit (V : (Y.Etale)ᵒᵖ) (t : (Hv V).obj (⊤_ _)) : t = unitV V :=
    @Subsingleton.elim _ ((Hv V).subsingleton_obj_terminal) _ _
  let addV (V : (Y.Etale)ᵒᵖ) (x y : (Hv V).obj 𝒮) : (Hv V).obj 𝒮 :=
    (Hv V).map a (((Hv V).prodEquiv 𝒮 𝒮).symm (x, y))
  let zeroV (V : (Y.Etale)ᵒᵖ) : (Hv V).obj 𝒮 := (Hv V).map z (unitV V)
  let smulV (V : (Y.Etale)ᵒᵖ) (c : Λ) (x : (Hv V).obj 𝒮) : (Hv V).obj 𝒮 := (Hv V).map (m c) x
  have s_assoc (V) (x y w : (Hv V).obj 𝒮) :
      addV V (addV V x y) w = addV V x (addV V y w) := by
    have := congrArg (fun φ ↦ (Hv V).map φ
      (((Hv V).prodEquiv 𝒮 (𝒮 ⨯ 𝒮)).symm (x, ((Hv V).prodEquiv 𝒮 𝒮).symm (y, w)))) L_assoc
    simpa only [Functor.map_comp_apply, Functor.map_prod_lift, Functor.map_fst_prodEquiv_symm,
      Functor.map_snd_prodEquiv_symm] using this
  have s_zero_add (V) (x : (Hv V).obj 𝒮) : addV V (zeroV V) x = x := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) L_zero_add
    simp only [Functor.map_comp_apply, Functor.map_prod_lift, Functor.map_id_apply] at this
    rwa [hunit V ((Hv V).map (terminal.from 𝒮) x)] at this
  have s_add_comm (V) (x y : (Hv V).obj 𝒮) : addV V x y = addV V y x := by
    have := congrArg (fun φ ↦ (Hv V).map φ (((Hv V).prodEquiv 𝒮 𝒮).symm (y, x))) L_add_comm
    simpa only [Functor.map_comp_apply, Functor.map_prod_lift, Functor.map_fst_prodEquiv_symm,
      Functor.map_snd_prodEquiv_symm] using this
  have s_neg (V) (x : (Hv V).obj 𝒮) : addV V (smulV V (-1) x) x = zeroV V := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) L_neg
    simp only [Functor.map_comp_apply, Functor.map_prod_lift, Functor.map_id_apply] at this
    rwa [hunit V ((Hv V).map (terminal.from 𝒮) x)] at this
  have s_one (V) (x : (Hv V).obj 𝒮) : smulV V 1 x = x := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) L_one
    simpa only [Functor.map_id_apply] using this
  have s_mul (V) (c d : Λ) (x : (Hv V).obj 𝒮) : smulV V (c * d) x = smulV V c (smulV V d x) := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) (L_mul c d)
    simpa only [Functor.map_comp_apply] using this
  have s_smul_add (V) (c : Λ) (x y : (Hv V).obj 𝒮) :
      smulV V c (addV V x y) = addV V (smulV V c x) (smulV V c y) := by
    have := congrArg (fun φ ↦ (Hv V).map φ (((Hv V).prodEquiv 𝒮 𝒮).symm (x, y))) (L_smul_add c)
    simpa only [Functor.map_comp_apply, Functor.map_prod_lift, Functor.map_fst_prodEquiv_symm,
      Functor.map_snd_prodEquiv_symm] using this
  have s_add_smul (V) (c d : Λ) (x : (Hv V).obj 𝒮) :
      smulV V (c + d) x = addV V (smulV V c x) (smulV V d x) := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) (L_add_smul c d)
    simpa only [Functor.map_comp_apply, Functor.map_prod_lift] using this
  have s_smul_zero (V) (c : Λ) : smulV V c (zeroV V) = zeroV V := by
    have := congrArg (fun φ ↦ (Hv V).map φ (unitV V)) (L_smul_zero c)
    simpa only [Functor.map_comp_apply] using this
  have s_zero_smul (V) (x : (Hv V).obj 𝒮) : smulV V 0 x = zeroV V := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) L_zero_smul
    simp only [Functor.map_comp_apply] at this
    rwa [hunit V ((Hv V).map (terminal.from 𝒮) x)] at this
  let grp (V : (Y.Etale)ᵒᵖ) : AddCommGroup ((Hv V).obj 𝒮) :=
    letI : Add ((Hv V).obj 𝒮) := ⟨addV V⟩
    letI : Zero ((Hv V).obj 𝒮) := ⟨zeroV V⟩
    letI : Neg ((Hv V).obj 𝒮) := ⟨smulV V (-1)⟩
    { add_assoc := s_assoc V
      zero_add := s_zero_add V
      add_zero x := (s_add_comm V x (zeroV V)).trans (s_zero_add V x)
      add_comm := s_add_comm V
      neg_add_cancel := s_neg V
      nsmul := nsmulRec
      zsmul := zsmulRec }
  let modV (V : (Y.Etale)ᵒᵖ) : @Module Λ ((Hv V).obj 𝒮) _ (grp V).toAddCommMonoid :=
    letI := grp V
    { smul := smulV V
      one_smul := s_one V
      mul_smul := s_mul V
      smul_zero := s_smul_zero V
      smul_add := s_smul_add V
      add_smul := s_add_smul V
      zero_smul := s_zero_smul V }
  -- the presheaf of modules
  have nat_pair {V W : (Y.Etale)ᵒᵖ} (f : V ⟶ W) (x y : (Hv V).obj 𝒮) :
      (𝒮 ⨯ 𝒮).obj.map f (((Hv V).prodEquiv 𝒮 𝒮).symm (x, y)) =
        ((Hv W).prodEquiv 𝒮 𝒮).symm (𝒮.obj.map f x, 𝒮.obj.map f y) := by
    apply ((Hv W).prodEquiv 𝒮 𝒮).injective
    rw [Equiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · change (prod.fst : 𝒮 ⨯ 𝒮 ⟶ 𝒮).hom.app W ((𝒮 ⨯ 𝒮).obj.map f _) = _
      rw [NatTrans.naturality_apply]
      exact congrArg (𝒮.obj.map f) ((Hv V).map_fst_prodEquiv_symm x y)
    · change (prod.snd : 𝒮 ⨯ 𝒮 ⟶ 𝒮).hom.app W ((𝒮 ⨯ 𝒮).obj.map f _) = _
      rw [NatTrans.naturality_apply]
      exact congrArg (𝒮.obj.map f) ((Hv V).map_snd_prodEquiv_symm x y)
  have nat_add {V W : (Y.Etale)ᵒᵖ} (f : V ⟶ W) (x y : (Hv V).obj 𝒮) :
      𝒮.obj.map f (addV V x y) = addV W (𝒮.obj.map f x) (𝒮.obj.map f y) := by
    change 𝒮.obj.map f (a.hom.app V _) = a.hom.app W _
    rw [← NatTrans.naturality_apply a.hom f, nat_pair]
  have nat_smul {V W : (Y.Etale)ᵒᵖ} (f : V ⟶ W) (c : Λ) (x : (Hv V).obj 𝒮) :
      𝒮.obj.map f (smulV V c x) = smulV W c (𝒮.obj.map f x) :=
    (NatTrans.naturality_apply (m c).hom f x).symm
  let Fp : (Y.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
    { obj V := letI := grp V; letI := modV V; ModuleCat.of Λ ((Hv V).obj 𝒮)
      map {V W} f :=
        letI := grp V; letI := modV V; letI := grp W; letI := modV W
        ModuleCat.ofHom
          { toFun := 𝒮.obj.map f
            map_add' := nat_add f
            map_smul' := nat_smul f }
      map_id V := by
        ext x
        change 𝒮.obj.map (𝟙 V) x = x
        simp
      map_comp f g := by
        ext x
        exact 𝒮.obj.map_comp_apply f g x }
  have hFp : Presheaf.IsSheaf Y.smallEtaleTopology Fp :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ Fp (CategoryTheory.forget _)).mpr 𝒮.property
  let F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) := ⟨Fp, hFp⟩
  have hFt : IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F) := S.property
  have hF := IsFiniteLocallyConstantSheaf.of_forget F hFt
  refine ⟨F, hF, ⟨?_⟩⟩
  -- the stalk of `F` is `M`
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let stF := ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F
  let L0 : stF ≃ M.V := (hF.stalkEquiv s).trans e
  have hgerm (V : Y.Etale) (v : (Scheme.pointSmallEtale s).fiber.obj V)
      (x : (Hv (Opposite.op V)).obj 𝒮) :
      hF.stalkEquiv s ((Scheme.pointSmallEtale s).toPresheafFiber V v F.obj x) =
        (Scheme.pointSmallEtale s).toPresheafFiber V v 𝒮.obj x := by
    have h := ConcreteCategory.congr_hom
      ((Scheme.pointSmallEtale s).toPresheafFiber_presheafFiberCompIso_hom_app V v F.obj
        (F := CategoryTheory.forget (ModuleCat.{u + 1} Λ))) x
    have h2 := ((((Scheme.pointSmallEtale s).presheafFiberCompIso
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F.obj).toEquiv).symm_apply_apply
      ((Scheme.pointSmallEtale s).toPresheafFiber V v
        (F.obj ⋙ CategoryTheory.forget (ModuleCat.{u + 1} Λ)) x)
    simp only [Iso.toEquiv_fun, Iso.toEquiv_symm_fun, Iso.app_hom, Iso.app_inv] at h2
    rw [ConcreteCategory.comp_apply] at h
    erw [h] at h2
    exact h2
  have hgermS (V : Y.Etale) (v : (Scheme.pointSmallEtale s).fiber.obj V)
      {A : Sheaf Y.smallEtaleTopology (Type (u + 1))} (φ : A ⟶ 𝒮)
      (t : (Hv (Opposite.op V)).obj A) :
      (Scheme.pointSmallEtale s).toPresheafFiber V v 𝒮.obj (φ.hom.app _ t) =
        St.map φ ((Scheme.pointSmallEtale s).toPresheafFiber V v A.obj t) :=
    ((Scheme.pointSmallEtale s).toPresheafFiber_naturality_apply φ.hom V v t).symm
  have L0_add (p q : stF) : L0 (p + q) = L0 p + L0 q := by
    obtain ⟨V, v, x, y, rfl, rfl⟩ :=
      (Scheme.pointSmallEtale s).toPresheafFiber_jointly_surjective₂ (P := F.obj) p q
    rw [← ((Scheme.pointSmallEtale s).toPresheafFiber V v F.obj).hom.map_add x y]
    simp only [L0, Equiv.trans_apply]
    erw [hgerm, hgerm, hgerm]
    change e ((Scheme.pointSmallEtale s).toPresheafFiber V v 𝒮.obj
      (a.hom.app _ (((Hv (Opposite.op V)).prodEquiv 𝒮 𝒮).symm (x, y)))) = _
    rw [hgermS, ha, ← hgermS, ← hgermS]
    erw [(Hv (Opposite.op V)).map_fst_prodEquiv_symm, (Hv (Opposite.op V)).map_snd_prodEquiv_symm]
    rfl
  have L0_smul (c : Λ) (p : stF) : L0 (c • p) = c • L0 p := by
    obtain ⟨V, v, x, rfl⟩ :=
      (Scheme.pointSmallEtale s).toPresheafFiber_jointly_surjective (P := F.obj) p
    rw [← ((Scheme.pointSmallEtale s).toPresheafFiber V v F.obj).hom.map_smul c x]
    simp only [L0, Equiv.trans_apply]
    erw [hgerm, hgerm]
    change e ((Scheme.pointSmallEtale s).toPresheafFiber V v 𝒮.obj ((m c).hom.app _ x)) = _
    rw [hgermS, hmc]
    rfl
  have L0_equiv (g : G) (p : stF) : L0 (hF.galoisAct s G g p) = M.ρ g (L0 p) := by
    simp only [L0, Equiv.trans_apply, Scheme.IsFiniteLocallyConstantSheaf.galoisAct]
    erw [Equiv.apply_symm_apply]
    exact he g _
  let Llin : stF ≃ₗ[Λ] M.V :=
    { L0 with
      map_add' := L0_add
      map_smul' := L0_smul }
  exact Rep.mkIso (Representation.Equiv.mk Llin fun g ↦ LinearMap.ext fun p ↦ L0_equiv g p)

end Construction

end EssSurj

end EssSurjAux

section GaloisRepEquivalence

variable {Y : Scheme.{u}} [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Y) {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (G : ProfiniteGrp.{u})
  [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
  [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G]

/-- The geometric stalk at `s` with its action of the fundamental group `G`, as a functor from
finite locally constant sheaves of `Λ`-modules to finite continuous representations of `G`
(`AlgebraicGeometry.Scheme.galoisRepFunctor`, corestricted). -/
noncomputable def Scheme.galoisRepFunctorFiniteContinuous :
    ObjectProperty.FullSubcategory
        (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          Scheme.IsFiniteLocallyConstantSheaf F) ⥤
      ObjectProperty.FullSubcategory (Rep.IsFiniteContinuous (Λ := Λ) (G := G)) :=
  ObjectProperty.lift (Rep.IsFiniteContinuous (Λ := Λ) (G := G))
    (Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ))
    (fun F ↦ Scheme.galoisRepFunctor_obj_isFiniteContinuous s G F)

/-- `AlgebraicGeometry.Scheme.galoisRepFunctorFiniteContinuous` is an equivalence: it is fully
faithful, and every finite continuous representation is the stalk of a finite locally constant
sheaf (`AlgebraicGeometry.Scheme.exists_galoisRepFunctor_obj_iso`). -/
instance : (Scheme.galoisRepFunctorFiniteContinuous s (Λ := Λ) G).IsEquivalence := by
  let Φ := Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)
  let Φ' := Scheme.galoisRepFunctorFiniteContinuous s (Λ := Λ) G
  have hΦ' : Φ'.FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful Φ).ofCompFaithful (G := ObjectProperty.ι _)
  have : Φ'.Full := hΦ'.full
  have : Φ'.Faithful := hΦ'.faithful
  -- essential surjectivity: a finite continuous `Λ[G]`-module is the stalk of a finite locally
  -- constant sheaf of `Λ`-modules
  have : Φ'.EssSurj := ⟨fun M ↦ by
    obtain ⟨F, hF, ⟨i⟩⟩ := Scheme.exists_galoisRepFunctor_obj_iso s G M.obj M.property
    exact ⟨⟨F, hF⟩, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso i⟩⟩⟩
  exact { }

end GaloisRepEquivalence

/-- Blueprint `proposition-lattices-representations-normal-scheme`: Galois correspondence for finite
local systems. Also blueprint `proposition-lattices-representations-normal-scheme`: Lisse sheaves
and continuous representations.

The steps *sheaves and covers* and *linear structure* of the proof, for a named fundamental
group: let `Y` be a connected scheme, `s : Spec Ω ⟶ Y` a geometric point, `Λ` a finite ring
and `G` a fundamental group of the fibre functor `AlgebraicGeometry.Scheme.FiniteEtale.fiber s`
on finite étale `Y`-schemes, i.e. `G = π₁(Y, s)`. Then the geometric stalk at `s` is an
equivalence between finite locally constant sheaves of `Λ`-modules on `Y_ét` and finite
`Λ`-modules with a continuous `G`-action.

Mathematically, a finite locally constant sheaf of sets is represented by a finite étale
`Y`-scheme, whose geometric fibre is the stalk at `s`; the Galois correspondence
`AlgebraicGeometry.Scheme.FiniteEtale.equivalenceContAction` identifies these with finite
continuous `G`-sets, and a `Λ`-module structure on the sheaf is transported to one on the
`G`-set. -/
theorem Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup
    (Y : Scheme.{u}) [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
    [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G] :
    ∃ e : ObjectProperty.FullSubcategory
            (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
              Scheme.IsFiniteLocallyConstantSheaf F) ≌
          ObjectProperty.FullSubcategory (Rep.IsFiniteContinuous (Λ := Λ) (G := G)),
      Nonempty (e.functor ⋙ ObjectProperty.ι _ ⋙
          forget₂ (Rep.{u + 1} Λ G) (ModuleCat.{u + 1} Λ) ≅
        ObjectProperty.ι _ ⋙ (Scheme.pointSmallEtale s).sheafFiber) := by
  exact ⟨(Scheme.galoisRepFunctorFiniteContinuous s (Λ := Λ) G).asEquivalence,
    ⟨Scheme.galoisRepFunctorCompForget₂Iso s G⟩⟩

/-- Blueprint `proposition-lattices-representations-normal-scheme`: Galois correspondence for finite
local systems.

Let `Y` be a connected scheme, `s : Spec Ω ⟶ Y` a geometric point and `Λ` a finite ring.
Then there is a profinite group `G` — the étale fundamental group `π₁(Y, s)`, a fundamental
group of `AlgebraicGeometry.Scheme.FiniteEtale.fiber s`, here existentially quantified as a
`ProfiniteGrp` — together with an equivalence between the category of finite locally
constant sheaves of `Λ`-modules on `Y_ét` and the category of finite `Λ`-modules with a
continuous `G`-action, compatible with the geometric stalk at `s`: the triangle

```
    FLC(Y_ét)  ──e.functor──▶  Rep^{fin,cont}_Λ(G)
         │                            │
         │ sheafFiber s               │ forget₂
         ▼                            ▼
     ModuleCat Λ  ══════════════  ModuleCat Λ
```

commutes up to isomorphism.

Exactness is `AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_shortExact_iff`.
Compatibility with `⊗_Λ` is not automatic for an equivalence of abelian categories; it is
`AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_tensor`, which
strengthens this statement by a natural isomorphism `(F ⊗ F')_s ≅ F_s ⊗ F'_s` of
representations and the identification of the stalk of `Λ_Y` with the trivial representation.
The compatibility with base change along a
map `Λ → Λ'` of finite rings is not restated here, see the module implementation notes and
`AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup`
for the version with `π₁(Y, s)` named. -/
theorem Scheme.exists_equivalence_isFiniteLocallyConstantSheaf (Y : Scheme.{u})
    [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∃ (G : ProfiniteGrp.{u})
      (e : ObjectProperty.FullSubcategory
            (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
              Scheme.IsFiniteLocallyConstantSheaf F) ≌
          ObjectProperty.FullSubcategory (Rep.IsFiniteContinuous (Λ := Λ) (G := G))),
      Nonempty (e.functor ⋙ ObjectProperty.ι _ ⋙
          forget₂ (Rep.{u + 1} Λ G) (ModuleCat.{u + 1} Λ) ≅
        ObjectProperty.ι _ ⋙ (Scheme.pointSmallEtale s).sheafFiber) := by
  obtain ⟨G, _, _⟩ := Scheme.FiniteEtale.exists_isFundamentalGroup s
  exact ⟨G, exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup Y s Λ G⟩

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)}
  [IsCurve p] {pU : U ⟶ Spec (.of K)} [IsCurve pU]

namespace WeilGroup

/-- Blueprint `definition-weil-representation--1`: The lisse sheaf–representation
equivalence.

The property of an object of `Rep ℚ̄_ℓ W(C₀)` of being a *lisse Weil representation*: the
underlying `ℚ̄_ℓ`-vector space is finite dimensional and the geometric subgroup `π₁(C)`
acts continuously (`AlgebraicGeometry.WeilGroup.IsLisse`). Under the equivalence of
`definition-weil-representation--1` these are exactly the objects corresponding to lisse
Weil sheaves on `C₀`. -/
def isLisseRep (W : WeilGroup p) (l : ℕ) [Fact l.Prime] :
    ObjectProperty (Rep.{u} (PadicAlgCl l) W.carrier) :=
  fun X ↦ FiniteDimensional (PadicAlgCl l) X.V ∧ W.IsLisse l X.ρ

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime]

/-- Blueprint `definition-weil-representation--1`: The lisse sheaf–representation
equivalence.

A subrepresentation of a lisse Weil representation is again lisse: it is finite dimensional,
and every coefficient `g ↦ φ (ρ g v)` of it is a coefficient of the ambient representation,
for a linear form extending `φ`. -/
instance isLisseRep.isClosedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects (W.isLisseRep l) where
  prop_of_mono {X Y} f _ hY := by
    obtain ⟨_, hρ⟩ := hY
    have hf : Function.Injective f.hom := (Rep.mono_iff_injective f).1 inferInstance
    have : FiniteDimensional (PadicAlgCl l) X.V :=
      Module.Finite.of_injective f.hom.toLinearMap hf
    refine ⟨this, IsLisse.of_continuous_apply fun φ v ↦ ?_⟩
    obtain ⟨ψ, hψ⟩ :=
      f.hom.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
    have hψ' (x : X.V) : ψ (f.hom x) = x := LinearMap.congr_fun hψ x
    simpa [← Rep.hom_comm_apply, hψ'] using hρ.continuous_apply (φ ∘ₗ ψ) (f.hom v)

/-- Blueprint `definition-weil-representation--1`: The lisse sheaf–representation
equivalence.

A quotient of a lisse Weil representation is again lisse: it is finite dimensional, and every
coefficient `g ↦ φ (ρ g (f v))` of it is the coefficient `g ↦ (φ ∘ f) (ρ g v)` of the source. -/
instance isLisseRep.isClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients (W.isLisseRep l) where
  prop_of_epi {X Y} f _ hX := by
    obtain ⟨_, hρ⟩ := hX
    have hf : Function.Surjective f.hom := (Rep.epi_iff_surjective f).1 inferInstance
    have : FiniteDimensional (PadicAlgCl l) Y.V :=
      Module.Finite.of_surjective f.hom.toLinearMap hf
    refine ⟨this, IsLisse.of_continuous_apply fun φ w ↦ ?_⟩
    obtain ⟨v, rfl⟩ := hf w
    simpa [Rep.hom_comm_apply] using hρ.continuous_apply (φ ∘ₗ f.hom.toLinearMap) v

/-- Blueprint `definition-weil-representation--1`: The lisse sheaf–representation
equivalence.

Lisse Weil representations are closed under kernels, so a subobject of a lisse Weil
representation is again lisse. -/
instance isLisseRep.isClosedUnderKernels :
    ObjectProperty.IsClosedUnderKernels (W.isLisseRep l) :=
  inferInstance

/-- Blueprint `definition-weil-representation--1`: The lisse sheaf–representation
equivalence.

Lisse Weil representations are closed under cokernels, so a quotient of a lisse Weil
representation is again lisse. -/
instance isLisseRep.isClosedUnderCokernels :
    ObjectProperty.IsClosedUnderCokernels (W.isLisseRep l) :=
  inferInstance

/-- Blueprint `definition-weil-representation--1`, node
`definition-weil-representation--1`: The lisse sheaf–representation equivalence.

A short complex of lisse Weil representations is short exact exactly when its geometric
generic stalk, i.e. its image under the forgetful functor to `ModuleCat ℚ̄_ℓ`, is short exact.
This is the form in which the exactness of the geometric-generic-stalk equivalence of
`definition-weil-representation--1` is used, lisse `ℚ̄_ℓ`-sheaves themselves being
unavailable.

The forgetful functor is faithful and exact, since kernels and cokernels of representations
are computed on the underlying vector spaces, so it preserves and reflects short exactness;
the lisse hypotheses are not needed. The exactness of the equivalence with lisse Weil sheaves
itself is `AlgebraicGeometry.WeilGroup.isLisse_shortExact_iff`. -/
theorem isLisseRep_shortExact_iff (S : ShortComplex (Rep.{u} (PadicAlgCl l) W.carrier))
    (_h₁ : W.isLisseRep l S.X₁) (_h₂ : W.isLisseRep l S.X₂) (_h₃ : W.isLisseRep l S.X₃) :
    S.ShortExact ↔ (S.map (forget₂ (Rep.{u} (PadicAlgCl l) W.carrier)
      (ModuleCat.{u} (PadicAlgCl l)))).ShortExact :=
  (ShortExact.shortExact_map_iff _).symm

variable {W l}

/-- Blueprint `proposition-lattices-representations-normal-scheme`: Integral models.

Let `ρ` be a lisse Weil representation on `V` over `ℚ̄_ℓ` and let `R` be a restriction of Weil
groups along a nonempty open subscheme `j : U₀ ⊆ C₀`. Then, after replacing the coefficient
field by a finite extension `E/ℚ_ℓ` — here a finite-dimensional intermediate field of
`ℚ_ℓ ⊆ ℚ̄_ℓ` — there is an `𝒪_E`-lattice `L ⊂ V`, that is a free `𝒪_E`-submodule of rank
`dim V` whose `ℚ̄_ℓ`-span is all of `V`, which is stable under `ρ (π₁(U))` and whose
reduction modulo `𝔪_E ^ n` has finite `π₁(U)`-image for every `n`.

The finiteness of the image in `Aut (L / 𝔪_E ^ n L)` is expressed as the finiteness of the
set of maps `L → V / 𝔪_E ^ n L` induced by the elements of `π₁(U)`; since `L` is stable and
`L / 𝔪_E ^ n L → V / 𝔪_E ^ n L` is injective, this is the same condition, and it avoids
having to restrict `ρ g` to `L` before the lattice is known to be stable. -/
theorem IsLisse.exists_lattice {l : ℕ} [Fact l.Prime] {W : WeilGroup p} {V : Type u}
    [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
    {ρ : Representation (PadicAlgCl l) W.carrier V} (hρ : W.IsLisse l ρ) {j : U ⟶ C}
    [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU} (R : Restriction j WU W) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      letI : Module (PadicAlgCl.integers l (E : Type)) V :=
        Module.compHom V ((algebraMap (E : Type) (PadicAlgCl l)).comp
          (PadicAlgCl.integers l (E : Type)).subtype)
      ∃ L : Submodule (PadicAlgCl.integers l (E : Type)) V,
        Module.Free (PadicAlgCl.integers l (E : Type)) L ∧
        Module.finrank (PadicAlgCl.integers l (E : Type)) L =
          Module.finrank (PadicAlgCl l) V ∧
        Submodule.span (PadicAlgCl l) (L : Set V) = ⊤ ∧
        (∀ g : WU.geometric, ∀ x ∈ L, ρ (R.restrict g) x ∈ L) ∧
        ∀ n : ℕ, (Set.range fun g : WU.geometric ↦ fun x : L ↦
          Submodule.Quotient.mk (p := (IsLocalRing.maximalIdeal
            (PadicAlgCl.integers l (E : Type)) ^ n) • L) (ρ (R.restrict g) x)).Finite := by
  classical
  let b := Module.finBasis (PadicAlgCl l) V
  -- the action `π₁(U) → GL(V)` of the geometric fundamental group of `U` through `R`
  let σ : Representation (PadicAlgCl l) WU.geometric V :=
    { toFun g := ρ (R.restrict g)
      map_one' := by simp
      map_mul' g h := by simp }
  have hmem (g : WU.geometric) : R.restrict g ∈ W.geometric := by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, R.deg_restrict]
    exact g.2
  let ψ : WU.geometric → W.geometric := fun g ↦ ⟨R.restrict g, hmem g⟩
  have hψ : Continuous ψ := (R.continuous_restrict.comp continuous_subtype_val).subtype_mk hmem
  have hcont (i j : Fin (Module.finrank (PadicAlgCl l) V)) :
      Continuous fun g ↦ LinearMap.toMatrix b b (σ g) i j := by
    have h := (hρ.continuous_toMatrix b i j).comp hψ
    have hσ (g : WU.geometric) : σ g = ρ (R.restrict g) := rfl
    simpa only [hσ, Function.comp_def] using h
  -- the coefficients lie in a finite extension `E` of `ℚ_ℓ` and are bounded
  obtain ⟨E, hE, hσE⟩ := PadicAlgCl.exists_finiteDimensional_forall_mem l
    ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp σ) fun i j ↦ by
      simpa [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply] using hcont i j
  have hσE' (g : WU.geometric) (i j) : LinearMap.toMatrix b b (σ g) i j ∈ E := by
    simpa [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply] using hσE g i j
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ p : Fin _ × Fin _, ∀ g : WU.geometric,
      ‖LinearMap.toMatrix b b (σ g) p.1 p.2‖ ≤ C := by
    choose C hC using fun p : Fin _ × Fin _ ↦
      (isCompact_range (hcont p.1 p.2)).isBounded.exists_norm_le
    obtain ⟨M, hM⟩ := Finite.exists_le C
    exact ⟨M, fun p g ↦ (hC p _ ⟨g, rfl⟩).trans (hM p)⟩
  exact ⟨E, hE, PadicAlgCl.exists_lattice_of_forall_mem l b σ E hσE' C
    fun g i j ↦ hC (i, j) g⟩

/-- Blueprint `lemma-degree-zero-top-cohomology--1`: Global sections as invariants.

The global sections `H⁰(U, F|_U)` of the lisse sheaf `F` with geometric generic stalk
`(V, ρ)`, rendered as in the proof sketch: a global section is a morphism from the constant
rank-one sheaf, i.e. a `π₁(U)`-equivariant `ℚ̄_ℓ`-linear map `ℚ̄_ℓ → V`, where `π₁(U)` acts
on `V` through the restriction `R : W(U₀) → W(C₀)` of Weil groups along the open `U₀ ⊆ C₀`. -/
noncomputable def globalSections (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u}
    [AddCommGroup V] [Module (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V)
    {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU}
    (R : Restriction j WU W) :
    Submodule (PadicAlgCl l) (PadicAlgCl l →ₗ[PadicAlgCl l] V) :=
  (Representation.linHom (Representation.trivial (PadicAlgCl l) WU.geometric (PadicAlgCl l))
    ((ρ.comp R.restrict).comp WU.geometric.subtype)).invariants

section Sections

variable {l : ℕ} [Fact l.Prime] {W : WeilGroup p} {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V) {j : U ⟶ C}
  [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU} (R : Restriction j WU W)

/-- Blueprint `lemma-degree-zero-top-cohomology--1`: Global sections as invariants.

The geometric Frobenius `F = ρ (res γ)` preserves the invariants `V ^ (π₁(U))`, because
`π₁(U)` is normal in `W(U₀)`. -/
theorem frobeniusLift_mem_invariants (v : V)
    (hv : v ∈ Representation.invariants ((ρ.comp R.restrict).comp WU.geometric.subtype)) :
    ρ (R.restrict WU.frobeniusLift) v ∈
      Representation.invariants ((ρ.comp R.restrict).comp WU.geometric.subtype) := by
  intro g
  have hg : WU.frobeniusLift⁻¹ * g * WU.frobeniusLift ∈ WU.geometric := by
    have : WU.deg g = 1 := g.2
    simp [MonoidHom.mem_ker, this]
  have := hv ⟨_, hg⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, map_mul,
    Module.End.mul_apply] at this ⊢
  conv_rhs => rw [← this]
  simp [← Module.End.mul_apply, ← map_mul]

/-- Blueprint `lemma-degree-zero-top-cohomology--1`: Global sections as invariants.

The geometric Frobenius `F = ρ (res γ)` acts on global sections by post-composition: `π₁(U)`
is normal in `W(U₀)`, so post-composing an equivariant map with `F` gives an equivariant
map. -/
theorem comp_mem_globalSections (f : PadicAlgCl l →ₗ[PadicAlgCl l] V)
    (hf : f ∈ W.globalSections l ρ R) :
    (ρ (R.restrict WU.frobeniusLift)).comp f ∈ W.globalSections l ρ R := by
  refine fun g ↦ LinearMap.ext fun a ↦ ?_
  simp only [Representation.linHom_apply, Representation.trivial_apply, MonoidHom.coe_comp,
    Function.comp_apply, Subgroup.coe_subtype, LinearMap.comp_apply]
  exact frobeniusLift_mem_invariants ρ R (f a)
    (fun g ↦ by simpa using LinearMap.congr_fun (hf g) a) g

/-- Blueprint `lemma-degree-zero-top-cohomology--1`, node `lemma-degree-zero-top-cohomology--1`:
Global sections as invariants.

For a lisse Weil representation `(V, ρ)` and a restriction `R` of Weil groups along a nonempty
open `U₀ ⊆ C₀`, the global sections `H⁰(U, F|_U) = Hom_{π₁(U)}(𝟙, V)` are the invariants
`V ^ (π₁(U))`, by evaluation at `1`: an equivariant map `ℚ̄_ℓ → V` is determined by the
image of `1`, which is fixed by `π₁(U)`, and every fixed vector arises this way. The finiteness
and lisse hypotheses are not needed for this. The corresponding statement for the étale global
sections of a lisse Weil sheaf is
`AlgebraicGeometry.WeilGroup.exists_globalSections_upperStar_linearEquiv_invariants`.

Both sides carry a residual action of the geometric Frobenius `F = ρ (res γ)`
(`AlgebraicGeometry.WeilGroup.comp_mem_globalSections` and
`AlgebraicGeometry.WeilGroup.frobeniusLift_mem_invariants`), and the identification is
equivariant for it:

```
    H⁰(U, F|_U) ──── e ────▶ V^{π₁(U)}
          │                      │
    F ∘ ─ │                      │ F
          ▼                      ▼
    H⁰(U, F|_U) ──── e ────▶ V^{π₁(U)}
```
-/
theorem globalSections_eq_invariants [FiniteDimensional (PadicAlgCl l) V]
    (_hρ : W.IsLisse l ρ) :
    ∃ e : W.globalSections l ρ R ≃ₗ[PadicAlgCl l]
      Representation.invariants ((ρ.comp R.restrict).comp WU.geometric.subtype),
      ∀ f : W.globalSections l ρ R,
        e ⟨(ρ (R.restrict WU.frobeniusLift)).comp (f : PadicAlgCl l →ₗ[PadicAlgCl l] V),
            comp_mem_globalSections ρ R f f.2⟩ =
          ⟨ρ (R.restrict WU.frobeniusLift) (e f),
            frobeniusLift_mem_invariants ρ R (e f) (e f).2⟩ := by
  refine ⟨(LinearMap.ringLmapEquivSelf (PadicAlgCl l) (PadicAlgCl l) V).ofSubmodules _ _ ?_,
    fun f ↦ rfl⟩
  ext v
  simp only [Submodule.mem_map_equiv, LinearMap.ringLmapEquivSelf_symm_apply]
  refine ⟨fun h g ↦ ?_, fun h g ↦ LinearMap.ext fun a ↦ ?_⟩
  · simpa using LinearMap.congr_fun (h g) 1
  · simpa using congrArg (a • ·) (h g)

end Sections

end WeilGroup

end AlgebraicGeometry
