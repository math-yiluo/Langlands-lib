/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.Sites.Torsor

import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
import WeilConjectures.CategoryTheory.ConcreteCategory.FinitelyGenerated
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable

/-! # Hom sets between finite constant torsor sheaves

Source: Stacks Project Tags 0A5G and 03RV.
(blueprint: lem-weil-pbc-finite-torsor-pullback-hom-bijective)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- Translation by a section trivializes a torsor under any constant group sheaf.
This generalizes the constant-coefficient theorem in EtaleTorsorDescent to an arbitrary
group sheaf equipped with IsConstant; no chosen coefficient type is required. -/
private theorem torsor_isConstant_over_of_section
    {Y : Scheme.{u}} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    [G.IsConstant Y.smallEtaleTopology] (P : Sheaf.Torsor G) (U : Y.Etale)
    (x : P.sheaf.obj.obj (op U)) :
    (P.sheaf.over U).IsConstant (Y.smallEtaleTopology.over U) := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  let G' := (sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G
  have : G'.IsConstant Y.smallEtaleTopology := inferInstance
  have hG' := Sheaf.isConstant_over (W := U) G'
  let e : (G'.over U).obj ≅ (P.sheaf.over U).obj :=
    NatIso.ofComponents (fun W ↦ Equiv.toIso (Equiv.ofBijective
      (fun a : G.obj.obj (op W.unop.left) ↦
        P.vadd (op W.unop.left) a (P.sheaf.obj.map W.unop.hom.op x))
      (P.bijective_vadd _ _))) (fun {W W'} h ↦ by
        ext a
        change P.vadd _ (G.obj.map h.unop.left.op a) (P.sheaf.obj.map W'.unop.hom.op x) =
          P.sheaf.obj.map h.unop.left.op (P.vadd _ a (P.sheaf.obj.map W.unop.hom.op x))
        rw [P.map_vadd, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
          Over.w h.unop])
  exact Sheaf.isConstant_congr _
    ((fullyFaithfulSheafToPresheaf _ _).preimageIso (X := G'.over U) (Y := P.sheaf.over U) e)

section

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}}
variable [TopologicalSpace M] [DiscreteTopology M]

/-- Finiteness of torsor stalks, by constant translates of a fixed local section. -/
private theorem finite_sheafFiber (R : Sheaf.Torsor (Scheme.Etale.continuousMapSheaf Y M))
    {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    Finite (ToType ((pointSmallEtale s).sheafFiber.obj R.sheaf)) := by
  let Φ := pointSmallEtale s
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 Y)) :=
    MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y
  let t₀ : Φ.fiber.obj (Scheme.Etale.mk (𝟙 Y)) := (Φ.uniqueFiberObj _ hT).default
  obtain ⟨V₀, g₀, ⟨x₀⟩, v₀, -⟩ :=
    Φ.jointly_surjective _ (R.nonemptySieve_mem (Scheme.Etale.mk (𝟙 Y))) t₀
  let φ : M → ToType (Φ.sheafFiber.obj R.sheaf) := fun m ↦
    Φ.toPresheafFiber V₀ v₀ R.sheaf.obj (R.vadd (op V₀) (ContinuousMap.const _ m) x₀)
  refine Finite.of_surjective φ fun p ↦ ?_
  obtain ⟨V, v, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := R.sheaf.obj) p
  let E₁ : Φ.fiber.Elements := Φ.fiber.elementsMk V v
  let E₂ : Φ.fiber.Elements := Φ.fiber.elementsMk V₀ v₀
  let Wel := IsCofiltered.min E₁ E₂
  let f₁ := IsCofiltered.minToLeft E₁ E₂
  let f₂ := IsCofiltered.minToRight E₁ E₂
  let W : Y.Etale := Wel.1
  let w : Φ.fiber.obj W := Wel.2
  obtain ⟨a₀, ha⟩ := (R.bijective_vadd (op W) (R.sheaf.obj.map f₂.1.op x₀)).2
    (R.sheaf.obj.map f₁.1.op z)
  let a : C(W.left, M) := a₀
  let m : M := a (w.left (IsLocalRing.closedPoint Ω))
  let U := W.left.fiberOpens a m
  have hU : Set.range w.left ⊆ (U : Set W.left) := by
    rintro _ ⟨ξ, rfl⟩
    change a (w.left ξ) = m
    rw [Subsingleton.elim (α := PrimeSpectrum Ω) ξ (IsLocalRing.closedPoint Ω)]
  obtain ⟨w', hw'⟩ := exists_pointSmallEtale_fiber_ofOpens s w U hU
  let ιU := Scheme.Etale.ofOpensι W U
  have hmap (F : Y.Etaleᵒᵖ ⥤ Type (u + 1)) {A B : Y.Etale} (f : B ⟶ W) (g : W ⟶ A)
      (y : F.obj (op A)) : F.map (f ≫ g).op y = F.map f.op (F.map g.op y) := by
    rw [op_comp, F.map_comp]
    rfl
  have hz : R.sheaf.obj.map (ιU ≫ f₁.1).op z =
      R.sheaf.obj.map (ιU ≫ f₂.1).op (R.vadd (op V₀) (ContinuousMap.const _ m) x₀) := by
    rw [hmap, hmap, ← ha, R.map_vadd, R.map_vadd, R.map_vadd]
    congr 1
    exact ContinuousMap.ext fun ξ ↦ ξ.2
  have h₁ : Φ.fiber.map (ιU ≫ f₁.1) w' = v := by
    rw [Functor.map_comp_apply, hw']
    exact f₁.2
  have h₂ : Φ.fiber.map (ιU ≫ f₂.1) w' = v₀ := by
    rw [Functor.map_comp_apply, hw']
    exact f₂.2
  have e₁ := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w (ιU ≫ f₁.1) w' R.sheaf.obj) z
  have e₂ := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w (ιU ≫ f₂.1) w' R.sheaf.obj)
    (R.vadd (op V₀) (ContinuousMap.const _ m) x₀)
  rw [ConcreteCategory.comp_apply, h₁] at e₁
  rw [ConcreteCategory.comp_apply, h₂] at e₂
  refine ⟨m, ?_⟩
  change Φ.toPresheafFiber V₀ v₀ R.sheaf.obj _ = Φ.toPresheafFiber V v R.sheaf.obj z
  rw [← e₁, ← e₂, hz]

omit [TopologicalSpace M] [DiscreteTopology M] in
end

/-- Finite étale full faithfulness gives bijections on maps of underlying torsor sheaves.
Source: Stacks Project Tag 0A5G, final paragraph, and Tag 03RV.
(blueprint: lem-weil-pbc-finite-torsor-pullback-hom-bijective)

Proof: Each torsor under finite constant M is finite locally constant:
over an étale object with a section, translation identifies it with M;
such objects cover the base by local nonemptiness of the torsor.
At a geometric point, every germ is a constant translate of a fixed local section,
so a surjection from M makes the stalk finite. Tag 03RV represents
both underlying sheaves by finite étale schemes P and Q. Yoneda identifies
their Hom set with Hom_Y(P,Q). The natural representable inverse-image
isomorphism identifies the pulled-back Hom set with
Hom_Y₀(P ×_Y Y₀,Q ×_Y Y₀), and identifies pullback on sheaf morphisms
with the finite étale base-change map. The equivalence hypothesis makes
the latter bijective. Conjugating by the representing isomorphisms gives
the stated bijection. This argument also covers empty schemes and the
trivial group, and uses no surjectivity assumption on i. -/
theorem finite_torsor_pullback_hom_bijective
    [(@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange]
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (hFE : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (T₁ T₂ : Sheaf.Torsor
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))) :
    Function.Bijective
      (fun f : T₁.sheaf ⟶ T₂.sheaf ↦ (Scheme.etaleSetPullback i).map f) := by
  let L := Scheme.etaleSetPullback i
  let F := MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i
  let I := MorphismProperty.Over.changeProp (Q := ⊤) (Q' := ⊤) Y
    (inf_le_right : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ @Etale) le_rfl
  let I₀ := MorphismProperty.Over.changeProp (Q := ⊤) (Q' := ⊤) Y₀
    (inf_le_right : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ @Etale) le_rfl
  let R := I ⋙ Y.smallEtaleTopology.uliftYoneda.{u + 1}
  let R₀ := I₀ ⋙ Y₀.smallEtaleTopology.uliftYoneda.{u + 1}
  have : F.IsEquivalence := hFE
  obtain ⟨e⟩ := nonempty_inverseImage_representable_iso.{u, u + 1} i L
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
      (Y.smallGrothendieckTopology @Etale) (Y₀.smallGrothendieckTopology @Etale))
  let c : R ⋙ L ≅ F ⋙ R₀ := Functor.isoWhiskerLeft I e
  have : (R ⋙ L).Full := Functor.Full.of_iso c.symm
  have : (R ⋙ L).Faithful := Functor.Faithful.of_iso c.symm
  have hb (P Q : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y) :
      Function.Bijective (fun f : R.obj P ⟶ R.obj Q ↦ L.map f) := by
    constructor
    · intro f g h
      have hh : (R ⋙ L).map (R.preimage f) = (R ⋙ L).map (R.preimage g) := by
        simpa using h
      have := (R ⋙ L).map_injective hh
      simpa using congr_arg R.map this
    · intro k
      exact ⟨R.map ((R ⋙ L).preimage k), (R ⋙ L).map_preimage k⟩
  have hlocal (T : Sheaf.Torsor
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M))) :
      (∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Y, ∀ j,
        (T.sheaf.over (𝒰.etalePrecoverageToEtale j)).IsConstant
          (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale j))) ∧
        Scheme.IsFiniteSheaf T.sheaf := by
    refine ⟨?_, ?_⟩
    · choose V g hg hy using
        (mem_smallEtaleTopology_iff _).1 (T.nonemptySieve_mem (Scheme.Etale.mk (𝟙 Y)))
      let 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Y :=
        Scheme.Cover.mkOfCovers Y (fun y ↦ (V y).left) (fun y ↦ (V y).hom) (fun y ↦ by
          obtain ⟨z, hz⟩ := hy y
          refine ⟨y, z, ?_⟩
          have h₂ : (g y).left ≫ 𝟙 Y = (V y).hom := MorphismProperty.Over.w (g y)
          calc (V y).hom z = ((g y).left ≫ 𝟙 Y) z := by rw [h₂]; rfl
            _ = (g y).left z := by erw [Category.comp_id]; rfl
            _ = y := hz) (fun y ↦ (V y).prop)
      have : ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)).IsConstant Y.smallEtaleTopology :=
        Sheaf.isConstant_of_iso _ (Iso.refl _)
      exact ⟨𝒰, fun y ↦ torsor_isConstant_over_of_section _ T (V y) (hg y).some⟩
    · let _ : TopologicalSpace M := ⊥
      have : DiscreteTopology M := ⟨rfl⟩
      refine ⟨fun Ω _ _ s ↦ (ConcreteCategory.isFinitelyGenerated_iff_finite _).2 ?_⟩
      exact finite_sheafFiber
        (Sheaf.Torsor.ofIso (Scheme.Etale.constantSheafIsoContinuousMapSheaf Y M) T) s
  obtain ⟨P₁, π₁, hfin₁, het₁, ⟨d₁⟩⟩ :=
    Scheme.finiteLocallyConstant_sets_representable Y T₁.sheaf
      (hlocal T₁).1 (hlocal T₁).2
  obtain ⟨P₂, π₂, hfin₂, het₂, ⟨d₂⟩⟩ :=
    Scheme.finiteLocallyConstant_sets_representable Y T₂.sheaf
      (hlocal T₂).1 (hlocal T₂).2
  let P : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
    MorphismProperty.Over.mk ⊤ π₁ ⟨hfin₁, het₁⟩
  let Q : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
    MorphismProperty.Over.mk ⊤ π₂ ⟨hfin₂, het₂⟩
  let d₁' : R.obj P ≅ T₁.sheaf :=
    ((fullyFaithfulSheafToPresheaf _ _).preimageIso
      (X := T₁.sheaf) (Y := R.obj P) d₁).symm
  let d₂' : R.obj Q ≅ T₂.sheaf :=
    ((fullyFaithfulSheafToPresheaf _ _).preimageIso
      (X := T₂.sheaf) (Y := R.obj Q) d₂).symm
  constructor
  · intro f g h
    have hh : L.map (d₁'.hom ≫ f ≫ d₂'.inv) =
        L.map (d₁'.hom ≫ g ≫ d₂'.inv) := by
      simpa only [L.map_comp] using congr_arg
        (fun k ↦ L.map d₁'.hom ≫ k ≫ L.map d₂'.inv) h
    have hh' := (hb P Q).1 hh
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using congr_arg (fun k ↦ d₁'.inv ≫ k ≫ d₂'.hom) hh'
  · intro k
    obtain ⟨f, hf⟩ := (hb P Q).2 (L.map d₁'.hom ≫ k ≫ L.map d₂'.inv)
    change L.map f = _ at hf
    refine ⟨d₁'.inv ≫ f ≫ d₂'.hom, ?_⟩
    change L.map (d₁'.inv ≫ f ≫ d₂'.hom) = k
    rw [L.map_comp, L.map_comp]
    rw [hf]
    change (L.mapIso d₁').inv ≫ (L.mapIso d₁').hom ≫ k ≫
      (L.mapIso d₂').inv ≫ (L.mapIso d₂').hom = k
    simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Etale
