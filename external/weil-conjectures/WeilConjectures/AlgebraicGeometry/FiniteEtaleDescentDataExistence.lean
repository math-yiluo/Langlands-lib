/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentData
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale

/-!
# Canonical finite etale descent functor

Source: Stacks Project, Descent, Definition Tag 023V; Step 2 of
`lem-galois-descent` (blueprint: lem-galois-descent-data-existence).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The pullback, transport, and morphism equations characterizing the canonical
base-change functor. Source: Stacks Project, Descent, Tag 023V
(blueprint: lem-galois-descent-data-existence). -/
def FiniteEtaleDescentCompatible {Y Y' : Scheme.{v}} {g : Y' ⟶ Y}
    (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
    (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left) : Prop :=
  (∀ P : Y.FiniteEtale,
    ∃ _hq : q P ≫ P.obj.hom = (F.obj P).obj.V.hom ≫ g,
      IsPullback (q P) (F.obj P).obj.V.hom P.obj.hom g ∧
      ∀ {T : Scheme.{v}} (f₁ f₂ : T ⟶ Y')
        (h : f₁ ≫ g = f₂ ≫ g) (z : Over.mk f₁ ⟶ (F.obj P).obj.V),
        ((F.obj P).obj.datum.transport f₁ f₂ h z).left ≫ q P = z.left ≫ q P) ∧
  ∀ P Q : Y.FiniteEtale, ∀ f : P ⟶ Q,
    (F.map f).hom.hom.left ≫ q Q = q P ≫ f.hom.left

private noncomputable def pullbackDatum {Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
    (P : Over Y) : Over.DescentDatum g (Over.mk (pullback.snd P.hom g)) where
  transport f₁ f₂ h z :=
    Over.homMk (pullback.lift (z.left ≫ pullback.fst P.hom g) f₂ (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact (congrArg (fun k ↦ k ≫ g) (Over.w z)).trans h))
      (by simp)
  transport_homMk_comp := by
    intros
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [Category.assoc]
  transport_self := by
    intro T f a
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp
    · simpa using (Over.w a).symm
  transport_transport := by
    intros
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp

private noncomputable def pullbackDataObj {Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
    (P : Y.FiniteEtale) : AlgebraicGeometry.FiniteEtaleDescentData g := by
  have : IsFinite P.obj.hom := P.property
  have : Etale P.obj.hom := P.obj.prop
  exact ⟨⟨Over.mk (pullback.snd P.obj.hom g), pullbackDatum g (Over.mk P.obj.hom)⟩,
    (show IsFinite (pullback.snd P.obj.hom g) by infer_instance),
    (show Etale (pullback.snd P.obj.hom g) by infer_instance)⟩

private noncomputable def pullbackDataMap {Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
    {P Q : Y.FiniteEtale} (f : P ⟶ Q) : pullbackDataObj g P ⟶ pullbackDataObj g Q :=
  ObjectProperty.homMk
    { hom := Over.homMk
        (pullback.lift (pullback.fst P.obj.hom g ≫ f.hom.left)
          (pullback.snd P.obj.hom g) (by
            rw [Category.assoc, Scheme.FiniteEtale.hom_left_comp, pullback.condition]))
        (by simp [pullbackDataObj])
      commutes := by
        intros
        apply Over.OverMorphism.ext
        apply pullback.hom_ext <;> simp [pullbackDataObj, pullbackDatum, Category.assoc] }

/-- The canonical finite etale base-change functor exists, without any covering
hypothesis. Source: Stacks Project, Descent, Tag 023V, canonical datum; Step 2
of `lem-galois-descent` (blueprint: lem-galois-descent-data-existence).

Proof: use the pullback of each finite etale scheme, which is finite etale by
base-change stability. Transport keeps the first projection and replaces the
second projection by the new point of the base. The pullback universal property
proves naturality, identity, and the cocycle. Map a morphism by its pullback;
the same universal property proves compatibility and the functor laws. The
first projections satisfy all the required equations. -/
theorem finiteEtaleDescent_data {Y Y' : Scheme.{v}} (g : Y' ⟶ Y) :
    ∃ (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
      (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left),
      FiniteEtaleDescentCompatible F q := by
  let F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g :=
    { obj := pullbackDataObj g
      map := pullbackDataMap g
      map_id := by
        intro P
        apply ObjectProperty.hom_ext
        apply Over.DescentDataCategory.Hom.ext
        apply Over.OverMorphism.ext
        change pullback.lift (pullback.fst P.obj.hom g ≫ 𝟙 P.obj.left) _ _ = 𝟙 _
        apply pullback.hom_ext <;> simp
      map_comp := by
        intro P Q R f k
        apply ObjectProperty.hom_ext
        apply Over.DescentDataCategory.Hom.ext
        apply Over.OverMorphism.ext
        change pullback.lift (pullback.fst P.obj.hom g ≫ (f.hom.left ≫ k.hom.left)) _ _ =
          pullback.lift _ _ _ ≫ pullback.lift _ _ _
        apply pullback.hom_ext <;> simp [Category.assoc] }
  refine ⟨F, fun P ↦ pullback.fst P.obj.hom g, ?_, ?_⟩
  · intro P
    refine ⟨pullback.condition, IsPullback.of_hasPullback _ _, ?_⟩
    intros
    simp [F, pullbackDataObj, pullbackDatum]
  · intros
    simp [F, pullbackDataMap]

end AlgebraicGeometry
