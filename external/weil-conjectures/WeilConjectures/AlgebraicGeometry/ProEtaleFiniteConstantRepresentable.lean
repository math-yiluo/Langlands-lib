/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen

/-! # Representing finite constant sheaves on the pro-etale site

Source: Stacks Project, Tags 0H7J, 03YW and 098T.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The disjoint union of copies of the base, as a weakly etale scheme. -/
noncomputable abbrev proEtaleFiniteConstantObject (U : Scheme.{u}) (E : Type u) : U.ProEt :=
  have : WeaklyEtale (Sigma.desc (fun _ : E ↦ 𝟙 U)) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)
  ProEt.mk (Sigma.desc (fun _ : E ↦ 𝟙 U))

/-- Finite disjoint unions, with maps induced by maps of labels. -/
noncomputable def proEtaleFiniteCopiesFunctor (U : Scheme.{u}) :
    FintypeCat.{u} ⥤ U.ProEt where
  obj E := proEtaleFiniteConstantObject U E
  map {E F} a := MorphismProperty.Over.homMk
    (Sigma.desc (fun e : E ↦ Sigma.ι (fun _ : F ↦ U) (a e))) (by
      apply Sigma.hom_ext
      intro e
      simp)
  map_id E := by
    apply MorphismProperty.Over.Hom.ext
    change Sigma.desc (fun e : E ↦ Sigma.ι (fun _ : E ↦ U) e) = 𝟙 _
    apply Sigma.hom_ext
    intro e
    simp
  map_comp {E F H} a b := by
    apply MorphismProperty.Over.Hom.ext
    change Sigma.desc (fun e : E ↦ Sigma.ι (fun _ : H ↦ U) (b (a e))) =
      Sigma.desc (fun e : E ↦ Sigma.ι (fun _ : F ↦ U) (a e)) ≫
        Sigma.desc (fun e : F ↦ Sigma.ι (fun _ : H ↦ U) (b e))
    apply Sigma.hom_ext
    intro e
    simp

/-- The lifted representable presheaf of the labelled disjoint union. -/
noncomputable abbrev proEtaleFiniteConstantPresheaf (U : Scheme.{u}) (E : Type u) :
    U.ProEtᵒᵖ ⥤ Type (u + 1) :=
  ((ProEt.topology U).uliftYoneda.{u + 1}.obj
    (proEtaleFiniteConstantObject U E)).obj

/-- The canonical presheaf map sending a label to its constant section. -/
noncomputable def proEtaleFiniteConstantSections (U : Scheme.{u}) (E : Type u) :
    (Functor.const U.ProEtᵒᵖ).obj (ULift.{u + 1, u} E) ⟶
      proEtaleFiniteConstantPresheaf U E :=
  { app := fun W => ↾fun e => ⟨MorphismProperty.Over.homMk
        (W.unop.hom ≫ Sigma.ι (fun _ : E => U) e.down) (by simp)⟩
    naturality := by
        intro W V g
        ext e
        apply ULift.ext
        apply MorphismProperty.Over.Hom.ext
        change V.unop.hom ≫ Sigma.ι (fun _ : E => U) e.down =
          g.unop.left ≫ (W.unop.hom ≫ Sigma.ι (fun _ : E => U) e.down)
        simp [← Category.assoc] }

/-- The sheafification of the canonical constant-section map. -/
noncomputable def proEtaleFiniteConstantComparison (U : Scheme.{u}) (E : Type u) :
    (constantSheaf (ProEt.topology U) (Type (u + 1))).obj (ULift.{u + 1, u} E) ⟶
      (ProEt.topology U).uliftYoneda.{u + 1}.obj (proEtaleFiniteConstantObject U E) :=
  ⟨sheafifyLift (ProEt.topology U) (proEtaleFiniteConstantSections U E)
    (((ProEt.topology U).uliftYoneda.{u + 1}.obj
      (proEtaleFiniteConstantObject U E)).property)⟩

/-- Finite disjoint unions represent finite constant pro-etale sheaves.
Source: Stacks Project, Tags 0H7J, 03YW and 098T.
(auxiliary; not a blueprint node)

Proof: The constant-section map labels the components. A represented section is a
clopen partition, so the map is locally surjective on the open cover by its pieces.
If two different labels give the same represented section then the domain is empty,
where the empty covering proves local injectivity. Sheafification is locally
bijective; hence its induced map into the representable sheaf is locally bijective,
and therefore is an isomorphism. This includes the empty finite set. -/
theorem proEtaleFiniteConstantComparison_isIso (U : Scheme.{u}) (E : Type u) [Finite E] :
    IsIso (proEtaleFiniteConstantComparison U E) := by
  let H := proEtaleFiniteConstantPresheaf U E
  let P := (Functor.const U.ProEtᵒᵖ).obj (ULift.{u + 1, u} E)
  let c := proEtaleFiniteConstantSections U E
  have hc : ∀ (W : U.ProEt) (e : E), ((c.app (Opposite.op W)) ⟨e⟩).down.left =
      W.hom ≫ Sigma.ι (fun _ : E => U) e := fun _ _ => rfl
  have hH : Presheaf.IsSheaf (ProEt.topology U) H :=
    ((ProEt.topology U).uliftYoneda.{u + 1}.obj
      (proEtaleFiniteConstantObject U E)).property
  have hinj : Presheaf.IsLocallyInjective (ProEt.topology U) c := by
    constructor
    intro W a b hab
    by_cases h : a = b
    · subst b
      exact (ProEt.topology U).superset_covering (fun _ _ _ => rfl)
        ((ProEt.topology U).top_mem _)
    · have hne : a.down ≠ b.down := fun h' => h (ULift.ext h')
      have heq : W.unop.hom ≫ Sigma.ι (fun _ : E => U) a.down =
          W.unop.hom ≫ Sigma.ι (fun _ : E => U) b.down :=
        congrArg (fun t => t.down.left) hab
      have ha := (coproductCopiesMorphismsClopen U W.unop.left E W.unop.hom).2.2.2.2.1
      have htop : (⊤ : W.unop.left.Opens) = ⊥ := by
        have h₁ := ha a.down a.down
        have h₂ := ha b.down a.down
        rw [heq] at h₁
        simpa [hne] using h₁.symm.trans h₂
      have : IsEmpty W.unop.left := ⟨fun x => by
        have hx : x ∈ (⊤ : W.unop.left.Opens) := trivial
        rw [htop] at hx
        exact hx⟩
      let j : ∀ i : PEmpty.{u + 1}, (i.elim : Scheme.{u}) ⟶ W.unop.left :=
        fun i ↦ i.elim
      let : ∀ i, IsOpenImmersion (j i) := fun i ↦ i.elim
      apply ProEt.mem_topology_of_openImmersion _ j
      · intro x
        exact isEmptyElim x
      · intro i
        exact i.elim
  have hsurj : Presheaf.IsLocallySurjective (ProEt.topology U) c := by
    constructor
    intro W s
    let f : W.left ⟶ ∐ fun _ : E => U := s.down.left
    have hf : f ≫ Sigma.desc (fun _ : E => 𝟙 U) = W.hom := s.down.w
    let V (e : E) := f ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange
    have hdecomp := (coproductCopiesMorphismsClopen U W.left E W.hom).1 f hf
    let Z (e : E) : U.ProEt := ProEt.mk ((V e).ι ≫ W.hom)
    let j (e : E) : Z e ⟶ W := MorphismProperty.Over.homMk (V e).ι rfl
    apply ProEt.mem_topology_of_openImmersion _ (fun e ↦ (V e).ι)
    · intro x
      have hx : x ∈ (⨆ e, V e) := by rw [hdecomp.1.2]; trivial
      obtain ⟨e, he⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨e, ⟨⟨x, he⟩, rfl⟩⟩
    · intro e
      refine ⟨⟨e⟩, ?_⟩
      apply ULift.ext
      apply MorphismProperty.Over.Hom.ext
      exact (hdecomp.2 e).symm
  let φ : (constantSheaf (ProEt.topology U) (Type (u + 1))).obj
      (ULift.{u + 1, u} E) ⟶ ⟨H, hH⟩ :=
    ⟨sheafifyLift (ProEt.topology U) c hH⟩
  have hφ : toSheafify (ProEt.topology U) P ≫ φ.hom = c :=
    toSheafify_sheafifyLift (ProEt.topology U) c hH
  change IsIso φ
  apply (Sheaf.isLocallyBijective_iff_isIso φ).mp
  constructor
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _
      (toSheafify (ProEt.topology U) P), hφ]
    exact hinj
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _
      (toSheafify (ProEt.topology U) P), hφ]
    exact hsurj

/-- The canonical comparison commutes with every map of finite label sets. -/
theorem proEtaleFiniteConstantComparison_naturality (U : Scheme.{u})
    {E F : FintypeCat.{u}} (a : E ⟶ F) :
    (constantSheaf (ProEt.topology U) (Type (u + 1))).map
        (uliftFunctor.{u + 1, u}.map ((CategoryTheory.forget FintypeCat.{u}).map a)) ≫
      proEtaleFiniteConstantComparison U F =
      proEtaleFiniteConstantComparison U E ≫
        (ProEt.topology U).uliftYoneda.{u + 1}.map
          ((proEtaleFiniteCopiesFunctor U).map a) := by
  apply ((sheafificationAdjunction (ProEt.topology U) (Type (u + 1))).homEquiv _ _).injective
  change toSheafify _ _ ≫ sheafifyMap _ _ ≫ sheafifyLift _ _ _ =
    toSheafify _ _ ≫ sheafifyLift _ _ _ ≫ _
  rw [← Category.assoc, ← toSheafify_naturality]
  simp only [Category.assoc]
  rw [toSheafify_sheafifyLift, ← Category.assoc, toSheafify_sheafifyLift]
  ext W e
  apply ULift.ext
  apply MorphismProperty.Over.Hom.ext
  change W.unop.hom ≫ Sigma.ι (fun _ : F ↦ U) (a e.down) =
    (W.unop.hom ≫ Sigma.ι (fun _ : E ↦ U) e.down) ≫
      Sigma.desc (fun e : E ↦ Sigma.ι (fun _ : F ↦ U) (a e))
  simp

/-- The natural representation of finite constant sheaves by labelled disjoint unions. -/
noncomputable def proEtaleFiniteConstantRepresentableIso (U : Scheme.{u}) :
    CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u} ⋙
        constantSheaf (ProEt.topology U) (Type (u + 1)) ≅
      proEtaleFiniteCopiesFunctor U ⋙ (ProEt.topology U).uliftYoneda.{u + 1} := by
  let (E : FintypeCat.{u}) : IsIso (proEtaleFiniteConstantComparison U E) :=
    proEtaleFiniteConstantComparison_isIso U E
  exact NatIso.ofComponents (fun E ↦ asIso (proEtaleFiniteConstantComparison U E))
    (fun a ↦ proEtaleFiniteConstantComparison_naturality U a)

end AlgebraicGeometry.Scheme
