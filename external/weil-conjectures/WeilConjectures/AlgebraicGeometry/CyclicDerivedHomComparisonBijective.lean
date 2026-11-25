/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CyclicDerivedHomComparisonMap
import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic

/-! # Bijectivity of free-representable cohomology comparison
Source: Stacks Project, Tags 03Q8 and 072W, and the free-sheaf adjunction.
(blueprint: lem-sbc-abelian-representable-cohomology-map-bijective). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

-- An ordinary corepresenting bijection extends to Ext by injective dimension shifting.
private theorem extComparison_bijective.{v, v', w, w', u'}
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (hR : ∀ (I : C), Injective I → Injective (R.obj I))
    (A : C) (B : D) (g : B ⟶ R.obj A)
    (h₀ : ∀ F : C, Function.Bijective (fun f : A ⟶ F ↦ g ≫ R.map f))
    (F : C) (n : ℕ) :
    Function.Bijective (((CategoryTheory.Abelian.Ext.mk₀ g).precomp (R.obj F) (zero_add n)).comp
      (R.mapExtAddHom A F n)) := open CategoryTheory.Abelian in by
  let c (F : C) (n : ℕ) :=
    ((Ext.mk₀ g).precomp (R.obj F) (zero_add n)).comp (R.mapExtAddHom A F n)
  change Function.Bijective (c F n)
  induction n generalizing F with
  | zero =>
    refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
      obtain ⟨y, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
      change (Ext.mk₀ g).comp ((Ext.mk₀ x).mapExactFunctor R) rfl =
        (Ext.mk₀ g).comp ((Ext.mk₀ y).mapExactFunctor R) rfl at hxy
      rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀,
        Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀] at hxy
      exact congrArg Ext.mk₀ ((h₀ F).1 ((Ext.mk₀_bijective _ _).1 hxy))
    · obtain ⟨z, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
      obtain ⟨f, hf⟩ := (h₀ F).2 z
      refine ⟨Ext.mk₀ f, ?_⟩
      change (Ext.mk₀ g).comp ((Ext.mk₀ f).mapExactFunctor R) rfl = _
      rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
      exact congrArg Ext.mk₀ hf
  | succ n hn =>
    let I : InjectivePresentation F := Classical.arbitrary _
    have : Injective I.J := I.injective
    have : Injective (R.obj I.J) := hR I.J I.injective
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hSR : (S.map R).ShortExact := hS.map_of_exact R
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Ext.mk₀ S.g).postcomp A (add_zero n)) (hS.extClass.postcomp A rfl)
      ((Ext.mk₀ (R.map S.g)).postcomp B (add_zero n)) (hSR.extClass.postcomp B rfl)
      (c S.X₂ n) (c S.X₃ n) (c S.X₁ (n + 1)) ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' B hSR n (n + 1) rfl))
      (hn _).2 (hn _) ?_ ?_
    · ext x
      change ((Ext.mk₀ g).comp (x.mapExactFunctor R) (zero_add n)).comp
        (Ext.mk₀ (R.map S.g)) (add_zero n) =
        (Ext.mk₀ g).comp ((x.comp (Ext.mk₀ S.g) (add_zero n)).mapExactFunctor R)
          (zero_add n)
      rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
      exact Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (zero_add n)
    · ext x
      change ((Ext.mk₀ g).comp (x.mapExactFunctor R) (zero_add n)).comp hSR.extClass rfl =
        (Ext.mk₀ g).comp ((x.comp hS.extClass rfl).mapExactFunctor R) (zero_add (n + 1))
      rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
      exact Ext.comp_assoc _ _ _ (zero_add n) rfl (zero_add (n + 1))
    · intro x
      exact Ext.covariant_sequence_exact₁ A hS x
        (Ext.eq_zero_of_injective (I := I.J) _) rfl
    · intro x
      exact Ext.covariant_sequence_exact₁ B hSR x
        (Ext.eq_zero_of_injective (I := R.obj I.J) _) rfl

private noncomputable def comparisonHomEquiv {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((upperStar AddCommGrpCat.{u + 1} h).obj ((etaleOpenFreeSheaf X).obj W) ⟶ F) ≃+
      ((constantSheaf (pullback h W.hom).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶
          (upperStar AddCommGrpCat.{u + 1} (pullback.fst h W.hom)).obj F) :=
    open CategoryTheory.Abelian in by
  let B := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj W
  let R : Y.Etale := MorphismProperty.Over.mk ⊤ (pullback.fst h W.hom) inferInstance
  let i : R ≅ B := MorphismProperty.Over.isoMk (pullbackSymmetry h W.hom) (by
    dsimp [B, R]
    simp)
  let T := pullback h W.hom
  let r := pullback.fst h W.hom
  let t : T.Etale := MorphismProperty.Over.mk ⊤ (𝟙 T)
    (inferInstance : AlgebraicGeometry.Etale (𝟙 T))
  let O := (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale r)).obj t
  let j : O ≅ R := MorphismProperty.Over.isoMk (Iso.refl _) (by
    dsimp [O, t, R, r]
    exact (Category.id_comp _).symm)
  let ρ := upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} r inferInstance
  let e := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).homAddEquiv
    ((etaleOpenFreeSheaf X).obj W) F).trans
      (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W _)
  let e' := e.trans (F.obj.mapIso i.op).addCommGroupIsoToAddEquiv
    |>.trans (F.obj.mapIso j.op).addCommGroupIsoToAddEquiv
    |>.trans (asIso ((ρ.inv.app F).hom.app (op t))).addCommGroupIsoToAddEquiv
  exact e'.trans (Sheaf.H.equiv₀ _
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).symm |>.trans Ext.addEquiv₀

set_option maxRecDepth 4096 in
private lemma comparisonHomEquiv_naturality {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (a : (upperStar AddCommGrpCat.{u + 1} h).obj ((etaleOpenFreeSheaf X).obj W) ⟶ F) :
    comparisonHomEquiv h W G (a ≫ f) = comparisonHomEquiv h W F a ≫
      (upperStar AddCommGrpCat.{u + 1} (pullback.fst h W.hom)).map f :=
    open CategoryTheory.Abelian in by
  let B := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj W
  let R : Y.Etale := MorphismProperty.Over.mk ⊤ (pullback.fst h W.hom) inferInstance
  let i : R ≅ B := MorphismProperty.Over.isoMk (pullbackSymmetry h W.hom) (by
    dsimp [B, R]
    simp)
  let T := pullback h W.hom
  let r := pullback.fst h W.hom
  let t : T.Etale := MorphismProperty.Over.mk ⊤ (𝟙 T)
    (inferInstance : AlgebraicGeometry.Etale (𝟙 T))
  let O := (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale r)).obj t
  let j : O ≅ R := MorphismProperty.Over.isoMk (Iso.refl _) (by
    dsimp [O, t, R, r]
    exact (Category.id_comp _).symm)
  let ρ := upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} r inferInstance
  let U := upperStar AddCommGrpCat.{u + 1} r
  let ht := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T
  let s := EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W
    ((lowerStar AddCommGrpCat.{u + 1} h).obj F)
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).homEquiv _ _ a)
  let z := ((ρ.inv.app F).hom.app (op t)) (F.obj.map j.hom.op (F.obj.map i.hom.op s))
  have hs : EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W
      ((lowerStar AddCommGrpCat.{u + 1} h).obj G)
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).homEquiv _ _ (a ≫ f)) =
      f.hom.app (op B) s := by
    rw [Adjunction.homEquiv_naturality_right]
    exact EtaleOpenComparison.sectionsEquiv_naturality X.smallEtaleTopology W
      ((lowerStar AddCommGrpCat.{u + 1} h).map f) _
  have hz : ((ρ.inv.app G).hom.app (op t))
      (G.obj.map j.hom.op (G.obj.map i.hom.op (f.hom.app (op B) s))) =
      ((U.map f).hom.app (op t)) z := by
    rw [← NatTrans.naturality_apply f.hom i.hom.op s,
      ← NatTrans.naturality_apply f.hom j.hom.op]
    have hn := congrArg (fun q ↦ q.hom.app (op t)) (ρ.inv.naturality f)
    change f.hom.app (op O) ≫ (ρ.inv.app G).hom.app (op t) =
      (ρ.inv.app F).hom.app (op t) ≫ (U.map f).hom.app (op t) at hn
    exact congrArg (fun k ↦ k (F.obj.map j.hom.op (F.obj.map i.hom.op s))) hn
  change Ext.addEquiv₀ ((Sheaf.H.equiv₀ (U.obj G) ht).symm
    (((ρ.inv.app G).hom.app (op t)) (G.obj.map j.hom.op (G.obj.map i.hom.op
      (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W
        ((lowerStar AddCommGrpCat.{u + 1} h).obj G)
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).homEquiv _ _
            (a ≫ f))))))) = Ext.addEquiv₀ ((Sheaf.H.equiv₀ (U.obj F) ht).symm z) ≫ U.map f
  rw [hs, hz]
  rw [← Sheaf.H.equiv₀_symm_naturality, Sheaf.H.addEquiv₀_map]

set_option maxRecDepth 4096 in
private lemma comparisonHomEquiv_id {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale) :
    comparisonHomEquiv h W _ (𝟙 ((upperStar AddCommGrpCat.{u + 1} h).obj
      ((abelianRepresentable X).obj W))) = abelianRepresentableGenerator h W := by
  simp only [comparisonHomEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_unit]
  rfl

private lemma generatorHom_bijective {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (fun f :
      (upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj W) ⟶ F ↦
        abelianRepresentableGenerator h W ≫
          (upperStar AddCommGrpCat.{u + 1} (pullback.fst h W.hom)).map f) := by
  have he : (fun f :
      (upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj W) ⟶ F ↦
        abelianRepresentableGenerator h W ≫
          (upperStar AddCommGrpCat.{u + 1} (pullback.fst h W.hom)).map f) =
      comparisonHomEquiv h W F := by
    funext f
    have hn := comparisonHomEquiv_naturality h W f (𝟙 _)
    rw [Category.id_comp, comparisonHomEquiv_id] at hn
    exact hn.symm
  rw [he]
  exact (comparisonHomEquiv h W F).bijective

/-- The explicit universal-section map computes the cohomology of the fibre product.

Source: Stacks Project, Tags 03Q8 and 072W; the free-sheaf/étale-extension-by-zero
argument of `WeilConjectures/SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/FreeSheaf.lean`.
(blueprint: lem-sbc-abelian-representable-cohomology-map-bijective).

Proof: Put T = Y ×_X W and r = T → Y. The free/sheafification/Yoneda adjunction
identifies maps from h*Z[W] with sections over T, naturally in the target sheaf.
The exact left adjoint r_! to r* takes the constant integer sheaf to h*Z[W], by
this same universal property. Its adjunction unit at the constant integer sheaf
is precisely abelianRepresentableGenerator: evaluate the h*-adjunction unit at
id_W, change the pullback order, and restrict to id_T. Since r_! and r* are
exact, their derived adjunction identifies Ext(h*Z[W], F, q) with
Ext(Z_T, r*F, q). The forward map is pullback of the Ext class followed by
precomposition with this generator, hence is abelianRepresentableCohomologyMap.
The fully faithful inclusion of D+ into D identifies its input with Ext through
abelianPlusHomExtEquiv. All constituent maps are bijective, proving the result
for every F and q, including q = 0 and empty T. -/
theorem abelianRepresentableCohomologyMap_bijective {X Y : Scheme.{u}}
    (h : Y ⟶ X) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (W : X.Etale) :
    Function.Bijective (abelianRepresentableCohomologyMap h F q W) :=
    open CategoryTheory.Abelian in by
  let R := upperStar AddCommGrpCat.{u + 1} (pullback.fst h W.hom)
  have hR : ∀ I : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1},
      Injective I → Injective (R.obj I) := by
    intro I hI
    let := hI
    exact injective_upperStar_obj_of_etale_addCommGrp (pullback.fst h W.hom) I
  have hExt := extComparison_bijective R hR _ _ (abelianRepresentableGenerator h W)
    (generatorHom_bijective h W) F q
  change Function.Bijective
    ((((Ext.mk₀ (abelianRepresentableGenerator h W)).precomp _ (zero_add q)).comp
      (R.mapExtAddHom _ F q)).comp (abelianPlusHomExtEquiv _ F q).toAddMonoidHom)
  exact hExt.comp (abelianPlusHomExtEquiv _ F q).bijective

end AlgebraicGeometry.Etale
