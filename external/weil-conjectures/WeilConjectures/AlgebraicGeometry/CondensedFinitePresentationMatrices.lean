/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison

/-!
# Descent of local finite presentation matrices

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph,
presentation-matrix step (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private noncomputable def unitHomSectionsEquiv (X : Scheme.{u})
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    (𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ S) ≃
      S.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) := by
  let e : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≅
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj (𝟙_ Ab.{u + 1}) :=
    Functor.Monoidal.εIso (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  exact (Iso.homCongr e (Iso.refl S)).trans
    (((constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
      (MorphismProperty.Over.mkIdTerminal @WeaklyEtale X)).homEquiv _ S).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv)

private lemma unitHomSectionsEquiv_naturality (X : Scheme.{u})
    {S S' : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    (g : S ⟶ S') (a : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ S) :
    unitHomSectionsEquiv X S' (a ≫ g) =
      g.hom.app (op (Scheme.ProEt.mk (𝟙 X))) (unitHomSectionsEquiv X S a) := by
  simp only [unitHomSectionsEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private lemma unitHom_stage (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (c : Cocone F) (hc : IsColimit c)
    (a : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ c.pt) :
    ∃ (i : I) (b : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ F.obj i),
      b ≫ c.ι.app i = a := by
  let S := (sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).obj
    (op (Scheme.ProEt.mk (𝟙 X)))
  have : CompactSpace (Scheme.ProEt.mk (𝟙 X)).left := ‹CompactSpace X›
  have : QuasiSeparatedSpace (Scheme.ProEt.mk (𝟙 X)).left := ‹QuasiSeparatedSpace X›
  have hb := (proetale_qcqs_fp_section_calculus X (Scheme.ProEt.mk (𝟙 X)) I).1 F |>.1
  have : IsIso (colimit.post F S) := (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have : PreservesColimit F S := preservesColimit_of_isIso_post S F
  have ht := isColimitOfPreserves (S ⋙ forget Ab.{u + 1}) hc
  obtain ⟨i, b, hb⟩ := Types.jointly_surjective_of_isColimit ht
    (unitHomSectionsEquiv X c.pt a)
  refine ⟨i, (unitHomSectionsEquiv X (F.obj i)).symm b, ?_⟩
  apply (unitHomSectionsEquiv X c.pt).injective
  rw [unitHomSectionsEquiv_naturality, Equiv.apply_symm_apply]
  exact hb

section Regular
open MonObj
variable {C : Type w} [Category.{v} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  (R S : C) [MonObj R] [MonObj S] [IsCommMonObj R]
  (φ : R ⟶ S) [IsMonHom φ]

omit [MonoidalPreadditive C] in
private lemma regular_map_entry (b : 𝟙_ C ⟶ R) :
    (Mod.extendScalars φ).map (Mod.regularLift (Mod.regular R) b) ≫
      (Mod.regularExtensionIso φ).hom =
    (Mod.regularExtensionIso φ).hom ≫ Mod.regularLift (Mod.regular S) (b ≫ φ) := by
  apply Mod.regularExtensionIso_naturality
  have h : Mod.regularLift (Mod.regular R) b ≫ Mod.regularCoefficientMap φ =
      Mod.regularCoefficientMap φ ≫
        (Mod.comap φ).map (Mod.regularLift (Mod.regular S) (b ≫ φ)) := by
    apply Mod.regular_hom_ext
    change η[R] ≫ ((Mod.regularLift (Mod.regular R) b).hom ≫ φ) =
      η[R] ≫ (φ ≫ (Mod.regularLift (Mod.regular S) (b ≫ φ)).hom)
    rw [← Category.assoc, Mod.one_comp_regularLift, ← Category.assoc,
      IsMonHom.one_hom φ, Mod.one_comp_regularLift]
  exact congrArg Mod.Hom.hom h

private noncomputable def extended_free_iso (n : ℕ) :
    (Mod.extendScalars φ).obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
  (Mod.extendScalars φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ Mod.regularExtensionIso φ)

private lemma matrix_extension (m n : ℕ) (b : Fin m → Fin n → (𝟙_ C ⟶ R)) :
    (extended_free_iso R S φ m).inv ≫
      (Mod.extendScalars φ).map (biproduct.desc fun i : Fin m ↦
        biproduct.lift fun j : Fin n ↦ Mod.regularLift (Mod.regular R) (b i j)) ≫
      (extended_free_iso R S φ n).hom =
    biproduct.desc fun i : Fin m ↦
      biproduct.lift fun j : Fin n ↦ Mod.regularLift (Mod.regular S) (b i j ≫ φ) := by
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simp only [extended_free_iso, Iso.trans_inv, Iso.trans_hom, biproduct.mapIso_inv,
    biproduct.mapIso_hom, Category.assoc, biproduct.ι_map_assoc,
    Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
    biproduct.ι_desc_assoc, biproduct.map_π, biproduct.lift_π]
  erw [biproduct.lift_π_assoc]
  simp only [← Category.assoc, ← Functor.map_comp, biproduct.ι_desc,
    biproduct.lift_π]
  simp only [Category.assoc]
  erw [regular_map_entry, Iso.inv_hom_id_assoc]
omit [SymmetricCategory C] [MonoidalClosed C] [IsCommMonObj R] in
private lemma matrix_reconstruct (m n : ℕ)
    (d : Mod.finiteFree R m ⟶ Mod.finiteFree R n) :
    (biproduct.desc fun i : Fin m ↦ biproduct.lift fun j : Fin n ↦
      Mod.regularLift (Mod.regular R)
        (η[R] ≫ (biproduct.ι _ i ≫ d ≫ biproduct.π _ j).hom)) = d := by
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  erw [biproduct.ι_desc, biproduct.lift_π]
  apply Mod.regular_hom_ext
  simpa only [Category.assoc] using Mod.one_comp_regularLift (A := R) _ _
end Regular
private lemma coefficient_unit_lift2 (T X Y : Scheme.{u})
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ T) (g : Y ⟶ X) (ℓ : ℕ) [Fact ℓ.Prime]
    (a : 𝟙_ (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) ⟶
      (upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (b : 𝟙_ (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) ⟶
        (upperStar Ab.{u + 1} g).obj
          ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))),
      b ≫ (upperStar Ab.{u + 1} g).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)) = a := by
  let I := ULift.{u + 1} (PadicAlgCl.FiniteIntermediateField ℓ)
  let e : I ≌ PadicAlgCl.FiniteIntermediateField ℓ := ULift.orderIso.equivalence
  have : IsFiltered I := IsFiltered.of_equivalence e.symm
  let c := (upperStar Ab.{u + 1} g).mapCocone
    ((upperStar Ab.{u + 1} f).mapCocone (padicAlgClRingObjCocone T ℓ))
  have hc : IsColimit c := isColimitOfPreserves (upperStar Ab.{u + 1} g)
    (isColimitOfPreserves (upperStar Ab.{u + 1} f)
      (isColimitPadicAlgClRingObjCocone T ℓ))
  obtain ⟨i, b, hb⟩ := unitHom_stage Y I _ (c.whisker e.functor)
    ((Functor.Final.isColimitWhiskerEquiv e.functor c).symm hc) a
  exact ⟨i.down, b, hb⟩

private lemma common_coefficient_unit_lift (T X : Scheme.{u}) (f : X ⟶ T)
    (ℓ : ℕ) [Fact ℓ.Prime] (J : Type u) [Finite J]
    (Y : J → Scheme.{u}) [∀ j, CompactSpace (Y j)] [∀ j, QuasiSeparatedSpace (Y j)]
    (g : ∀ j, Y j ⟶ X)
    (a : ∀ j, 𝟙_ (Sheaf (Scheme.ProEt.topology (Y j)) Ab.{u + 1}) ⟶
      (upperStar Ab.{u + 1} (g j)).obj
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (b : ∀ j, 𝟙_ (Sheaf (Scheme.ProEt.topology (Y j)) Ab.{u + 1}) ⟶
        (upperStar Ab.{u + 1} (g j)).obj
          ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))),
      ∀ j, b j ≫ (upperStar Ab.{u + 1} (g j)).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)) = a j := by
  classical
  choose E b hb using fun j ↦ coefficient_unit_lift2 T X (Y j) f (g j) ℓ (a j)
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨H, hH⟩ := IsFiltered.sup_objs_exists (Finset.univ.image E)
  let q (j : J) : E j ⟶ H :=
    Classical.choice (hH (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  let c j := (upperStar Ab.{u + 1} (g j)).mapCocone
    ((upperStar Ab.{u + 1} f).mapCocone (padicAlgClRingObjCocone T ℓ))
  let D j := Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint T ⋙
    upperStar Ab.{u + 1} f ⋙ upperStar Ab.{u + 1} (g j)
  refine ⟨H, fun j ↦ b j ≫ (D j).map (q j), ?_⟩
  intro j
  change (b j ≫ (D j).map (q j)) ≫ (c j).ι.app H = a j
  simp only [Category.assoc]
  erw [(c j).w (q j)]
  exact hb j
private instance compMonoidal {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} g f).inv := by
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (g ≫ f))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction Ab.{u + 1} f).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} g))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact Adjunction.isMonoidal_comp _ _
  exact isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp Ab.{u + 1} g f).inv

private lemma fp_pullback_comp {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (h : Mod.IsFinitelyPresented ((upperStar Ab.{u + 1} f).obj R)
      (((upperStar Ab.{u + 1} f).mapMod R).obj M)) :
    Mod.IsFinitelyPresented ((upperStar Ab.{u + 1} (g ≫ f)).obj R)
      (((upperStar Ab.{u + 1} (g ≫ f)).mapMod R).obj M) := by
  let F := upperStar Ab.{u + 1} f
  let G := upperStar Ab.{u + 1} g
  let H := upperStar Ab.{u + 1} (g ≫ f)
  let τ : F ⋙ G ⟶ H := (upperStarComp Ab.{u + 1} g f).inv
  have : NatTrans.IsMonoidal τ := compMonoidal g f
  let eR : G.obj (F.obj R) ≅ H.obj R := asIso (Functor.compAlgHom F G τ R)
  let e := (Functor.mapModCompIso F G τ R).app M
  let N := ((F.mapMod R).obj M)
  have hN : Mod.IsFinitelyPresented (G.obj (F.obj R)) ((G.mapMod (F.obj R)).obj N) :=
    fp_map _ _ (G.mapMod (F.obj R))
      (Mod.isoMk (Iso.refl _) (by simp)) h
  let K : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (G.obj (F.obj R)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (H.obj R) := Mod.comap eR.inv
  have hK := fp_map _ _ K (Mod.regularIsoOfIsIso eR.hom) hN
  let E := Mod.comapEquivalenceOfIsIso eR.hom
  exact (fp_iff_of_iso ((E.unitIso.app ((H.mapMod R).obj M)) ≪≫
    (K.mapIso e).symm)).mpr hK

private lemma finite_affine_lfp_cover (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (h : IsLocallyFinitelyPresented R M) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      Finite U.I₀ ∧ (∀ i, IsAffine (U.X i)) ∧
      ∀ i, Mod.IsFinitelyPresented ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M) := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨V, q, hfin, ho⟩ := QuasiCompactCover.exists_hom U.forgetQc
  have : Finite V.cover.I₀ := hfin
  have (i : V.cover.I₀) : QuasiCompact (V.cover.f i) := by
    infer_instance
  let W := Scheme.Cover.ofQuasiCompactCover V.cover
  refine ⟨W, hfin, fun i ↦ ?_, fun i ↦ ?_⟩
  · change IsAffine (Spec (V.X i))
    infer_instance
  · have hi := fp_pullback_comp (q.h₀ i) (U.f (q.s₀ i)) R M (hU (q.s₀ i))
    have hw : q.h₀ i ≫ U.f (q.s₀ i) = W.f i := q.w₀ i
    rw [hw] at hi
    exact hi

/-- Local finite presentation matrices lift simultaneously to one finite coefficient field.

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph, first
finite-presentation step (auxiliary; not a blueprint node).

Proof: refine the given presentation cover using quasi-compactness to a finite affine
pro-etale cover. Monoidal inverse image preserves finite free modules and cokernels,
so it preserves the presentations on this refinement. The coefficient cocone is a
colimit, also after inverse image along f and the covering arrows. On each affine
covering scheme the qcqs section calculus lifts every entry of each finite matrix to
a finite coefficient field. Directedness moves all finitely many lifts to one field.
Take these matrices over that field. Scalar extension preserves their cokernels and
finite free modules, giving the displayed local comparisons. Empty covers and zero
ranks use empty families and any coefficient stage supplied by filteredness. -/
theorem exists_common_finiteCoefficient_presentation_matrices
    (T X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (hM : IsLocallyFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)) M) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X),
      Finite U.I₀ ∧ (∀ i, IsAffine (U.X i)) ∧
      ∃ (n m : U.I₀ → ℕ)
        (d : ∀ i, Mod.finiteFree
          ((upperStar Ab.{u + 1} (U.f i)).obj
            ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (m i) ⟶
          Mod.finiteFree
          ((upperStar Ab.{u + 1} (U.f i)).obj
            ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (n i)),
        ∀ i, Nonempty ((Mod.extendScalars
          ((upperStar Ab.{u + 1} (U.f i)).map
            ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj
              (cokernel (d i)) ≅
          ((upperStar Ab.{u + 1} (U.f i)).mapMod
            ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M) := by
  classical
  obtain ⟨U, hfinite, haffine, hU⟩ := finite_affine_lfp_cover X _ M hM
  let : Finite U.I₀ := hfinite
  have (i : U.I₀) : IsAffine (U.X i) := haffine i
  choose n m d hd using hU
  let J := Σ i : U.I₀, Fin (m i) × Fin (n i)
  let Y (j : J) := U.X j.1
  let g (j : J) := U.f j.1
  let R (i : U.I₀) := (upperStar Ab.{u + 1} (U.f i)).obj
    ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))
  let a (j : J) : 𝟙_ (Sheaf (Scheme.ProEt.topology (Y j)) Ab.{u + 1}) ⟶ R j.1 :=
    (MonObj.one : 𝟙_ (Sheaf (Scheme.ProEt.topology (Y j)) Ab.{u + 1}) ⟶ R j.1) ≫
      (biproduct.ι _ j.2.1 ≫ d j.1 ≫ biproduct.π _ j.2.2).hom
  obtain ⟨E, b, hb⟩ := common_coefficient_unit_lift T X f ℓ J Y g a
  let RE (i : U.I₀) := (upperStar Ab.{u + 1} (U.f i)).obj
    ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))
  let φ (i : U.I₀) : RE i ⟶ R i := (upperStar Ab.{u + 1} (U.f i)).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))
  let dE (i : U.I₀) : Mod.finiteFree (RE i) (m i) ⟶ Mod.finiteFree (RE i) (n i) :=
    biproduct.desc fun k : Fin (m i) ↦ biproduct.lift fun l : Fin (n i) ↦
      Mod.regularLift (Mod.regular (RE i)) (b ⟨i, k, l⟩)
  refine ⟨E, U, hfinite, haffine, n, m, dE, fun i ↦ ?_⟩
  let F := Mod.extendScalars (φ i)
  let en := extended_free_iso (RE i) (R i) (φ i)
  have he : (en (m i)).inv ≫ F.map (dE i) ≫ (en (n i)).hom = d i := by
    change (extended_free_iso (RE i) (R i) (φ i) (m i)).inv ≫
      (Mod.extendScalars (φ i)).map (biproduct.desc fun k : Fin (m i) ↦
        biproduct.lift fun l : Fin (n i) ↦
          Mod.regularLift (Mod.regular (RE i)) (b ⟨i, k, l⟩)) ≫
      (extended_free_iso (RE i) (R i) (φ i) (n i)).hom = d i
    rw [matrix_extension]
    rw [show (fun k : Fin (m i) ↦ biproduct.lift fun l : Fin (n i) ↦
        Mod.regularLift (Mod.regular (R i)) (b ⟨i, k, l⟩ ≫ φ i)) =
        (fun k : Fin (m i) ↦ biproduct.lift fun l : Fin (n i) ↦
          Mod.regularLift (Mod.regular (R i)) (a ⟨i, k, l⟩)) by
      apply funext
      intro k
      apply congrArg biproduct.lift
      apply funext
      intro l
      exact congrArg (Mod.regularLift (Mod.regular (R i))) (hb ⟨i, k, l⟩)]
    exact matrix_reconstruct (R i) (m i) (n i) (d i)
  have hs : F.map (dE i) ≫ (en (n i)).hom = (en (m i)).hom ≫ d i := by
    rw [← he]
    simp
  obtain ⟨ei⟩ := hd i
  exact ⟨PreservesCokernel.iso F (dE i) ≪≫
    cokernel.mapIso (F.map (dE i)) (d i) (en (m i)) (en (n i)) hs ≪≫ ei.symm⟩

end AlgebraicGeometry.ProEtale
