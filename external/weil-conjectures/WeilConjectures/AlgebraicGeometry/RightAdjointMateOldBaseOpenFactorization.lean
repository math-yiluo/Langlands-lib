/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DualityEquationBaseChangeMap
import WeilConjectures.AlgebraicGeometry.RightAdjointMateSchemeIsoTransport
import WeilConjectures.AlgebraicGeometry.RightAdjointMateSuccessiveBaseChange
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Factorization of a right-adjoint mate through an old-base open

Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem transport_arrow_factorization
    {C : Type*} [Category C] {G O L G' O' H : Arrow C}
    (eg : G ≅ G') (eo : O ≅ O') (eh : H ≅ L)
    (e₀ : G'.left ≅ O'.left) (e₁ : O'.right ≅ H.left) (e₂ : G'.right ≅ H.right)
    (hpaste : G'.hom ≫ e₂.hom = e₀.hom ≫ O'.hom ≫ e₁.hom ≫ H.hom) :
    ∃ (d₀ : G.left ≅ O.left) (d₁ : O.right ≅ L.left) (d₂ : G.right ≅ L.right),
      G.hom ≫ d₂.hom = d₀.hom ≫ O.hom ≫ d₁.hom ≫ L.hom := by
  refine ⟨Arrow.leftFunc.mapIso eg ≪≫ e₀ ≪≫ (Arrow.leftFunc.mapIso eo).symm,
    Arrow.rightFunc.mapIso eo ≪≫ e₁ ≪≫ Arrow.leftFunc.mapIso eh,
    Arrow.rightFunc.mapIso eg ≪≫ e₂ ≪≫ Arrow.rightFunc.mapIso eh, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc]
  change G.hom ≫ eg.hom.right ≫ e₂.hom ≫ eh.hom.right =
    eg.hom.left ≫ e₀.hom ≫ eo.inv.left ≫ O.hom ≫
      eo.hom.right ≫ e₁.hom ≫ eh.hom.left ≫ L.hom
  calc
    _ = eg.hom.left ≫ (G'.hom ≫ e₂.hom) ≫ eh.hom.right := by
      simp only [← Category.assoc]
      rw [← Arrow.w eg.hom]
    _ = eg.hom.left ≫ (e₀.hom ≫ O'.hom ≫ e₁.hom ≫ H.hom) ≫ eh.hom.right := by
      rw [hpaste]
    _ = _ := by
      rw [Arrow.iso_w eo]
      simp only [Category.assoc]
      rw [← Arrow.w eh.hom]


/-- Pasting through the old-base open factors the global mate through the open mate.
The open mate is retained as a morphism and is not assumed invertible.
Only quasi-compactness and quasi-separatedness are needed for f; properness,
flatness, and finite presentation play no role in this categorical factorization.
Source: Stacks Project, duality.tex, Lemma 48.5.2 (Tag 0ATR) and
Remark 48.6.1 (Tag 0E9S).
(blueprint: lem-sc-right-adjoint-mate-old-base-open-factorization)

Proof: The restriction square is cartesian. Its pullback along gV identifies
U times_V T with the iterated pullback of X along V and then T. The supplied
projection equations uniquely specify s and t under this identification.
Pullback composition supplies e₀. The isomorphism between U and X times_Y V,
direct-image composition, and uniqueness of right adjoints identify aV with b;
pulling this identification along the projection to U supplies e₁.
Likewise the scheme isomorphism U times_V T to X times_Y T, direct-image
composition, and right-adjoint uniqueness supply e₂ comparing c and b'.
Expand each mate as pullback of the right adjoint applied to the pullback unit,
followed by the inverse conjugate of ordinary base change, followed by the
pullback counit. Composite adjunction units and counits are the pasted units
and counits. Pasting ordinary base change follows by applying the adjunction
Hom equivalence and the associative derived-pullback composition comparisons.
ConjugateEquiv respects composition; conjugation takes the inverses to inverses.
Substituting these three identities in the global mate and cancelling the
adjunction unit/counit pairs with the triangle identities gives the displayed
factorization, with the open mate O.hom remaining in the middle. No inversion
of O.hom is used here. The argument remains valid on empty schemes and for
noninvertible local mates; it is an equality of morphisms, not a claim that
base change for the right adjoints is universally invertible.
-/
theorem rightAdjoint_mate_oldBase_open_factorization
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y T : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (V : Y.Opens) [IsAffine V.toScheme]
    [CompactSpace (f ⁻¹ᵁ V).toScheme] [QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme]
    (g0 : T ⟶ Y) (gV : T ⟶ V.toScheme) (hg : gV ≫ V.ι = g0)
    (c : schemeDerivedQCohCategory T ⥤
      schemeDerivedQCohCategory (pullback f g0))
    (adjc : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback f g0)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g0)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g0)) _ _ _ _
          (pullback.snd f g0) _ _).fst E.obj E.property) ⊣ c)
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g0) g0
        (pullback.fst f g0) pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y)
    (b : schemeDerivedQCohCategory V.toScheme ⥤
      schemeDerivedQCohCategory (f ⁻¹ᵁ V).toScheme)
    (b' : schemeDerivedQCohCategory T ⥤
      schemeDerivedQCohCategory (pullback (f ∣_ V) gV))
    (adjb : (schemeDerivedQCohProperty V.toScheme).lift
      ((schemeDerivedQCohProperty (f ⁻¹ᵁ V).toScheme).ι ⋙
        schemeDerivedDirectImage (f ∣_ V))
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ (f ∣_ V)).fst
        E.obj E.property) ⊣ b)
    (adjb' : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback (f ∣_ V) gV)).ι ⋙
        schemeDerivedDirectImage (pullback.snd (f ∣_ V) gV))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated
          (pullback.snd (f ∣_ V) gV)) _ _ _ _
        (pullback.snd (f ∣_ V) gV) _ _).fst E.obj E.property) ⊣ b')
    (hβV : ∀ E : schemeDerivedQCohCategory (f ⁻¹ᵁ V).toScheme,
      IsIso (schemeDerivedBaseChangeMap (f ∣_ V)
        (pullback.snd (f ∣_ V) gV) gV
        (pullback.fst (f ∣_ V) gV) pullback.condition E.obj))
    (aV : schemeDerivedQCohCategory V.toScheme ⥤
      schemeDerivedQCohCategory (pullback f V.ι))
    (adjV : (schemeDerivedQCohProperty V.toScheme).lift
      ((schemeDerivedQCohProperty (pullback f V.ι)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f V.ι)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f V.ι)) _ _ _ _
          (pullback.snd f V.ι) _ _).fst E.obj E.property) ⊣ aV)
    (hβ₀ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f V.ι) V.ι
        (pullback.fst f V.ι) pullback.condition E.obj))
    (s : pullback (f ∣_ V) gV ⟶ pullback f g0)
    (t : pullback (f ∣_ V) gV ⟶ pullback f V.ι)
    (hs₁ : s ≫ pullback.fst f g0 =
      pullback.fst (f ∣_ V) gV ≫ (f ⁻¹ᵁ V).ι)
    (hs₂ : s ≫ pullback.snd f g0 = pullback.snd (f ∣_ V) gV)
    (ht₁ : t ≫ pullback.fst f V.ι =
      pullback.fst (f ∣_ V) gV ≫ (f ⁻¹ᵁ V).ι)
    (ht₂ : t ≫ pullback.snd f V.ι = pullback.snd (f ∣_ V) gV ≫ gV) :
    let G := Arrow.mk ((derivedPullback s).map
      ((schemeDerivedQCohProperty (pullback f g0)).ι.map
        (@dualityEquationBaseChangeMap _ X Y T
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
          f g0 a c adjf adjc hβ K)))
    let O := Arrow.mk ((derivedPullback t).map
      ((schemeDerivedQCohProperty (pullback f V.ι)).ι.map
        (@dualityEquationBaseChangeMap _ X Y V.toScheme
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
          f V.ι a aV adjf adjV hβ₀ K)))
    let L := Arrow.mk ((schemeDerivedQCohProperty (pullback (f ∣_ V) gV)).ι.map
      (dualityEquationBaseChangeMap (f ∣_ V) gV b b' adjb adjb' hβV
        ⟨(derivedPullback V.ι).obj K.obj,
          (derivedPullback_tensor_preserve_QCoh V.ι).1 K.obj K.property⟩))
    ∃ (e₀ : G.left ≅ O.left) (e₁ : O.right ≅ L.left) (e₂ : G.right ≅ L.right),
      G.hom ≫ e₂.hom = e₀.hom ≫ O.hom ≫ e₁.hom ≫ L.hom := by
  classical
  subst g0
  intro G O L
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let : QuasiSeparatedSpace (pullback f V.ι : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f V.ι)
  let q := pullback.fst (pullback.snd f V.ι) gV
  let z := pullback.snd (pullback.snd f V.ι) gV
  let k : pullback (pullback.snd f V.ι) gV ⟶ pullback f (gV ≫ V.ι) :=
    pullback.lift (q ≫ pullback.fst f V.ι) z (by
      dsimp only [q, z]
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        pullback.condition, Category.assoc])
  have hk₁ : k ≫ pullback.fst f (gV ≫ V.ι) = q ≫ pullback.fst f V.ι :=
    pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd f (gV ≫ V.ι) = z := pullback.lift_snd _ _ _
  let e := (pullbackRestrictIsoRestrict f V).symm
  have he : e.hom ≫ pullback.snd f V.ι = f ∣_ V := rfl
  let r : pullback (f ∣_ V) gV ⟶ pullback (pullback.snd f V.ι) gV :=
    pullback.lift (pullback.fst (f ∣_ V) gV ≫ e.hom)
      (pullback.snd (f ∣_ V) gV) (by rw [Category.assoc, he, pullback.condition])
  have hr₁ : r ≫ q = pullback.fst (f ∣_ V) gV ≫ e.hom :=
    pullback.lift_fst _ _ _
  have hr₂ : r ≫ z = pullback.snd (f ∣_ V) gV := pullback.lift_snd _ _ _
  have hrs : r ≫ k = s := by
    apply pullback.hom_ext
    · rw [Category.assoc, hk₁, ← Category.assoc, hr₁, Category.assoc]
      simpa only [e, Iso.symm_hom, pullbackRestrictIsoRestrict_inv_fst] using hs₁.symm
    · rw [Category.assoc, hk₂, hr₂, hs₂]
  have hrt : r ≫ q = t := by
    apply pullback.hom_ext
    · rw [hr₁, Category.assoc, ht₁]
      simp only [e, Iso.symm_hom, pullbackRestrictIsoRestrict_inv_fst]
    · rw [Category.assoc, show q ≫ pullback.snd f V.ι = z ≫ gV from pullback.condition,
        ← Category.assoc, hr₂, ht₂]
  let Fd := (schemeDerivedQCohProperty T).lift
    ((schemeDerivedQCohProperty (pullback (pullback.snd f V.ι) gV)).ι ⋙
      schemeDerivedDirectImage (pullback.snd (pullback.snd f V.ι) gV)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f V.ι) gV))
          _ _ _ _ (pullback.snd (pullback.snd f V.ι) gV) _ _).fst E.obj E.property)
  let : Fd.IsLeftAdjoint :=
    (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f V.ι) gV))
      _ _ _ _ (pullback.snd (pullback.snd f V.ι) gV) _ _).snd
  let d := Fd.rightAdjoint
  let adjd := Adjunction.ofIsLeftAdjoint Fd
  let KV : schemeDerivedQCohCategory V.toScheme :=
    ⟨(derivedPullback V.ι).obj K.obj,
      (derivedPullback_tensor_preserve_QCoh V.ι).1 K.obj K.property⟩
  obtain ⟨hβI, htransport⟩ := rightAdjoint_mate_scheme_iso_transport
    (pullback.snd f V.ι) (f ∣_ V) e he gV aV b d b'
    adjV adjb adjd adjb' hβV KV r hr₁ hr₂
  obtain ⟨eh⟩ := htransport hβI
  obtain ⟨e₀, e₁, e₂, hpaste⟩ := rightAdjoint_mate_successive_baseChange
    f V.ι gV a aV c d adjf adjV adjc adjd hβ hβ₀ hβI K k hk₁ hk₂
  obtain ⟨_, _, _, comp, _⟩ := exists_derivedPullbackComposition.{u, w}
  let cs : derivedPullback k ⋙ derivedPullback r ≅ derivedPullback s :=
    comp r k ≪≫ eqToIso (congrArg (fun v ↦ derivedPullback v) hrs)
  let ct : derivedPullback q ⋙ derivedPullback r ≅ derivedPullback t :=
    comp r q ≪≫ eqToIso (congrArg (fun v ↦ derivedPullback v) hrt)
  let M := Arrow.mk ((schemeDerivedQCohProperty (pullback f (gV ≫ V.ι))).ι.map
    (dualityEquationBaseChangeMap f (gV ≫ V.ι) a c adjf adjc hβ K))
  let N := Arrow.mk ((schemeDerivedQCohProperty (pullback f V.ι)).ι.map
    (dualityEquationBaseChangeMap f V.ι a aV adjf adjV hβ₀ K))
  let eg := (Arrow.isoOfNatIso cs M).symm
  let eo := (Arrow.isoOfNatIso ct N).symm
  apply transport_arrow_factorization eg eo eh
    ((derivedPullback r).mapIso e₀) ((derivedPullback r).mapIso e₁)
    ((derivedPullback r).mapIso e₂)
  simpa only [M, N, KV, q, Functor.map_comp, Arrow.mk_hom, Functor.mapIso_hom,
    Functor.comp_map, Functor.mapArrow] using
    congrArg ((derivedPullback r).map) hpaste

end AlgebraicGeometry
