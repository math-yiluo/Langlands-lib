/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces

/-! # Scalar action on strict étale compact support

Source: Zheng, Construction 4.1; Stacks 09MK, 070I and 015F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry

open Opposite

@[irreducible]
private def scalarSection (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t r : O) (n : ℕ) (U : T.Etaleᵒᵖ) :
    (coefficientQuotientSheaf (J := T.smallEtaleTopology) O t n).obj.obj U :=
  (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
    (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1))))).app U
      (Ideal.Quotient.mk _ r)

private theorem scalarSection_map (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t r : O) (n : ℕ) {U V : T.Etaleᵒᵖ} (h : U ⟶ V) :
    (coefficientQuotientSheaf (J := T.smallEtaleTopology) O t n).obj.map h
      (scalarSection T O t r n U) = scalarSection T O t r n V := by
  unfold scalarSection
  have hn := (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
    (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1))))).naturality h
  exact (ConcreteCategory.congr_hom hn (Ideal.Quotient.mk _ r)).symm

private theorem scalarSection_quotient (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t r : O) {m n : ℕ} (h : n ≤ m) (U : T.Etaleᵒᵖ) :
    (coefficientQuotientMap (J := T.smallEtaleTopology) O t h).hom.app U
      (scalarSection T O t r m U) = scalarSection T O t r n U := by
  unfold scalarSection
  have hn := congr_app (toSheafify_naturality T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).map (CommRingCat.ofHom (show
      (O ⧸ (Ideal.span ({t} : Set O)) ^ (m + 1)) →+*
        (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)) from
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))))) U
  exact (ConcreteCategory.congr_hom hn (Ideal.Quotient.mk _ r)).symm

section GeneralScalar

universe v w
variable {C : Type v} [Category C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

private def sectionScalar (R : Sheaf J CommRingCat.{w})
    (s : ∀ U, R.obj.obj U)
    (hs : ∀ {U V} (f : U ⟶ V), R.obj.map f (s U) = s V)
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    M ⟶ M where
  val := {
    app := fun U ↦ ModuleCat.ofHom (LinearMap.lsmul _ (M.val.obj U) (s U))
    naturality := by
      intro U V f
      ext x
      exact ((M.val.map_smul f (s U) x).trans
        (congrArg (fun a : R.obj.obj V ↦ a • (show M.val.obj V from M.val.map f x))
          (hs f))).symm }

private theorem sectionScalar_naturality (R : Sheaf J CommRingCat.{w})
    (s : ∀ U, R.obj.obj U)
    (hs : ∀ {U V} (f : U ⟶ V), R.obj.map f (s U) = s V)
    (M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (f : M ⟶ N) : f ≫ sectionScalar R s hs N = sectionScalar R s hs M ≫ f := by
  ext U x
  exact ((f.val.app U).hom.map_smul _ _).symm

private theorem sectionScalar_restrict (R R' : Sheaf J CommRingCat.{w})
    (α : R ⟶ R') (s : ∀ U, R.obj.obj U) (s' : ∀ U, R'.obj.obj U)
    (hs : ∀ {U V} (f : U ⟶ V), R.obj.map f (s U) = s V)
    (hs' : ∀ {U V} (f : U ⟶ V), R'.obj.map f (s' U) = s' V)
    (hα : ∀ U, α.hom.app U (s U) = s' U)
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R'))
    (f : M ⟶ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :
    sectionScalar R s hs M ≫ f = f ≫ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).map
        (sectionScalar R' s' hs' N) := by
  ext U x
  change f.val.app U (s U • x) = s' U • (show N.val.obj U from f.val.app U x)
  exact ((f.val.app U).hom.map_smul (s U) x).trans
    (congrArg (fun a : R'.obj.obj U ↦ a • (show N.val.obj U from f.val.app U x)) (hα U))

end GeneralScalar

private def levelScalar (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t r : O) (n : ℕ) (M : strictEtaleLevel T O t n) : M ⟶ M :=
  sectionScalar _ (scalarSection T O t r n) (scalarSection_map T O t r n) M

private theorem system_hom_ext {T : Scheme.{u}} {O : Type (u + 1)}
    [CommRing O] {t : O} {M N : strictEtaleCoefficientSystem T O t}
    (f g : M ⟶ N) (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

private theorem levelScalar_transition (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t r : O) (M : strictEtaleCoefficientSystem T O t) (n : ℕ) :
    levelScalar T O t r (n + 1) (M.level (n + 1)) ≫ M.transition n =
      M.transition n ≫ (coefficientRestriction (J := T.smallEtaleTopology) O t
        (Nat.le_succ n)).map (levelScalar T O t r n (M.level n)) := by
  exact sectionScalar_restrict _ _
    (coefficientQuotientMap (J := T.smallEtaleTopology) O t (Nat.le_succ n))
    (scalarSection T O t r (n + 1)) (scalarSection T O t r n)
    (scalarSection_map T O t r (n + 1)) (scalarSection_map T O t r n)
    (scalarSection_quotient T O t r (Nat.le_succ n)) _ _ (M.transition n)

private theorem levelScalar_naturality (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t r : O) (n : ℕ) (M N : strictEtaleLevel T O t n) (f : M ⟶ N) :
    f ≫ levelScalar T O t r n N = levelScalar T O t r n M ≫ f :=
  sectionScalar_naturality _ _ _ M N f

private def ordinaryScalar (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t r : O) :
    𝟭 (strictEtaleCoefficientSystem T O t) ⟶ 𝟭 _ where
  app M := {
    app := fun n ↦ levelScalar T O t r n (M.level n)
    comm := levelScalar_transition T O t r M }
  naturality M N f := by
    apply system_hom_ext
    funext n
    exact levelScalar_naturality T O t r n (M.level n) (N.level n) (f.app n)

private def derivedScalar (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t r : O) :
    𝟭 (DerivedCategory (strictEtaleCoefficientSystem T O t)) ⟶ 𝟭 _ := by
  let Q := DerivedCategory.Q (C := strictEtaleCoefficientSystem T O t)
  let W := HomologicalComplex.quasiIso (strictEtaleCoefficientSystem T O t) (.up ℤ)
  letI : Localization.Lifting Q W Q (𝟭 _) := ⟨Functor.rightUnitor Q⟩
  exact Localization.liftNatTrans Q W Q Q (𝟭 _) (𝟭 _)
    (whiskerRight ((ordinaryScalar T O t r).mapHomologicalComplex (.up ℤ)) Q)

private theorem derivedScalar_rep (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t r : O) (K : CochainComplex (strictEtaleCoefficientSystem T O t) ℤ) :
    (derivedScalar T O t r).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (((ordinaryScalar T O t r).mapHomologicalComplex (.up ℤ)).app K) := by
  dsimp only [derivedScalar]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Functor.rightUnitor_hom_app,
    Functor.rightUnitor_inv_app, whiskerRight_app, Category.comp_id]
  exact Category.id_comp _

private def scalarAction (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (t : O) :
    StrictEtaleScalarAction T O t :=
  ⟨(ordinaryScalar T O t, derivedScalar T O t),
    ⟨by
      intro r M n U x
      change scalarSection T O t r n U • x = _
      unfold scalarSection
      rfl, derivedScalar_rep T O t⟩⟩

private theorem constantSection_apply (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t r : O) (n : ℕ) (U : T.Etaleᵒᵖ)
    (x : (((constantSheaf T.smallEtaleTopology (Type (u + 1))).obj
      PUnit).obj.obj U)) :
    (coefficientConstantSection (J := T.smallEtaleTopology) O t n
      (Ideal.Quotient.mk _ r)).hom.app U x = scalarSection T O t r n U := by
  let P := (Functor.const T.Etaleᵒᵖ).obj (PUnit : Type (u + 1))
  have hp : Presheaf.IsSheaf T.smallEtaleTopology P :=
    Presheaf.isSheaf_of_isTerminal _ Types.isTerminalPUnit
  have hi := isIso_toSheafify T.smallEtaleTopology hp
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((toSheafify T.smallEtaleTopology P).app U)).surjective x
  let R := coefficientQuotientSheaf (J := T.smallEtaleTopology) O t n
  let B := (sheafCompose T.smallEtaleTopology
    (CategoryTheory.forget CommRingCat.{u + 1})).obj R
  have he := ((sheafificationAdjunction T.smallEtaleTopology (Type (u + 1))).homEquiv
    P B).apply_symm_apply
      ((Functor.const T.Etaleᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦
        (Ideal.Quotient.mk ((Ideal.span ({t} : Set O)) ^ (n + 1)) r))) ≫
        whiskerRight (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)))))
            (CategoryTheory.forget CommRingCat.{u + 1}))
  unfold scalarSection
  exact ConcreteCategory.congr_hom (congr_app he U) y

private theorem inverse_levelScalar
    {O : Type (u + 1)} [CommRing O] {t : O} {X Y : Scheme.{u}} {g : X ⟶ Y}
    (S : StrictEtaleOrdinaryImage O t g) (r : O) (n : ℕ)
    (M : strictEtaleLevel Y O t n) :
    (S.lift n).modules.map (levelScalar Y O t r n M) =
      levelScalar X O t r n ((S.lift n).modules.obj M) := by
  let L := Scheme.etaleSetPullback g
  let B := coefficientUnderlying (J := Y.smallEtaleTopology) O t n
  let BX := coefficientUnderlying (J := X.smallEtaleTopology) O t n
  let A := S.lift n
  let terminal : B.obj M ⟶ (constantSheaf Y.smallEtaleTopology (Type (u + 1))).obj
      PUnit :=
    ⟨(Functor.isTerminalConst _ Types.isTerminalPUnit).from _ ≫
      toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj PUnit)⟩
  let a := terminal ≫ coefficientConstantSection (J := Y.smallEtaleTopology) O t n
    (Ideal.Quotient.mk _ r)
  let b := 𝟙 (B.obj M)
  let tm := B.map (levelScalar Y O t r n M)
  have ha : L.map a ≫ A.ringUnderlying.hom = L.map terminal ≫ S.singleton.hom ≫
      coefficientConstantSection (J := X.smallEtaleTopology) O t n
        (Ideal.Quotient.mk _ r) := by
    dsimp only [a]
    rw [L.map_comp, Category.assoc, S.constants]
  have hm := A.moduleSMul M (B.obj M) a b tm (by
    intro U x
    change scalarSection Y O t r n U • (show M.val.obj U from x) =
      (show (coefficientQuotientSheaf (J := Y.smallEtaleTopology) O t n).obj.obj U from
        a.hom.app U x) • (show M.val.obj U from b.hom.app U x)
    dsimp only [a, b]
    change scalarSection Y O t r n U • (show M.val.obj U from x) =
      (show (coefficientQuotientSheaf (J := Y.smallEtaleTopology) O t n).obj.obj U from
        (coefficientConstantSection (J := Y.smallEtaleTopology) O t n
          (Ideal.Quotient.mk _ r)).hom.app U (terminal.hom.app U x)) •
          (show M.val.obj U from x)
    rw [constantSection_apply])
  apply (BX ⋙ sheafToPresheaf X.smallEtaleTopology (Type (u + 1))).map_injective
  apply (cancel_epi ((A.moduleUnderlying.inv.app M).hom)).mp
  ext U x
  have hn := ConcreteCategory.congr_hom (congr_app
    (congrArg InducedCategory.Hom.hom
      (A.moduleUnderlying.inv.naturality (levelScalar Y O t r n M))) U) x
  change (A.moduleUnderlying.inv.app M).hom.app U ((L.map tm).hom.app U x) = _ at hn
  change ((A.modules.map (levelScalar Y O t r n M)).val.app U)
      ((A.moduleUnderlying.inv.app M).hom.app U x) =
    scalarSection X O t r n U •
      (show ((A.modules.obj M).val.obj U) from
        (A.moduleUnderlying.inv.app M).hom.app U x)
  change (A.moduleUnderlying.inv.app M).hom.app U ((L.map tm).hom.app U x) =
    ((A.modules.map (levelScalar Y O t r n M)).val.app U)
      ((A.moduleUnderlying.inv.app M).hom.app U x) at hn
  rw [← hn]
  trans (show (coefficientQuotientSheaf (J := X.smallEtaleTopology) O t n).obj.obj U from
    A.ringUnderlying.hom.hom.app U ((L.map a).hom.app U x)) •
    (show ((A.modules.obj M).val.obj U) from
      (A.moduleUnderlying.inv.app M).hom.app U ((L.map b).hom.app U x))
  · exact hm U x
  have hc := ConcreteCategory.congr_hom (congr_app (congrArg InducedCategory.Hom.hom ha) U) x
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply] at hc
  rw [constantSection_apply] at hc
  rw [hc]
  congr 1
  change (A.moduleUnderlying.inv.app M).hom.app U ((L.map (𝟙 _)).hom.app U x) = _
  rw [L.map_id]
  rfl

private theorem inverse_ordinaryScalar
    {O : Type (u + 1)} [CommRing O] {t : O} {X Y : Scheme.{u}} {g : X ⟶ Y}
    (S : StrictEtaleOrdinaryImage O t g) (r : O)
    (M : strictEtaleCoefficientSystem Y O t) :
    S.inverse.map ((ordinaryScalar Y O t r).app M) =
      (ordinaryScalar X O t r).app (S.inverse.obj M) := by
  apply system_hom_ext
  funext n
  apply (cancel_mono ((S.inverseEvaluation n).hom.app M)).mp
  have hn := (S.inverseEvaluation n).hom.naturality ((ordinaryScalar Y O t r).app M)
  change _ = (S.inverseEvaluation n).hom.app M ≫
    (S.lift n).modules.map (levelScalar Y O t r n (M.level n)) at hn
  change (S.inverse.map ((ordinaryScalar Y O t r).app M)).app n ≫
    (S.inverseEvaluation n).hom.app M = _ at hn
  calc
    _ = (S.inverseEvaluation n).hom.app M ≫
        (S.lift n).modules.map (levelScalar Y O t r n (M.level n)) := hn
    _ = (S.inverseEvaluation n).hom.app M ≫
        levelScalar X O t r n ((S.lift n).modules.obj (M.level n)) := by
      exact congrArg (fun k ↦ (S.inverseEvaluation n).hom.app M ≫ k)
        (inverse_levelScalar S r n (M.level n))
    _ = _ := levelScalar_naturality X O t r n _ _ ((S.inverseEvaluation n).hom.app M)

private theorem adjoint_preserves_right
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) (a : 𝟭 A ⟶ 𝟭 A) (b : 𝟭 B ⟶ 𝟭 B)
    (h : ∀ M, F.map (a.app M) = b.app (F.obj M)) (N : B) :
    G.map (b.app N) = a.app (G.obj N) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [h]
  exact (adj.counit.naturality (b.app N)).trans
    (b.naturality (adj.counit.app N))

private theorem adjoint_preserves_left
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) (a : 𝟭 A ⟶ 𝟭 A) (b : 𝟭 B ⟶ 𝟭 B)
    (h : ∀ N, G.map (b.app N) = a.app (G.obj N)) (M : A) :
    F.map (a.app M) = b.app (F.obj M) := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [h]
  exact (adj.unit.naturality (a.app M)).symm.trans
    (a.naturality (adj.unit.app M)).symm

private theorem exact_preserves_scalar
    {O : Type (u + 1)} [CommRing O] {t : O} {X Y : Scheme.{u}}
    (F : strictEtaleCoefficientSystem X O t ⥤ strictEtaleCoefficientSystem Y O t)
    [F.Additive]
    (FD : DerivedCategory (strictEtaleCoefficientSystem X O t) ⥤
      DerivedCategory (strictEtaleCoefficientSystem Y O t))
    (e : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (a : StrictEtaleScalarAction X O t) (b : StrictEtaleScalarAction Y O t)
    (h : ∀ r M, F.map ((a.val.1 r).app M) = (b.val.1 r).app (F.obj M))
    (r : O) (M : DerivedCategory (strictEtaleCoefficientSystem X O t)) :
    FD.map ((a.derived r).app M) = (b.derived r).app (FD.obj M) := by
  have he : whiskerRight (a.derived r) FD = whiskerLeft FD (b.derived r) := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleCoefficientSystem X O t) (.up ℤ))
    intro K
    change FD.map ((a.derived r).app (DerivedCategory.Q.obj K)) = _
    rw [a.property.2]
    apply (cancel_mono (e.hom.app K)).mp
    have hc : (F.mapHomologicalComplex (.up ℤ)).map
        (((a.val.1 r).mapHomologicalComplex (.up ℤ)).app K) =
        ((b.val.1 r).mapHomologicalComplex (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
      ext i
      exact h r (K.X i)
    calc
      _ = e.hom.app K ≫ DerivedCategory.Q.map
          ((F.mapHomologicalComplex (.up ℤ)).map
            (((a.val.1 r).mapHomologicalComplex (.up ℤ)).app K)) :=
        e.hom.naturality _
      _ = e.hom.app K ≫ (b.derived r).app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) := by
        rw [hc, b.property.2]
      _ = (b.derived r).app (FD.obj (DerivedCategory.Q.obj K)) ≫ e.hom.app K :=
        (b.derived r).naturality _
  exact congr_app he M

/-- The canonical coefficient action on source and target derived systems is preserved
by ordinary étale compact support.
Source: Zheng, Construction 4.1; Stacks 09MK, 070I and 015F
(blueprint: lem-pur-etale-compact-support-scalar-action).

Proof: on an ordinary system multiply each section at level n by the image of r in
O/(t^(n+1)) under the constant-ring sheafification unit. Naturality of that unit and
semilinearity of the transition maps make these maps a system endomorphism, natural
in the system. Apply this natural endomorphism termwise to complexes and descend
through the quasi-isomorphism localization. This gives the derived natural
endomorphism, with exactly the representative equation in StrictEtaleScalarAction.
Extension by zero preserves it on sections, since it uses the same section maps and
zero outside the open. Ordinary direct image preserves it by its normalized constant
coefficient comparison. The open derived factorization therefore preserves the
derived action by the universal property of localization. For proper direct image,
compute on K-injective resolutions: the ordinary scalar endomorphism of a resolution
represents the derived scalar endomorphism, and the normalized direct-derived unit
is natural in it. The universal property of the right derived functor extends this
identity from the resolution models to every object. Composing the two identities
and the normalized factorization isomorphisms gives the displayed equation for S. -/
theorem etaleCompactSupport_scalarAction
    {O : Type (u + 1)} [CommRing O] {t : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O t c) :
    ∃ (scalarX : StrictEtaleScalarAction X O t)
      (scalarY : StrictEtaleScalarAction Y O t),
      ∀ r K, S.functor.map ((scalarX.derived r).app K) =
        (scalarY.derived r).app (S.functor.obj K) := by
  -- The normalized inverse images preserve scalars. Naturality of the derived
  -- adjunctions transfers this to both factors of compact support.
  let aX := scalarAction X O t
  let aY := scalarAction Y O t
  let aZ := scalarAction c.Z O t
  have hi (r : O) (M : DerivedCategory (strictEtaleCoefficientSystem c.Z O t)) :
      S.openDerived.system.inverse.map ((aZ.derived r).app M) =
        (aX.derived r).app (S.openDerived.system.inverse.obj M) :=
    exact_preserves_scalar S.openImage.inverse S.openDerived.system.inverse
      S.openDerived.system.inverseFactors aZ aX
      (inverse_ordinaryScalar S.openImage) r M
  have ho (r : O) (M : DerivedCategory (strictEtaleCoefficientSystem X O t)) :
      S.derivedOpen.map ((aX.derived r).app M) =
        (aZ.derived r).app (S.derivedOpen.obj M) :=
    adjoint_preserves_left S.derivedOpenAdjunction (aX.derived r) (aZ.derived r) (hi r) M
  have hp (r : O) (M : DerivedCategory (strictEtaleCoefficientSystem Y O t)) :
      S.properDerived.system.inverse.map ((aY.derived r).app M) =
        (aZ.derived r).app (S.properDerived.system.inverse.obj M) :=
    exact_preserves_scalar S.properImage.inverse S.properDerived.system.inverse
      S.properDerived.system.inverseFactors aY aZ
      (inverse_ordinaryScalar S.properImage) r M
  refine ⟨aX, aY, ?_⟩
  intro r K
  change S.properDerived.system.direct.map (S.derivedOpen.map ((aX.derived r).app K)) = _
  rw [ho]
  exact adjoint_preserves_right S.properDerived.system.adjunction
    (aY.derived r) (aZ.derived r) (hp r) _

end AlgebraicGeometry
