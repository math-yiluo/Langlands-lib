/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces

/-! # Scalar actions for exceptional pro-etale operations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vC uC vD uD w d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

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
    {A : Type uC} [Category.{vC} A] [Abelian A] [HasDerivedCategory.{d} A]
    {B : Type uD} [Category.{vD} B] [Abelian B] [HasDerivedCategory.{d} B]
    (F : A ⥤ B) [F.Additive] (FD : DerivedCategory A ⥤ DerivedCategory B)
    (e : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (a : 𝟭 A ⟶ 𝟭 A) (b : 𝟭 B ⟶ 𝟭 B)
    (ad : 𝟭 (DerivedCategory A) ⟶ 𝟭 _) (bd : 𝟭 (DerivedCategory B) ⟶ 𝟭 _)
    (arep : ∀ K, ad.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app K))
    (brep : ∀ K, bd.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).app K))
    (h : ∀ M, F.map (a.app M) = b.app (F.obj M)) (M : DerivedCategory A) :
    FD.map (ad.app M) = bd.app (FD.obj M) := by
  have he : whiskerRight ad FD = whiskerLeft FD bd := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro K
    change FD.map (ad.app (DerivedCategory.Q.obj K)) = _
    rw [arep]
    apply (cancel_mono (e.hom.app K)).mp
    have hc : (F.mapHomologicalComplex (.up ℤ)).map
        ((a.mapHomologicalComplex (.up ℤ)).app K) =
        (b.mapHomologicalComplex (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
      ext i
      exact h (K.X i)
    calc
      _ = e.hom.app K ≫ DerivedCategory.Q.map
          ((F.mapHomologicalComplex (.up ℤ)).map
            ((a.mapHomologicalComplex (.up ℤ)).app K)) := e.hom.naturality _
      _ = e.hom.app K ≫ bd.app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) := by
        rw [hc, brep]
      _ = bd.app (FD.obj (DerivedCategory.Q.obj K)) ≫ e.hom.app K := bd.naturality _
  exact congr_app he M

section GeneralScalar

universe v
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
      change s V • (show M.val.obj V from M.val.map f x) = M.val.map f (s U • x)
      rw [M.val.map_smul]
      congr 1
      exact (hs f).symm }

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

section ScalarConstruction
variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]

@[irreducible]
private def scalarSection (O : Type w)
    [CommRing O] (t r : O) (n : ℕ) (U : Cᵒᵖ) :
    (coefficientQuotientSheaf (J := J) O t n).obj.obj U :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj
    (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1))))).app U
      (Ideal.Quotient.mk _ r)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem scalarSection_map (O : Type w)
    [CommRing O] (t r : O) (n : ℕ) {U V : Cᵒᵖ} (h : U ⟶ V) :
    (coefficientQuotientSheaf (J := J) O t n).obj.map h
      (scalarSection J O t r n U) = scalarSection J O t r n V := by
  unfold scalarSection
  have hn := (toSheafify J ((Functor.const Cᵒᵖ).obj
    (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1))))).naturality h
  exact (ConcreteCategory.congr_hom hn (Ideal.Quotient.mk _ r)).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem scalarSection_quotient (O : Type w)
    [CommRing O] (t r : O) {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) :
    (coefficientQuotientMap (J := J) O t h).hom.app U
      (scalarSection J O t r m U) = scalarSection J O t r n U := by
  unfold scalarSection
  have hn := congr_app (toSheafify_naturality J
    ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom (show
      (O ⧸ (Ideal.span ({t} : Set O)) ^ (m + 1)) →+*
        (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)) from
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))))) U
  exact (ConcreteCategory.congr_hom hn (Ideal.Quotient.mk _ r)).symm

private def levelScalar (O : Type w)
    [CommRing O] (t r : O) (n : ℕ) (M : coefficientLevelModules (J := J) O t n) : M ⟶ M :=
  sectionScalar _ (scalarSection J O t r n) (scalarSection_map J O t r n) M

private theorem system_hom_ext {O : Type w}
    [CommRing O] {t : O} {M N : CoefficientSystem (J := J) O t}
    (f g : M ⟶ N) (h : f.app = g.app) : f = g := by
  cases f using CoefficientSystem.Hom.rec
  cases g using CoefficientSystem.Hom.rec
  cases h
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem levelScalar_transition (O : Type w)
    [CommRing O] (t r : O) (M : CoefficientSystem (J := J) O t) (n : ℕ) :
    levelScalar J O t r (n + 1) (M.level (n + 1)) ≫ M.transition n =
      M.transition n ≫ (coefficientRestriction (J := J) O t
        (Nat.le_succ n)).map (levelScalar J O t r n (M.level n)) := by
  exact sectionScalar_restrict _ _
    (coefficientQuotientMap (J := J) O t (Nat.le_succ n))
    (scalarSection J O t r (n + 1)) (scalarSection J O t r n)
    (scalarSection_map J O t r (n + 1)) (scalarSection_map J O t r n)
    (scalarSection_quotient J O t r (Nat.le_succ n)) _ _ (M.transition n)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem levelScalar_naturality (O : Type w)
    [CommRing O] (t r : O) (n : ℕ) (M N : coefficientLevelModules (J := J) O t n) (f : M ⟶ N) :
    f ≫ levelScalar J O t r n N = levelScalar J O t r n M ≫ f :=
  sectionScalar_naturality _ _ _ M N f

private def ordinaryScalar (O : Type w)
    [CommRing O] (t r : O) :
    𝟭 (CoefficientSystem (J := J) O t) ⟶ 𝟭 _ where
  app M := {
    app := fun n ↦ levelScalar J O t r n (M.level n)
    comm := levelScalar_transition J O t r M }
  naturality M N f := by
    apply system_hom_ext
    funext n
    exact levelScalar_naturality J O t r n (M.level n) (N.level n) (f.app n)

private def derivedScalar (O : Type w)
    [CommRing O] (t r : O)
    [HasDerivedCategory.{d} (CoefficientSystem (J := J) O t)] :
    𝟭 (DerivedCategory (CoefficientSystem (J := J) O t)) ⟶ 𝟭 _ := by
  let Q := DerivedCategory.Q (C := CoefficientSystem (J := J) O t)
  let W := HomologicalComplex.quasiIso (CoefficientSystem (J := J) O t) (.up ℤ)
  letI : Localization.Lifting Q W Q (𝟭 _) := ⟨Functor.rightUnitor Q⟩
  exact Localization.liftNatTrans Q W Q Q (𝟭 _) (𝟭 _)
    (whiskerRight ((ordinaryScalar J O t r).mapHomologicalComplex (.up ℤ)) Q)

private theorem derivedScalar_rep (O : Type w)
    [CommRing O] (t r : O)
    [HasDerivedCategory.{d} (CoefficientSystem (J := J) O t)]
    (K : CochainComplex (CoefficientSystem (J := J) O t) ℤ) :
    (derivedScalar J O t r).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (((ordinaryScalar J O t r).mapHomologicalComplex (.up ℤ)).app K) := by
  dsimp only [derivedScalar]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Functor.rightUnitor_hom_app,
    Functor.rightUnitor_inv_app, whiskerRight_app, Category.comp_id]
  exact Category.id_comp _

variable [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
private theorem constantSection_apply (O : Type w)
    [CommRing O] (t r : O) (n : ℕ) (U : Cᵒᵖ)
    (x : (((constantSheaf J (Type w)).obj
      PUnit).obj.obj U)) :
    (coefficientConstantSection (J := J) O t n
      (Ideal.Quotient.mk _ r)).hom.app U x = scalarSection J O t r n U := by
  let P := (Functor.const Cᵒᵖ).obj (PUnit : Type w)
  have hp : Presheaf.IsSheaf J P :=
    Presheaf.isSheaf_of_isTerminal _ Types.isTerminalPUnit
  have hi := isIso_toSheafify J hp
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((toSheafify J P).app U)).surjective x
  let R := coefficientQuotientSheaf (J := J) O t n
  let B := (sheafCompose J
    (CategoryTheory.forget CommRingCat.{w})).obj R
  have he := ((sheafificationAdjunction J (Type w)).homEquiv
    P B).apply_symm_apply
      ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{w + 1}) ↦
        (Ideal.Quotient.mk ((Ideal.span ({t} : Set O)) ^ (n + 1)) r))) ≫
        whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj
          (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)))))
            (CategoryTheory.forget CommRingCat.{w}))
  unfold scalarSection
  exact ConcreteCategory.congr_hom (congr_app he U) y

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] (K : GrothendieckTopology D)
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
  {V : Sheaf K (Type w) ⥤ Sheaf J (Type w)} (adj : L ⊣ V)

private theorem inverse_levelScalar
    {O : Type w} [CommRing O] {t : O}
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O t L V adj) (r : O) (n : ℕ)
    (M : coefficientLevelModules (J := J) O t n) :
    (S.lift n).modules.map (levelScalar J O t r n M) =
      levelScalar K O t r n ((S.lift n).modules.obj M) := by
  let B := coefficientUnderlying (J := J) O t n
  let BX := coefficientUnderlying (J := K) O t n
  let A := S.lift n
  let terminal : B.obj M ⟶ (constantSheaf J (Type w)).obj
      PUnit :=
    ⟨(Functor.isTerminalConst _ Types.isTerminalPUnit).from _ ≫
      toSheafify J ((Functor.const Cᵒᵖ).obj PUnit)⟩
  let a := terminal ≫ coefficientConstantSection (J := J) O t n
    (Ideal.Quotient.mk _ r)
  let b := 𝟙 (B.obj M)
  let tm := B.map (levelScalar J O t r n M)
  have ha : L.map a ≫ A.ringUnderlying.hom = L.map terminal ≫ S.singleton.hom ≫
      coefficientConstantSection (J := K) O t n
        (Ideal.Quotient.mk _ r) := by
    dsimp only [a]
    rw [L.map_comp, Category.assoc, S.constants]
  have hm := A.moduleSMul M (B.obj M) a b tm (by
    intro U x
    change scalarSection J O t r n U • (show M.val.obj U from x) =
      (show (coefficientQuotientSheaf (J := J) O t n).obj.obj U from a.hom.app U x) •
        (show M.val.obj U from b.hom.app U x)
    dsimp only [a, b]
    change scalarSection J O t r n U • (show M.val.obj U from x) =
      (show (coefficientQuotientSheaf (J := J) O t n).obj.obj U from
        (coefficientConstantSection (J := J) O t n
          (Ideal.Quotient.mk _ r)).hom.app U (terminal.hom.app U x)) •
        (show M.val.obj U from x)
    rw [constantSection_apply])
  apply (BX ⋙ sheafToPresheaf K (Type w)).map_injective
  apply (cancel_epi ((A.moduleUnderlying.inv.app M).hom)).mp
  ext U x
  have hn := ConcreteCategory.congr_hom (congr_app
    (congrArg InducedCategory.Hom.hom
      (A.moduleUnderlying.inv.naturality (levelScalar J O t r n M))) U) x
  change (A.moduleUnderlying.inv.app M).hom.app U ((L.map tm).hom.app U x) = _ at hn
  change ((A.modules.map (levelScalar J O t r n M)).val.app U)
      ((A.moduleUnderlying.inv.app M).hom.app U x) =
    scalarSection K O t r n U •
      (show ((A.modules.obj M).val.obj U) from
        (A.moduleUnderlying.inv.app M).hom.app U x)
  change (A.moduleUnderlying.inv.app M).hom.app U ((L.map tm).hom.app U x) =
    ((A.modules.map (levelScalar J O t r n M)).val.app U)
      ((A.moduleUnderlying.inv.app M).hom.app U x) at hn
  rw [← hn]
  trans (show (coefficientQuotientSheaf (J := K) O t n).obj.obj U from
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
    {O : Type w} [CommRing O] {t : O}
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O t L V adj) (r : O)
    (M : CoefficientSystem (J := J) O t) :
    S.inverse.map ((ordinaryScalar J O t r).app M) =
      (ordinaryScalar K O t r).app (S.inverse.obj M) := by
  apply system_hom_ext
  funext n
  apply (cancel_mono ((S.inverseEvaluation n).hom.app M)).mp
  have hn := (S.inverseEvaluation n).hom.naturality ((ordinaryScalar J O t r).app M)
  change _ = (S.inverseEvaluation n).hom.app M ≫
    (S.lift n).modules.map (levelScalar J O t r n (M.level n)) at hn
  change (S.inverse.map ((ordinaryScalar J O t r).app M)).app n ≫
    (S.inverseEvaluation n).hom.app M = _ at hn
  calc
    _ = (S.inverseEvaluation n).hom.app M ≫
        (S.lift n).modules.map (levelScalar J O t r n (M.level n)) := hn
    _ = (S.inverseEvaluation n).hom.app M ≫
        levelScalar K O t r n ((S.lift n).modules.obj (M.level n)) := by
      exact congrArg (fun k ↦ (S.inverseEvaluation n).hom.app M ≫ k)
        (inverse_levelScalar J K adj S r n (M.level n))
    _ = _ := levelScalar_naturality K O t r n _ _ ((S.inverseEvaluation n).hom.app M)

private theorem inverse_derivedScalar
    {O : Type w} [CommRing O] {t : O}
    [HasDerivedCategory.{d} (CoefficientSystem (J := J) O t)]
    [HasDerivedCategory.{d} (CoefficientSystem (J := K) O t)]
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O t L V adj)
    (FD : DerivedCategory (CoefficientSystem (J := J) O t) ⥤
      DerivedCategory (CoefficientSystem (J := K) O t))
    (e : DerivedCategory.Q ⋙ FD ≅ S.inverse.mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q) (r : O) (M : DerivedCategory (CoefficientSystem (J := J) O t)) :
    FD.map ((derivedScalar J O t r).app M) =
      (derivedScalar K O t r).app (FD.obj M) :=
  exact_preserves_scalar S.inverse FD e (ordinaryScalar J O t r) (ordinaryScalar K O t r)
    (derivedScalar J O t r) (derivedScalar K O t r)
    (derivedScalar_rep J O t r) (derivedScalar_rep K O t r)
    (inverse_ordinaryScalar J K adj S r) M

end ScalarConstruction

private def proScalarAction (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (t : O) :
    ExceptionalProScalarAction T O t where
  ordinary := ordinaryScalar (Scheme.ProEt.topology T) O t
  derived := fun r ↦ derivedScalar (Scheme.ProEt.topology T) O t r
  ordinaryNormalized := by
    intro r M n U x
    change scalarSection (Scheme.ProEt.topology T) O t r n U • x = _
    unfold scalarSection
    rfl
  representative := fun r K ↦ derivedScalar_rep (Scheme.ProEt.topology T) O t r K

private theorem etaleScalar_unique (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t : O) (a : StrictEtaleScalarAction T O t) (r : O) :
    a.derived r = derivedScalar T.smallEtaleTopology O t r := by
  have h : a.val.1 r = ordinaryScalar T.smallEtaleTopology O t r := by
    apply NatTrans.ext
    funext M
    apply system_hom_ext
    funext n
    ext U x
    change (((a.val.1 r).app M).app n).val.app U x =
      scalarSection T.smallEtaleTopology O t r n U • x
    unfold scalarSection
    exact a.property.1 r M n U x
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (strictEtaleCoefficientSystem T O t) (.up ℤ))
  intro K
  rw [a.property.2, h]
  exact (derivedScalar_rep T.smallEtaleTopology O t r K).symm

variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (G : StrictEtaleExceptionalAdjoint O ell c S)
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)
  (P : ExceptionalProCompactSupport O ell c
    CX.proEvaluation CY.proEvaluation CZ.proEvaluation)

/-- Canonical scalar actions on the pro-etale compact-support and transported right
functors, together with their compatibility equations.
Source: Zheng Proposition 2.29(2), Construction 5.15 and Lemma 5.22.
(blueprint: lem-sf-exceptional-pro-origin-scalar-actions).

Proof: define multiplication by the image of each scalar on every quotient
coefficient sheaf and localize the resulting ordinary natural transformations.
The inverse-image, open-extension, proper-derived and etale right-adjoint
comparison equations transport these transformations through the two composites.
The localization universal property upgrades the representative equalities to
all derived objects, yielding both displayed linearity equations. -/
theorem exceptionalProScalarActions :
    ∃ (scalarX : ExceptionalProScalarAction X O ell)
      (scalarY : ExceptionalProScalarAction Y O ell),
      (∀ r M, (exceptionalProSupport P).map ((scalarX.derived r).app M) =
        (scalarY.derived r).app ((exceptionalProSupport P).obj M)) ∧
      (∀ r N, (exceptionalSystemRight G CX CY).map ((scalarY.derived r).app N) =
        (scalarX.derived r).app ((exceptionalSystemRight G CX CY).obj N)) := by
  let aX := proScalarAction X O ell
  let aY := proScalarAction Y O ell
  let aZ := proScalarAction c.Z O ell
  have hi (r : O) (M : DerivedCategory
      (CoefficientSystem (J := Scheme.ProEt.topology c.Z) O ell)) :
      P.val.openDerived.system.inverse.map ((aZ.derived r).app M) =
        (aX.derived r).app (P.val.openDerived.system.inverse.obj M) :=
    inverse_derivedScalar _ _ _ P.val.openImage P.val.openDerived.system.inverse
      P.val.openDerived.system.inverseFactors r M
  have ho (r : O) (M : DerivedCategory
      (CoefficientSystem (J := Scheme.ProEt.topology X) O ell)) :
      P.val.derivedOpen.map ((aX.derived r).app M) =
        (aZ.derived r).app (P.val.derivedOpen.obj M) :=
    adjoint_preserves_left P.val.derivedOpenAdjunction (aX.derived r) (aZ.derived r) (hi r) M
  have hp (r : O) (M : DerivedCategory
      (CoefficientSystem (J := Scheme.ProEt.topology Y) O ell)) :
      P.val.properDerived.system.inverse.map ((aY.derived r).app M) =
        (aZ.derived r).app (P.val.properDerived.system.inverse.obj M) :=
    inverse_derivedScalar _ _ _ P.val.properImage P.val.properDerived.system.inverse
      P.val.properDerived.system.inverseFactors r M
  have hCX (r : O) (M : DerivedCategory (strictEtaleCoefficientSystem X O ell)) :
      CX.image.system.inverse.map
          ((derivedScalar X.smallEtaleTopology O ell r).app M) =
        (aX.derived r).app (CX.image.system.inverse.obj M) :=
    inverse_derivedScalar _ _ _ CX.ordinary CX.image.system.inverse
      CX.image.system.inverseFactors r M
  have hCY (r : O) (M : DerivedCategory (strictEtaleCoefficientSystem Y O ell)) :
      CY.image.system.inverse.map
          ((derivedScalar Y.smallEtaleTopology O ell r).app M) =
        (aY.derived r).app (CY.image.system.inverse.obj M) :=
    inverse_derivedScalar _ _ _ CY.ordinary CY.image.system.inverse
      CY.image.system.inverseFactors r M
  have hG (r : O) (M : DerivedCategory (strictEtaleCoefficientSystem Y O ell)) :
      G.right.map ((derivedScalar Y.smallEtaleTopology O ell r).app M) =
        (derivedScalar X.smallEtaleTopology O ell r).app (G.right.obj M) := by
    have h := G.property.2.1 r M
    rw [etaleScalar_unique, etaleScalar_unique] at h
    exact h
  refine ⟨aX, aY, ?_, ?_⟩
  · intro r M
    change P.val.properDerived.system.direct.map
      (P.val.derivedOpen.map ((aX.derived r).app M)) = _
    rw [ho]
    exact adjoint_preserves_right P.val.properDerived.system.adjunction
      (aY.derived r) (aZ.derived r) (hp r) _
  · intro r N
    have h := adjoint_preserves_right CY.image.system.adjunction
      (derivedScalar Y.smallEtaleTopology O ell r) (aY.derived r) (hCY r) N
    change CX.image.system.inverse.map (G.right.map
      (CY.image.system.direct.map ((aY.derived r).app N))) = _
    rw [h, hG]
    exact hCX r _

end AlgebraicGeometry
