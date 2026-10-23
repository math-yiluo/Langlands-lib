import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackStatements
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u

noncomputable section

namespace Langlands.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

section Scalar

/-- Pushforward turns multiplication by a pulled-back global function into multiplication
by the function itself. -/
lemma pushforward_map_appTop_smul (f : X ⟶ Y) {M N : X.Modules} (r : Γ(Y, ⊤))
    (φ : M ⟶ N) :
    (AlgebraicGeometry.Scheme.Modules.pushforward f).map (f.appTop r • φ) =
      r • (AlgebraicGeometry.Scheme.Modules.pushforward f).map φ := by
  ext U x
  change restrictScalar (f ⁻¹ᵁ U) (f.appTop r) • φ.app (f ⁻¹ᵁ U) x =
    f.app U (restrictScalar U r) • φ.app (f ⁻¹ᵁ U) x
  congr 1
  exact (ConcreteCategory.congr_hom
    (f.naturality (homOfLE le_top : U ⟶ ⊤).op) r).symm

/-- Pullback of module sheaves is semilinear for global scalars. -/
lemma pullback_map_smul (f : X ⟶ Y) {M N : Y.Modules} (r : Γ(Y, ⊤)) (φ : M ⟶ N) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map (r • φ) =
      f.appTop r • (AlgebraicGeometry.Scheme.Modules.pullback f).map φ := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pushforward_map_appTop_smul,
    Linear.comp_smul, Adjunction.unit_naturality, Adjunction.unit_naturality, Linear.smul_comp]

/-- The local scalar on `U`, viewed as a global function on the open subscheme. -/
abbrev openScalar (U : Y.Opens) (r : Γ(Y, U)) : Γ(U.toScheme, ⊤) :=
  U.topIso.inv r

/-- Scalar multiplication of local morphisms is scalar multiplication on the open subscheme. -/
lemma internalHomSectionsEquiv_smul (M N : Y.Modules) (U : Y.Opens) (r : Γ(Y, U))
    (h : LocalHom M N U) :
    internalHomSectionsEquiv M N U (r • h) =
      openScalar U r • internalHomSectionsEquiv M N U h := by
  ext W x
  change Y.presheaf.map (homOfLE (U.ι_image_le W)).op r •
      (LocalHom.app h (homOfLE (U.ι_image_le W)) x : Γ(N, U.ι ''ᵁ W)) =
    (U.ι.appIso W).inv (restrictScalar W (openScalar U r)) •
      (LocalHom.app h (homOfLE (U.ι_image_le W)) x : Γ(N, U.ι ''ᵁ W))
  congr 1
  rw [Scheme.Opens.ι_appIso]
  change _ = Y.presheaf.map _ (Y.presheaf.map _ r)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting a morphism to an inverse-image open sends the local scalar to its pullback. -/
lemma morphismRestrict_appTop_openScalar (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    (f ∣_ U).appTop (openScalar U r) = openScalar (f ⁻¹ᵁ U) (f.app U r) := by
  have key : U.topIso.inv ≫ (f ∣_ U).appTop = f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := by
    rw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv,
      ← Category.assoc, Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom key r

lemma localHomPullback_smul : LocalHomPullbackScalarStatement.{u} := by
  intro X Y f M N U r h
  apply (internalHomSectionsEquiv _ _ _).injective
  rw [internalHomSectionsEquiv_localHomPullback, internalHomSectionsEquiv_smul,
    internalHomSectionsEquiv_smul, internalHomSectionsEquiv_localHomPullback,
    pullback_map_smul, Linear.smul_comp, Linear.comp_smul, morphismRestrict_appTop_openScalar]

end Scalar

section Restriction

open AlgebraicGeometry.Scheme.Modules (pullback pushforward pullbackComp pullbackCongr
  restrictFunctor restrictFunctorIsoPullback restrictFunctorComp restrictFunctorCongr
  restrictAdjunction pullbackPushforwardAdjunction pushforwardComp)
open Langlands.SchemeModule.RigidifiedModule (compHom compHom_assoc compHom_rfl)

/-- Parallel restriction maps of a presheaf on opens agree. -/
lemma presheaf_map_subsingleton {T : AlgebraicGeometry.Scheme.{u}} {D : Type*} [Category* D]
    (F : T.Opensᵒᵖ ⥤ D) {P Q : T.Opensᵒᵖ} (p q : P ⟶ Q) : F.map p = F.map q := by
  rw [show p = q from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

instance compHom_isIso {A B C : AlgebraicGeometry.Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (N : C.Modules) : IsIso (compHom a b c h N) := by
  unfold compHom
  infer_instance

/-- Conjugating a morphism through two ways around a square of functors gives the same result,
provided the two conjugating isomorphisms agree on source and target. -/
lemma conjugate_square {C D₁ D₂ E : Type*} [Category* C] [Category* D₁] [Category* D₂]
    [Category* E] {F₁ : C ⥤ D₁} {G₁ : D₁ ⥤ E} {F₂ : C ⥤ D₂} {G₂ : D₂ ⥤ E}
    (e : F₂ ⋙ G₂ ≅ F₁ ⋙ G₁) {A B : C} (k : A ⟶ B) {P₁ Q₁ : D₁} {P₂ Q₂ : D₂} {S T : E}
    (r₁ : P₁ ≅ F₁.obj A) (s₁ : Q₁ ≅ F₁.obj B) (r₂ : P₂ ≅ F₂.obj A) (s₂ : Q₂ ≅ F₂.obj B)
    (t₁ : S ≅ G₁.obj P₁) (u₁ : T ≅ G₁.obj Q₁) (t₂ : S ≅ G₂.obj P₂) (u₂ : T ≅ G₂.obj Q₂)
    (hA : t₁.hom ≫ G₁.map r₁.hom = t₂.hom ≫ G₂.map r₂.hom ≫ e.hom.app A)
    (hB : u₁.hom ≫ G₁.map s₁.hom = u₂.hom ≫ G₂.map s₂.hom ≫ e.hom.app B) :
    t₁.hom ≫ G₁.map (r₁.hom ≫ F₁.map k ≫ s₁.inv) ≫ u₁.inv =
      t₂.hom ≫ G₂.map (r₂.hom ≫ F₂.map k ≫ s₂.inv) ≫ u₂.inv := by
  have hB' : e.hom.app B ≫ G₁.map s₁.inv ≫ u₁.inv = G₂.map s₂.inv ≫ u₂.inv := by
    rw [← cancel_epi (u₂.hom ≫ G₂.map s₂.hom)]
    simp only [Category.assoc]
    rw [← reassoc_of% hB]
    simp
  have hn := e.hom.naturality k
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hA, ← reassoc_of% hn, hB']

/-- The comparison `a^* b^* ⟶ c^*` is natural in the module. -/
@[reassoc]
lemma compHom_naturality {A B C : AlgebraicGeometry.Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) {N N' : C.Modules} (g : N ⟶ N') :
    compHom a b c h N ≫ (pullback c).map g =
      (pullback a).map ((pullback b).map g) ≫ compHom a b c h N' := by
  subst h
  rw [compHom_rfl, compHom_rfl]
  exact ((pullbackComp a b).hom.naturality g).symm

section OpenImmersions

variable {A B C : AlgebraicGeometry.Scheme.{u}}

/-- Restriction along an open immersion factored as `a ≫ b = c` is iterated restriction. -/
def restrictCompIso (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c] :
    restrictFunctor c ≅ restrictFunctor b ⋙ restrictFunctor a :=
  restrictFunctorCongr h.symm ≪≫ restrictFunctorComp a b

lemma restrictFunctor_map_app (a : A ⟶ B) [IsOpenImmersion a] {M N : B.Modules}
    (φ : M ⟶ N) (W : A.Opens) :
    ((restrictFunctor a).map φ).app W = φ.app (a ''ᵁ W) := rfl

/-- The restriction unit composed with the comparison to pullback is the pullback unit. -/
@[reassoc]
lemma restrictAdjunction_unit_restrictFunctorIsoPullback (a : A ⟶ B) [IsOpenImmersion a]
    (M : B.Modules) :
    (restrictAdjunction a).unit.app M ≫
        (pushforward a).map ((restrictFunctorIsoPullback a).hom.app M) =
      (pullbackPushforwardAdjunction a).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

/-- The unit of restriction along a composite, followed by iterated restriction. -/
lemma restrictAdjunction_unit_restrictCompIso (a : A ⟶ B) (b : B ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b] (M : C.Modules) :
    (restrictAdjunction (a ≫ b)).unit.app M ≫
        (pushforward (a ≫ b)).map ((restrictCompIso a b (a ≫ b) rfl).hom.app M) =
      (restrictAdjunction b).unit.app M ≫
        (pushforward b).map ((restrictAdjunction a).unit.app ((restrictFunctor b).obj M)) ≫
        (pushforwardComp a b).hom.app ((restrictFunctor a).obj ((restrictFunctor b).obj M)) := by
  ext U : 1
  simp only [restrictCompIso, Iso.trans_hom, NatTrans.comp_app,
    AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.pushforward_map_app,
    AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr_hom_app_app,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_hom_app_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app,
    AlgebraicGeometry.Scheme.Modules.restrict_map, ← Functor.map_comp]
  erw [Category.comp_id, ← Functor.map_comp]
  exact presheaf_map_subsingleton M.presheaf _ _

/-- The pullback units of `b` and `a` compose to the pullback unit of `a ≫ b`. -/
lemma pullbackPushforwardAdjunction_unit_comp (a : A ⟶ B) (b : B ⟶ C) (M : C.Modules) :
    (pullbackPushforwardAdjunction b).unit.app M ≫
        (pushforward b).map ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)) ≫
        (pushforwardComp a b).hom.app ((pullback a).obj ((pullback b).obj M)) ≫
        (pushforward (a ≫ b)).map ((pullbackComp a b).hom.app M) =
      (pullbackPushforwardAdjunction (a ≫ b)).unit.app M := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction b).comp (pullbackPushforwardAdjunction a))
    (pullbackPushforwardAdjunction (a ≫ b)) (pullbackComp a b).inv M
  rw [AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    Adjunction.comp_unit_app] at h
  simp only [Category.assoc] at h
  rw [reassoc_of% h, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- Iterated restriction matches iterated pullback under the restriction-pullback comparison. -/
@[reassoc]
lemma restrictCompIso_hom_app_comp (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c] (M : C.Modules) :
    (restrictCompIso a b c h).hom.app M ≫
        (restrictFunctor a).map ((restrictFunctorIsoPullback b).hom.app M) ≫
        (restrictFunctorIsoPullback a).hom.app ((pullback b).obj M) ≫ compHom a b c h M =
      (restrictFunctorIsoPullback c).hom.app M := by
  subst h
  apply ((restrictAdjunction (a ≫ b)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    restrictAdjunction_unit_restrictFunctorIsoPullback, compHom_rfl]
  simp only [Functor.map_comp]
  rw [reassoc_of% (restrictAdjunction_unit_restrictCompIso a b M),
    ← (pushforwardComp a b).hom.naturality_assoc, ← (pushforwardComp a b).hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [Adjunction.unit_naturality_assoc, restrictAdjunction_unit_restrictFunctorIsoPullback,
    Functor.map_comp_assoc, restrictAdjunction_unit_restrictFunctorIsoPullback_assoc,
    pullbackPushforwardAdjunction_unit_comp]

end OpenImmersions

section Square

variable {X Y U₁ U₂ V₁ V₂ : AlgebraicGeometry.Scheme.{u}}

/-- Restriction after pullback, for a commutative square with open immersions `j` and `k`. -/
def restrictPullbackSquareIso (f : X ⟶ Y) (j : U₁ ⟶ Y) (k : U₂ ⟶ X) (g : U₂ ⟶ U₁)
    [IsOpenImmersion j] [IsOpenImmersion k] (h : g ≫ j = k ≫ f) :
    pullback f ⋙ restrictFunctor k ≅ restrictFunctor j ⋙ pullback g :=
  isoWhiskerLeft _ (restrictFunctorIsoPullback k) ≪≫ pullbackComp _ _ ≪≫
    pullbackCongr h.symm ≪≫ (pullbackComp _ _).symm ≪≫
    isoWhiskerRight (restrictFunctorIsoPullback j).symm _

lemma restrictPullbackNatIso_eq (f : X ⟶ Y) (U : Y.Opens) :
    restrictPullbackNatIso f U =
      restrictPullbackSquareIso f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U) (morphismRestrict_ι f U) := rfl

@[reassoc]
lemma restrictPullbackSquareIso_hom_app_comp (f : X ⟶ Y) (j : U₁ ⟶ Y) (k : U₂ ⟶ X)
    (g : U₂ ⟶ U₁) [IsOpenImmersion j] [IsOpenImmersion k] (h : g ≫ j = k ≫ f)
    (M : Y.Modules) :
    (restrictPullbackSquareIso f j k g h).hom.app M ≫
        (pullback g).map ((restrictFunctorIsoPullback j).hom.app M) =
      (restrictFunctorIsoPullback k).hom.app ((pullback f).obj M) ≫
        compHom k f (g ≫ j) h.symm M ≫ (pullbackComp g j).inv.app M := by
  dsimp only [restrictPullbackSquareIso, compHom, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Iso.symm_hom]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

variable (f : X ⟶ Y) (jU : U₁ ⟶ Y) (jV : V₁ ⟶ Y) (a : V₁ ⟶ U₁)
  (kU : U₂ ⟶ X) (kV : V₂ ⟶ X) (b : V₂ ⟶ U₂) (fU : U₂ ⟶ U₁) (fV : V₂ ⟶ V₁)
  [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion a]
  [IsOpenImmersion kU] [IsOpenImmersion kV] [IsOpenImmersion b]
  (ha : a ≫ jU = jV) (hb : b ≫ kU = kV) (hU : fU ≫ jU = kU ≫ f) (hV : fV ≫ jV = kV ≫ f)
  (sq : b ≫ fU = fV ≫ a)

omit [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion a]
  [IsOpenImmersion kU] [IsOpenImmersion kV] [IsOpenImmersion b] in
include ha hb hU hV sq in
/-- The pure pullback coherence behind compatibility with restriction. -/
lemma pullback_restriction_coherence (M : Y.Modules) :
    compHom b kU kV hb ((pullback f).obj M) ≫ compHom kV f (fV ≫ jV) hV.symm M ≫
        (pullbackComp fV jV).inv.app M =
      (pullback b).map (compHom kU f (fU ≫ jU) hU.symm M) ≫
        (pullback b).map ((pullbackComp fU jU).inv.app M) ≫
        compHom b fU (fV ≫ a) sq ((pullback jU).obj M) ≫
        (pullbackComp fV a).inv.app ((pullback jU).obj M) ≫
        (pullback fV).map (compHom a jU jV ha M) := by
  have e : (fV ≫ a) ≫ jU = fV ≫ jV := by rw [Category.assoc, ha]
  have e' : b ≫ fU ≫ jU = fV ≫ jV := by rw [← Category.assoc, sq, Category.assoc, ha]
  rw [← cancel_mono ((pullbackComp fV jV).hom.app M)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← compHom_rfl fV jV, ← compHom_assoc fV a jU (fV ≫ a) jV (fV ≫ jV) rfl ha e rfl M,
    compHom_rfl, Iso.inv_hom_id_app_assoc,
    compHom_assoc b fU jU (fV ≫ a) (fU ≫ jU) (fV ≫ jV) sq rfl e e' M,
    compHom_rfl, ← Functor.map_comp_assoc (pullback b) ((pullbackComp fU jU).inv.app M),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    compHom_assoc b kU f kV (fU ≫ jU) (fV ≫ jV) hb hU.symm hV.symm e' M]

include ha hb hU hV sq in
/-- Restriction-pullback comparisons commute with iterated restriction. -/
lemma restrictPullbackSquareIso_restrict (M : Y.Modules) :
    (restrictPullbackSquareIso f jV kV fV hV).hom.app M ≫
        (pullback fV).map ((restrictCompIso a jU jV ha).hom.app M) =
      (restrictCompIso b kU kV hb).hom.app ((pullback f).obj M) ≫
        (restrictFunctor b).map ((restrictPullbackSquareIso f jU kU fU hU).hom.app M) ≫
        (restrictPullbackSquareIso fU a b fV sq.symm).hom.app ((restrictFunctor jU).obj M) := by
  rw [← cancel_mono ((pullback fV).map ((restrictFunctor a).map
    ((restrictFunctorIsoPullback jU).hom.app M) ≫
    (restrictFunctorIsoPullback a).hom.app ((pullback jU).obj M) ≫ compHom a jU jV ha M))]
  simp only [Category.assoc]
  rw [← Functor.map_comp, restrictCompIso_hom_app_comp,
    restrictPullbackSquareIso_hom_app_comp]
  simp only [Functor.map_comp]
  have hn := (restrictPullbackSquareIso fU a b fV sq.symm).hom.naturality
    ((restrictFunctorIsoPullback jU).hom.app M)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, restrictPullbackSquareIso_hom_app_comp_assoc, ← Functor.map_comp_assoc,
    restrictPullbackSquareIso_hom_app_comp, Functor.map_comp_assoc,
    (restrictFunctorIsoPullback b).hom.naturality_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← pullback_restriction_coherence f jU jV a kU kV b fU fV ha hb hU hV sq M,
    restrictCompIso_hom_app_comp_assoc]

include ha hb hU hV sq in
/-- Pulling back a morphism on the larger open and then restricting agrees with restricting
first and then pulling back. -/
lemma restrict_conjugation {M N : Y.Modules}
    (φ : (restrictFunctor jU).obj M ⟶ (restrictFunctor jU).obj N) :
    (restrictPullbackSquareIso f jV kV fV hV).hom.app M ≫
        (pullback fV).map ((restrictCompIso a jU jV ha).hom.app M ≫
          (restrictFunctor a).map φ ≫ (restrictCompIso a jU jV ha).inv.app N) ≫
        (restrictPullbackSquareIso f jV kV fV hV).inv.app N =
      (restrictCompIso b kU kV hb).hom.app ((pullback f).obj M) ≫
        (restrictFunctor b).map ((restrictPullbackSquareIso f jU kU fU hU).hom.app M ≫
          (pullback fU).map φ ≫ (restrictPullbackSquareIso f jU kU fU hU).inv.app N) ≫
        (restrictCompIso b kU kV hb).inv.app ((pullback f).obj N) :=
  conjugate_square (restrictPullbackSquareIso fU a b fV sq.symm) φ
    ((restrictCompIso a jU jV ha).app M) ((restrictCompIso a jU jV ha).app N)
    ((restrictPullbackSquareIso f jU kU fU hU).app M)
    ((restrictPullbackSquareIso f jU kU fU hU).app N)
    ((restrictPullbackSquareIso f jV kV fV hV).app M)
    ((restrictPullbackSquareIso f jV kV fV hV).app N)
    ((restrictCompIso b kU kV hb).app _) ((restrictCompIso b kU kV hb).app _)
    (restrictPullbackSquareIso_restrict f jU jV a kU kV b fU fV ha hb hU hV sq M)
    (restrictPullbackSquareIso_restrict f jU jV a kU kV b fU fV ha hb hU hV sq N)

end Square

section Opens

variable {T : AlgebraicGeometry.Scheme.{u}}

/-- A local morphism commutes with the restriction maps between smaller opens. -/
lemma LocalHom.app_map' {M N : T.Modules} {U A B : T.Opens} (h : LocalHom M N U)
    (k : op B ⟶ op A) (iA : A ⟶ U) (iB : B ⟶ U) (x : Γ(M, B)) :
    LocalHom.app h iA (M.presheaf.map k x) = N.presheaf.map k (LocalHom.app h iB x) :=
  PresheafOfModules.naturality_apply h.val
    (Over.homMk k.unop (Subsingleton.elim _ _) : Over.mk iA ⟶ Over.mk iB).op x

/-- Conjugating a local morphism by mutually inverse restriction maps changes nothing. -/
lemma LocalHom.app_conj {M N : T.Modules} {U A B : T.Opens} (h : LocalHom M N U)
    (p : op A ⟶ op B) (q : op B ⟶ op A) (iA : A ⟶ U) (iB : B ⟶ U) (x : Γ(M, A)) :
    N.presheaf.map q (LocalHom.app h iB (M.presheaf.map p x)) = LocalHom.app h iA x := by
  rw [LocalHom.app_map' h p iB iA x, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    presheaf_map_subsingleton N.presheaf (p ≫ q) (𝟙 _), CategoryTheory.Functor.map_id]
  rfl

/-- The section identification sends restriction of a local morphism to restriction of the
corresponding morphism of modules on the open subscheme. -/
lemma internalHomSectionsEquiv_restrict (M N : T.Modules) {U V : T.Opens} (i : V ⟶ U)
    (h : LocalHom M N U) :
    internalHomSectionsEquiv M N V (LocalHom.restrict i h) =
      (restrictCompIso (T.homOfLE (leOfHom i)) U.ι V.ι (T.homOfLE_ι _)).hom.app M ≫
        (restrictFunctor (T.homOfLE (leOfHom i))).map (internalHomSectionsEquiv M N U h) ≫
        (restrictCompIso (T.homOfLE (leOfHom i)) U.ι V.ι (T.homOfLE_ι _)).inv.app N := by
  ext W x
  simp only [restrictCompIso, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    AlgebraicGeometry.Scheme.Modules.Hom.comp_app, restrictFunctor_map_app,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr_hom_app_app,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr_inv_app_app,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_hom_app_app,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_inv_app_app,
    internalHomSectionsEquiv_app]
  rw [LocalHom.restrict_app, ← Functor.map_comp, ← Functor.map_comp]
  exact (LocalHom.app_conj h _ _ _ _ x).symm

/-- Inverse images of nested opens form a commutative square of open immersions. -/
lemma morphismRestrict_homOfLE {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Opens} (i : V ⟶ U) :
    X.homOfLE (leOfHom ((TopologicalSpace.Opens.map f.base).map i)) ≫ f ∣_ U =
      f ∣_ V ≫ Y.homOfLE (leOfHom i) := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι]

end Opens

lemma localHomPullback_restrict : LocalHomPullbackRestrictionStatement.{u} := by
  intro X Y f M N U V i h
  apply (internalHomSectionsEquiv _ _ _).injective
  rw [internalHomSectionsEquiv_localHomPullback, internalHomSectionsEquiv_restrict,
    internalHomSectionsEquiv_restrict, internalHomSectionsEquiv_localHomPullback]
  exact restrict_conjugation f U.ι V.ι (Y.homOfLE (leOfHom i)) (f ⁻¹ᵁ U).ι (f ⁻¹ᵁ V).ι
    (X.homOfLE (leOfHom ((TopologicalSpace.Opens.map f.base).map i))) (f ∣_ U) (f ∣_ V)
    (Y.homOfLE_ι _) (X.homOfLE_ι _) (morphismRestrict_ι f U) (morphismRestrict_ι f V)
    (morphismRestrict_homOfLE f i) (internalHomSectionsEquiv M N U h)

end Restriction

/-- Pullback of local module morphisms satisfies both sheaf laws. -/
theorem localHomPullbackSheafLaws : LocalHomPullbackSheafLawsStatement.{u} :=
  ⟨localHomPullback_restrict, localHomPullback_smul⟩

end Langlands.Scheme.Modules
