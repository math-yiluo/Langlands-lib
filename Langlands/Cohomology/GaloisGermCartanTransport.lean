import Langlands.Cohomology.GaloisGerms

/-! # Galois–Čech covers computed on cofinal germ systems -/

noncomputable section

namespace Langlands.Cohomology.GaloisGerms

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w a b

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (R : Type w) [CommRing R]

section Reindex

variable {I I' : Type w} [SmallCategory I] [SmallCategory I']

/-- Restricting to an initial diagram induces an isomorphism on section germs. -/
def germReindexIso (V : I ⥤ C) (q : I' ⥤ I) [q.Initial] :
    germ J R V ≅ germ J R (q ⋙ V) :=
  Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{w} R) ⋙
    (Functor.whiskeringLeft _ _ _).obj V.op)
    (Functor.Final.colimIso q.op (E := ModuleCat.{w} R)).symm

@[reassoc]
theorem germι_germReindexIso_inv (V : I ⥤ C) (q : I' ⥤ I) [q.Initial]
    (F : Sheaf J (ModuleCat.{w} R)) (i : I') :
    germι J R (q ⋙ V) F i ≫ (germReindexIso J R V q).inv.app F =
      germι J R V F (q.obj i) :=
  Functor.Final.ι_colimitIso_hom q.op (V.op ⋙ F.obj) (op i)

@[reassoc]
theorem germι_germReindexIso_hom (V : I ⥤ C) (q : I' ⥤ I) [q.Initial]
    (F : Sheaf J (ModuleCat.{w} R)) (i : I') :
    germι J R V F (q.obj i) ≫ (germReindexIso J R V q).hom.app F =
      germι J R (q ⋙ V) F i := by
  rw [← germι_germReindexIso_inv J R V q, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end Reindex

/-- A Galois cover of two germ functors, computed on one cofiltered diagram
which may depend on the cover. -/
structure GermCover (T T' : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R) where
  Index : Type w
  [instIndex : SmallCategory Index]
  [instCofiltered : IsCofiltered Index]
  base : Index ⥤ C
  covering : Index ⥤ C
  Γ : Type w
  [instGroup : Group Γ]
  [instFinite : Finite Γ]
  datum : GermGaloisDatum J Γ covering base
  baseIso : T ≅ germ J R base
  coveringIso : T' ≅ germ J R covering

attribute [instance] GermCover.instIndex GermCover.instCofiltered
  GermCover.instGroup GermCover.instFinite

namespace GermCover

variable {J R} {T T' : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R}
variable (E : GermCover J R T T')

/-- The deck action transported to the target germ functor. -/
def action : GaloisCartan.NaturalAction E.Γ T' where
  act γ := E.coveringIso.hom ≫ (E.datum.action R).act γ ≫ E.coveringIso.inv
  act_one := by rw [(E.datum.action R).act_one, Category.id_comp, Iso.hom_inv_id]
  act_mul γ δ := by
    rw [(E.datum.action R).act_mul]
    simp [Category.assoc]

/-- Restriction to the cover, transported to the two germ functors. -/
def aug : T ⟶ T' :=
  E.baseIso.hom ≫ E.datum.aug R ≫ E.coveringIso.inv

theorem aug_act (γ : E.Γ) : E.aug ≫ E.action.act γ = E.aug := by
  simp [aug, action, Category.assoc, reassoc_of% (E.datum.aug_act R γ)]

@[reassoc]
theorem action_comp_coveringIso (γ : E.Γ) :
    E.action.act γ ≫ E.coveringIso.hom = E.coveringIso.hom ≫ (E.datum.action R).act γ := by
  simp [action, Category.assoc]

/-- The transported representation is equivariantly isomorphic to the
representation computed from the cover diagram. -/
def repIso (F : Sheaf J (ModuleCat.{w} R)) :
    E.action.rep F ≅ (E.datum.action R).rep F :=
  Rep.mkIso (Representation.Equiv.mk (E.coveringIso.app F).toLinearEquiv fun γ =>
    LinearMap.ext fun x => by
      exact ConcreteCategory.congr_hom
        (congrArg (fun η => NatTrans.app η F) (E.action_comp_coveringIso γ)) x)

variable [LocallySmall.{w} C]

theorem aug_injective (F : Sheaf J (ModuleCat.{w} R)) : Function.Injective (E.aug.app F) :=
  (E.coveringIso.app F).toLinearEquiv.symm.injective.comp
    ((E.datum.aug_injective R F).comp (E.baseIso.app F).toLinearEquiv.injective)

theorem exists_aug_eq (F : Sheaf J (ModuleCat.{w} R)) (x : T'.obj F)
    (hx : ∀ γ : E.Γ, (E.action.act γ).app F x = x) :
    ∃ s, E.aug.app F s = x := by
  let y := E.coveringIso.hom.app F x
  have hy (γ : E.Γ) : ((E.datum.action R).act γ).app F y = y := by
    have he := ConcreteCategory.congr_hom
      (congrArg (fun η => NatTrans.app η F) (E.action_comp_coveringIso γ)) x
    simpa only [y, NatTrans.comp_app, ConcreteCategory.comp_apply, hx γ] using he.symm
  obtain ⟨s, hs⟩ := E.datum.exists_aug_eq R F y hy
  refine ⟨E.baseIso.inv.app F s, ?_⟩
  have hbase : E.baseIso.hom.app F (E.baseIso.inv.app F s) = s :=
    (E.baseIso.app F).toLinearEquiv.apply_symm_apply s
  rw [aug, NatTrans.comp_app, NatTrans.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, hbase, hs]
  exact (E.coveringIso.app F).toLinearEquiv.symm_apply_apply x

end GermCover

variable [LocallySmall.{w} C] [HasSheafify J (ModuleCat.{w} R)]

/-- Assemble a Galois–Čech system from individual covers and local lifting. -/
def galoisCechSystemOfGermCovers {ι : Type a}
    (T : ι → Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R)
    (Cover : ι → Type b) (target : ∀ i, Cover i → ι)
    (E : ∀ i c, GermCover J R (T i) (T (target i c)))
    (local_lift : ∀ (S : ShortComplex (Sheaf J (ModuleCat.{w} R))), S.ShortExact →
      ∀ i (s : (T i).obj S.X₃), ∃ (c : Cover i) (t : (T (target i c)).obj S.X₂),
        (T (target i c)).map S.g t = (E i c).aug.app S.X₃ s) :
    GaloisCartan.GaloisCechSystem T where
  Cover := Cover
  group i c := (E i c).Γ
  target := target
  action i c := (E i c).action
  aug i c := (E i c).aug
  aug_injective i c F := (E i c).aug_injective F
  aug_act i c γ := (E i c).aug_act γ
  exists_aug_eq i c F x := (E i c).exists_aug_eq F x
  local_lift := local_lift
  injective_acyclic i c Inj _ n := ((E i c).datum.injective_acyclic R Inj n).of_iso
    ((groupCohomology.functor R (E i c).Γ (n + 1)).mapIso ((E i c).repIso Inj))

end Langlands.Cohomology.GaloisGerms
