import Langlands.AlgebraicGeometry.Picard.RigidifiedClassPresheaf
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Picard.RigidifiedIsoUniquenessProof
import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Langlands.AlgebraicGeometry.Picard.LineBundleAutomorphismUnits

/-! # Line bundles rigidified along a morphism of relative spaces -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SubschemeRigidification

open Langlands.SchemeModule

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (g : Z ⟶ S) (z : Z ⟶ X) (hz : z ≫ f = g)

/-- The map `T ×_S Z ⟶ T ×_S X` induced by `z`, natural in the test scheme `T`. -/
def zRel : relativeSpace g ⟶ relativeSpace f where
  app T := pullback.map T.hom g T.hom f (𝟙 T.left) z (𝟙 S) (by simp) (by simp [hz])
  naturality {T U} h := by
    apply pullback.hom_ext
    · simp [relativeSpace, Over.pullback, pullback.map]
    · simp [relativeSpace, Over.pullback, pullback.map]

@[reassoc (attr := simp)]
lemma zRel_fst (T : Over S) :
    (zRel f g z hz).app T ≫ pullback.fst T.hom f = pullback.fst T.hom g := by
  simp [zRel]

@[reassoc (attr := simp)]
lemma zRel_snd (T : Over S) :
    (zRel f g z hz).app T ≫ pullback.snd T.hom f = pullback.snd T.hom g ≫ z := by
  simp [zRel]

/-- Line bundles on `T ×_S X` rigidified along `T ×_S Z`. -/
abbrev relative (T : Over S) := RigidifiedLineBundle ((zRel f g z hz).app T)

/-- Pullback of rigidified line bundles along a morphism of test schemes. -/
def relativePullback {T U : Over S} (h : T ⟶ U) :
    relative f g z hz U ⥤ relative f g z hz T :=
  RigidifiedLineBundle.pullback ((relativeSpace f).map h) ((relativeSpace g).map h)
    ((zRel f g z hz).naturality h).symm

/-- Identity comparison for relative pullback. -/
def relativePullbackId (T : Over S) :
    relativePullback f g z hz (𝟙 T) ≅ 𝟭 (relative f g z hz T) :=
  RigidifiedLineBundle.pullbackCongr ((relativeSpace f).map_id T)
      ((relativeSpace g).map_id T) _ _ ≪≫
    RigidifiedLineBundle.pullbackId RigidifiedModule.pullbackCoherence _

/-- Composition comparison for relative pullback. -/
def relativePullbackComp {T U V : Over S} (h : T ⟶ U) (k : U ⟶ V) :
    relativePullback f g z hz k ⋙ relativePullback f g z hz h ≅
      relativePullback f g z hz (h ≫ k) :=
  RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence
      ((relativeSpace f).map k) ((relativeSpace g).map k)
      ((relativeSpace f).map h) ((relativeSpace g).map h) _ _
      (by rw [← Functor.map_comp, ← Functor.map_comp]
          exact ((zRel f g z hz).naturality (h ≫ k)).symm) ≪≫
    RigidifiedLineBundle.pullbackCongr ((relativeSpace f).map_comp h k).symm
      ((relativeSpace g).map_comp h k).symm _ _

/-- Isomorphism classes of rigidified line bundles. -/
abbrev Classes (T : Over S) :=
  Quotient (isIsomorphicSetoid (relative f g z hz T))

/-- The class of a rigidified line bundle. -/
def classOf {T : Over S} (L : relative f g z hz T) : Classes f g z hz T :=
  Quotient.mk _ L

/-- Pullback of classes. -/
def classesPullback {T U : Over S} (h : T ⟶ U) :
    Classes f g z hz U → Classes f g z hz T :=
  Quotient.map (relativePullback f g z hz h).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(relativePullback f g z hz h).mapIso e⟩)

/-- The presheaf of classes of line bundles rigidified along `z`. -/
def classPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Classes f g z hz T.unop
  map h := TypeCat.ofHom (classesPullback f g z hz h.unop)
  map_id T := by
    ext q
    refine Quotient.inductionOn q (fun L ↦ ?_)
    exact Quotient.sound ⟨(relativePullbackId f g z hz T.unop).app L⟩
  map_comp h k := by
    ext q
    refine Quotient.inductionOn q (fun L ↦ ?_)
    exact Quotient.sound ⟨((relativePullbackComp f g z hz k.unop h.unop).app L).symm⟩

@[simp]
lemma classPresheaf_map_classOf {T U : Over S} (h : T ⟶ U) (L : relative f g z hz U) :
    (classPresheaf f g z hz).map h.op (classOf f g z hz L) =
      classOf f g z hz ((relativePullback f g z hz h).obj L) := rfl

/-- Forget the rigidification on isomorphism classes. -/
def forgetClasses (T : Over S) :
    Classes f g z hz T → (RelativePicard.classPresheaf f).obj (op T) :=
  Quotient.lift
    (fun L ↦ RelativePicard.classOf f T
      ((RigidifiedLineBundle.forget ((zRel f g z hz).app T)).obj L))
    (by
      intro L M h
      obtain ⟨e⟩ := h
      exact (RelativePicard.classOf_eq_iff_iso f T _ _).2
        ⟨(RigidifiedLineBundle.forget _).mapIso e⟩)

@[simp]
lemma forgetClasses_classOf (T : Over S) (L : relative f g z hz T) :
    forgetClasses f g z hz T (classOf f g z hz L) =
      RelativePicard.classOf f T
        ((RigidifiedLineBundle.forget ((zRel f g z hz).app T)).obj L) := rfl

/-- Forgetting the rigidification, as a natural transformation. -/
def forgetClassNatTrans : classPresheaf f g z hz ⟶ RelativePicard.classPresheaf f where
  app T := TypeCat.ofHom (forgetClasses f g z hz T.unop)
  naturality {T U} h := by
    ext q
    refine Quotient.inductionOn q (fun L ↦ ?_)
    change RelativePicard.classOf f U.unop
        ((RigidifiedLineBundle.forget _).obj ((relativePullback f g z hz h.unop).obj L)) =
      (RelativePicard.classPresheaf f).map h.unop.op
        (RelativePicard.classOf f T.unop ((RigidifiedLineBundle.forget _).obj L))
    rw [RelativePicard.map_classOf]
    exact (RelativePicard.classOf_eq_iff_iso f U.unop _ _).2
      ⟨(RigidifiedLineBundle.pullbackForgetIso ((relativeSpace f).map h.unop)
        ((relativeSpace g).map h.unop) ((zRel f g z hz).naturality h.unop).symm).app L⟩

@[simp]
lemma forgetClassNatTrans_app_classOf (T : Over S) (L : relative f g z hz T) :
    (forgetClassNatTrans f g z hz).app (op T) (classOf f g z hz L) =
      RelativePicard.classOf f T
        ((RigidifiedLineBundle.forget ((zRel f g z hz).app T)).obj L) := rfl

/-- Rigidified isomorphisms are unique when `z` is injective on global functions after every
base change. -/
lemma iso_subsingleton
    (hinj : ∀ T : Over S, Function.Injective ((zRel f g z hz).app T).appTop)
    (T : Over S) (L M : relative f g z hz T) : Subsingleton (L ≅ M) := by
  refine ⟨fun e₁ e₂ ↦ ?_⟩
  have h := RigidifiedLineBundle.endo_eq_id (hinj T) L (e₁.hom ≫ e₂.inv)
  ext1
  simpa using congrArg (· ≫ e₂.hom) h

section Generic

open Langlands.Scheme.Modules

variable {S₀ X₀ : Scheme.{u}} {ε : S₀ ⟶ X₀}

/-- Multiply the rigidification of a rigidified line bundle by a global unit of the base. -/
def rigAct (r : Γ(S₀, ⊤)ˣ) (L : RigidifiedLineBundle ε) : RigidifiedLineBundle ε :=
  ⟨⟨L.obj.carrier, unitAut _ r ≪≫ L.obj.rigidification⟩, L.property⟩

lemma smul_comp_rigidification (c : Γ(S₀, ⊤)) (L : RigidifiedLineBundle ε) :
    (c • 𝟙 (structureModule S₀)) ≫ L.obj.rigidification.hom =
      c • L.obj.rigidification.hom := by
  rw [Linear.smul_comp, Category.id_comp]

/-- The unit action fixes a rigidified line bundle up to isomorphism exactly when the unit comes
from a global unit of the total space. -/
lemma rigAct_iso_self_iff (r : Γ(S₀, ⊤)ˣ) (L : RigidifiedLineBundle ε) :
    Nonempty (rigAct r L ≅ L) ↔ r ∈ (Units.map ε.appTop.hom.toMonoidHom).range := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨c, hc⟩ :=
      Langlands.Scheme.Modules.exists_eq_smul_id_of_isLocallyFreeRankOne L.property e.hom.hom.val
    obtain ⟨c', hc'⟩ :=
      Langlands.Scheme.Modules.exists_eq_smul_id_of_isLocallyFreeRankOne L.property e.inv.hom.val
    have hcc : c' * c = 1 := by
      have h := congrArg (fun φ ↦ φ.hom.val) e.hom_inv_id
      change e.hom.hom.val ≫ e.inv.hom.val = 𝟙 L.obj.carrier at h
      rw [hc, hc'] at h
      change (c • 𝟙 L.obj.carrier) ≫ (c' • 𝟙 L.obj.carrier) = 𝟙 L.obj.carrier at h
      rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at h
      rw [mul_comm]
      exact smul_id_injective_of_isLocallyFreeRankOne L.property (h.trans (one_smul _ _).symm)
    let v : Γ(X₀, ⊤)ˣ := ⟨c, c', by rw [mul_comm]; exact hcc, hcc⟩
    have hφ : e.hom.hom.val = (v : Γ(X₀, ⊤)) • 𝟙 L.obj.carrier := hc
    have hp := e.hom.hom.property
    change ((unitAut _ r).hom ≫ L.obj.rigidification.hom) ≫
      (Scheme.Modules.pullback ε).map e.hom.hom.val = L.obj.rigidification.hom at hp
    rw [hφ, pullback_map_smul, CategoryTheory.Functor.map_id, Linear.comp_smul,
      Category.comp_id, unitAut_hom, smul_comp_rigidification, smul_smul] at hp
    have h1 : (ε.appTop (v : Γ(X₀, ⊤)) * (r : Γ(S₀, ⊤))) •
        𝟙 (structureModule S₀) = (1 : Γ(S₀, ⊤)) • 𝟙 _ := by
      rw [← cancel_mono L.obj.rigidification.hom, smul_comp_rigidification,
        smul_comp_rigidification, hp, one_smul]
    have h2 := smul_id_injective_of_isLocallyFreeRankOne (LineBundle.trivial S₀).property h1
    refine ⟨v⁻¹, Units.ext ?_⟩
    change ε.appTop ((v⁻¹ : Γ(X₀, ⊤)ˣ) : Γ(X₀, ⊤)) = r
    have h3 : ε.appTop ((v⁻¹ : Γ(X₀, ⊤)ˣ) : Γ(X₀, ⊤)) * ε.appTop (v : Γ(X₀, ⊤)) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc ε.appTop ((v⁻¹ : Γ(X₀, ⊤)ˣ) : Γ(X₀, ⊤))
        = ε.appTop ((v⁻¹ : Γ(X₀, ⊤)ˣ) : Γ(X₀, ⊤)) * (ε.appTop (v : Γ(X₀, ⊤)) * r) := by
          rw [h2, mul_one]
      _ = r := by rw [← mul_assoc, h3, one_mul]
  · rintro ⟨v, rfl⟩
    refine ⟨RigidifiedLineBundle.isoMk (unitAut L.obj.carrier v⁻¹) ?_⟩
    change ((unitAut _ (Units.map ε.appTop.hom.toMonoidHom v)).hom ≫
      L.obj.rigidification.hom) ≫
        (Scheme.Modules.pullback ε).map (unitAut L.obj.carrier v⁻¹).hom =
      L.obj.rigidification.hom
    rw [unitAut_hom, unitAut_hom, pullback_map_smul, CategoryTheory.Functor.map_id,
      Linear.comp_smul, Category.comp_id, smul_comp_rigidification, smul_smul]
    have h3 : ε.appTop ((v⁻¹ : Γ(X₀, ⊤)ˣ) : Γ(X₀, ⊤)) *
        ((Units.map ε.appTop.hom.toMonoidHom v : Γ(S₀, ⊤)ˣ) : Γ(S₀, ⊤)) = 1 := by
      change ε.appTop ((v⁻¹ : Γ(X₀, ⊤)ˣ) : Γ(X₀, ⊤)) * ε.appTop (v : Γ(X₀, ⊤)) = 1
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h3, one_smul]

/-- An isomorphism of underlying line bundles is a rigidified isomorphism after changing the
rigidification of the target by a unit. -/
lemma exists_iso_rigAct (M N : RigidifiedLineBundle ε)
    (ψ : (RigidifiedLineBundle.forget ε).obj M ≅ (RigidifiedLineBundle.forget ε).obj N) :
    ∃ r : Γ(S₀, ⊤)ˣ, Nonempty (M ≅ rigAct r N) := by
  let a : LineBundle.trivial S₀ ≅ LineBundle.trivial S₀ :=
    ObjectProperty.isoMk _ (M.obj.rigidification ≪≫
      (Scheme.Modules.pullback ε).mapIso ((LineBundle.forget X₀).mapIso ψ) ≪≫
        N.obj.rigidification.symm)
  obtain ⟨r, hr⟩ := (LineBundle.unitAutEquiv (LineBundle.trivial S₀)).surjective a
  have hr' : (unitAut (structureModule S₀) r).hom =
      M.obj.rigidification.hom ≫ (Scheme.Modules.pullback ε).map ψ.hom.hom ≫
        N.obj.rigidification.inv :=
    congrArg (fun b : LineBundle.trivial S₀ ≅ LineBundle.trivial S₀ ↦ b.hom.hom) hr
  refine ⟨r, ⟨RigidifiedLineBundle.isoMk ((LineBundle.forget X₀).mapIso ψ) ?_⟩⟩
  change M.obj.rigidification.hom ≫ (Scheme.Modules.pullback ε).map ψ.hom.hom =
    (unitAut _ r).hom ≫ N.obj.rigidification.hom
  rw [hr']
  simp

end Generic

section Action

open Langlands.Scheme.Modules

/-- Multiply the rigidification by a global unit of `T ×_S Z`. -/
def actObj {T : Over S} (r : Γ((relativeSpace g).obj T, ⊤)ˣ) (L : relative f g z hz T) :
    relative f g z hz T :=
  rigAct r L

/-- The unit action respects rigidified isomorphisms. -/
def actIso {T : Over S} (r : Γ((relativeSpace g).obj T, ⊤)ˣ) {L M : relative f g z hz T}
    (e : L ≅ M) : actObj f g z hz r L ≅ actObj f g z hz r M :=
  RigidifiedLineBundle.isoMk
    ((RigidifiedLineBundle.forgetToRigidified _ ⋙ RigidifiedModule.forget _).mapIso e) (by
      change ((unitAut _ r).hom ≫ L.obj.rigidification.hom) ≫
        (Scheme.Modules.pullback _).map e.hom.hom.val =
          (unitAut _ r).hom ≫ M.obj.rigidification.hom
      rw [Category.assoc, e.hom.hom.property])

/-- The unit action on classes. -/
def actClasses {T : Over S} (r : Γ((relativeSpace g).obj T, ⊤)ˣ) :
    Classes f g z hz T → Classes f g z hz T :=
  Quotient.map (actObj f g z hz r) (fun _ _ ⟨e⟩ ↦ ⟨actIso f g z hz r e⟩)

@[simp]
lemma actClasses_classOf {T : Over S} (r : Γ((relativeSpace g).obj T, ⊤)ˣ)
    (L : relative f g z hz T) :
    actClasses f g z hz r (classOf f g z hz L) = classOf f g z hz (actObj f g z hz r L) := rfl

lemma actClasses_one {T : Over S} (q : Classes f g z hz T) :
    actClasses f g z hz 1 q = q := by
  refine Quotient.inductionOn q (fun L ↦ Quotient.sound ⟨?_⟩)
  refine RigidifiedLineBundle.isoMk (Iso.refl _) ?_
  change ((unitAut _ 1).hom ≫ L.obj.rigidification.hom) ≫
    (Scheme.Modules.pullback _).map (𝟙 _) = L.obj.rigidification.hom
  simp

lemma actClasses_mul {T : Over S} (r s : Γ((relativeSpace g).obj T, ⊤)ˣ)
    (q : Classes f g z hz T) :
    actClasses f g z hz (r * s) q = actClasses f g z hz r (actClasses f g z hz s q) := by
  refine Quotient.inductionOn q (fun L ↦ Quotient.sound ⟨?_⟩)
  refine RigidifiedLineBundle.isoMk (Iso.refl _) ?_
  change ((unitAut _ (r * s)).hom ≫ L.obj.rigidification.hom) ≫
    (Scheme.Modules.pullback _).map (𝟙 _) =
      (unitAut _ r).hom ≫ (unitAut _ s).hom ≫ L.obj.rigidification.hom
  simp [smul_smul, mul_comm]

lemma forgetClasses_actClasses {T : Over S} (r : Γ((relativeSpace g).obj T, ⊤)ˣ)
    (q : Classes f g z hz T) :
    forgetClasses f g z hz T (actClasses f g z hz r q) = forgetClasses f g z hz T q := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  rfl

/-- Pulled-back rigidifications commute with the unit action on the base. -/
lemma pullback_rigidification_unitAut {S₀ X₀ S₁ X₁ : Scheme.{u}} {ε₀ : S₀ ⟶ X₀}
    {ε₁ : S₁ ⟶ X₁} (a : X₁ ⟶ X₀) (b : S₁ ⟶ S₀) (comm : ε₁ ≫ a = b ≫ ε₀)
    (M : RigidifiedModule ε₀) (r : Γ(S₀, ⊤)ˣ) :
    (pullbackUnitIso b).inv ≫
        (Scheme.Modules.pullback b).map
          ((unitAut (SheafOfModules.unit S₀.ringCatSheaf) r).hom ≫ M.rigidification.hom) ≫
          (RigidifiedModule.squarePullbackIso a b comm).hom.app M.carrier =
      (unitAut (SheafOfModules.unit S₁.ringCatSheaf)
          (Units.map b.appTop.hom.toMonoidHom r)).hom ≫
        (pullbackUnitIso b).inv ≫ (Scheme.Modules.pullback b).map M.rigidification.hom ≫
          (RigidifiedModule.squarePullbackIso a b comm).hom.app M.carrier := by
  have hu := congrArg Iso.hom
    (pullback_mapIso_unitAut b (SheafOfModules.unit S₀.ringCatSheaf) r)
  have hn := unitAut_naturality (pullbackUnitIso b).inv
    (Units.map b.appTop.hom.toMonoidHom r)
  simp only [Functor.mapIso_hom] at hu
  rw [Functor.map_comp, hu]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]

/-- Pulling back after the unit action is the unit action after pulling back. -/
lemma relativePullback_actObj {T U : Over S} (h : T ⟶ U)
    (r : Γ((relativeSpace g).obj U, ⊤)ˣ) (L : relative f g z hz U) :
    (relativePullback f g z hz h).obj (actObj f g z hz r L) =
      actObj f g z hz (Units.map ((relativeSpace g).map h).appTop.hom.toMonoidHom r)
        ((relativePullback f g z hz h).obj L) := by
  have key := pullback_rigidification_unitAut ((relativeSpace f).map h)
    ((relativeSpace g).map h) ((zRel f g z hz).naturality h).symm L.obj r
  change (⟨⟨_, _⟩, _⟩ : relative f g z hz T) = ⟨⟨_, _⟩, _⟩
  congr 2
  exact Iso.ext key

/-- Pulling back the unit action. -/
lemma classesPullback_actClasses {T U : Over S} (h : T ⟶ U)
    (r : Γ((relativeSpace g).obj U, ⊤)ˣ) (q : Classes f g z hz U) :
    classesPullback f g z hz h (actClasses f g z hz r q) =
      actClasses f g z hz (Units.map ((relativeSpace g).map h).appTop.hom.toMonoidHom r)
        (classesPullback f g z hz h q) := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact congrArg (classOf f g z hz) (relativePullback_actObj f g z hz h r L)

/-- The unit action fixes a class exactly when the unit comes from `T ×_S X`. -/
lemma actClasses_eq_self_iff {T : Over S} (r : Γ((relativeSpace g).obj T, ⊤)ˣ)
    (q : Classes f g z hz T) :
    actClasses f g z hz r q = q ↔
      r ∈ (Units.map ((zRel f g z hz).app T).appTop.hom.toMonoidHom).range := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact ⟨fun h ↦ (rigAct_iso_self_iff r L).mp (Quotient.exact h),
    fun h ↦ Quotient.sound ((rigAct_iso_self_iff r L).mpr h)⟩

/-- Classes with the same underlying line-bundle class differ by the unit action. -/
lemma exists_eq_actClasses_of_forgetClasses_eq {T : Over S} (q q' : Classes f g z hz T)
    (h : forgetClasses f g z hz T q = forgetClasses f g z hz T q') :
    ∃ r : Γ((relativeSpace g).obj T, ⊤)ˣ, q = actClasses f g z hz r q' := by
  induction q using Quotient.inductionOn with
  | h M =>
    induction q' using Quotient.inductionOn with
    | h N =>
      obtain ⟨ψ⟩ := (RelativePicard.classOf_eq_iff_iso f T _ _).1 h
      obtain ⟨r, ⟨e⟩⟩ := exists_iso_rigAct M N ψ
      exact ⟨r, Quotient.sound ⟨e⟩⟩

end Action

end Langlands.AlgebraicGeometry.Picard.SubschemeRigidification
