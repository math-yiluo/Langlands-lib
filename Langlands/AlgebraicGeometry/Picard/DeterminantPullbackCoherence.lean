import Langlands.AlgebraicGeometry.Picard.DeterminantPullback
import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackCoherenceProofs
import Langlands.AlgebraicGeometry.SectionPullback

/-! # Coherence of determinant pullback comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.DeterminantFrames

open Langlands.Scheme.Modules

variable {X Y Z : Scheme.{u}} {M N : X.Modules} {ι κ I : Type u}
  [Fintype I] {T : ι → X.Opens} {S : κ → X.Opens}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i)) I ≅ M.over (T i))
  (d : ∀ j, SheafOfModules.free (R := X.ringCatSheaf.over (S j)) I ≅ N.over (S j))

local instance : DecidableEq I := Classical.decEq I

omit [Fintype I] in
lemma frameGenerator_mapFrames (φ : M ≅ N) (i : ι) {V : X.Opens}
    (hi : V ≤ T i) (a : I) :
    frameGenerator (mapFrames e φ) i hi a =
      frameGenerator e i hi a ≫ φ.hom.over V := by
  apply LocalHom.ext
  intro W j
  rfl

lemma localHomPullback_precomp {A B C : X.Modules} (q : Y ⟶ X)
    (a : A ⟶ B) (V : X.Opens) (h : LocalHom B C V) :
    localHomPullback q V (a.over V ≫ h) =
      ((Scheme.Modules.pullback q).map a).over (q ⁻¹ᵁ V) ≫ localHomPullback q V h := by
  simpa only [SheafOfModules.Hom.over, CategoryTheory.Functor.map_id,
    Category.comp_id] using localHomPullback_naturality q a (𝟙 C) V h

lemma localHomPullback_postcomp {A B C : X.Modules} (q : Y ⟶ X)
    (b : B ⟶ C) (V : X.Opens) (h : LocalHom A B V) :
    localHomPullback q V (h ≫ b.over V) =
      localHomPullback q V h ≫ ((Scheme.Modules.pullback q).map b).over (q ⁻¹ᵁ V) := by
  simpa only [SheafOfModules.Hom.over, CategoryTheory.Functor.map_id,
    Category.id_comp] using localHomPullback_naturality q (𝟙 A) b V h

lemma frameGenerator_pullback_id (i : ι) {V : X.Opens}
    (hi : V ≤ T i) (a : I) :
    frameGenerator (pullbackFrames e (𝟙 X)) i hi a ≫
        ((Scheme.Modules.pullbackId X).hom.app M).over V =
      frameGenerator e i hi a := by
  have hu : pullbackUnitIso (𝟙 X) =
      (Scheme.Modules.pullbackId X).app (SheafOfModules.unit X.ringCatSheaf) :=
    Iso.ext (pullbackUnitIdentity X)
  rw [frameGenerator_pullback e (𝟙 X) i hi a,
    localHomPullbackIdentity X (SheafOfModules.unit X.ringCatSheaf) M V, hu]
  change ((Scheme.Modules.pullbackId X).inv.app
      (SheafOfModules.unit X.ringCatSheaf)).over V ≫
    (((Scheme.Modules.pullbackId X).hom.app
      (SheafOfModules.unit X.ringCatSheaf)).over V ≫
      frameGenerator e i hi a ≫ ((Scheme.Modules.pullbackId X).inv.app M).over V) ≫
    ((Scheme.Modules.pullbackId X).hom.app M).over V = _
  simp only [SheafOfModules.Hom.over, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

lemma frameGenerator_pullback_comp (f : Z ⟶ Y) (g : Y ⟶ X)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) (a : I) :
    frameGenerator (pullbackFrames (pullbackFrames e g) f) i
        (f.preimage_mono (g.preimage_mono hi)) a ≫
      ((Scheme.Modules.pullbackComp f g).hom.app M).over ((f ≫ g) ⁻¹ᵁ V) =
    frameGenerator (pullbackFrames e (f ≫ g)) i ((f ≫ g).preimage_mono hi) a := by
  rw [frameGenerator_pullback (pullbackFrames e g) f i (g.preimage_mono hi) a,
    frameGenerator_pullback e g i hi a, localHomPullback_precomp,
    localHomPullbackComposition f g (SheafOfModules.unit X.ringCatSheaf) M V]
  have hcancel :
      ((Scheme.Modules.pullbackComp f g).inv.app M).over ((f ≫ g) ⁻¹ᵁ V) ≫
        ((Scheme.Modules.pullbackComp f g).hom.app M).over ((f ≫ g) ⁻¹ᵁ V) = 𝟙 _ := by
    simp only [SheafOfModules.Hom.over, ← Functor.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.assoc]
  rw [hcancel, Category.comp_id]
  change (SheafOfModules.overFunctor Z.ringCatSheaf ((f ≫ g) ⁻¹ᵁ V)).map
      (pullbackUnitIso f).inv ≫
    (SheafOfModules.overFunctor Z.ringCatSheaf ((f ≫ g) ⁻¹ᵁ V)).map
      ((Scheme.Modules.pullback f).map (pullbackUnitIso g).inv) ≫
    (SheafOfModules.overFunctor Z.ringCatSheaf ((f ≫ g) ⁻¹ᵁ V)).map
      ((Scheme.Modules.pullbackComp f g).hom.app
        (SheafOfModules.unit X.ringCatSheaf)) ≫
    localHomPullback (f ≫ g) V (frameGenerator e i hi a) = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  have hu := congrArg
    (fun t => (SheafOfModules.overFunctor Z.ringCatSheaf ((f ≫ g) ⁻¹ᵁ V)).map t ≫
      localHomPullback (f ≫ g) V (frameGenerator e i hi a))
    ((Category.assoc _ _ _).trans
      (Langlands.SchemeModule.RigidifiedModule.pullbackUnitIso_inv_comp f g))
  exact hu.trans (frameGenerator_pullback e (f ≫ g) i hi a).symm

/-- An actual isomorphism that preserves the chosen local generators has matrix one. -/
lemma isoMatrix_eq_one_of_frameGenerator (φ : M ≅ N)
    (i : ι) (j : κ) {V : X.Opens} (hi : V ≤ T i) (hj : V ≤ S j)
    (h : ∀ a, frameGenerator e i hi a ≫ φ.hom.over V = frameGenerator d j hj a) :
    isoMatrix e d φ i j hi hj = 1 := by
  ext a b
  have hs := congrArg (localUnitSection N V) (h b)
  rw [localUnitSection_comp, frameGenerator_section, frameGenerator_section] at hs
  change φ.hom.app V (basis e i hi b) = basis d j hj b at hs
  change (basis d j hj).repr (φ.hom.app V (basis e i hi b)) a =
    (1 : Matrix I I Γ(X, V)) a b
  rw [hs]
  simp only [Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply, eq_comm]

lemma isoUnit_eq_one_of_frameGenerator (φ : M ≅ N)
    (i : ι) (j : κ) {V : X.Opens} (hi : V ≤ T i) (hj : V ≤ S j)
    (h : ∀ a, frameGenerator e i hi a ≫ φ.hom.over V = frameGenerator d j hj a) :
    (isoUnit e d φ i j hi hj : Γ(X, V)) = 1 := by
  rw [isoUnit_val, isoMatrix_eq_one_of_frameGenerator e d φ i j hi hj h, Matrix.det_one]

/-- Local generators determine a map into any actual module sheaf when the charts cover. -/
lemma hom_ext_genSec_to (hT : (⨆ i, T i) = ⊤) {P : X.Modules}
    {a b : CocycleGluing.glued (cocycle e) ⟶ P}
    (h : ∀ (i : ι) (V : X.Opens) (hi : V ≤ T i),
      a.app V (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) =
        b.app V (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)) : a = b := by
  apply OpenCoverHomGluing.hom_ext_of_local (V := T) (fun x => by
    apply Opens.mem_iSup.mp
    rw [hT]
    trivial)
  intro i V hi
  ext m
  obtain ⟨r, rfl⟩ := (CocycleGluing.smul_genSec_bijective
    (cocycle e) (isCocycle e) i hi).2 m
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, h i V hi]

/-- Pullback maps from a determinant sheaf are determined by the pulled-back generators. -/
lemma pullback_hom_ext_genSec (q : Y ⟶ X) (hT : (⨆ i, T i) = ⊤) {P : Y.Modules}
    {a b : (Scheme.Modules.pullback q).obj (CocycleGluing.glued (cocycle e)) ⟶ P}
    (h : ∀ (i : ι) (V : X.Opens) (hi : V ≤ T i),
      a.app (q ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection q
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)) =
      b.app (q ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection q
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi))) : a = b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).injective
  apply hom_ext_genSec_to e hT
  intro i V hi
  exact (Scheme.Modules.app_pullbackLocalSection q a _).symm.trans
    ((h i V hi).trans (Scheme.Modules.app_pullbackLocalSection q b _))

omit [Fintype I] in
lemma genSec_identity_preimage
    (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : CocycleGluing.IsCocycle g)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    CocycleGluing.genSec g hg i (V := (𝟙 X) ⁻¹ᵁ V) hi =
      CocycleGluing.genSec g hg i hi := rfl

omit [Fintype I] in
lemma hom_app_genSec_identity_preimage
    (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : CocycleGluing.IsCocycle g)
    {P : X.Modules} (a : CocycleGluing.glued g ⟶ P)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    a.app ((𝟙 X) ⁻¹ᵁ V) (CocycleGluing.genSec g hg i (V := (𝟙 X) ⁻¹ᵁ V) hi) =
      a.app V (CocycleGluing.genSec g hg i hi) := rfl

omit [Fintype I] in
lemma pullbackLocalSection_identity (P : X.Modules) (V : X.Opens) (s : Γ(P, V)) :
    ((Scheme.Modules.pullbackId X).app P).hom.app ((𝟙 X) ⁻¹ᵁ V)
      (Scheme.Modules.pullbackLocalSection (𝟙 X) s) = s := by
  exact sectionPullback_id P V s

omit [Fintype I] in
lemma isoTrans_hom_app_apply {P Q R : X.Modules} (a : P ≅ Q) (b : Q ≅ R)
    (V : X.Opens) (s : Γ(P, V)) :
    (a ≪≫ b).hom.app V s = b.hom.app V (a.hom.app V s) := rfl

/-- A generator-preserving map induces a generator-preserving determinant map. -/
lemma isoMap_hom_app_genSec_of_frameGenerator (φ : M ≅ N)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤)
    (i : ι) (j : κ) {V : X.Opens} (hi : V ≤ T i) (hj : V ≤ S j)
    (h : ∀ a, frameGenerator e i hi a ≫ φ.hom.over V = frameGenerator d j hj a) :
    (isoMap e d φ hT hS).hom.app V
      (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) =
    CocycleGluing.genSec (cocycle d) (isCocycle d) j hj := by
  have hs := isoMap_hom_app_genSec e d φ hT hS i j hi hj
  rw [isoUnit_eq_one_of_frameGenerator e d φ i j hi hj h, one_smul] at hs
  exact hs

/-- A pair of comparison maps is the identity comparison if their composite
returns every original generator. -/
lemma pullback_identity_of_genSec (hT : (⨆ i, T i) = ⊤) {P : X.Modules}
    (a : (Scheme.Modules.pullback (𝟙 X)).obj
      (CocycleGluing.glued (cocycle e)) ≅ P)
    (b : P ≅ CocycleGluing.glued (cocycle e))
    (h : ∀ (i : ι) (V : X.Opens) (hi : V ≤ T i),
      b.hom.app ((𝟙 X) ⁻¹ᵁ V)
        (a.hom.app ((𝟙 X) ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection (𝟙 X)
          (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi))) =
        CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) :
    a ≪≫ b = (Scheme.Modules.pullbackId X).app (CocycleGluing.glued (cocycle e)) := by
  apply Iso.ext
  apply pullback_hom_ext_genSec e (𝟙 X) hT
  intro i V hi
  exact (isoTrans_hom_app_apply a b _ _).trans ((h i V hi).trans
    (pullbackLocalSection_identity (CocycleGluing.glued (cocycle e)) V
      (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)).symm)

/-- The identity comparison of modules has determinant coefficient one. -/
lemma isoUnit_pullback_id (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    (isoUnit (pullbackFrames e (𝟙 X)) e ((Scheme.Modules.pullbackId X).app M)
      i i hi hi : Γ(X, V)) = 1 :=
  isoUnit_eq_one_of_frameGenerator (pullbackFrames e (𝟙 X)) e
    ((Scheme.Modules.pullbackId X).app M) i i hi hi (frameGenerator_pullback_id e i hi)

/-- Determinant map induced by the canonical identity pullback of the module. -/
def pullbackIdentityIso (hT : (⨆ i, T i) = ⊤) :
    CocycleGluing.glued (cocycle (pullbackFrames e (𝟙 X))) ≅
      CocycleGluing.glued (cocycle e) :=
  isoMap (pullbackFrames e (𝟙 X)) e ((Scheme.Modules.pullbackId X).app M)
    ((𝟙 X : X ⟶ X).iSup_preimage_eq_top hT) hT

/-- The determinant of the module identity comparison preserves generators. -/
lemma isoMap_pullback_id_genSec (hT : (⨆ i, T i) = ⊤)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    (pullbackIdentityIso e hT).hom.app V
      (CocycleGluing.genSec (cocycle (pullbackFrames e (𝟙 X)))
        (isCocycle (pullbackFrames e (𝟙 X))) i hi) =
    CocycleGluing.genSec (cocycle e) (isCocycle e) i hi := by
  have h := isoMap_hom_app_genSec (pullbackFrames e (𝟙 X)) e
    ((Scheme.Modules.pullbackId X).app M)
    ((𝟙 X : X ⟶ X).iSup_preimage_eq_top hT) hT i i hi hi
  rw [isoUnit_pullback_id e i hi, one_smul] at h
  exact h

end Langlands.AlgebraicGeometry.Picard.DeterminantFrames
