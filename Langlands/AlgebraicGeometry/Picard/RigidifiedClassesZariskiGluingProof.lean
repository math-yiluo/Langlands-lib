import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiGluingStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof
import Langlands.AlgebraicGeometry.Modules.OpenCoverModuleGluingProof
import Langlands.AlgebraicGeometry.Modules.PullbackTransport

/-! # Zariski gluing of actual rigidified abelian-scheme classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.Scheme.Modules

open Langlands.SchemeModule Langlands.SchemeModule.RigidifiedModule

attribute [local simp] compIso_hom

/-- A square comparison followed by an equal-composite comparison. -/
lemma squarePullbackIso_hom_compHom {X Y X' Y' : AlgebraicGeometry.Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y)
    (hs : p' ≫ t = s ≫ p) (M : Y.Modules) (z : X' ⟶ Y) (hz : s ≫ p = z) :
    (squarePullbackIso p p' s t hs M).hom ≫ compHom s p z hz M =
      compHom p' t z (hs.trans hz) M := by
  subst hz
  rw [compHom_rfl]
  simp [squarePullbackIso, compHom]

/-- The unit comparison of a composite, read through the equal-composite comparison. -/
lemma pullback_map_pullbackUnitIso_hom {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a ≫ b = c) :
    (AlgebraicGeometry.Scheme.Modules.pullback a).map (pullbackUnitIso b).hom =
      compHom a b c h (SheafOfModules.unit Z.ringCatSheaf) ≫ (pullbackUnitIso c).hom ≫
        (pullbackUnitIso a).inv := by
  subst h
  rw [compHom_rfl]
  have h := pullbackUnitIso_inv_comp a b
  have h' : (AlgebraicGeometry.Scheme.Modules.pullback a).map (pullbackUnitIso b).inv ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp a b).hom.app
        (SheafOfModules.unit Z.ringCatSheaf) =
      (pullbackUnitIso a).hom ≫ (pullbackUnitIso (a ≫ b)).inv := by
    rw [← h]
    simp
  rw [← cancel_epi ((AlgebraicGeometry.Scheme.Modules.pullback a).map (pullbackUnitIso b).inv),
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, reassoc_of% h']
  simp

/-- The base rigidification determined by a rigidified chart of a module. -/
def chartRigidification {B Y Bi Yi : AlgebraicGeometry.Scheme.{u}} (ε : B ⟶ Y)
    (N : Y.Modules) {εi : Bi ⟶ Yi} {Gi : Yi ⟶ Y} {fi : Bi ⟶ B}
    (ci : εi ≫ Gi = fi ≫ ε)
    (ri : structureModule Bi ≅ (AlgebraicGeometry.Scheme.Modules.pullback εi).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback Gi).obj N)) :
    (AlgebraicGeometry.Scheme.Modules.pullback fi).obj (structureModule B) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback fi).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback ε).obj N) :=
  pullbackUnitIso fi ≪≫ ri ≪≫ ((RigidifiedModule.squarePullbackIso Gi fi ci).app N).symm

/-- The chart rigidification, read on the common composite. -/
lemma chartRigidification_hom_compHom {B Y Bi Yi : AlgebraicGeometry.Scheme.{u}}
    (ε : B ⟶ Y) (N : Y.Modules) {εi : Bi ⟶ Yi} {Gi : Yi ⟶ Y} {fi : Bi ⟶ B}
    (ci : εi ≫ Gi = fi ≫ ε)
    (ri : structureModule Bi ≅ (AlgebraicGeometry.Scheme.Modules.pullback εi).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback Gi).obj N)) :
    (chartRigidification ε N ci ri).hom ≫ compHom fi ε (fi ≫ ε) rfl N =
      (pullbackUnitIso fi).hom ≫ ri.hom ≫ compHom εi Gi (fi ≫ ε) ci N := by
  rw [compHom_rfl]
  simp [chartRigidification, RigidifiedModule.squarePullbackIso, compHom,
    AlgebraicGeometry.Scheme.Modules.pullbackCongr]

/-- Restricting a chart rigidification gives the rigidification of the restricted chart. -/
lemma chartRigidification_restrict {B Y Bi Yi W P : AlgebraicGeometry.Scheme.{u}}
    (ε : B ⟶ Y) (N : Y.Modules) {εi : Bi ⟶ Yi} {Gi : Yi ⟶ Y} {fi : Bi ⟶ B}
    (ci : εi ≫ Gi = fi ≫ ε)
    (ri : structureModule Bi ≅ (AlgebraicGeometry.Scheme.Modules.pullback εi).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback Gi).obj N))
    {εP : W ⟶ P} (pa : P ⟶ Yi) (a : W ⟶ Bi) (ca : εP ≫ pa = a ≫ εi)
    (z : W ⟶ B) (hz : a ≫ fi = z) (w : P ⟶ Y) (hw : pa ≫ Gi = w)
    (cw : εP ≫ w = z ≫ ε) :
    (AlgebraicGeometry.Scheme.Modules.pullback a).map (chartRigidification ε N ci ri).hom ≫
        compHom a fi z hz ((AlgebraicGeometry.Scheme.Modules.pullback ε).obj N) =
      compHom a fi z hz (structureModule B) ≫
        (chartRigidification ε N cw
          (((RigidifiedModule.pullback pa a ca).obj
              (⟨(AlgebraicGeometry.Scheme.Modules.pullback Gi).obj N, ri⟩ :
                RigidifiedModule εi)).rigidification ≪≫
            (AlgebraicGeometry.Scheme.Modules.pullback εP).mapIso
              (compIso pa Gi w hw N))).hom := by
  subst hz hw
  rw [← cancel_mono (compIso (a ≫ fi) ε ((a ≫ fi) ≫ ε) rfl N).hom]
  simp only [Category.assoc, compIso_hom]
  have e1 := compHom_assoc a fi ε (a ≫ fi) (fi ≫ ε) ((a ≫ fi) ≫ ε) rfl rfl rfl
    (Category.assoc _ _ _).symm N
  have e2 := compHom_assoc εP pa Gi (εP ≫ pa) (pa ≫ Gi) ((a ≫ fi) ≫ ε) rfl rfl
    (by rw [Category.assoc]; exact cw) cw N
  have e3 := compHom_assoc a εi Gi (εP ≫ pa) (fi ≫ ε) ((a ≫ fi) ≫ ε) ca.symm ci
    (by rw [Category.assoc]; exact cw) (by rw [Category.assoc]) N
  have hr := pullback_rigidification_hom_comp pa a ca
    (⟨(AlgebraicGeometry.Scheme.Modules.pullback Gi).obj N, ri⟩ : RigidifiedModule εi)
  rw [e1, ← Functor.map_comp_assoc, chartRigidification_hom_compHom,
    chartRigidification_hom_compHom]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Functor.map_comp, compIso_hom]
  rw [← e2, compHom_rfl εP pa, reassoc_of% hr, e3,
    pullback_map_pullbackUnitIso_hom a fi (a ≫ fi) rfl]
  simp only [Category.assoc]
  rfl

/-- Restricted chart rigidifications agree when a rigidified map between the restricted charts
has the square comparison of the glued module as underlying map. -/
lemma restricted_rigidification_eq {W P Bi Yi Bj Yj Y : AlgebraicGeometry.Scheme.{u}}
    {εP : W ⟶ P} {εi : Bi ⟶ Yi} {εj : Bj ⟶ Yj} (Gi : Yi ⟶ Y) (Gj : Yj ⟶ Y)
    (pa : P ⟶ Yi) (pb : P ⟶ Yj) (a : W ⟶ Bi) (b : W ⟶ Bj)
    (ca : εP ≫ pa = a ≫ εi) (cb : εP ≫ pb = b ≫ εj) (hs : pa ≫ Gi = pb ≫ Gj)
    (N : Y.Modules)
    (ri : structureModule Bi ≅ (AlgebraicGeometry.Scheme.Modules.pullback εi).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback Gi).obj N))
    (rj : structureModule Bj ≅ (AlgebraicGeometry.Scheme.Modules.pullback εj).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback Gj).obj N))
    (Θ : (RigidifiedModule.pullback pa a ca).obj
        (⟨(AlgebraicGeometry.Scheme.Modules.pullback Gi).obj N, ri⟩ : RigidifiedModule εi) ⟶
      (RigidifiedModule.pullback pb b cb).obj
        (⟨(AlgebraicGeometry.Scheme.Modules.pullback Gj).obj N, rj⟩ : RigidifiedModule εj))
    (hΘ : Θ.val = (Langlands.Scheme.Modules.squarePullbackIso Gj pa pb Gi hs N).hom)
    (w : P ⟶ Y) (hw : pa ≫ Gi = w) (hw' : pb ≫ Gj = w) :
    ((RigidifiedModule.pullback pa a ca).obj
        (⟨(AlgebraicGeometry.Scheme.Modules.pullback Gi).obj N, ri⟩ :
          RigidifiedModule εi)).rigidification ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback εP).mapIso (compIso pa Gi w hw N) =
    ((RigidifiedModule.pullback pb b cb).obj
        (⟨(AlgebraicGeometry.Scheme.Modules.pullback Gj).obj N, rj⟩ :
          RigidifiedModule εj)).rigidification ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback εP).mapIso (compIso pb Gj w hw' N) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, compIso_hom]
  rw [← Θ.property, hΘ, Category.assoc, ← Functor.map_comp,
    squarePullbackIso_hom_compHom Gj pa pb Gi hs N w hw']

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule

/-- The underlying module functor of rigidified line bundles. -/
def forgetModule {S X : Scheme.{u}} (ε : S ⟶ X) : RigidifiedLineBundle ε ⥤ X.Modules :=
  forgetToRigidified ε ⋙ RigidifiedModule.forget ε

@[simp]
lemma forgetModule_map_pullback_map {S X S' X' : Scheme.{u}} {ε : S ⟶ X} {ε' : S' ⟶ X'}
    (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε) {L M : RigidifiedLineBundle ε}
    (h : L ⟶ M) :
    (forgetModule ε').map ((pullback f g comm).map h) =
      (Scheme.Modules.pullback f).map ((forgetModule ε).map h) :=
  rfl

variable {S X S' X' S'' X'' : Scheme.{u}} {ε : S ⟶ X} {ε' : S' ⟶ X'} {ε'' : S'' ⟶ X''}

/-- Iterated rigidified pullback, compared with pullback along chosen equal composites. -/
def pullbackCompTo (f : X' ⟶ X) (g : S' ⟶ S) (f' : X'' ⟶ X') (g' : S'' ⟶ S')
    (F : X'' ⟶ X) (G : S'' ⟶ S) (hF : f' ≫ f = F) (hG : g' ≫ g = G)
    (comm : ε' ≫ f = g ≫ ε) (comm' : ε'' ≫ f' = g' ≫ ε') (commF : ε'' ≫ F = G ≫ ε) :
    pullback f g comm ⋙ pullback f' g' comm' ≅ pullback F G commF :=
  pullbackComp RigidifiedModule.pullbackCoherence f g f' g' comm comm'
      (by subst hF hG; exact commF) ≪≫
    pullbackCongr hF hG _ _

lemma forgetModule_map_pullbackCompTo_hom (f : X' ⟶ X) (g : S' ⟶ S) (f' : X'' ⟶ X')
    (g' : S'' ⟶ S') (F : X'' ⟶ X) (G : S'' ⟶ S) (hF : f' ≫ f = F) (hG : g' ≫ g = G)
    (comm : ε' ≫ f = g ≫ ε) (comm' : ε'' ≫ f' = g' ≫ ε') (commF : ε'' ≫ F = G ≫ ε)
    (L : RigidifiedLineBundle ε) :
    (forgetModule ε'').map ((pullbackCompTo f g f' g' F G hF hG comm comm' commF).hom.app L) =
      RigidifiedModule.compHom f' f F hF L.obj.carrier := by
  subst hF hG
  change _ ≫ ((pullbackCongr _ _ _ _).hom.app L).hom.val = _
  rw [pullbackCongr_hom_val]
  rfl

variable {Y Y' B B' Z Z' C C' : Scheme.{u}} {εY : B ⟶ Y} {εY' : B' ⟶ Y'} {εZ : C ⟶ Z}
  {εZ' : C' ⟶ Z'}

/-- The rigidified comparison between the two orders of pullback around a square. -/
def squareIso (t : Y' ⟶ Y) (tb : B' ⟶ B) (ct : εY' ≫ t = tb ≫ εY)
    (p : Z ⟶ Y) (pb : C ⟶ B) (cp : εZ ≫ p = pb ≫ εY)
    (p' : Z' ⟶ Y') (p'b : C' ⟶ B') (cp' : εZ' ≫ p' = p'b ≫ εY')
    (s : Z' ⟶ Z) (sb : C' ⟶ C) (cs : εZ' ≫ s = sb ≫ εZ)
    (hs : p' ≫ t = s ≫ p) (hsb : p'b ≫ tb = sb ≫ pb) (L : RigidifiedLineBundle εY) :
    (pullback p' p'b cp').obj ((pullback t tb ct).obj L) ≅
      (pullback s sb cs).obj ((pullback p pb cp).obj L) :=
  (pullbackComp RigidifiedModule.pullbackCoherence t tb p' p'b ct cp'
      (by rw [← Category.assoc, cp', Category.assoc, ct, Category.assoc])).app L ≪≫
    (pullbackCongr hs hsb _ _).app L ≪≫
      ((pullbackComp RigidifiedModule.pullbackCoherence p pb s sb cp cs
        (by rw [← Category.assoc, cs, Category.assoc, cp, Category.assoc])).app L).symm

lemma forgetModule_map_squareIso_hom (t : Y' ⟶ Y) (tb : B' ⟶ B) (ct : εY' ≫ t = tb ≫ εY)
    (p : Z ⟶ Y) (pb : C ⟶ B) (cp : εZ ≫ p = pb ≫ εY)
    (p' : Z' ⟶ Y') (p'b : C' ⟶ B') (cp' : εZ' ≫ p' = p'b ≫ εY')
    (s : Z' ⟶ Z) (sb : C' ⟶ C) (cs : εZ' ≫ s = sb ≫ εZ)
    (hs : p' ≫ t = s ≫ p) (hsb : p'b ≫ tb = sb ≫ pb) (L : RigidifiedLineBundle εY) :
    (forgetModule εZ').map (squareIso t tb ct p pb cp p' p'b cp' s sb cs hs hsb L).hom =
      (Langlands.Scheme.Modules.squarePullbackIso p p' s t hs L.obj.carrier).hom := by
  change _ ≫ ((pullbackCongr _ _ _ _).hom.app L).hom.val ≫ _ = _
  rw [pullbackCongr_hom_val]
  rfl

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

/-- Rigidified isomorphisms are unique over any base identified with a relative space. -/
lemma rigidifiedIso_subsingleton_of_iso {S : Scheme.{u}} (A : AbelianScheme S) (V : Over S)
    {Y : Scheme.{u}} (Q : (relativeSpace A.X.hom).obj V ≅ Y) {σ : V.left ⟶ Y}
    (hσ : (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app V ≫ Q.hom = σ)
    (L M : RigidifiedLineBundle σ) : Subsingleton (L ≅ M) := by
  constructor
  intro α β
  let F := RigidifiedLineBundle.pullback Q.hom (𝟙 V.left)
    (by rw [hσ, Category.id_comp] :
      (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app V ≫ Q.hom =
        𝟙 V.left ≫ σ)
  have h := (rigidifiedIsoUniqueness S A V (F.obj L) (F.obj M)).elim (F.mapIso α) (F.mapIso β)
  have hv : (Scheme.Modules.pullback Q.hom).map α.hom.hom.val =
      (Scheme.Modules.pullback Q.hom).map β.hom.hom.val :=
    congrArg (fun e ↦ e.hom.hom.val) h
  apply Iso.ext
  apply ObjectProperty.hom_ext
  apply Subtype.ext
  exact Langlands.Scheme.Modules.pullback_map_injective_of_iso Q hv

/-- A scheme pullback of two slice maps is a pullback in the slice category. -/
lemma over_isPullback {S : Scheme.{u}} (Y : Over S) {X₁ X₂ : Scheme.{u}}
    (x₁ : X₁ ⟶ Y.left) (x₂ : X₂ ⟶ Y.left) :
    IsPullback
      (Over.homMk (pullback.fst x₁ x₂) :
        Over.mk (pullback.fst x₁ x₂ ≫ x₁ ≫ Y.hom) ⟶ Over.mk (x₁ ≫ Y.hom))
      (Over.homMk (pullback.snd x₁ x₂) (by simp [pullback.condition_assoc]) :
        Over.mk (pullback.fst x₁ x₂ ≫ x₁ ≫ Y.hom) ⟶ Over.mk (x₂ ≫ Y.hom))
      (Over.homMk x₁ : Over.mk (x₁ ≫ Y.hom) ⟶ Y) (Over.homMk x₂ : Over.mk (x₂ ≫ Y.hom) ⟶ Y) := by
  apply IsPullback.of_map (Over.forget S)
  · ext
    simp [pullback.condition]
  · exact IsPullback.of_hasPullback x₁ x₂

/-- The relative section, transported along identifications of relative spaces. -/
lemma relativeSection_comp_square {S : Scheme.{u}} (A : AbelianScheme S) {V V' : Over S}
    (h : V ⟶ V') {Y : Scheme.{u}} (Q : (relativeSpace A.X.hom).obj V ≅ Y)
    (m : Y ⟶ (relativeSpace A.X.hom).obj V')
    (hm : Q.hom ≫ m = (relativeSpace A.X.hom).map h) :
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app V ≫ Q.hom) ≫ m =
      h.left ≫ (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app V' := by
  rw [Category.assoc, hm]
  exact ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality h).symm

end Langlands.AbelianScheme

namespace Langlands.AlgebraicGeometry.Picard

/-- Local rank one on the pullback to an open immersion gives local rank one near its image. -/
lemma IsLocallyFreeRankOne.exists_of_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] {M : X.Modules}
    (hM : IsLocallyFreeRankOne ((Scheme.Modules.pullback g).obj M)) (y : Y) :
    ∃ U : X.Opens, g y ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  obtain ⟨V, hy, ⟨e⟩⟩ := hM y
  refine ⟨(V.ι ≫ g).opensRange, ⟨⟨y, hy⟩, rfl⟩, ⟨?_⟩⟩
  let E := (V.ι ≫ g).isoOpensRange
  let P := (Scheme.Modules.pullback (V.ι ≫ g).opensRange.ι).obj M
  let e₂ : (Scheme.Modules.pullback E.hom).obj P ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
    Langlands.Scheme.Modules.compIso E.hom _ (V.ι ≫ g) (V.ι ≫ g).isoOpensRange_hom_ι M ≪≫
      (Langlands.Scheme.Modules.compIso V.ι g (V.ι ≫ g) rfl M).symm ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm ≪≫ e
  exact (Scheme.Modules.restrictFunctorIsoPullback _).app M ≪≫
    ((Scheme.Modules.pullbackId _).app P).symm ≪≫
      (Langlands.Scheme.Modules.compIso E.inv E.hom (𝟙 _) E.inv_hom_id P).symm ≪≫
        (Scheme.Modules.pullback E.inv).mapIso e₂ ≪≫ Langlands.Scheme.Modules.pullbackUnitIso E.inv

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

/-- The relative section, carried through chosen maps out of two relative spaces. -/
lemma relativeSection_comp_square' {S : Scheme.{u}} (A : AbelianScheme S) {V V' : Over S}
    (h : V ⟶ V') {Y Y' : Scheme.{u}} (g : (relativeSpace A.X.hom).obj V ⟶ Y)
    (n : (relativeSpace A.X.hom).obj V' ⟶ Y') (m : Y ⟶ Y')
    (hm : g ≫ m = (relativeSpace A.X.hom).map h ≫ n) :
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app V ≫ g) ≫ m =
      h.left ≫ (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app V' ≫ n := by
  rw [Category.assoc, hm, ← Category.assoc, ← Category.assoc]
  congr 1
  exact ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality h).symm

/-- A rigidified isomorphism over a slice object, transported to an identified total space. -/
def isoTransport {S : Scheme.{u}} (A : AbelianScheme S) {V U U' : Over S}
    (a : V ⟶ U) (b : V ⟶ U') {P : Scheme.{u}}
    (Q : (relativeSpace A.X.hom).obj V ≅ P) (fa : P ⟶ (relativeSpace A.X.hom).obj U)
    (fb : P ⟶ (relativeSpace A.X.hom).obj U')
    (ha : Q.hom ≫ fa = (relativeSpace A.X.hom).map a)
    (hb : Q.hom ≫ fb = (relativeSpace A.X.hom).map b)
    {L : RigidifiedFamily A U} {M : RigidifiedFamily A U'}
    (Φ : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        a).obj L ≅
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        b).obj M) :
    (RigidifiedLineBundle.pullback fa a.left (relativeSection_comp_square A a Q fa ha)).obj L ≅
      (RigidifiedLineBundle.pullback fb b.left (relativeSection_comp_square A b Q fb hb)).obj M :=
  ((RigidifiedLineBundle.pullbackCompTo
      (ε'' := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app V ≫ Q.hom)
      ((relativeSpace A.X.hom).map a) a.left Q.inv (𝟙 V.left) fa a.left
      (by rw [← ha, Iso.inv_hom_id_assoc]) (Category.id_comp _)
      ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality a).symm
      (by simp) _).app L).symm ≪≫
    (RigidifiedLineBundle.pullback
      (ε := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app V)
      (ε' := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app V ≫ Q.hom)
      Q.inv (𝟙 V.left) (by simp)).mapIso Φ ≪≫
    (RigidifiedLineBundle.pullbackCompTo
      (ε'' := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app V ≫ Q.hom)
      ((relativeSpace A.X.hom).map b) b.left Q.inv (𝟙 V.left) fb b.left
      (by rw [← hb, Iso.inv_hom_id_assoc]) (Category.id_comp _)
      ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality b).symm
      (by simp) _).app M

section Gluing

variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (𝒰 : T.left.OpenCover.{u})

/-- The relative space of a pairwise base overlap is the overlap of the induced cover. -/
def overlapIso (i j : 𝒰.I₀) :
    (relativeSpace A.X.hom).obj (Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)) ≅
      pullback ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f j) :=
  ((relativeSpace A.X.hom).map_isPullback (over_isPullback T (𝒰.f i) (𝒰.f j))).isoPullback

@[reassoc]
lemma overlapIso_hom_fst (i j : 𝒰.I₀) :
    (overlapIso A T 𝒰 i j).hom ≫ pullback.fst _ _ =
      (relativeSpace A.X.hom).map (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
        Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶ Over.mk (𝒰.f i ≫ T.hom)) :=
  IsPullback.isoPullback_hom_fst _

@[reassoc]
lemma overlapIso_hom_snd (i j : 𝒰.I₀) :
    (overlapIso A T 𝒰 i j).hom ≫ pullback.snd _ _ =
      (relativeSpace A.X.hom).map (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j))
          (by simp [pullback.condition_assoc]) :
        Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶ Over.mk (𝒰.f j ≫ T.hom)) :=
  IsPullback.isoPullback_hom_snd _

/-- The unit section on the pairwise overlap of the induced cover. -/
def overlapSection (i j : 𝒰.I₀) :
    pullback (𝒰.f i) (𝒰.f j) ⟶
      pullback ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f j) :=
  (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
    (Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)) ≫ (overlapIso A T 𝒰 i j).hom

@[reassoc]
lemma overlapSection_fst (i j : 𝒰.I₀) :
    overlapSection A T 𝒰 i j ≫ pullback.fst _ _ =
      pullback.fst (𝒰.f i) (𝒰.f j) ≫
        (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
          (Over.mk (𝒰.f i ≫ T.hom)) :=
  relativeSection_comp_square A _ _ _ (overlapIso_hom_fst A T 𝒰 i j)

@[reassoc]
lemma overlapSection_snd (i j : 𝒰.I₀) :
    overlapSection A T 𝒰 i j ≫ pullback.snd _ _ =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫
        (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
          (Over.mk (𝒰.f j ≫ T.hom)) :=
  relativeSection_comp_square A _ _ _ (overlapIso_hom_snd A T 𝒰 i j)

/-- The base triple overlap map to the second pairwise overlap. -/
def tripleLift (i j k : 𝒰.I₀) :
    pullback (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ⟶
      pullback (𝒰.f j) (𝒰.f k) :=
  pullback.lift
    (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
      pullback.snd (𝒰.f i) (𝒰.f j))
    (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
      pullback.snd (𝒰.f i) (𝒰.f k))
    (by simp only [Category.assoc, ← pullback.condition, pullback.condition_assoc])

/-- The relative space of a base triple overlap is the triple overlap of the induced cover. -/
def tripleIso (i j k : 𝒰.I₀) :
    (relativeSpace A.X.hom).obj
        (Over.mk (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
          pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)) ≅
      pullback (pullback.fst ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f j))
        (pullback.fst ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f k)) :=
  IsPullback.isoPullback
    (((relativeSpace A.X.hom).map_isPullback
      (over_isPullback (Over.mk (𝒰.f i ≫ T.hom)) (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.fst (𝒰.f i) (𝒰.f k)))).of_iso (Iso.refl _) (overlapIso A T 𝒰 i j)
      (overlapIso A T 𝒰 i k) (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm
      (by rw [Iso.refl_hom, Category.comp_id, overlapIso_hom_fst])
      (by rw [Iso.refl_hom, Category.comp_id, overlapIso_hom_fst]))

/-- The unit section on the triple overlap of the induced cover. -/
def tripleSection (i j k : 𝒰.I₀) :
    pullback (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ⟶
      pullback (pullback.fst ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f j))
        (pullback.fst ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f k)) :=
  (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
      (Over.mk (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
          pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)) ≫
    (tripleIso A T 𝒰 i j k).hom

@[reassoc]
lemma tripleSection_fst (i j k : 𝒰.I₀) :
    tripleSection A T 𝒰 i j k ≫ pullback.fst _ _ =
      pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
        overlapSection A T 𝒰 i j := by
  unfold tripleSection overlapSection
  exact relativeSection_comp_square' A _ _ _ _ (IsPullback.isoPullback_hom_fst _)

@[reassoc]
lemma tripleSection_snd (i j k : 𝒰.I₀) :
    tripleSection A T 𝒰 i j k ≫ pullback.snd _ _ =
      pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
        overlapSection A T 𝒰 i k := by
  unfold tripleSection overlapSection
  exact relativeSection_comp_square' A _ _ _ _ (IsPullback.isoPullback_hom_snd _)

@[reassoc]
lemma tripleLift_fst (i j k : 𝒰.I₀) :
    tripleLift T 𝒰 i j k ≫ pullback.fst (𝒰.f j) (𝒰.f k) =
      pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
        pullback.snd (𝒰.f i) (𝒰.f j) :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma tripleLift_snd (i j k : 𝒰.I₀) :
    tripleLift T 𝒰 i j k ≫ pullback.snd (𝒰.f j) (𝒰.f k) =
      pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
        pullback.snd (𝒰.f i) (𝒰.f k) :=
  pullback.lift_snd _ _ _

/-- The unit sections on triple and pairwise overlaps are compatible with the lift. -/
lemma tripleSection_lift (i j k : 𝒰.I₀)
    (w : (pullback.fst
          (pullback.fst ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f j))
          (pullback.fst ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f k)) ≫
        pullback.snd ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f j)) ≫
          (relativeOpenCover S A T 𝒰).f j =
      (pullback.snd
          (pullback.fst ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f j))
          (pullback.fst ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f k)) ≫
        pullback.snd ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f k)) ≫
          (relativeOpenCover S A T 𝒰).f k) :
    tripleSection A T 𝒰 i j k ≫ pullback.lift _ _ w =
      tripleLift T 𝒰 i j k ≫ overlapSection A T 𝒰 j k := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, tripleSection_fst_assoc, overlapSection_snd,
      Category.assoc, overlapSection_fst, tripleLift_fst_assoc]
  · rw [Category.assoc, pullback.lift_snd, tripleSection_snd_assoc, overlapSection_snd,
      Category.assoc, overlapSection_snd, tripleLift_snd_assoc]

/-- A rigidified overlap isomorphism, transported to the overlap of the induced cover. -/
def overlapRigidIso (i j : 𝒰.I₀) {L : RigidifiedFamily A (Over.mk (𝒰.f i ≫ T.hom))}
    {M : RigidifiedFamily A (Over.mk (𝒰.f j ≫ T.hom))}
    (Φ : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f i ≫ T.hom))).obj L ≅
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j)) (by simp [pullback.condition_assoc]) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f j ≫ T.hom))).obj M) :
    (RigidifiedLineBundle.pullback (ε' := overlapSection A T 𝒰 i j) (pullback.fst _ _)
        (pullback.fst (𝒰.f i) (𝒰.f j)) (overlapSection_fst A T 𝒰 i j)).obj L ≅
      (RigidifiedLineBundle.pullback (ε' := overlapSection A T 𝒰 i j) (pullback.snd _ _)
        (pullback.snd (𝒰.f i) (𝒰.f j)) (overlapSection_snd A T 𝒰 i j)).obj M :=
  isoTransport A _ _ (overlapIso A T 𝒰 i j) _ _ (overlapIso_hom_fst A T 𝒰 i j)
    (overlapIso_hom_snd A T 𝒰 i j) Φ

/-- The transported overlap isomorphisms of rigidified families glue to a module sheaf. -/
lemma exists_glued (glue : Langlands.Scheme.Modules.OpenCoverModuleGluingStatement.{u})
    (L : ∀ i, RigidifiedFamily A (Over.mk (𝒰.f i ≫ T.hom)))
    (Φ : ∀ i j,
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f i ≫ T.hom))).obj (L i) ≅
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j)) (by simp [pullback.condition_assoc]) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f j ≫ T.hom))).obj (L j)) :
    ∃ (N : ((relativeSpace A.X.hom).obj T).Modules)
      (ψ : ∀ i, (Scheme.Modules.pullback ((relativeOpenCover S A T 𝒰).f i)).obj N ≅
        (L i).obj.carrier),
      ∀ i j,
        (Scheme.Modules.pullback (pullback.fst ((relativeOpenCover S A T 𝒰).f i)
            ((relativeOpenCover S A T 𝒰).f j))).map (ψ i).hom ≫
          (overlapRigidIso A T 𝒰 i j (Φ i j)).hom.hom.val =
        (Langlands.Scheme.Modules.squarePullbackIso ((relativeOpenCover S A T 𝒰).f j)
            (pullback.fst ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f j))
            (pullback.snd ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f j))
            ((relativeOpenCover S A T 𝒰).f i) pullback.condition N).hom ≫
          (Scheme.Modules.pullback (pullback.snd ((relativeOpenCover S A T 𝒰).f i)
            ((relativeOpenCover S A T 𝒰).f j))).map (ψ j).hom := by
  refine glue _ (relativeOpenCover S A T 𝒰) (fun i ↦ (L i).obj.carrier)
    (fun i j ↦ (RigidifiedLineBundle.forgetModule (overlapSection A T 𝒰 i j)).mapIso
      (overlapRigidIso A T 𝒰 i j (Φ i j))) ?_
  intro i j k
  have cs := tripleSection_lift A T 𝒰 i j k
    (by simp only [Category.assoc, ← pullback.condition, pullback.condition_assoc])
  let α := (RigidifiedLineBundle.pullback _ _ (tripleSection_fst A T 𝒰 i j k)).mapIso
      (overlapRigidIso A T 𝒰 i j (Φ i j)) ≪≫
    RigidifiedLineBundle.squareIso _ _ (overlapSection_snd A T 𝒰 i j) _ _
      (overlapSection_fst A T 𝒰 j k) _ _ (tripleSection_fst A T 𝒰 i j k) _ _ cs
      (pullback.lift_fst _ _ _).symm (tripleLift_fst T 𝒰 i j k).symm (L j) ≪≫
    (RigidifiedLineBundle.pullback _ _ cs).mapIso (overlapRigidIso A T 𝒰 j k (Φ j k)) ≪≫
    RigidifiedLineBundle.squareIso _ _ (overlapSection_snd A T 𝒰 j k) _ _
      (overlapSection_snd A T 𝒰 i k) _ _ cs _ _ (tripleSection_snd A T 𝒰 i j k)
      (pullback.lift_snd _ _ _) (tripleLift_snd T 𝒰 i j k) (L k)
  let β := RigidifiedLineBundle.squareIso _ _ (overlapSection_fst A T 𝒰 i j) _ _
      (overlapSection_fst A T 𝒰 i k) _ _ (tripleSection_fst A T 𝒰 i j k) _ _
      (tripleSection_snd A T 𝒰 i j k) pullback.condition pullback.condition (L i) ≪≫
    (RigidifiedLineBundle.pullback _ _ (tripleSection_snd A T 𝒰 i j k)).mapIso
      (overlapRigidIso A T 𝒰 i k (Φ i k))
  have hαβ : α = β :=
    (rigidifiedIso_subsingleton_of_iso A _ (tripleIso A T 𝒰 i j k) rfl _ _).elim α β
  have h := congrArg
    (fun e ↦ (RigidifiedLineBundle.forgetModule (tripleSection A T 𝒰 i j k)).map e.hom) hαβ
  simp only [α, β, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    RigidifiedLineBundle.forgetModule_map_pullback_map,
    RigidifiedLineBundle.forgetModule_map_squareIso_hom] at h
  exact h

/-- The base-section square of a cover member. -/
lemma chartComm (i : 𝒰.I₀) :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
        (Over.mk (𝒰.f i ≫ T.hom)) ≫ (relativeOpenCover S A T 𝒰).f i =
      𝒰.f i ≫ (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T :=
  ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality
    (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).symm

/-- A module whose pullbacks to the induced cover are line bundles is a line bundle. -/
lemma glued_isLocallyFreeRankOne (L : ∀ i, RigidifiedFamily A (Over.mk (𝒰.f i ≫ T.hom)))
    (N : ((relativeSpace A.X.hom).obj T).Modules)
    (ψ : ∀ i, (Scheme.Modules.pullback ((relativeOpenCover S A T 𝒰).f i)).obj N ≅
      (L i).obj.carrier) :
    IsLocallyFreeRankOne N := by
  intro x
  obtain ⟨i, y, rfl⟩ := (relativeOpenCover S A T 𝒰).exists_eq x
  exact IsLocallyFreeRankOne.exists_of_pullback _ ((L i).property.of_iso (ψ i).symm) y

/-- The rigidification of a local representative, moved to the chart of a module. -/
def chartRig (i : 𝒰.I₀) (L : RigidifiedFamily A (Over.mk (𝒰.f i ≫ T.hom)))
    (N : ((relativeSpace A.X.hom).obj T).Modules)
    (ψ : (Scheme.Modules.pullback ((relativeOpenCover S A T 𝒰).f i)).obj N ≅ L.obj.carrier) :
    structureModule (Over.mk (𝒰.f i ≫ T.hom)).left ≅
      (Scheme.Modules.pullback ((relativeSection A.X.hom (unitSection A)
        (unitSection_comp A)).app (Over.mk (𝒰.f i ≫ T.hom)))).obj
          ((Scheme.Modules.pullback ((relativeOpenCover S A T 𝒰).f i)).obj N) :=
  L.obj.rigidification ≪≫ (Scheme.Modules.pullback _).mapIso ψ.symm

/-- The chart identification as a rigidified isomorphism. -/
def chartRigIso (i : 𝒰.I₀) (L : RigidifiedFamily A (Over.mk (𝒰.f i ≫ T.hom)))
    (N : ((relativeSpace A.X.hom).obj T).Modules)
    (ψ : (Scheme.Modules.pullback ((relativeOpenCover S A T 𝒰).f i)).obj N ≅ L.obj.carrier) :
    (⟨(Scheme.Modules.pullback ((relativeOpenCover S A T 𝒰).f i)).obj N,
        chartRig A T 𝒰 i L N ψ⟩ :
      RigidifiedModule ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
        (Over.mk (𝒰.f i ≫ T.hom)))) ≅ L.obj :=
  RigidifiedModule.isoMk ψ (by simp [chartRig])

/-- Compatible chart identifications glue the chart rigidifications to the whole base. -/
lemma exists_rigidification (L : ∀ i, RigidifiedFamily A (Over.mk (𝒰.f i ≫ T.hom)))
    (Θ : ∀ i j,
      (RigidifiedLineBundle.pullback (ε' := overlapSection A T 𝒰 i j) (pullback.fst _ _)
          (pullback.fst (𝒰.f i) (𝒰.f j)) (overlapSection_fst A T 𝒰 i j)).obj (L i) ≅
        (RigidifiedLineBundle.pullback (ε' := overlapSection A T 𝒰 i j) (pullback.snd _ _)
          (pullback.snd (𝒰.f i) (𝒰.f j)) (overlapSection_snd A T 𝒰 i j)).obj (L j))
    (N : ((relativeSpace A.X.hom).obj T).Modules)
    (ψ : ∀ i, (Scheme.Modules.pullback ((relativeOpenCover S A T 𝒰).f i)).obj N ≅
      (L i).obj.carrier)
    (hψ : ∀ i j,
        (Scheme.Modules.pullback (pullback.fst ((relativeOpenCover S A T 𝒰).f i)
            ((relativeOpenCover S A T 𝒰).f j))).map (ψ i).hom ≫
          (Θ i j).hom.hom.val =
        (Langlands.Scheme.Modules.squarePullbackIso ((relativeOpenCover S A T 𝒰).f j)
            (pullback.fst ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f j))
            (pullback.snd ((relativeOpenCover S A T 𝒰).f i) ((relativeOpenCover S A T 𝒰).f j))
            ((relativeOpenCover S A T 𝒰).f i) pullback.condition N).hom ≫
          (Scheme.Modules.pullback (pullback.snd ((relativeOpenCover S A T 𝒰).f i)
            ((relativeOpenCover S A T 𝒰).f j))).map (ψ j).hom) :
    ∃ ρ : structureModule T.left ≅ (Scheme.Modules.pullback
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)).obj N,
      ∀ i, (Scheme.Modules.pullback (𝒰.f i)).map ρ.hom =
        (Langlands.Scheme.Modules.chartRigidification _ N (chartComm A T 𝒰 i)
          (chartRig A T 𝒰 i (L i) N (ψ i))).hom := by
  refine (Langlands.Scheme.Modules.openCoverIsoGluing_of_homGluing
    Langlands.Scheme.Modules.OpenCoverHomGluing.openCoverHomGluing T.left 𝒰
    (structureModule T.left) _
    (fun i ↦ Langlands.Scheme.Modules.chartRigidification _ N (chartComm A T 𝒰 i)
      (chartRig A T 𝒰 i (L i) N (ψ i))) ?_).exists
  intro i j
  have hz : pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j = pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i :=
    pullback.condition.symm
  have cw : overlapSection A T 𝒰 i j ≫ pullback.fst ((relativeOpenCover S A T 𝒰).f i)
        ((relativeOpenCover S A T 𝒰).f j) ≫ (relativeOpenCover S A T 𝒰).f i =
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) ≫
        (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T := by
    rw [overlapSection_fst_assoc, chartComm, Category.assoc]
  have hi := Langlands.Scheme.Modules.chartRigidification_restrict _ N (chartComm A T 𝒰 i)
    (chartRig A T 𝒰 i (L i) N (ψ i)) (pullback.fst _ _) (pullback.fst (𝒰.f i) (𝒰.f j))
    (overlapSection_fst A T 𝒰 i j) _ rfl _ rfl cw
  have hj := Langlands.Scheme.Modules.chartRigidification_restrict _ N (chartComm A T 𝒰 j)
    (chartRig A T 𝒰 j (L j) N (ψ j)) (pullback.snd _ _) (pullback.snd (𝒰.f i) (𝒰.f j))
    (overlapSection_snd A T 𝒰 i j) _ hz _ pullback.condition.symm cw
  let Θ' := (RigidifiedModule.pullback (pullback.fst _ _) (pullback.fst (𝒰.f i) (𝒰.f j))
      (overlapSection_fst A T 𝒰 i j)).map (chartRigIso A T 𝒰 i (L i) N (ψ i)).hom ≫
    (Θ i j).hom.hom ≫
      (RigidifiedModule.pullback (pullback.snd _ _) (pullback.snd (𝒰.f i) (𝒰.f j))
        (overlapSection_snd A T 𝒰 i j)).map (chartRigIso A T 𝒰 j (L j) N (ψ j)).inv
  have hΘ' : Θ'.val = (Langlands.Scheme.Modules.squarePullbackIso
      ((relativeOpenCover S A T 𝒰).f j) (pullback.fst _ _) (pullback.snd _ _)
      ((relativeOpenCover S A T 𝒰).f i) pullback.condition N).hom := by
    change (Scheme.Modules.pullback (pullback.fst _ _)).map (ψ i).hom ≫
        (Θ i j).hom.hom.val ≫ (Scheme.Modules.pullback (pullback.snd _ _)).map (ψ j).inv = _
    rw [reassoc_of% (hψ i j)]
    simp
  have hr := Langlands.Scheme.Modules.restricted_rigidification_eq
    (εP := overlapSection A T 𝒰 i j) _ _ (pullback.fst _ _) (pullback.snd _ _)
    (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j))
    (overlapSection_fst A T 𝒰 i j) (overlapSection_snd A T 𝒰 i j) pullback.condition N
    (chartRig A T 𝒰 i (L i) N (ψ i)) (chartRig A T 𝒰 j (L j) N (ψ j)) Θ' hΘ' _ rfl
    pullback.condition.symm
  rw [← hr] at hj
  exact Langlands.Scheme.Modules.square_compatible_of_common_map (𝒰.f j) (pullback.fst _ _)
    (pullback.snd _ _) (𝒰.f i) pullback.condition (Iso.refl _) _ _ _ (Category.id_comp _)
    (Category.id_comp _) hz rfl _ _ _ _ _ hi hj

/-- The glued rigidified family restricts to each local representative. -/
lemma glued_restrict_iso (i : 𝒰.I₀) (L : RigidifiedFamily A (Over.mk (𝒰.f i ≫ T.hom)))
    (N : ((relativeSpace A.X.hom).obj T).Modules) (hN : IsLocallyFreeRankOne N)
    (ψ : (Scheme.Modules.pullback ((relativeOpenCover S A T 𝒰).f i)).obj N ≅ L.obj.carrier)
    (ρ : structureModule T.left ≅ (Scheme.Modules.pullback
      ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)).obj N)
    (hρ : (Scheme.Modules.pullback (𝒰.f i)).map ρ.hom =
      (Langlands.Scheme.Modules.chartRigidification _ N (chartComm A T 𝒰 i)
        (chartRig A T 𝒰 i L N ψ)).hom) :
    Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj
        (⟨⟨N, ρ⟩, hN⟩ : RigidifiedFamily A T) ≅ L) := by
  refine ⟨RigidifiedLineBundle.isoMk ψ ?_⟩
  change ((Langlands.Scheme.Modules.pullbackUnitIso (𝒰.f i)).inv ≫
      (Scheme.Modules.pullback (𝒰.f i)).map ρ.hom ≫
        (RigidifiedModule.squarePullbackIso ((relativeOpenCover S A T 𝒰).f i) (𝒰.f i)
          (chartComm A T 𝒰 i)).hom.app N) ≫
      (Scheme.Modules.pullback _).map ψ.hom = L.obj.rigidification.hom
  rw [hρ]
  simp [Langlands.Scheme.Modules.chartRigidification, chartRig]

end Gluing

/-- Zariski gluing of actual rigidified classes, from gluing of actual module sheaves. -/
theorem rigidifiedClassesZariskiGluing_of_moduleGluing
    (glue : Langlands.Scheme.Modules.OpenCoverModuleGluingStatement.{u}) :
    RigidifiedClassesZariskiGluingStatement.{u} := by
  classical
  intro S A T 𝒰 q hq
  have hΦ : ∀ i j, Nonempty
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f i ≫ T.hom))).obj (q i).out ≅
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j)) (by simp [pullback.condition_assoc]) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f j ≫ T.hom))).obj (q j).out) := by
    intro i j
    have h := hq i j
    rw [← Quotient.out_eq (q i), ← Quotient.out_eq (q j)] at h
    exact Quotient.exact h
  let Φ := fun i j ↦ Classical.choice (hΦ i j)
  obtain ⟨N, ψ, hψ⟩ := exists_glued A T 𝒰 glue (fun i ↦ (q i).out) Φ
  have hN := glued_isLocallyFreeRankOne A T 𝒰 (fun i ↦ (q i).out) N ψ
  obtain ⟨ρ, hρ⟩ := exists_rigidification A T 𝒰 (fun i ↦ (q i).out)
    (fun i j ↦ overlapRigidIso A T 𝒰 i j (Φ i j)) N ψ hψ
  refine ⟨Quotient.mk _ (⟨⟨N, ρ⟩, hN⟩ : RigidifiedFamily A T), fun i ↦ ?_⟩
  exact (Quotient.sound (glued_restrict_iso A T 𝒰 i (q i).out N hN (ψ i) ρ (hρ i))).trans
    (Quotient.out_eq (q i))

/-- Zariski gluing of actual rigidified abelian-scheme classes. -/
theorem rigidifiedClassesZariskiGluing : RigidifiedClassesZariskiGluingStatement.{u} :=
  rigidifiedClassesZariskiGluing_of_moduleGluing Langlands.Scheme.Modules.openCoverModuleGluing

end Langlands.AbelianScheme
