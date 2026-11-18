import Langlands.Geometry.FormalGroup.AtlasCoefficientAssociativity
import Langlands.Geometry.FormalGroup.AtlasOrderComparisonIdentity
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlongSquare

/-! # Actual composition of commuting coefficient squares -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Cancel the same actual full-order integral atlas isomorphism. -/
theorem Iso.trans_right_cancel (a b : Iso E E' h) (c : Iso E' E'' k)
    (he : a.trans c = b.trans c) : a = b := by
  have ht := congrArg (fun q => q.trans c.symm) he
  simpa only [Iso.trans_assoc, Iso.self_trans_symm, Iso.trans_refl] using ht

variable {S T : Type v} [CommRing S] [CommRing T] [Algebra O S] [Algebra O T]

/-- Actual supplied coefficient extension preserves whole integral composition. -/
theorem Iso.baseChangeAlong_trans (a : Iso E E' h) (b : Iso E' E'' k)
    (m : R →ₐ[O] S) :
    (a.trans b).baseChangeAlong m = (a.baseChangeAlong m).trans (b.baseChangeAlong m) := by
  apply Iso.ext_hom
  simp only [Iso.baseChangeAlong_hom, Iso.trans]
  exact Hom.baseChangeAlong_comp b.hom a.hom m

/-- Actual supplied coefficient extension preserves the same stored integral inverse. -/
theorem Iso.baseChangeAlong_symm (a : Iso E E' h) (m : R →ₐ[O] S) :
    a.symm.baseChangeAlong m = (a.baseChangeAlong m).symm := by
  apply Iso.ext_hom
  exact (Iso.baseChangeAlong_hom a.symm m).trans (Iso.baseChangeAlong_inv a m).symm

/-- Actual supplied coefficient extension preserves the integral identity. -/
theorem Iso.baseChangeAlong_refl (E : OrderAction D X) (m : R →ₐ[O] S) :
    (Iso.refl E).baseChangeAlong m = Iso.refl (E.baseChangeAlong m) := by
  apply Iso.ext_hom
  rw [Iso.baseChangeAlong_hom]
  exact Hom.baseChangeAlong_id E m

/-- Identity-coordinate equality transports compose as actual whole integral atlas maps. -/
theorem baseAlongEqIso_trans (E : OrderAction D X) {f g j : R →ₐ[O] S}
    (a : f = g) (b : g = j) :
    (E.baseAlongEqIso a).trans (E.baseAlongEqIso b) = E.baseAlongEqIso (a.trans b) := by
  cases a
  cases b
  exact Iso.refl_trans _

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Equality in the first coefficient map gives its actual coefficient-composition square. -/
theorem baseAlongEqIso_comp_left (E : OrderAction D X) {f f' : R →ₐ[O] S}
    (a : f = f') (g : S →ₐ[O] T) :
    ((E.baseAlongEqIso a).baseChangeAlong g).trans (E.baseAlongCompIso f' g) =
      (E.baseAlongCompIso f g).trans (E.baseAlongEqIso (congrArg (fun q => g.comp q) a)) := by
  cases a
  simp only [baseAlongEqIso, Iso.baseChangeAlong_refl, Iso.refl_trans, Iso.trans_refl]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Equality in the second coefficient map gives its actual coefficient-composition square. -/
theorem baseAlongEqIso_comp_right (E : OrderAction D X) (f : R →ₐ[O] S)
    {g g' : S →ₐ[O] T} (a : g = g') :
    ((E.baseChangeAlong f).baseAlongEqIso a).trans (E.baseAlongCompIso f g') =
      (E.baseAlongCompIso f g).trans (E.baseAlongEqIso (congrArg (fun q => q.comp f) a)) := by
  cases a
  exact (Iso.refl_trans _).trans (Iso.trans_refl _).symm

variable {S' : Type v} [CommRing S'] [Algebra O S']

/-- Compose the canonical coefficient-square map with its specified target normalization. -/
theorem baseAlongSquareIso_cancel (E : OrderAction D X) (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (E.baseAlongSquareIso f g p q e).trans (E.baseAlongCompIso p q) =
      (E.baseAlongCompIso f g).trans (E.baseAlongEqIso e) := by
  unfold baseAlongSquareIso
  rw [Iso.trans_assoc, Iso.symm_trans_self, Iso.trans_refl]

variable {R' T' : Type v} [CommRing R'] [CommRing T'] [Algebra O R'] [Algebra O T']

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Two adjacent actual commuting coefficient squares compose through their specified normalizations. -/
theorem baseAlongSquareIso_comp (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] R') (q : S →ₐ[O] S') (r : T →ₐ[O] T')
    (f' : R' →ₐ[O] S') (g' : S' →ₐ[O] T')
    (ef : q.comp f = f'.comp p) (eg : r.comp g = g'.comp q)
    (ec : r.comp (g.comp f) = (g'.comp f').comp p) :
    (((E.baseChangeAlong f).baseAlongSquareIso g r q g' eg).trans
        ((E.baseAlongSquareIso f q p f' ef).baseChangeAlong g')).trans
          ((E.baseChangeAlong p).baseAlongCompIso f' g') =
      ((E.baseAlongCompIso f g).baseChangeAlong r).trans
        (E.baseAlongSquareIso (g.comp f) r p (g'.comp f') ec) := by
  let a := (E.baseChangeAlong f).baseAlongSquareIso g r q g' eg
  let b := (E.baseAlongSquareIso f q p f' ef).baseChangeAlong g'
  let c := (E.baseChangeAlong p).baseAlongCompIso f' g'
  let d := E.baseAlongCompIso p (g'.comp f')
  let m := (E.baseAlongCompIso p f').baseChangeAlong g'
  let n := E.baseAlongCompIso (f'.comp p) g'
  let w := (E.baseAlongCompIso f q).baseChangeAlong g'
  let z := (E.baseAlongEqIso ef).baseChangeAlong g'
  let q₁ := E.baseAlongCompIso (q.comp f) g'
  let u₁ := E.baseAlongEqIso (congrArg (fun j => g'.comp j) ef)
  let cfq := (E.baseChangeAlong f).baseAlongCompIso q g'
  let cfm := E.baseAlongCompIso f (g'.comp q)
  let cfg := (E.baseChangeAlong f).baseAlongCompIso g r
  let eta := (E.baseChangeAlong f).baseAlongEqIso eg
  let cfr := E.baseAlongCompIso f (r.comp g)
  let u₂ := E.baseAlongEqIso (congrArg (fun j => j.comp f) eg)
  let norm := (E.baseAlongCompIso f g).baseChangeAlong r
  let direct := E.baseAlongCompIso (g.comp f) r
  let ue := E.baseAlongEqIso ec
  let sc := E.baseAlongSquareIso (g.comp f) r p (g'.comp f') ec
  have hA : c.trans d = m.trans n := (E.baseAlongCompIso_assoc p f' g').symm
  have hB : w.trans q₁ = cfq.trans cfm := E.baseAlongCompIso_assoc f q g'
  have hC : norm.trans direct = cfg.trans cfr := E.baseAlongCompIso_assoc f g r
  have hsF : b.trans m = w.trans z := by
    have hh := congrArg (fun j => j.baseChangeAlong g') (E.baseAlongSquareIso_cancel f q p f' ef)
    simpa only [Iso.baseChangeAlong_trans] using hh
  have hsG : a.trans cfq = cfg.trans eta :=
    (E.baseChangeAlong f).baseAlongSquareIso_cancel g r q g' eg
  have heF : z.trans n = q₁.trans u₁ := E.baseAlongEqIso_comp_left ef g'
  have heG : eta.trans cfm = cfr.trans u₂ := E.baseAlongEqIso_comp_right f eg
  have he : u₂.trans u₁ = ue := E.baseAlongEqIso_trans _ _
  have hd : sc.trans d = direct.trans ue := E.baseAlongSquareIso_cancel (g.comp f) r p (g'.comp f') ec
  apply Iso.trans_right_cancel _ _ d
  change ((a.trans b).trans c).trans d = (norm.trans sc).trans d
  have hl : ((a.trans b).trans c).trans d = norm.trans (direct.trans ue) := by
    simp only [Iso.trans_assoc]
    rw [hA, ← Iso.trans_assoc b m n, hsF, Iso.trans_assoc w z n, heF,
      ← Iso.trans_assoc w q₁ u₁, hB]
    simp only [Iso.trans_assoc]
    rw [← Iso.trans_assoc a cfq (cfm.trans u₁), hsG]
    simp only [Iso.trans_assoc]
    rw [← Iso.trans_assoc eta cfm u₁, heG]
    simp only [Iso.trans_assoc]
    rw [he, ← Iso.trans_assoc cfg cfr ue, hC.symm, Iso.trans_assoc]
  exact hl.trans ((Iso.trans_assoc norm sc d).trans (congrArg (fun j => norm.trans j) hd)).symm

variable [IsDomain O] {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The two actual composed coefficient-square routes, rationalized on their specified common test. -/
def baseAlongSquareCompositionTestSquare (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] R') (q : S →ₐ[O] S') (r : T →ₐ[O] T')
    (f' : R' →ₐ[O] S') (g' : S' →ₐ[O] T')
    (ef : q.comp f = f'.comp p) (eg : r.comp g = g'.comp q)
    (ec : r.comp (g.comp f) = (g'.comp f').comp p)
    (A : CommAlgCat.{v} T')
    (b : ((X.baseChangeAlong p).baseChangeAlong (g'.comp f')).opens)
    (hb : IsUnit (algebraMap T' A b.val)) :=
  let l := ((((E.baseChangeAlong f).baseAlongSquareIso g r q g' eg).trans
    ((E.baseAlongSquareIso f q p f' ef).baseChangeAlong g')).trans
      ((E.baseChangeAlong p).baseAlongCompIso f' g')).onChart A b hb
  let r₁ := (((E.baseAlongCompIso f g).baseChangeAlong r).trans
    (E.baseAlongSquareIso (g.comp f) r p (g'.comp f') ec)).onChart A b hb
  ModuleLaw.OrderAction.Iso.rationalSquare (F := F) l (ModuleLaw.OrderAction.Iso.refl _)
    r₁ (ModuleLaw.OrderAction.Iso.refl _) (by
      have he := congrArg (fun j => j.onChart A b hb)
        (E.baseAlongSquareIso_comp f g p q r f' g' ef eg ec)
      apply ModuleLaw.OrderAction.Iso.ext_hom
      change (ModuleLaw.OrderAction.Hom.id _).comp l.hom = (ModuleLaw.OrderAction.Hom.id _).comp r₁.hom
      simp only [ModuleLaw.OrderAction.Hom.id_comp]
      exact congrArg ModuleLaw.OrderAction.Iso.hom he)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
