import Langlands.Geometry.FormalGroup.AtlasRationalBaseChangeSelf
import Langlands.Geometry.FormalGroup.AtlasRationalBaseChangeAlongComposition

/-! # Actual formal comparisons for commuting coefficient squares -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R S S' T : Type v} [CommRing R] [CommRing S] [CommRing S'] [CommRing T]
variable [Algebra O R] [Algebra O S] [Algebra O S'] [Algebra O T]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Equal supplied coefficient maps have equal actual image covers. -/
theorem baseAlongEqOpens_eq (X : BasicAtlas O R σ)
    {f g : R →ₐ[O] T} (e : f = g) :
    (X.baseChangeAlong f).opens = (X.baseChangeAlong g).opens := by
  cases e
  rfl

/-- Equal supplied coefficient maps compare by transport of the actual identity. -/
def baseAlongEqIso (X : BasicAtlas O R σ) {f g : R →ₐ[O] T} (e : f = g) :
    Iso (X.baseChangeAlong f) (X.baseChangeAlong g) (X.baseAlongEqOpens_eq e) := by
  cases e
  exact Iso.refl _

/-- Transport original complete families between equal restricted coefficient tests. -/
def baseAlongEqPointEquiv (X : BasicAtlas O R σ) {f g : R →ₐ[O] T} (e : f = g)
    (A : CommAlgCat.{v} T) :
    X.Point (restrictCoefficientAlgebra f A) ≃ₗ[O]
      X.Point (restrictCoefficientAlgebra g A) := by
  cases e
  exact LinearEquiv.refl O _

/-- The actual identity transport realizes the whole-family equality comparison. -/
theorem baseAlongEq_onPoints (X : BasicAtlas O R σ)
    {f g : R →ₐ[O] T} (e : f = g) (A : CommAlgCat.{v} T)
    (x : X.Point (restrictCoefficientAlgebra f A)) :
    (X.baseAlongEqIso e).onPoints A (X.baseChangeAlongPointEquiv f A x) =
      X.baseChangeAlongPointEquiv g A (X.baseAlongEqPointEquiv e A x) := by
  cases e
  exact Hom.onPoints_id _ _ _

namespace Hom

/-- Transport along equal maps is natural in actual integral formal maps. -/
theorem baseAlongEq_natural (a : Hom X Y h) {f g : R →ₐ[O] T} (e : f = g) :
    (Y.baseAlongEqIso e).hom.comp
        (h := baseAlongMapOpens_eq X Y f h) (a.baseChangeAlong f) =
      (a.baseChangeAlong g).comp (X.baseAlongEqIso e).hom := by
  cases e
  exact (id_comp _).trans (comp_id _).symm

/-- The inverse equality comparison gives the reverse integral square. -/
theorem baseAlongEq_inv_natural (a : Hom X Y h) {f g : R →ₐ[O] T} (e : f = g) :
    (a.baseChangeAlong f).comp
        (k := baseAlongMapOpens_eq X Y f h) (X.baseAlongEqIso e).inv =
      (Y.baseAlongEqIso e).inv.comp (a.baseChangeAlong g) := by
  cases e
  exact (comp_id _).trans (id_comp _).symm

end Hom

/-- The two successive image covers of a commuting coefficient square agree. -/
theorem baseAlongSquareOpens_eq (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    ((X.baseChangeAlong f).baseChangeAlong g).opens =
      ((X.baseChangeAlong p).baseChangeAlong q).opens :=
  ((X.baseAlongCompOpens_eq f g).trans (X.baseAlongEqOpens_eq e)).trans
    (X.baseAlongCompOpens_eq p q).symm

/-- Compare both routes by actual composition maps and equality of their composites. -/
def baseAlongSquareIso (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    Iso ((X.baseChangeAlong f).baseChangeAlong g)
      ((X.baseChangeAlong p).baseChangeAlong q) (X.baseAlongSquareOpens_eq f g p q e) :=
  ((X.baseAlongCompIso f g).trans (X.baseAlongEqIso e)).trans
    (X.baseAlongCompIso p q).symm

/-- The specified formal comparison realizes both routes on entire compatible families. -/
theorem baseAlongSquare_onPoints (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p)
    (A : CommAlgCat.{v} T) (x : X.Point (restrictCoefficientAlgebra (g.comp f) A)) :
    (X.baseAlongSquareIso f g p q e).onPoints A
      ((X.baseChangeAlong f).baseChangeAlongPointEquiv g A
        (X.baseChangeAlongPointEquiv f (restrictCoefficientAlgebra g A) x)) =
      (X.baseChangeAlong p).baseChangeAlongPointEquiv q A
        (X.baseChangeAlongPointEquiv p (restrictCoefficientAlgebra q A)
          (X.baseAlongEqPointEquiv e A x)) := by
  change ((X.baseAlongCompIso p q).inv.comp
    ((X.baseAlongEqIso e).hom.comp (X.baseAlongCompIso f g).hom)).onPoints A _ = _
  rw [Hom.onPoints_comp, Hom.onPoints_comp]
  change ((X.baseAlongCompIso p q).onPoints A).symm
    ((X.baseAlongEqIso e).onPoints A ((X.baseAlongCompIso f g).onPoints A _)) = _
  rw [baseAlongComp_onPoints, baseAlongEq_onPoints]
  exact X.baseAlongComp_inv_onPoints p q A _

/-- The same formal inverse gives the reverse entire-family square. -/
theorem baseAlongSquare_inv_onPoints (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p)
    (A : CommAlgCat.{v} T) (x : X.Point (restrictCoefficientAlgebra (g.comp f) A)) :
    ((X.baseAlongSquareIso f g p q e).onPoints A).symm
      ((X.baseChangeAlong p).baseChangeAlongPointEquiv q A
        (X.baseChangeAlongPointEquiv p (restrictCoefficientAlgebra q A)
          (X.baseAlongEqPointEquiv e A x))) =
      (X.baseChangeAlong f).baseChangeAlongPointEquiv g A
        (X.baseChangeAlongPointEquiv f (restrictCoefficientAlgebra g A) x) :=
  (LinearEquiv.symm_apply_eq ((X.baseAlongSquareIso f g p q e).onPoints A)).mpr
    (X.baseAlongSquare_onPoints f g p q e A x).symm

namespace Hom

/-- A commuting coefficient square compares actual integral maps naturally. -/
theorem baseAlongSquare_natural (a : Hom X Y h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (Y.baseAlongSquareIso f g p q e).hom.comp
        (h := baseAlongCompMapOpens_eq X Y f g h)
        ((a.baseChangeAlong f).baseChangeAlong g) =
      ((a.baseChangeAlong p).baseChangeAlong q).comp
        (X.baseAlongSquareIso f g p q e).hom := by
  let aL : Hom ((X.baseChangeAlong f).baseChangeAlong g)
      ((Y.baseChangeAlong f).baseChangeAlong g)
      (baseAlongCompMapOpens_eq X Y f g h) :=
    (a.baseChangeAlong f).baseChangeAlong g
  let aC : Hom (X.baseChangeAlong (g.comp f)) (Y.baseChangeAlong (g.comp f))
      (baseAlongMapOpens_eq X Y (g.comp f) h) := a.baseChangeAlong (g.comp f)
  let aD : Hom (X.baseChangeAlong (q.comp p)) (Y.baseChangeAlong (q.comp p))
      (baseAlongMapOpens_eq X Y (q.comp p) h) := a.baseChangeAlong (q.comp p)
  let aR : Hom ((X.baseChangeAlong p).baseChangeAlong q)
      ((Y.baseChangeAlong p).baseChangeAlong q)
      (baseAlongCompMapOpens_eq X Y p q h) :=
    (a.baseChangeAlong p).baseChangeAlong q
  have left : (Y.baseAlongCompIso f g).hom.comp aL =
      aC.comp (X.baseAlongCompIso f g).hom := a.baseAlongComp_natural f g
  have middle : (Y.baseAlongEqIso e).hom.comp aC =
      aD.comp (X.baseAlongEqIso e).hom := a.baseAlongEq_natural e
  have right : aR.comp (X.baseAlongCompIso p q).inv =
      (Y.baseAlongCompIso p q).inv.comp aD := a.baseAlongComp_inv_natural p q
  change
    ((Y.baseAlongCompIso p q).inv.comp
      ((Y.baseAlongEqIso e).hom.comp (Y.baseAlongCompIso f g).hom)).comp aL =
    aR.comp ((X.baseAlongCompIso p q).inv.comp
      ((X.baseAlongEqIso e).hom.comp (X.baseAlongCompIso f g).hom))
  rw [comp_assoc, comp_assoc, left,
    ← comp_assoc (Y.baseAlongEqIso e).hom, middle,
    comp_assoc, ← comp_assoc (Y.baseAlongCompIso p q).inv,
    ← right, comp_assoc]

/-- The inverse of the same comparison gives the reverse integral square. -/
theorem baseAlongSquare_inv_natural (a : Hom X Y h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    ((a.baseChangeAlong f).baseChangeAlong g).comp
        (k := baseAlongCompMapOpens_eq X Y f g h)
        (X.baseAlongSquareIso f g p q e).inv =
      (Y.baseAlongSquareIso f g p q e).inv.comp
        ((a.baseChangeAlong p).baseChangeAlong q) := by
  let aL : Hom ((X.baseChangeAlong f).baseChangeAlong g)
      ((Y.baseChangeAlong f).baseChangeAlong g)
      (baseAlongCompMapOpens_eq X Y f g h) :=
    (a.baseChangeAlong f).baseChangeAlong g
  let aC : Hom (X.baseChangeAlong (g.comp f)) (Y.baseChangeAlong (g.comp f))
      (baseAlongMapOpens_eq X Y (g.comp f) h) := a.baseChangeAlong (g.comp f)
  let aD : Hom (X.baseChangeAlong (q.comp p)) (Y.baseChangeAlong (q.comp p))
      (baseAlongMapOpens_eq X Y (q.comp p) h) := a.baseChangeAlong (q.comp p)
  let aR : Hom ((X.baseChangeAlong p).baseChangeAlong q)
      ((Y.baseChangeAlong p).baseChangeAlong q)
      (baseAlongCompMapOpens_eq X Y p q h) :=
    (a.baseChangeAlong p).baseChangeAlong q
  have left : aL.comp (X.baseAlongCompIso f g).inv =
      (Y.baseAlongCompIso f g).inv.comp aC := a.baseAlongComp_inv_natural f g
  have middle : aC.comp (X.baseAlongEqIso e).inv =
      (Y.baseAlongEqIso e).inv.comp aD := a.baseAlongEq_inv_natural e
  have right : (Y.baseAlongCompIso p q).hom.comp aR =
      aD.comp (X.baseAlongCompIso p q).hom := a.baseAlongComp_natural p q
  change
    aL.comp (((X.baseAlongCompIso f g).inv.comp
      (X.baseAlongEqIso e).inv).comp (X.baseAlongCompIso p q).hom) =
    (((Y.baseAlongCompIso f g).inv.comp
      (Y.baseAlongEqIso e).inv).comp (Y.baseAlongCompIso p q).hom).comp aR
  rw [← comp_assoc, ← comp_assoc, left,
    comp_assoc (Y.baseAlongCompIso f g).inv, middle,
    ← comp_assoc, comp_assoc, ← right, ← comp_assoc]

end Hom

variable {F : Type w} [Field F] [Algebra O F]

namespace RationalHom

/-- Equality transport is natural on the entire global rational Hom. -/
theorem baseAlongEq_natural (a : RationalHom F X Y h) {f g : R →ₐ[O] T} (e : f = g) :
    comp (h := baseAlongMapOpens_eq X Y f h)
        (ofHom (F := F) (Y.baseAlongEqIso e).hom)
        (baseChangeAlong (X := X) (Y := Y) (h := h) f a) =
      comp (baseChangeAlong (X := X) (Y := Y) (h := h) g a)
        (ofHom (X.baseAlongEqIso e).hom) := by
  cases e
  exact (id_comp _).trans (comp_id _).symm

/-- The inverse equality transport gives the reverse global rational square. -/
theorem baseAlongEq_inv_natural (a : RationalHom F X Y h) {f g : R →ₐ[O] T}
    (e : f = g) :
    comp (k := baseAlongMapOpens_eq X Y f h)
        (baseChangeAlong (X := X) (Y := Y) (h := h) f a)
        (ofHom (F := F) (X.baseAlongEqIso e).inv) =
      comp (ofHom (Y.baseAlongEqIso e).inv)
        (baseChangeAlong (X := X) (Y := Y) (h := h) g a) := by
  cases e
  exact (comp_id _).trans (id_comp _).symm

/-- Commuting coefficient squares compare every global tensor map naturally. -/
theorem baseAlongSquare_natural (a : RationalHom F X Y h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    comp (h := baseAlongCompMapOpens_eq X Y f g h)
        (ofHom (F := F) (Y.baseAlongSquareIso f g p q e).hom)
        (baseChangeAlong (X := X.baseChangeAlong f) (Y := Y.baseChangeAlong f)
          (h := baseAlongMapOpens_eq X Y f h) g
          (baseChangeAlong (X := X) (Y := Y) (h := h) f a)) =
      comp (baseChangeAlong (X := X.baseChangeAlong p) (Y := Y.baseChangeAlong p)
          (h := baseAlongMapOpens_eq X Y p h) q
          (baseChangeAlong (X := X) (Y := Y) (h := h) p a))
        (ofHom (X.baseAlongSquareIso f g p q e).hom) := by
  let aL : RationalHom F ((X.baseChangeAlong f).baseChangeAlong g)
      ((Y.baseChangeAlong f).baseChangeAlong g)
      (baseAlongCompMapOpens_eq X Y f g h) :=
    baseChangeAlong (h := baseAlongMapOpens_eq X Y f h) g
      (baseChangeAlong (X := X) (Y := Y) (h := h) f a)
  let aC : RationalHom F (X.baseChangeAlong (g.comp f)) (Y.baseChangeAlong (g.comp f))
      (baseAlongMapOpens_eq X Y (g.comp f) h) := baseChangeAlong (h := h) (g.comp f) a
  let aD : RationalHom F (X.baseChangeAlong (q.comp p)) (Y.baseChangeAlong (q.comp p))
      (baseAlongMapOpens_eq X Y (q.comp p) h) := baseChangeAlong (h := h) (q.comp p) a
  let aR : RationalHom F ((X.baseChangeAlong p).baseChangeAlong q)
      ((Y.baseChangeAlong p).baseChangeAlong q)
      (baseAlongCompMapOpens_eq X Y p q h) :=
    baseChangeAlong (h := baseAlongMapOpens_eq X Y p h) q
      (baseChangeAlong (X := X) (Y := Y) (h := h) p a)
  have left : comp (ofHom (Y.baseAlongCompIso f g).hom) aL =
      comp aC (ofHom (X.baseAlongCompIso f g).hom) := baseAlongComp_natural a f g
  have middle : comp (ofHom (Y.baseAlongEqIso e).hom) aC =
      comp aD (ofHom (X.baseAlongEqIso e).hom) := baseAlongEq_natural a e
  have right : comp aR (ofHom (X.baseAlongCompIso p q).inv) =
      comp (ofHom (Y.baseAlongCompIso p q).inv) aD := baseAlongComp_inv_natural a p q
  change comp (ofHom ((Y.baseAlongCompIso p q).inv.comp
    ((Y.baseAlongEqIso e).hom.comp (Y.baseAlongCompIso f g).hom))) aL =
    comp aR (ofHom ((X.baseAlongCompIso p q).inv.comp
      ((X.baseAlongEqIso e).hom.comp (X.baseAlongCompIso f g).hom)))
  simp only [ofHom_comp]
  rw [comp_assoc, comp_assoc, left,
    ← comp_assoc (ofHom (Y.baseAlongEqIso e).hom), middle,
    comp_assoc, ← comp_assoc (ofHom (Y.baseAlongCompIso p q).inv),
    ← right, comp_assoc]

/-- The inverse comparison gives the reverse square on the entire global tensor Hom. -/
theorem baseAlongSquare_inv_natural (a : RationalHom F X Y h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    comp (k := baseAlongCompMapOpens_eq X Y f g h)
        (baseChangeAlong (X := X.baseChangeAlong f) (Y := Y.baseChangeAlong f)
          (h := baseAlongMapOpens_eq X Y f h) g
          (baseChangeAlong (X := X) (Y := Y) (h := h) f a))
        (ofHom (F := F) (X.baseAlongSquareIso f g p q e).inv) =
      comp (ofHom (Y.baseAlongSquareIso f g p q e).inv)
        (baseChangeAlong (X := X.baseChangeAlong p) (Y := Y.baseChangeAlong p)
          (h := baseAlongMapOpens_eq X Y p h) q
          (baseChangeAlong (X := X) (Y := Y) (h := h) p a)) := by
  let aL : RationalHom F ((X.baseChangeAlong f).baseChangeAlong g)
      ((Y.baseChangeAlong f).baseChangeAlong g)
      (baseAlongCompMapOpens_eq X Y f g h) :=
    baseChangeAlong (h := baseAlongMapOpens_eq X Y f h) g
      (baseChangeAlong (X := X) (Y := Y) (h := h) f a)
  let aC : RationalHom F (X.baseChangeAlong (g.comp f)) (Y.baseChangeAlong (g.comp f))
      (baseAlongMapOpens_eq X Y (g.comp f) h) := baseChangeAlong (h := h) (g.comp f) a
  let aD : RationalHom F (X.baseChangeAlong (q.comp p)) (Y.baseChangeAlong (q.comp p))
      (baseAlongMapOpens_eq X Y (q.comp p) h) := baseChangeAlong (h := h) (q.comp p) a
  let aR : RationalHom F ((X.baseChangeAlong p).baseChangeAlong q)
      ((Y.baseChangeAlong p).baseChangeAlong q)
      (baseAlongCompMapOpens_eq X Y p q h) :=
    baseChangeAlong (h := baseAlongMapOpens_eq X Y p h) q
      (baseChangeAlong (X := X) (Y := Y) (h := h) p a)
  have left : comp aL (ofHom (X.baseAlongCompIso f g).inv) =
      comp (ofHom (Y.baseAlongCompIso f g).inv) aC := baseAlongComp_inv_natural a f g
  have middle : comp aC (ofHom (X.baseAlongEqIso e).inv) =
      comp (ofHom (Y.baseAlongEqIso e).inv) aD := baseAlongEq_inv_natural a e
  have right : comp (ofHom (Y.baseAlongCompIso p q).hom) aR =
      comp aD (ofHom (X.baseAlongCompIso p q).hom) := baseAlongComp_natural a p q
  change comp aL (ofHom (((X.baseAlongCompIso f g).inv.comp
    (X.baseAlongEqIso e).inv).comp (X.baseAlongCompIso p q).hom)) =
    comp (ofHom (((Y.baseAlongCompIso f g).inv.comp
      (Y.baseAlongEqIso e).inv).comp (Y.baseAlongCompIso p q).hom)) aR
  simp only [ofHom_comp]
  rw [← comp_assoc, ← comp_assoc, left,
    comp_assoc (ofHom (Y.baseAlongCompIso f g).inv), middle,
    ← comp_assoc, comp_assoc, ← right, ← comp_assoc]

end RationalHom

section FractionField

variable [IsDomain O] [IsFractionRing O F]

/-- Rationalize the actual forward and inverse commuting-square comparison maps. -/
def baseAlongSquareQuasiIsogeny (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    QuasiIsogeny F ((X.baseChangeAlong f).baseChangeAlong g)
      ((X.baseChangeAlong p).baseChangeAlong q) (X.baseAlongSquareOpens_eq f g p q e) :=
  QuasiIsogeny.ofIso (X.baseAlongSquareIso f g p q e)

@[simp]
theorem baseAlongSquareQuasiIsogeny_hom (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (X.baseAlongSquareQuasiIsogeny (F := F) f g p q e).hom =
      RationalHom.ofHom (X.baseAlongSquareIso f g p q e).hom := rfl

@[simp]
theorem baseAlongSquareQuasiIsogeny_inv (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (X.baseAlongSquareQuasiIsogeny (F := F) f g p q e).inv =
      RationalHom.ofHom (X.baseAlongSquareIso f g p q e).inv := rfl

namespace QuasiIsogeny

/-- Actual quasi-isogenies commute with the forward square comparison. -/
theorem baseAlongSquare_natural (a : QuasiIsogeny F X Y h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    ((a.baseChangeAlong f).baseChangeAlong g).trans
        (h := baseAlongCompMapOpens_eq X Y f g h)
        (Y.baseAlongSquareQuasiIsogeny f g p q e) =
      (X.baseAlongSquareQuasiIsogeny f g p q e).trans
        ((a.baseChangeAlong p).baseChangeAlong q) := by
  apply ext_hom
  exact RationalHom.baseAlongSquare_natural a.hom f g p q e

/-- The inverse of the same comparison gives the reverse quasi-isogeny square. -/
theorem baseAlongSquare_inv_natural (a : QuasiIsogeny F X Y h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (X.baseAlongSquareQuasiIsogeny f g p q e).symm.trans
        (k := baseAlongCompMapOpens_eq X Y f g h)
        ((a.baseChangeAlong f).baseChangeAlong g) =
      ((a.baseChangeAlong p).baseChangeAlong q).trans
        (Y.baseAlongSquareQuasiIsogeny f g p q e).symm := by
  apply ext_hom
  exact RationalHom.baseAlongSquare_inv_natural a.hom f g p q e

end QuasiIsogeny

end FractionField

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
