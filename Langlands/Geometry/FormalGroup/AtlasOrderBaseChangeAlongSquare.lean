import Langlands.Geometry.FormalGroup.AtlasBaseChangeAlongSquare
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChangeAlongComposition

/-! # Commuting coefficient squares with the full acting order -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R S S' T : Type v} [CommRing R] [CommRing S] [CommRing S'] [CommRing T]
variable [Algebra O R] [Algebra O S] [Algebra O S'] [Algebra O T]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Equal coefficient maps compare by transport of the actual full-order identity. -/
def baseAlongEqIso (E : OrderAction D X) {f g : R →ₐ[O] T} (e : f = g) :
    Iso (E.baseChangeAlong f) (E.baseChangeAlong g) (X.baseAlongEqOpens_eq e) := by
  cases e
  exact Iso.refl _

/-- Forgetting the order retains the actual forward identity transport. -/
@[simp]
theorem baseAlongEqIso_hom_val (E : OrderAction D X) {f g : R →ₐ[O] T} (e : f = g) :
    (E.baseAlongEqIso e).hom.val = (X.baseAlongEqIso e).hom := by
  cases e
  rfl

/-- Forgetting the order retains the actual inverse identity transport. -/
@[simp]
theorem baseAlongEqIso_inv_val (E : OrderAction D X) {f g : R →ₐ[O] T} (e : f = g) :
    (E.baseAlongEqIso e).inv.val = (X.baseAlongEqIso e).inv := by
  cases e
  rfl

/-- Transport complete families between equal restrictions with full D-linearity. -/
def baseAlongEqPointEquiv (E : OrderAction D X) {f g : R →ₐ[O] T} (e : f = g)
    (A : CommAlgCat.{v} T) :
    E.Point (restrictCoefficientAlgebra f A) ≃ₗ[D]
      E.Point (restrictCoefficientAlgebra g A) := by
  cases e
  exact LinearEquiv.refl D _

/-- The full-order family transport has exactly the ambient underlying function. -/
theorem baseAlongEqPointEquiv_eq (E : OrderAction D X) {f g : R →ₐ[O] T} (e : f = g)
    (A : CommAlgCat.{v} T) (x : E.Point (restrictCoefficientAlgebra f A)) :
    E.baseAlongEqPointEquiv e A x = X.baseAlongEqPointEquiv e A x := by
  cases e
  rfl

/-- Actual order-linear equality transport realizes the entire-family comparison. -/
theorem baseAlongEq_onPoints (E : OrderAction D X) {f g : R →ₐ[O] T} (e : f = g)
    (A : CommAlgCat.{v} T) (x : E.Point (restrictCoefficientAlgebra f A)) :
    (E.baseAlongEqIso e).onPoints A (E.baseChangeAlongPointEquiv f A x) =
      E.baseChangeAlongPointEquiv g A (E.baseAlongEqPointEquiv e A x) := by
  cases e
  exact Hom.onPoints_id _ _ _

/-- Actual full-order isomorphism between the two routes around a coefficient square. -/
def baseAlongSquareIso (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    Iso ((E.baseChangeAlong f).baseChangeAlong g)
      ((E.baseChangeAlong p).baseChangeAlong q) (X.baseAlongSquareOpens_eq f g p q e) :=
  ((E.baseAlongCompIso f g).trans (E.baseAlongEqIso e)).trans
    (E.baseAlongCompIso p q).symm

/-- The forward full-order map retains exactly the ambient formal comparison. -/
@[simp]
theorem baseAlongSquareIso_hom_val (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (E.baseAlongSquareIso f g p q e).hom.val =
      (X.baseAlongSquareIso f g p q e).hom := by
  change (E.baseAlongCompIso p q).inv.val.comp
      ((E.baseAlongEqIso e).hom.val.comp (E.baseAlongCompIso f g).hom.val) = _
  rw [baseAlongCompIso_inv_val, baseAlongEqIso_hom_val, baseAlongCompIso_hom_val]
  rfl

/-- The inverse full-order map retains exactly the ambient inverse comparison. -/
@[simp]
theorem baseAlongSquareIso_inv_val (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (E.baseAlongSquareIso f g p q e).inv.val =
      (X.baseAlongSquareIso f g p q e).inv := by
  change ((E.baseAlongCompIso f g).inv.val.comp
    (E.baseAlongEqIso e).inv.val).comp (E.baseAlongCompIso p q).hom.val = _
  rw [baseAlongCompIso_inv_val, baseAlongEqIso_inv_val, baseAlongCompIso_hom_val]
  rfl

/-- The actual comparison realizes both routes on entire D-module families. -/
theorem baseAlongSquare_onPoints (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p)
    (A : CommAlgCat.{v} T) (x : E.Point (restrictCoefficientAlgebra (g.comp f) A)) :
    (E.baseAlongSquareIso f g p q e).onPoints A
      ((E.baseChangeAlong f).baseChangeAlongPointEquiv g A
        (E.baseChangeAlongPointEquiv f (restrictCoefficientAlgebra g A) x)) =
      (E.baseChangeAlong p).baseChangeAlongPointEquiv q A
        (E.baseChangeAlongPointEquiv p (restrictCoefficientAlgebra q A)
          (E.baseAlongEqPointEquiv e A x)) := by
  change ((E.baseAlongCompIso p q).inv.comp
    ((E.baseAlongEqIso e).hom.comp (E.baseAlongCompIso f g).hom)).onPoints A _ = _
  rw [Hom.onPoints_comp, Hom.onPoints_comp]
  change ((E.baseAlongCompIso p q).onPoints A).symm
    ((E.baseAlongEqIso e).onPoints A ((E.baseAlongCompIso f g).onPoints A _)) = _
  rw [baseAlongComp_onPoints, baseAlongEq_onPoints]
  exact E.baseAlongComp_inv_onPoints p q A _

/-- The same inverse realizes the reverse entire-family square with D-linearity. -/
theorem baseAlongSquare_inv_onPoints (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p)
    (A : CommAlgCat.{v} T) (x : E.Point (restrictCoefficientAlgebra (g.comp f) A)) :
    ((E.baseAlongSquareIso f g p q e).onPoints A).symm
      ((E.baseChangeAlong p).baseChangeAlongPointEquiv q A
        (E.baseChangeAlongPointEquiv p (restrictCoefficientAlgebra q A)
          (E.baseAlongEqPointEquiv e A x))) =
      (E.baseChangeAlong f).baseChangeAlongPointEquiv g A
        (E.baseChangeAlongPointEquiv f (restrictCoefficientAlgebra g A) x) :=
  (LinearEquiv.symm_apply_eq ((E.baseAlongSquareIso f g p q e).onPoints A)).mpr
    (E.baseAlongSquare_onPoints f g p q e A x).symm

namespace Hom

/-- The full-order square comparison is natural in every integral order-linear map. -/
theorem baseAlongSquare_natural (a : Hom E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (E'.baseAlongSquareIso f g p q e).hom.comp
        (h := baseAlongCompMapOpens_eq X Y f g h)
        ((a.baseChangeAlong f).baseChangeAlong g) =
      ((a.baseChangeAlong p).baseChangeAlong q).comp
        (E.baseAlongSquareIso f g p q e).hom := by
  apply Subtype.ext
  change (E'.baseAlongSquareIso f g p q e).hom.val.comp
      ((a.baseChangeAlong f).baseChangeAlong g).val =
    ((a.baseChangeAlong p).baseChangeAlong q).val.comp
      (E.baseAlongSquareIso f g p q e).hom.val
  rw [baseChangeAlong_val (h := baseAlongOpens_eq X Y f h) (a.baseChangeAlong f) g,
    baseChangeAlong_val (h := baseAlongOpens_eq X Y p h) (a.baseChangeAlong p) q,
    baseChangeAlong_val a f, baseChangeAlong_val a p,
    baseAlongSquareIso_hom_val, baseAlongSquareIso_hom_val]
  exact BasicAtlas.Hom.baseAlongSquare_natural a.val f g p q e

/-- The actual inverse comparison gives the reverse full-order integral square. -/
theorem baseAlongSquare_inv_natural (a : Hom E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    ((a.baseChangeAlong f).baseChangeAlong g).comp
        (k := baseAlongCompMapOpens_eq X Y f g h) (E.baseAlongSquareIso f g p q e).inv =
      (E'.baseAlongSquareIso f g p q e).inv.comp
        ((a.baseChangeAlong p).baseChangeAlong q) := by
  apply Subtype.ext
  change ((a.baseChangeAlong f).baseChangeAlong g).val.comp
      (E.baseAlongSquareIso f g p q e).inv.val =
    (E'.baseAlongSquareIso f g p q e).inv.val.comp
      ((a.baseChangeAlong p).baseChangeAlong q).val
  rw [baseChangeAlong_val (h := baseAlongOpens_eq X Y f h) (a.baseChangeAlong f) g,
    baseChangeAlong_val (h := baseAlongOpens_eq X Y p h) (a.baseChangeAlong p) q,
    baseChangeAlong_val a f, baseChangeAlong_val a p,
    baseAlongSquareIso_inv_val, baseAlongSquareIso_inv_val]
  exact BasicAtlas.Hom.baseAlongSquare_inv_natural a.val f g p q e

end Hom

namespace RationalHom

/-- The square comparison is natural on the entire full-order rational centralizer. -/
theorem baseAlongSquare_natural (a : RationalHom F E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    comp (h := baseAlongCompMapOpens_eq X Y f g h)
        (ofHom (F := F) (E'.baseAlongSquareIso f g p q e).hom)
        (baseChangeAlong (E := E.baseChangeAlong f) (E' := E'.baseChangeAlong f)
          (h := baseAlongOpens_eq X Y f h) g
          (baseChangeAlong (E := E) (E' := E') (h := h) f a)) =
      comp (baseChangeAlong (E := E.baseChangeAlong p) (E' := E'.baseChangeAlong p)
          (h := baseAlongOpens_eq X Y p h) q
          (baseChangeAlong (E := E) (E' := E') (h := h) p a))
        (ofHom (E.baseAlongSquareIso f g p q e).hom) := by
  apply ext
  simp only [comp_val, ofHom_val, baseAlongSquareIso_hom_val, baseChangeAlong_val]
  exact BasicAtlas.RationalHom.baseAlongSquare_natural a.val f g p q e

/-- The inverse comparison gives the reverse square on every rational centralizer map. -/
theorem baseAlongSquare_inv_natural (a : RationalHom F E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    comp (k := baseAlongCompMapOpens_eq X Y f g h)
        (baseChangeAlong (E := E.baseChangeAlong f) (E' := E'.baseChangeAlong f)
          (h := baseAlongOpens_eq X Y f h) g
          (baseChangeAlong (E := E) (E' := E') (h := h) f a))
        (ofHom (F := F) (E.baseAlongSquareIso f g p q e).inv) =
      comp (ofHom (E'.baseAlongSquareIso f g p q e).inv)
        (baseChangeAlong (E := E.baseChangeAlong p) (E' := E'.baseChangeAlong p)
          (h := baseAlongOpens_eq X Y p h) q
          (baseChangeAlong (E := E) (E' := E') (h := h) p a)) := by
  apply ext
  simp only [comp_val, ofHom_val, baseAlongSquareIso_inv_val, baseChangeAlong_val]
  exact BasicAtlas.RationalHom.baseAlongSquare_inv_natural a.val f g p q e

end RationalHom

section FractionField

variable [IsDomain O] [IsFractionRing O F]

/-- Rationalize both actual full-order formal comparison maps of a coefficient square. -/
def baseAlongSquareQuasiIsogeny (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    QuasiIsogeny F ((E.baseChangeAlong f).baseChangeAlong g)
      ((E.baseChangeAlong p).baseChangeAlong q) (X.baseAlongSquareOpens_eq f g p q e) :=
  QuasiIsogeny.ofIso (E.baseAlongSquareIso f g p q e)

@[simp]
theorem baseAlongSquareQuasiIsogeny_hom (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (E.baseAlongSquareQuasiIsogeny (F := F) f g p q e).hom =
      RationalHom.ofHom (E.baseAlongSquareIso f g p q e).hom := rfl

@[simp]
theorem baseAlongSquareQuasiIsogeny_inv (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (E.baseAlongSquareQuasiIsogeny (F := F) f g p q e).inv =
      RationalHom.ofHom (E.baseAlongSquareIso f g p q e).inv := rfl

/-- Forgetting the order recovers the whole actual ambient square quasi-isogeny. -/
@[simp]
theorem baseAlongSquareQuasiIsogeny_toAtlas (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (E.baseAlongSquareQuasiIsogeny (F := F) f g p q e).toAtlasQuasiIsogeny =
      X.baseAlongSquareQuasiIsogeny f g p q e := by
  apply BasicAtlas.QuasiIsogeny.ext_hom
  change BasicAtlas.RationalHom.ofHom (E.baseAlongSquareIso f g p q e).hom.val =
    BasicAtlas.RationalHom.ofHom (X.baseAlongSquareIso f g p q e).hom
  rw [baseAlongSquareIso_hom_val]

namespace QuasiIsogeny

/-- Actual quasi-isogenies commute with the full-order square comparison. -/
theorem baseAlongSquare_natural (a : QuasiIsogeny F E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    ((a.baseChangeAlong f).baseChangeAlong g).trans
        (h := baseAlongCompMapOpens_eq X Y f g h)
        (E'.baseAlongSquareQuasiIsogeny f g p q e) =
      (E.baseAlongSquareQuasiIsogeny f g p q e).trans
        ((a.baseChangeAlong p).baseChangeAlong q) := by
  apply ext_hom
  exact RationalHom.baseAlongSquare_natural a.hom f g p q e

/-- The same inverse gives the reverse whole full-order quasi-isogeny square. -/
theorem baseAlongSquare_inv_natural (a : QuasiIsogeny F E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    (p : R →ₐ[O] S') (q : S' →ₐ[O] T) (e : g.comp f = q.comp p) :
    (E.baseAlongSquareQuasiIsogeny f g p q e).symm.trans
        (k := baseAlongCompMapOpens_eq X Y f g h)
        ((a.baseChangeAlong f).baseChangeAlong g) =
      ((a.baseChangeAlong p).baseChangeAlong q).trans
        (E'.baseAlongSquareQuasiIsogeny f g p q e).symm := by
  apply ext_hom
  exact RationalHom.baseAlongSquare_inv_natural a.hom f g p q e

end QuasiIsogeny

end FractionField

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
