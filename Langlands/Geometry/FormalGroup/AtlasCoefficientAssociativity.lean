import Langlands.Geometry.FormalGroup.AtlasOrderCoefficientUnit

/-! # Actual associativity of three coefficient extensions -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option backward.isDefEq.respectTransparency false in
/-- The two actual coefficient-composition routes agree on complete formal maps. -/
theorem baseCompHom_assoc (X : BasicAtlas O R σ) (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) (U : CommAlgCat.{v} T) :
    (X.baseCompHom (restrictTest S T) U).comp
        ((X.baseCompHom S T).baseChange U) =
      (X.baseCompHom S (restrictTest T U)).comp ((X.baseChange S).baseCompHom T U) := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  let ST := restrictTest S T
  let TU := restrictTest T U
  let V := restrictTest ST U
  let C := restrictTest V A
  let bl := sourceChart (X.baseCompOpens_eq ST U) b
  let br := sourceChart (X.baseCompOpens_eq S TU) b
  let m := (X.baseChange ST).baseSource U bl
  let n := (X.baseChange S).baseSource TU br
  let xl := X.baseCompIterSource S T m
  let xm := X.baseSource ST m
  let yr := (X.baseChange S).baseCompIterSource T U br
  let yl := X.baseSource S yr
  let ym := X.baseSource S n
  let d := X.baseSource V b
  have hbl : IsUnit (algebraMap U A bl.val) := hb
  have hbr : IsUnit (algebraMap U A br.val) := hb
  have hm := (X.baseChange ST).baseSource_unit U A bl hbl
  have hn := (X.baseChange S).baseSource_unit TU A br hbr
  have hyr := (X.baseChange S).baseCompIter_unit T U A br hbr
  have hxl : IsUnit (algebraMap R C xl.val) :=
    X.baseCompIter_unit S T (restrictTest U A) m hm
  have hxm : IsUnit (algebraMap R C xm.val) := X.baseSource_unit ST (restrictTest U A) m hm
  have hyl : IsUnit (algebraMap R C yl.val) := X.baseSource_unit S (restrictTest TU A) yr hyr
  have hym : IsUnit (algebraMap R C ym.val) := X.baseSource_unit S (restrictTest TU A) n hn
  have hd : IsUnit (algebraMap R C d.val) := X.baseSource_unit V A b hb
  change (X.baseCompChartIso ST U A b hb).hom.toHom.toCoordinateMap.comp
      (((X.baseCompHom S T).baseChange U).hom A bl hbl).toHom.toCoordinateMap =
    (X.baseCompChartIso S TU A b hb).hom.toHom.toCoordinateMap.comp
      ((X.baseChange S).baseCompChartIso T U A br hbr).hom.toHom.toCoordinateMap
  rw [Hom.baseChange_coordinates, X.baseCompChartIso_coordinates,
    X.baseCompChartIso_coordinates]
  change (X.transition C xm d hxm hd).hom.toHom.toCoordinateMap.comp
      (X.baseCompChartIso S T (restrictTest U A) m hm).hom.toHom.toCoordinateMap =
    (X.transition C ym d hym hd).hom.toHom.toCoordinateMap.comp
      ((X.baseChange S).baseCompChartIso T U A br hbr).hom.toHom.toCoordinateMap
  rw [X.baseCompChartIso_coordinates, (X.baseChange S).baseCompChartIso_coordinates]
  change (X.transition C xm d hxm hd).hom.toHom.toCoordinateMap.comp
      (X.transition C xl xm hxl hxm).hom.toHom.toCoordinateMap =
    (X.transition C ym d hym hd).hom.toHom.toCoordinateMap.comp
      (X.baseTransition S (restrictTest TU A) yr n hyr hn).hom.toHom.toCoordinateMap
  rw [X.baseTransition_coordinates]
  have hc₁ := congrArg (fun q => q.hom.toHom.toCoordinateMap)
    (X.transition_cocycle C xl xm d hxl hxm hd)
  have hc₂ := congrArg (fun q => q.hom.toHom.toCoordinateMap)
    (X.transition_cocycle C yl ym d hyl hym hd)
  change (X.transition C xm d _ _).hom.toHom.toCoordinateMap.comp
    (X.transition C xl xm _ _).hom.toHom.toCoordinateMap = _ at hc₁
  change (X.transition C ym d _ _).hom.toHom.toCoordinateMap.comp
    (X.transition C yl ym _ _).hom.toHom.toCoordinateMap = _ at hc₂
  have hb' : sourceChart ((X.baseChange S).baseCompOpens_eq T U) br =
      sourceChart (baseOpens_eq U (X.baseCompOpens_eq S T)) bl := by
    apply Subtype.ext
    rfl
  have hh := baseSource_sourceChart U (X.baseCompOpens_eq S T) bl
  have hs : yr = (X.baseChange S).baseSource T (sourceChart (X.baseCompOpens_eq S T) m) := by
    exact (congrArg (fun q => (X.baseChange S).baseSource T
      (((X.baseChange S).baseChange T).baseSource U q)) hb').trans
        (congrArg (fun q => (X.baseChange S).baseSource T q) hh)
  have he : yl = xl := congrArg (fun q => X.baseSource S q) hs
  exact hc₁.trans ((X.testTransition_coordinates_eq C xl d yl d hxl hd hyl hd he.symm rfl).trans hc₂.symm)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual full-order coefficient comparisons satisfy associativity as whole integral maps. -/
theorem baseCompIso_assoc (E : OrderAction D X) (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) (U : CommAlgCat.{v} T) :
    ((E.baseCompIso S T).baseChange U).trans (E.baseCompIso (restrictTest S T) U) =
      ((E.baseChange S).baseCompIso T U).trans (E.baseCompIso S (restrictTest T U)) := by
  apply Iso.ext_hom
  apply Subtype.ext
  exact X.baseCompHom_assoc S T U

/-- Retype all three actual coefficient extensions and retain their whole-map associativity. -/
theorem baseCompReAlgebraIso_assoc (E : OrderAction D X)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) (U : CommAlgCat.{v} T)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ)
    (δ : Algebra O U) (a : (letI := γ; coefficientAlgebra (O := O) U) = δ) :
    (letI := δ;
      ((letI := γ; (E.baseCompReAlgebraIso S T β e γ d).baseChange U).reAlgebra δ a).trans
          (E.baseCompReAlgebraIso (restrictTest S T) U γ
            ((coefficientAlgebra_comp_transport S T β e).trans d) δ a)) =
    (letI := δ;
      (letI := β; ((E.baseChange S).reAlgebra β e).baseCompReAlgebraIso T U γ d δ a).trans
        (E.baseCompReAlgebraIso S (restrictTest T U) β e δ
          (letI := β; (coefficientAlgebra_comp_transport T U γ d).trans a))) := by
  cases e
  cases d
  cases a
  exact E.baseCompIso_assoc S T U

variable {S T U : Type v} [CommRing S] [CommRing T] [CommRing U]
variable [Algebra O S] [Algebra O T] [Algebra O U]

/-- The specified supplied-coefficient comparisons satisfy actual associativity without injectivity. -/
theorem baseAlongCompIso_assoc (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (h : T →ₐ[O] U) :
    ((E.baseAlongCompIso f g).baseChangeAlong h).trans (E.baseAlongCompIso (g.comp f) h) =
      ((E.baseChangeAlong f).baseAlongCompIso g h).trans (E.baseAlongCompIso f (h.comp g)) :=
  E.baseCompReAlgebraIso_assoc (coefficientTest f) (coefficientTest g) (coefficientTest h)
    _ (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g) _ (coefficientAlgebraAlong_eq h)

variable [IsDomain O] {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]

/-- Four actual rational test maps for the associative supplied-coefficient composition square. -/
def baseAlongAssociativityTestSquare (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (h : T →ₐ[O] U)
    (A : CommAlgCat.{v} U) (b : (X.baseChangeAlong (h.comp (g.comp f))).opens)
    (hb : IsUnit (algebraMap U A b.val)) :=
  let l := (((E.baseAlongCompIso f g).baseChangeAlong h).trans
    (E.baseAlongCompIso (g.comp f) h)).onChart A b hb
  let r := (((E.baseChangeAlong f).baseAlongCompIso g h).trans
    (E.baseAlongCompIso f (h.comp g))).onChart A b hb
  ModuleLaw.OrderAction.Iso.rationalSquare (F := F) l (ModuleLaw.OrderAction.Iso.refl _)
    r (ModuleLaw.OrderAction.Iso.refl _) (by
      have he := congrArg (fun q => q.onChart A b hb) (E.baseAlongCompIso_assoc f g h)
      apply ModuleLaw.OrderAction.Iso.ext_hom
      change (ModuleLaw.OrderAction.Hom.id _).comp l.hom = (ModuleLaw.OrderAction.Hom.id _).comp r.hom
      simp only [ModuleLaw.OrderAction.Hom.id_comp]
      exact congrArg ModuleLaw.OrderAction.Iso.hom he)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
