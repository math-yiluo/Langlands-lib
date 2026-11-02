import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Affine finite charts after an etale base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A finite affine chart through `x`, after an etale change of the target. -/
structure EtaleFiniteChart {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) where
  source : Scheme.{u}
  base : Scheme.{u}
  sourceAffine : IsAffine source
  baseAffine : IsAffine base
  toSource : source ⟶ X
  toBase : base ⟶ Y
  finiteMap : source ⟶ base
  sourceEtale : Etale toSource
  baseEtale : Etale toBase
  finite : IsFinite finiteMap
  comm : toSource ≫ f = finiteMap ≫ toBase
  point : source
  point_eq : toSource point = x

attribute [instance] EtaleFiniteChart.sourceAffine EtaleFiniteChart.baseAffine
  EtaleFiniteChart.sourceEtale EtaleFiniteChart.baseEtale EtaleFiniteChart.finite

/-- The chart also maps etale to the base change of the original source. -/
theorem EtaleFiniteChart.etale_lift {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
    (C : EtaleFiniteChart f x) :
    Etale (pullback.lift C.toSource C.finiteMap C.comm) := by
  have : Etale (pullback.lift C.toSource C.finiteMap C.comm ≫ pullback.fst f C.toBase) := by
    rw [pullback.lift_fst]
    exact C.sourceEtale
  exact Etale.of_comp _ (pullback.fst f C.toBase)

/-- A separated morphism locally of finite type has a finite affine chart at every
point where it is quasi-finite. -/
theorem nonempty_etaleFiniteChart {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsSeparated f] (x : X) (hx : f.QuasiFiniteAt x) :
    Nonempty (EtaleFiniteChart f x) := by
  obtain ⟨T, e, he, _, V, _, v, _, hfin, hv⟩ :=
    exists_etale_isCompl_of_quasiFiniteAt f rfl hx
  let : Etale e := he
  let q : V.toScheme ⟶ T := V.ι ≫ pullback.snd f e
  let : IsFinite q := hfin
  let i := T.affineCover.idx (q v)
  obtain ⟨t, ht⟩ := T.affineCover.covers (q v)
  let e₀ := T.affineCover.f i
  let D := pullback q e₀
  let q₀ : D ⟶ T.affineCover.X i := pullback.snd q e₀
  let j : D ⟶ X := pullback.fst q e₀ ≫ V.ι ≫ pullback.fst f e
  have hD : IsAffine D := isAffine_of_isAffineHom q₀
  obtain ⟨d, hd, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := q) (g := e₀) v t ht.symm
  have hj : j ≫ f = q₀ ≫ (e₀ ≫ e) := by
    dsimp [j, q₀]
    rw [Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ e) (pullback.condition (f := q) (g := e₀))
  refine ⟨{
    source := D
    base := T.affineCover.X i
    sourceAffine := hD
    baseAffine := inferInstance
    toSource := j
    toBase := e₀ ≫ e
    finiteMap := q₀
    sourceEtale := by dsimp [j]; infer_instance
    baseEtale := by dsimp [e₀]; infer_instance
    finite := by dsimp [q₀]; infer_instance
    comm := hj
    point := d
    point_eq := ?_ }⟩
  change (pullback.fst f e) (V.ι ((pullback.fst q e₀) d)) = x
  rw [hd]
  exact hv

end Langlands.AlgebraicGeometry.AlgebraicSpace
