import Langlands.GroupScheme.Reductive.WeilFactorTransfer
import Langlands.GroupScheme.Reductive.AffineWeilChartCombination
import Langlands.GroupScheme.AffineWeilUnit

/-! # Factor projections of a group described by a Weil-restriction chart -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option maxRecDepth 4000

namespace Langlands.GroupScheme.WeilChart

open AffineWeil.ChartCombination (affinePointsIsoEquiv)

variable {A A' C : Type u} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A' C]
  [Module.Finite A' C] [Module.Projective A' C]
  {G : GroupScheme (Spec (CommRingCat.of A))}
  {H : GroupScheme (Spec (CommRingCat.of C))} [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (P : (GroupScheme.baseChange (Spec.algebraMap A A')).obj G ≅ AffineWeil.groupScheme A' C H)

section Generic

variable (X : Type u) [CommRing X] [Algebra A X] [Algebra A' X] [IsScalarTower A A' X]

/-- Points of `G` on an `A'`-algebra are points of `H` on the coefficient tensor product. -/
def chartPointsEquiv :
    G.affinePoints (CommAlgCat.of (CommRingCat.of A) X) ≃*
      H.affinePoints (CommAlgCat.of (CommRingCat.of C) (C ⊗[A'] X)) :=
  (affinePointsBaseChangeMulEquiv A A' X G).trans <|
    (affinePointsIsoEquiv P _).trans (AffineWeil.pointsEquiv A' C H X)

/-- The chart points are natural in the `A'`-algebra. -/
theorem chartPointsEquiv_naturality (X' : Type u) [CommRing X'] [Algebra A X'] [Algebra A' X']
    [IsScalarTower A A' X'] (a : X →ₐ[A'] X')
    (p : G.affinePoints (CommAlgCat.of (CommRingCat.of A) X)) :
    chartPointsEquiv P X' (G.affinePointMap (CommAlgCat.ofHom (a.restrictScalars A)) p) =
      H.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := C) C a))
        (chartPointsEquiv P X p) := by
  simp only [chartPointsEquiv, MulEquiv.trans_apply]
  rw [← affinePointsBaseChangeMulEquiv_naturality]
  have h := DFunLike.congr_fun (GroupScheme.affinePointsTarget_naturality
    ((GroupScheme.baseChange (Spec.algebraMap A A')).obj G) P.hom (CommAlgCat.ofHom a))
    (affinePointsBaseChangeMulEquiv A A' X G p)
  simp only [MonoidHom.comp_apply] at h
  change AffineWeil.pointsEquiv A' C H X'
      (((GroupScheme.baseChange (Spec.algebraMap A A')).obj G).affinePointsTarget P.hom _
        (((GroupScheme.baseChange (Spec.algebraMap A A')).obj G).affinePointMap
          (CommAlgCat.ofHom a) (affinePointsBaseChangeMulEquiv A A' X G p))) = _
  rw [← h]
  exact AffineWeil.pointsEquiv_naturality A' C H a _

/-- The factor projection attached to an idempotent of `C ⊗[A'] X`, acting on the points of
`G` through the chart. -/
def chartProj (e : C ⊗[A'] X) :
    G.affinePoints (CommAlgCat.of (CommRingCat.of A) X) →*
      G.affinePoints (CommAlgCat.of (CommRingCat.of A) X) :=
  (chartPointsEquiv P X).symm.toMonoidHom.comp
    ((IdempotentPoints.proj H e).comp (chartPointsEquiv P X).toMonoidHom)

theorem chartPointsEquiv_chartProj (e : C ⊗[A'] X)
    (p : G.affinePoints (CommAlgCat.of (CommRingCat.of A) X)) :
    chartPointsEquiv P X (chartProj P X e p) =
      IdempotentPoints.proj H e (chartPointsEquiv P X p) := by
  simp [chartProj]

/-- Chart factor projections are natural in the `A'`-algebra. -/
theorem chartProj_naturality (X' : Type u) [CommRing X'] [Algebra A X'] [Algebra A' X']
    [IsScalarTower A A' X'] (a : X →ₐ[A'] X') {e : C ⊗[A'] X} (he : IsIdempotentElem e)
    (p : G.affinePoints (CommAlgCat.of (CommRingCat.of A) X)) :
    G.affinePointMap (CommAlgCat.ofHom (a.restrictScalars A)) (chartProj P X e p) =
      chartProj P X' (Algebra.TensorProduct.lTensor (S := C) C a e)
        (G.affinePointMap (CommAlgCat.ofHom (a.restrictScalars A)) p) := by
  apply (chartPointsEquiv P X').injective
  rw [chartPointsEquiv_chartProj, chartPointsEquiv_naturality, chartPointsEquiv_naturality,
    chartPointsEquiv_chartProj]
  exact IdempotentPoints.proj_map H _ he rfl _

end Generic

section Under

variable (G) in
/-- The group functor of `G` on `T`-algebras. -/
abbrev GFun (T : CommAlgCat.{u} (CommRingCat.of A)) : Under T ⥤ GrpCat.{u} :=
  Under.forget T ⋙ G.affinePointFunctor

variable {T : CommAlgCat.{u} (CommRingCat.of A)} (f : A' →ₐ[A] T)

/-- The `A'`-algebra structure on `T` given by the chart map `f`. -/
@[instance_reducible]
def chartAlgebra : Algebra A' T := f.toRingHom.toAlgebra

/-- The `A'`-algebra structure on a `T`-algebra through the chart map `f`. -/
@[instance_reducible]
def underAlgebra (X : Under T) : Algebra A' X.right :=
  (X.hom.hom.toRingHom.comp f.toRingHom).toAlgebra

theorem underAlgebra_isScalarTower (X : Under T) :
    letI := underAlgebra f X
    IsScalarTower A A' X.right :=
  letI := underAlgebra f X
  IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap A X.right a = X.hom.hom (f (algebraMap A A' a))
    rw [f.commutes, X.hom.hom.commutes])

/-- The structure map of a `T`-algebra, as a map of `A'`-algebras through `f`. -/
def underMap (X : Under T) :
    letI := chartAlgebra f
    letI := underAlgebra f X
    T →ₐ[A'] X.right :=
  letI := chartAlgebra f
  letI := underAlgebra f X
  { X.hom.hom.toRingHom with commutes' := fun _ => rfl }

/-- The image of an element of `C ⊗[A'] T` in `C ⊗[A'] X` for a `T`-algebra `X`. -/
def baseIdem (X : Under T) (e : letI := chartAlgebra f; C ⊗[A'] T) :
    letI := underAlgebra f X
    C ⊗[A'] X.right :=
  letI := chartAlgebra f
  letI := underAlgebra f X
  Algebra.TensorProduct.lTensor (S := C) C (underMap f X) e

/-- A map of `T`-algebras, as a map of `A'`-algebras through `f`. -/
def underHom {X Y : Under T} (a : X ⟶ Y) :
    letI := underAlgebra f X
    letI := underAlgebra f Y
    X.right →ₐ[A'] Y.right :=
  letI := underAlgebra f X
  letI := underAlgebra f Y
  { a.right.hom.toRingHom with
    commutes' := fun r => by
      change a.right.hom (X.hom.hom (f r)) = Y.hom.hom (f r)
      rw [← CommAlgCat.comp_apply, Under.w a] }

omit [Module.Finite A' C] [Module.Projective A' C] in
theorem ofHom_underHom {X Y : Under T} (a : X ⟶ Y) :
    letI := underAlgebra f X
    letI := underAlgebra f Y
    haveI := underAlgebra_isScalarTower f X
    haveI := underAlgebra_isScalarTower f Y
    CommAlgCat.ofHom ((underHom f a).restrictScalars A) = a.right := by
  rfl

omit [Module.Finite A' C] [Module.Projective A' C] in
theorem baseIdem_underHom {X Y : Under T} (a : X ⟶ Y)
    (e : letI := chartAlgebra f; C ⊗[A'] T) :
    letI := underAlgebra f X
    letI := underAlgebra f Y
    Algebra.TensorProduct.lTensor (S := C) C (underHom f a) (baseIdem f X e) =
      baseIdem f Y e := by
  letI := chartAlgebra f
  letI := underAlgebra f X
  letI := underAlgebra f Y
  rw [baseIdem, baseIdem, WeilFactor.lTensor_lTensor]
  congr 2
  apply AlgHom.ext
  intro t
  change a.right.hom (X.hom.hom t) = Y.hom.hom t
  rw [← CommAlgCat.comp_apply, Under.w a]

set_option maxRecDepth 4000 in
/-- The factor projection of `G` on `T`-algebras attached to an idempotent of `C ⊗[A'] T`,
through the chart `P` and the chart map `f`. -/
def chartFactor (e : letI := chartAlgebra f; C ⊗[A'] T) (he : IsIdempotentElem e) :
    GFun G T ⟶ GFun G T where
  app X := GrpCat.ofHom (@chartProj A A' C _ _ _ _ _ _ _ G H _ _ P X.right _ _
    (underAlgebra f X) (underAlgebra_isScalarTower f X) (baseIdem f X e))
  naturality X Y a := by
    letI := chartAlgebra f
    have hX := underAlgebra_isScalarTower f X
    have hY := underAlgebra_isScalarTower f Y
    refine GrpCat.ext ?_
    intro (p : G.affinePoints (CommAlgCat.of (CommRingCat.of A) X.right))
    have hn := @chartProj_naturality A A' C _ _ _ _ _ _ _ G H _ _ P X.right _ _
      (underAlgebra f X) hX Y.right _ _ (underAlgebra f Y) hY (underHom f a)
      (baseIdem f X e) (he.map _) p
    rw [baseIdem_underHom] at hn
    change @chartProj A A' C _ _ _ _ _ _ _ G H _ _ P Y.right _ _ (underAlgebra f Y) hY
        (baseIdem f Y e) (G.affinePointMap (CommAlgCat.ofHom a.right.hom) p) =
      G.affinePointMap (CommAlgCat.ofHom a.right.hom)
        (@chartProj A A' C _ _ _ _ _ _ _ G H _ _ P X.right _ _
        (underAlgebra f X) hX (baseIdem f X e) p)
    exact hn.symm

/-- A transformation of `GFun G T` acting on points over the test algebra `X`. -/
abbrev gpt {T : CommAlgCat.{u} (CommRingCat.of A)} (ψ : GFun G T ⟶ GFun G T) (X : Under T) :
    G.affinePoints (CommAlgCat.of (CommRingCat.of A) X.right) →*
      G.affinePoints (CommAlgCat.of (CommRingCat.of A) X.right) :=
  (ψ.app X).hom

omit [Module.Finite A' C] [Module.Projective A' C] [IsAffine H.X.left]
  [LocallyOfFiniteType H.X.hom] in
theorem gpt_comp {T : CommAlgCat.{u} (CommRingCat.of A)} (ψ ψ' : GFun G T ⟶ GFun G T)
    (X : Under T) (x : G.affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    gpt (ψ ≫ ψ') X x = gpt ψ' X (gpt ψ X x) := rfl

omit [Module.Finite A' C] [Module.Projective A' C] [IsAffine H.X.left]
  [LocallyOfFiniteType H.X.hom] in
theorem ext_gpt {T : CommAlgCat.{u} (CommRingCat.of A)} {ψ ψ' : GFun G T ⟶ GFun G T}
    (h : ∀ X x, gpt ψ X x = gpt ψ' X x) : ψ = ψ' := by
  refine NatTrans.ext (funext fun X => GrpCat.ext ?_)
  intro x
  exact h X x

/-- The chart point equivalence on a `T`-algebra, with its `A'`-structure through `f`. -/
abbrev underPointsEquiv (X : Under T) :
    G.affinePoints (CommAlgCat.of (CommRingCat.of A) X.right) ≃*
      (letI := underAlgebra f X
       H.affinePoints (CommAlgCat.of (CommRingCat.of C) (C ⊗[A'] X.right))) :=
  @chartPointsEquiv A A' C _ _ _ _ _ _ _ G H _ _ P X.right _ _
    (underAlgebra f X) (underAlgebra_isScalarTower f X)

theorem underPointsEquiv_gpt_chartFactor (e : letI := chartAlgebra f; C ⊗[A'] T)
    (he : IsIdempotentElem e) (X : Under T)
    (x : G.affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    underPointsEquiv P f X (gpt (chartFactor P f e he) X x) =
      IdempotentPoints.proj H (baseIdem f X e) (underPointsEquiv P f X x) :=
  @chartPointsEquiv_chartProj A A' C _ _ _ _ _ _ _ G H _ _ P X.right _ _
    (underAlgebra f X) (underAlgebra_isScalarTower f X) _ x

omit [Module.Finite A' C] [Module.Projective A' C] in
theorem baseIdem_isIdempotentElem {e : letI := chartAlgebra f; C ⊗[A'] T}
    (he : IsIdempotentElem e) (X : Under T) : IsIdempotentElem (baseIdem f X e) := by
  letI := chartAlgebra f
  letI := underAlgebra f X
  exact he.map _

theorem chartFactor_comp {e e' : letI := chartAlgebra f; C ⊗[A'] T}
    (he : IsIdempotentElem e) (he' : IsIdempotentElem e') :
    chartFactor P f e he ≫ chartFactor P f e' he' =
      chartFactor P f (e' * e) (he'.mul he) := by
  letI := chartAlgebra f
  refine ext_gpt fun X x => ?_
  apply (underPointsEquiv P f X).injective
  rw [gpt_comp, underPointsEquiv_gpt_chartFactor, underPointsEquiv_gpt_chartFactor,
    underPointsEquiv_gpt_chartFactor,
    IdempotentPoints.proj_proj H (baseIdem_isIdempotentElem f he' X)
      (baseIdem_isIdempotentElem f he X)]
  congr 1
  letI := underAlgebra f X
  rw [baseIdem, baseIdem, baseIdem, map_mul]

theorem chartFactor_idem {e : letI := chartAlgebra f; C ⊗[A'] T} (he : IsIdempotentElem e) :
    chartFactor P f e he ≫ chartFactor P f e he = chartFactor P f e he := by
  rw [chartFactor_comp]
  congr 1

theorem gpt_chartFactor_conj {e : letI := chartAlgebra f; C ⊗[A'] T} (he : IsIdempotentElem e)
    (X : Under T) (h x : G.affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    gpt (chartFactor P f e he) X (h * x * h⁻¹) = h * gpt (chartFactor P f e he) X x * h⁻¹ := by
  apply (underPointsEquiv P f X).injective
  rw [underPointsEquiv_gpt_chartFactor, map_mul (underPointsEquiv P f X),
    map_mul (underPointsEquiv P f X), map_inv (underPointsEquiv P f X),
    IdempotentPoints.proj_conj H (baseIdem_isIdempotentElem f he X),
    map_mul (underPointsEquiv P f X), map_mul (underPointsEquiv P f X),
    map_inv (underPointsEquiv P f X), underPointsEquiv_gpt_chartFactor]

variable (G) in
/-- Restriction of a transformation over `T` to `T₁`-algebras along `χ : T ⟶ T₁`. -/
def grestrict {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)
    (ψ : GFun G T ⟶ GFun G T) : GFun G T₁ ⟶ GFun G T₁ where
  app X := ψ.app ((Under.map χ).obj X)
  naturality _ _ a := ψ.naturality ((Under.map χ).map a)

/-- A map of test algebras over `T`, as a map of `A'`-algebras through `f`. -/
def chartMap {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) :
    letI := chartAlgebra f
    letI := chartAlgebra (χ.hom.comp f)
    T →ₐ[A'] T₁ :=
  letI := chartAlgebra f
  letI := chartAlgebra (χ.hom.comp f)
  { χ.hom.toRingHom with commutes' := fun _ => rfl }

omit [Module.Finite A' C] [Module.Projective A' C] in
theorem baseIdem_map {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) (X : Under T₁)
    (e : letI := chartAlgebra f; C ⊗[A'] T) :
    baseIdem f ((Under.map χ).obj X) e =
      baseIdem (χ.hom.comp f) X
        (letI := chartAlgebra f
         letI := chartAlgebra (χ.hom.comp f)
         Algebra.TensorProduct.lTensor (S := C) C (chartMap f χ) e) := by
  letI := chartAlgebra f
  letI := chartAlgebra (χ.hom.comp f)
  letI := underAlgebra (χ.hom.comp f) X
  rw [baseIdem, baseIdem, WeilFactor.lTensor_lTensor]
  rfl

theorem grestrict_chartFactor {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)
    {e : letI := chartAlgebra f; C ⊗[A'] T} (he : IsIdempotentElem e) :
    grestrict G χ (chartFactor P f e he) =
      chartFactor P (χ.hom.comp f)
        (letI := chartAlgebra f
         letI := chartAlgebra (χ.hom.comp f)
         Algebra.TensorProduct.lTensor (S := C) C (chartMap f χ) e)
        (letI := chartAlgebra f
         letI := chartAlgebra (χ.hom.comp f)
         he.map _) := by
  refine ext_gpt fun X x => ?_
  change gpt (chartFactor P f e he) ((Under.map χ).obj X) x = _
  apply (underPointsEquiv P (χ.hom.comp f) X).injective
  rw [underPointsEquiv_gpt_chartFactor, ← baseIdem_map]
  exact underPointsEquiv_gpt_chartFactor P f e he ((Under.map χ).obj X) x

end Under

section Transport

variable {T : CommAlgCat.{u} (CommRingCat.of A)} (f : A' →ₐ[A] T)

/-- `T` as an `A'`-algebra through the chart map `f`. -/
abbrev chartTest : CommAlgCat.{u} (CommRingCat.of A') :=
  letI := chartAlgebra f
  CommAlgCat.of (CommRingCat.of A') T

/-- An `A'`-algebra regarded as an `A`-algebra. -/
@[instance_reducible]
def restrictAlgebra (Y : Type u) [CommRing Y] [i : Algebra A' Y] : Algebra A Y :=
  Algebra.compHom (R := A') (S := A) Y (algebraMap A A')

/-- The `A`-algebra structure of an algebra over `A'` given as an object of `CommAlgCat`. -/
abbrev resInst (Y : CommAlgCat.{u} (CommRingCat.of A')) : Algebra A Y :=
  restrictAlgebra (A := A) (Y := Y) (i := (Y.algebra : Algebra A' Y))

theorem restrictAlgebra_isScalarTower (Y : Type u) [CommRing Y] [Algebra A' Y] :
    letI := restrictAlgebra (A := A) (A' := A') Y
    IsScalarTower A A' Y :=
  letI := restrictAlgebra (A := A) (A' := A') Y
  IsScalarTower.of_algebraMap_eq' rfl

/-- A `T`-algebra as an algebra under `T` regarded as an `A'`-algebra through `f`. -/
def extObj (X : Under T) : Under (chartTest f) :=
  letI := chartAlgebra f
  letI := underAlgebra f X
  Under.mk (Y := CommAlgCat.of (CommRingCat.of A') X.right) (CommAlgCat.ofHom (underMap f X))

/-- The structure map of an algebra under `T` regarded as an `A'`-algebra, as an
`A`-algebra map. -/
def resMap (X' : Under (chartTest f)) :
    letI := resInst (A := A) X'.right
    T →ₐ[A] X'.right :=
  letI := resInst (A := A) X'.right
  { X'.hom.hom.toRingHom with
    commutes' := fun a => by
      have h1 : (algebraMap A T a : T) = f (algebraMap A A' a) := (f.commutes a).symm
      have h2 := X'.hom.hom.commutes (algebraMap A A' a)
      exact (congrArg X'.hom.hom h1).trans h2 }

/-- An algebra under `T` (as an `A'`-algebra) regarded as an algebra under `T`. -/
def resObj (X' : Under (chartTest f)) : Under T :=
  letI := resInst (A := A) X'.right
  Under.mk (Y := CommAlgCat.of (CommRingCat.of A) X'.right) (CommAlgCat.ofHom (resMap f X'))

/-- A map of algebras under `T` regarded as an `A'`-algebra, as an `A`-algebra map. -/
def resAlgHom {X' Y' : Under (chartTest f)} (a : X' ⟶ Y') :
    @AlgHom A X'.right Y'.right _ _ _ (resInst X'.right) (resInst Y'.right) :=
  @AlgHom.mk A X'.right Y'.right _ _ _ (resInst X'.right) (resInst Y'.right)
    a.right.hom.toRingHom (fun r => a.right.hom.commutes (algebraMap A A' r))

/-- Maps of algebras under `T` regarded as an `A'`-algebra, as maps under `T`. -/
def resHom {X' Y' : Under (chartTest f)} (a : X' ⟶ Y') : resObj f X' ⟶ resObj f Y' :=
  letI := resInst (A := A) X'.right
  letI := resInst (A := A) Y'.right
  Under.homMk (CommAlgCat.ofHom (resAlgHom f a)) (by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro t
    change a.right.hom (X'.hom.hom t) = Y'.hom.hom t
    rw [← CommAlgCat.comp_apply, Under.w a])

/-- The identity of a `T`-algebra, from its round trip through `A'`-algebras. -/
def resExtEquiv (X : Under T) :
    @AlgEquiv A X.right X.right _ _ _
      (restrictAlgebra (A := A) (Y := X.right) (i := underAlgebra f X)) _ :=
  @AlgEquiv.mk A X.right X.right _ _ _
    (restrictAlgebra (A := A) (Y := X.right) (i := underAlgebra f X)) _
    (Equiv.refl X.right) (fun _ _ => rfl) (fun _ _ => rfl) (fun a => by
      change X.hom.hom (f (algebraMap A A' a)) = algebraMap A X.right a
      rw [f.commutes, X.hom.hom.commutes])

/-- A `T`-algebra is isomorphic, under `T`, to its round trip through `A'`-algebras. -/
def resExtIso (X : Under T) : resObj f (extObj f X) ≅ X :=
  Under.isoMk (CommAlgCat.isoMk (resExtEquiv f X)) (by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro t
    rfl)

/-- The identity of an algebra under `T` (as an `A'`-algebra), to the round trip of its
underlying `T`-algebra. -/
def extResEquiv (X' : Under (chartTest f)) :
    @AlgEquiv A' X'.right X'.right _ _ _ (X'.right.algebra : Algebra A' X'.right)
      (underAlgebra f (resObj f X')) :=
  @AlgEquiv.mk A' X'.right X'.right _ _ _ (X'.right.algebra : Algebra A' X'.right)
    (underAlgebra f (resObj f X')) (Equiv.refl X'.right) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun a => (X'.hom.hom.commutes a).symm)

/-- An algebra under `T` (as an `A'`-algebra) is isomorphic to the round trip of its
underlying `T`-algebra. -/
def extResIso (X' : Under (chartTest f)) : X' ≅ extObj f (resObj f X') :=
  Under.isoMk (CommAlgCat.isoMk (extResEquiv f X')) (by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro t
    rw [CommAlgCat.comp_apply]
    rfl)

/-- The chart points on an algebra under `T` regarded as an `A'`-algebra, with its own
`A'`-structure and the restricted `A`-structure. -/
abbrev resPointsEquiv (X' : Under (chartTest f)) :
    G.affinePoints (resObj f X').right ≃*
      H.affinePoints (CommAlgCat.of (CommRingCat.of C) (C ⊗[A'] X'.right)) :=
  @chartPointsEquiv A A' C _ _ _ _ _ _ _ G H _ _ P X'.right _ (resInst X'.right) _
    (restrictAlgebra_isScalarTower (A := A) (A' := A') X'.right)

theorem resPointsEquiv_naturality {X' Y' : Under (chartTest f)} (a : X' ⟶ Y')
    (p : G.affinePoints (resObj f X').right) :
    resPointsEquiv P f Y' (G.affinePointMap (resHom f a).right p) =
      H.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := C) C a.right.hom))
        (resPointsEquiv P f X' p) :=
  @chartPointsEquiv_naturality A A' C _ _ _ _ _ _ _ G H _ _ P X'.right _ (resInst X'.right) _
    (restrictAlgebra_isScalarTower (A := A) (A' := A') X'.right) Y'.right _ (resInst Y'.right) _
    (restrictAlgebra_isScalarTower (A := A) (A' := A') Y'.right) a.right.hom p

/-- A transformation of the group functor of `G` on `T`-algebras, transported to the group
functor of `R_{C/A'}(H)` on algebras under `T` regarded as an `A'`-algebra through `f`. -/
def transportEnd (ψ : GFun G T ⟶ GFun G T) :
    WeilFactor.Fun A' C H (chartTest f) ⟶ WeilFactor.Fun A' C H (chartTest f) where
  app X' := GrpCat.ofHom (((AffineWeil.pointsEquiv A' C H X'.right).symm.toMonoidHom.comp
    (resPointsEquiv P f X').toMonoidHom).comp ((gpt ψ (resObj f X')).comp
      ((resPointsEquiv P f X').symm.toMonoidHom.comp
        (AffineWeil.pointsEquiv A' C H X'.right).toMonoidHom)))
  naturality X' Y' a := by
    refine GrpCat.ext ?_
    intro (y : (AffineWeil.groupScheme A' C H).affinePoints
      (CommAlgCat.of (CommRingCat.of A') X'.right))
    change (AffineWeil.pointsEquiv A' C H Y'.right).symm (resPointsEquiv P f Y'
        (gpt ψ (resObj f Y') ((resPointsEquiv P f Y').symm (AffineWeil.pointsEquiv A' C H Y'.right
          ((AffineWeil.groupScheme A' C H).affinePointMap (CommAlgCat.ofHom a.right.hom) y))))) =
      (AffineWeil.groupScheme A' C H).affinePointMap (CommAlgCat.ofHom a.right.hom)
        ((AffineWeil.pointsEquiv A' C H X'.right).symm (resPointsEquiv P f X'
          (gpt ψ (resObj f X') ((resPointsEquiv P f X').symm
            (AffineWeil.pointsEquiv A' C H X'.right y)))))
    apply (AffineWeil.pointsEquiv A' C H Y'.right).injective
    rw [MulEquiv.apply_symm_apply, AffineWeil.pointsEquiv_naturality,
      AffineWeil.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
    set q := (resPointsEquiv P f X').symm (AffineWeil.pointsEquiv A' C H X'.right y) with hq
    have hw : AffineWeil.pointsEquiv A' C H X'.right y = resPointsEquiv P f X' q := by
      rw [hq, MulEquiv.apply_symm_apply]
    rw [hw, ← resPointsEquiv_naturality, MulEquiv.symm_apply_apply]
    have hψ := congrArg (fun φ => φ.hom q) (ψ.naturality (resHom f a))
    change gpt ψ (resObj f Y') (G.affinePointMap (resHom f a).right q) =
      G.affinePointMap (resHom f a).right (gpt ψ (resObj f X') q) at hψ
    rw [hψ, resPointsEquiv_naturality]

omit [Module.Finite A' C] [Module.Projective A' C] [IsAffine H.X.left]
  [LocallyOfFiniteType H.X.hom] in
/-- Natural transformations agreeing at an object agree at every isomorphic object. -/
theorem app_eq_of_iso {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {F F' : 𝒞 ⥤ 𝒟}
    {φ₁ φ₂ : F ⟶ F'} {X Y : 𝒞} (i : X ≅ Y) (h : φ₁.app Y = φ₂.app Y) :
    φ₁.app X = φ₂.app X := by
  have h₁ : φ₁.app X = F.map i.hom ≫ φ₁.app Y ≫ F'.map i.inv := by
    rw [← Category.assoc, φ₁.naturality, Category.assoc, ← F'.map_comp, i.hom_inv_id,
      F'.map_id, Category.comp_id]
  have h₂ : φ₂.app X = F.map i.hom ≫ φ₂.app Y ≫ F'.map i.inv := by
    rw [← Category.assoc, φ₂.naturality, Category.assoc, ← F'.map_comp, i.hom_inv_id,
      F'.map_id, Category.comp_id]
  rw [h₁, h₂, h]

theorem pt_transportEnd (ψ : GFun G T ⟶ GFun G T) (X' : Under (chartTest f))
    (y : (AffineWeil.groupScheme A' C H).affinePoints
      (CommAlgCat.of (CommRingCat.of A') X'.right)) :
    WeilFactor.pt (transportEnd P f ψ) X' y =
      (AffineWeil.pointsEquiv A' C H X'.right).symm (resPointsEquiv P f X'
        (gpt ψ (resObj f X') ((resPointsEquiv P f X').symm
          (AffineWeil.pointsEquiv A' C H X'.right y)))) :=
  rfl

/-- At a `T`-algebra regarded as an `A'`-algebra, the transported chart factor projection is
the factor projection of the Weil restriction. -/
theorem transportEnd_chartFactor_app_ext {e : letI := chartAlgebra f; C ⊗[A'] T}
    (he : IsIdempotentElem e) (X : Under T) :
    (transportEnd P f (chartFactor P f e he)).app (extObj f X) =
      (WeilFactor.factorProjection A' C H (T := chartTest f) e he).app (extObj f X) := by
  refine GrpCat.ext ?_
  intro (y : (AffineWeil.groupScheme A' C H).affinePoints
    (CommAlgCat.of (CommRingCat.of A') (extObj f X).right))
  change WeilFactor.pt (transportEnd P f (chartFactor P f e he)) (extObj f X) y =
    WeilFactor.pt (WeilFactor.factorProjection A' C H (T := chartTest f) e he) (extObj f X) y
  apply (AffineWeil.pointsEquiv A' C H (extObj f X).right).injective
  rw [pt_transportEnd, MulEquiv.apply_symm_apply, WeilFactor.pointsEquiv_pt_factorProjection]
  have h := underPointsEquiv_gpt_chartFactor P f e he (resObj f (extObj f X))
    ((resPointsEquiv P f (extObj f X)).symm
      (AffineWeil.pointsEquiv A' C H (extObj f X).right y))
  refine h.trans ?_
  change IdempotentPoints.proj H (baseIdem f (resObj f (extObj f X)) e)
      (resPointsEquiv P f (extObj f X) ((resPointsEquiv P f (extObj f X)).symm
        (AffineWeil.pointsEquiv A' C H (extObj f X).right y))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The transported chart factor projection is the factor projection of the Weil
restriction. -/
theorem transportEnd_chartFactor {e : letI := chartAlgebra f; C ⊗[A'] T}
    (he : IsIdempotentElem e) :
    transportEnd P f (chartFactor P f e he) =
      WeilFactor.factorProjection A' C H (T := chartTest f) e he := by
  refine NatTrans.ext (funext fun X' => ?_)
  exact app_eq_of_iso (extResIso f X') (transportEnd_chartFactor_app_ext P f he (resObj f X'))

/-- Equal transported transformations have equal components on restricted objects. -/
theorem app_resObj_eq_of_transportEnd {ψ₁ ψ₂ : GFun G T ⟶ GFun G T} (X' : Under (chartTest f))
    (h : (transportEnd P f ψ₁).app X' = (transportEnd P f ψ₂).app X') :
    ψ₁.app (resObj f X') = ψ₂.app (resObj f X') := by
  refine GrpCat.ext ?_
  intro (q : G.affinePoints (resObj f X').right)
  change gpt ψ₁ (resObj f X') q = gpt ψ₂ (resObj f X') q
  have hy := congrArg (fun φ => φ.hom ((AffineWeil.pointsEquiv A' C H X'.right).symm
    (resPointsEquiv P f X' q))) h
  change WeilFactor.pt (transportEnd P f ψ₁) X' _ = WeilFactor.pt (transportEnd P f ψ₂) X' _
    at hy
  rw [pt_transportEnd, pt_transportEnd, MulEquiv.apply_symm_apply,
    MulEquiv.symm_apply_apply] at hy
  exact (resPointsEquiv P f X').injective
    ((AffineWeil.pointsEquiv A' C H X'.right).symm.injective hy)

theorem transportEnd_comp (ψ ψ' : GFun G T ⟶ GFun G T) :
    transportEnd P f (ψ ≫ ψ') = transportEnd P f ψ ≫ transportEnd P f ψ' := by
  refine WeilFactor.ext_pt fun X' y => ?_
  rw [WeilFactor.pt_comp, pt_transportEnd, pt_transportEnd, pt_transportEnd,
    MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  rfl

theorem pt_transportEnd_conj {ψ : GFun G T ⟶ GFun G T}
    (hψ : ∀ X h x, gpt ψ X (h * x * h⁻¹) = h * gpt ψ X x * h⁻¹) (X' : Under (chartTest f))
    (h x : (AffineWeil.groupScheme A' C H).affinePoints
      (CommAlgCat.of (CommRingCat.of A') X'.right)) :
    WeilFactor.pt (transportEnd P f ψ) X' (h * x * h⁻¹) =
      h * WeilFactor.pt (transportEnd P f ψ) X' x * h⁻¹ := by
  let Ψ := (AffineWeil.pointsEquiv A' C H X'.right).trans (resPointsEquiv P f X').symm
  have key : ∀ y, WeilFactor.pt (transportEnd P f ψ) X' y =
      Ψ.symm (gpt ψ (resObj f X') (Ψ y)) := fun y => rfl
  rw [key, key, map_mul Ψ, map_mul Ψ, map_inv Ψ, hψ, map_mul Ψ.symm, map_mul Ψ.symm,
    map_inv Ψ.symm, Ψ.symm_apply_apply]

variable [Algebra.Etale A' C] (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive H) (hsimple : ∀ s, IsAlmostSimple (geometricFiber H s))

include hR hred hsimple in
/-- **Rigidity through a chart.** Every normal idempotent endomorphism of the group functor
of `G` on `T`-algebras is a chart factor projection. -/
theorem exists_chartFactor (ψ : GFun G T ⟶ GFun G T) (hidem : ψ ≫ ψ = ψ)
    (hnorm : ∀ X h x, gpt ψ X (h * x * h⁻¹) = h * gpt ψ X x * h⁻¹) :
    ∃ (e : letI := chartAlgebra f; C ⊗[A'] T) (he : IsIdempotentElem e),
      ψ = chartFactor P f e he := by
  obtain ⟨e, he, hψ⟩ := WeilFactor.rigidity (T := chartTest f) hR hred hsimple
    (transportEnd P f ψ) (by rw [← transportEnd_comp, hidem])
    (fun X' h x => pt_transportEnd_conj P f hnorm X' h x)
  refine ⟨e, he, NatTrans.ext (funext fun X => ?_)⟩
  refine app_eq_of_iso (resExtIso f X).symm ?_
  apply app_resObj_eq_of_transportEnd P f
  rw [hψ, transportEnd_chartFactor]

include hR hred hsimple in
/-- Chart factor projections determine their idempotents. -/
theorem chartFactor_injective {e₁ e₂ : letI := chartAlgebra f; C ⊗[A'] T}
    (h₁ : IsIdempotentElem e₁) (h₂ : IsIdempotentElem e₂)
    (h : chartFactor P f e₁ h₁ = chartFactor P f e₂ h₂) : e₁ = e₂ := by
  apply WeilFactor.factorProjection_injective (T := chartTest f) hR hred hsimple h₁ h₂
  rw [← transportEnd_chartFactor P f h₁, ← transportEnd_chartFactor P f h₂, h]

end Transport

section ChartTransfer

variable [Algebra.Etale A' C] (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive H) (hsimple : ∀ s, IsAlmostSimple (geometricFiber H s))
  {T : CommAlgCat.{u} (CommRingCat.of A)}

open Classical in
/-- The idempotent of `C ⊗[A', f₂] T` whose chart factor projection through `f₂` equals the
chart factor projection through `f₁` of an idempotent of `C ⊗[A', f₁] T` (and `0` if the input
is not idempotent). -/
def chartTransfer (f₁ f₂ : A' →ₐ[A] T) (e : letI := chartAlgebra f₁; C ⊗[A'] T) :
    letI := chartAlgebra f₂; C ⊗[A'] T :=
  if he : IsIdempotentElem e then
    Classical.choose (exists_chartFactor P f₂ hR hred hsimple (chartFactor P f₁ e he)
      (chartFactor_idem P f₁ he) (fun X h x => gpt_chartFactor_conj P f₁ he X h x))
  else 0

theorem chartTransfer_spec (f₁ f₂ : A' →ₐ[A] T) {e : letI := chartAlgebra f₁; C ⊗[A'] T}
    (he : IsIdempotentElem e) :
    ∃ h : IsIdempotentElem (chartTransfer P hR hred hsimple f₁ f₂ e),
      chartFactor P f₂ (chartTransfer P hR hred hsimple f₁ f₂ e) h = chartFactor P f₁ e he := by
  have hex := exists_chartFactor P f₂ hR hred hsimple (chartFactor P f₁ e he)
    (chartFactor_idem P f₁ he) (fun X h x => gpt_chartFactor_conj P f₁ he X h x)
  obtain ⟨h, heq⟩ := Classical.choose_spec hex
  have hT : chartTransfer P hR hred hsimple f₁ f₂ e = Classical.choose hex := by
    simp only [chartTransfer, he, dite_true]
  have key : ∀ (e' : letI := chartAlgebra f₂; C ⊗[A'] T) (he' : IsIdempotentElem e'),
      e' = Classical.choose hex → chartFactor P f₂ e' he' = chartFactor P f₁ e he := by
    rintro e' he' rfl
    exact heq.symm
  exact ⟨hT ▸ h, key _ _ hT⟩

theorem chartTransfer_isIdempotentElem (f₁ f₂ : A' →ₐ[A] T)
    {e : letI := chartAlgebra f₁; C ⊗[A'] T} (he : IsIdempotentElem e) :
    IsIdempotentElem (chartTransfer P hR hred hsimple f₁ f₂ e) :=
  (chartTransfer_spec P hR hred hsimple f₁ f₂ he).1

theorem chartFactor_chartTransfer (f₁ f₂ : A' →ₐ[A] T)
    {e : letI := chartAlgebra f₁; C ⊗[A'] T} (he : IsIdempotentElem e) :
    chartFactor P f₂ (chartTransfer P hR hred hsimple f₁ f₂ e)
        (chartTransfer_isIdempotentElem P hR hred hsimple f₁ f₂ he) =
      chartFactor P f₁ e he :=
  (chartTransfer_spec P hR hred hsimple f₁ f₂ he).2

/-- The chart transfer is characterized by its chart factor projection. -/
theorem chartTransfer_eq (f₁ f₂ : A' →ₐ[A] T) {e : letI := chartAlgebra f₁; C ⊗[A'] T}
    (he : IsIdempotentElem e) {e₂ : letI := chartAlgebra f₂; C ⊗[A'] T}
    (he₂ : IsIdempotentElem e₂) (h : chartFactor P f₂ e₂ he₂ = chartFactor P f₁ e he) :
    chartTransfer P hR hred hsimple f₁ f₂ e = e₂ :=
  chartFactor_injective P f₂ hR hred hsimple _ he₂
    ((chartFactor_chartTransfer P hR hred hsimple f₁ f₂ he).trans h.symm)

theorem chartTransfer_self (f : A' →ₐ[A] T) {e : letI := chartAlgebra f; C ⊗[A'] T}
    (he : IsIdempotentElem e) : chartTransfer P hR hred hsimple f f e = e :=
  chartTransfer_eq P hR hred hsimple f f he he rfl

theorem chartTransfer_trans (f₁ f₂ f₃ : A' →ₐ[A] T) {e : letI := chartAlgebra f₁; C ⊗[A'] T}
    (he : IsIdempotentElem e) :
    chartTransfer P hR hred hsimple f₂ f₃ (chartTransfer P hR hred hsimple f₁ f₂ e) =
      chartTransfer P hR hred hsimple f₁ f₃ e := by
  refine chartTransfer_eq P hR hred hsimple f₂ f₃
    (chartTransfer_isIdempotentElem P hR hred hsimple f₁ f₂ he)
    (chartTransfer_isIdempotentElem P hR hred hsimple f₁ f₃ he) ?_
  rw [chartFactor_chartTransfer P hR hred hsimple f₁ f₃ he,
    chartFactor_chartTransfer P hR hred hsimple f₁ f₂ he]

theorem chartTransfer_mul (f₁ f₂ : A' →ₐ[A] T) {e e' : letI := chartAlgebra f₁; C ⊗[A'] T}
    (he : IsIdempotentElem e) (he' : IsIdempotentElem e') :
    chartTransfer P hR hred hsimple f₁ f₂ (e' * e) =
      chartTransfer P hR hred hsimple f₁ f₂ e' * chartTransfer P hR hred hsimple f₁ f₂ e := by
  apply chartTransfer_eq P hR hred hsimple f₁ f₂ (he'.mul he)
    ((chartTransfer_isIdempotentElem P hR hred hsimple f₁ f₂ he').mul
      (chartTransfer_isIdempotentElem P hR hred hsimple f₁ f₂ he))
  rw [← chartFactor_comp P f₂ (chartTransfer_isIdempotentElem P hR hred hsimple f₁ f₂ he)
      (chartTransfer_isIdempotentElem P hR hred hsimple f₁ f₂ he'),
    ← chartFactor_comp P f₁ he he', chartFactor_chartTransfer, chartFactor_chartTransfer]

omit [Algebra.Etale A' C] in
theorem gpt_chartFactor_zero (f : A' →ₐ[A] T) (X : Under T)
    (x : G.affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    gpt (chartFactor P f (letI := chartAlgebra f; (0 : C ⊗[A'] T)) IsIdempotentElem.zero) X x =
      1 := by
  apply (underPointsEquiv P f X).injective
  rw [underPointsEquiv_gpt_chartFactor, map_one]
  letI := chartAlgebra f
  letI := underAlgebra f X
  rw [baseIdem, map_zero, IdempotentPoints.proj_zero]

theorem chartTransfer_zero (f₁ f₂ : A' →ₐ[A] T) :
    chartTransfer P hR hred hsimple f₁ f₂ (letI := chartAlgebra f₁; (0 : C ⊗[A'] T)) =
      (letI := chartAlgebra f₂; (0 : C ⊗[A'] T)) := by
  apply chartTransfer_eq P hR hred hsimple f₁ f₂ IsIdempotentElem.zero IsIdempotentElem.zero
  refine ext_gpt fun X x => ?_
  rw [gpt_chartFactor_zero, gpt_chartFactor_zero]

/-- The chart transfer is natural in the test algebra. -/
theorem chartTransfer_map {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)
    (f₁ f₂ : A' →ₐ[A] T) {e : letI := chartAlgebra f₁; C ⊗[A'] T} (he : IsIdempotentElem e) :
    chartTransfer P hR hred hsimple (χ.hom.comp f₁) (χ.hom.comp f₂)
        (letI := chartAlgebra f₁
         letI := chartAlgebra (χ.hom.comp f₁)
         Algebra.TensorProduct.lTensor (S := C) C (chartMap f₁ χ) e) =
      (letI := chartAlgebra f₂
       letI := chartAlgebra (χ.hom.comp f₂)
       Algebra.TensorProduct.lTensor (S := C) C (chartMap f₂ χ)
        (chartTransfer P hR hred hsimple f₁ f₂ e)) := by
  letI := chartAlgebra f₁
  letI := chartAlgebra f₂
  apply chartTransfer_eq P hR hred hsimple (χ.hom.comp f₁) (χ.hom.comp f₂)
    (by letI := chartAlgebra (χ.hom.comp f₁); exact he.map _)
    (by letI := chartAlgebra (χ.hom.comp f₂)
        exact (chartTransfer_isIdempotentElem P hR hred hsimple f₁ f₂ he).map _)
  rw [← grestrict_chartFactor P f₂ χ (chartTransfer_isIdempotentElem P hR hred hsimple f₁ f₂ he),
    ← grestrict_chartFactor P f₁ χ he, chartFactor_chartTransfer]

end ChartTransfer

end Langlands.GroupScheme.WeilChart
