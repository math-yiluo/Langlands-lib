import Langlands.Geometry.FormalGroup.AtlasOrderMorphism
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderAction
import Langlands.Geometry.FormalGroup.SpecialModule

/-! # Special formal division-order modules in local coordinates -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [algR : Algebra O R]
variable {A : Type w} [Ring A] [Algebra O A]
variable {σ τ : Type} [Finite σ] [Finite τ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The ring map underlying the canonical chart coefficient extension. -/
def coefficientRingLift (a : R) (B : CommAlgCat.{v} R)
    (hb : IsUnit (algebraMap R B a)) : Localization.Away a →+* B :=
  (coefficientLift (O := O) a B hb).toRingHom

/-- The localization coefficient map back to its own chart is the identity ring map. -/
theorem coefficientLift_self (a : R) :
    coefficientRingLift (O := O) a (CommAlgCat.of R (Localization.Away a))
      (IsLocalization.Away.algebraMap_isUnit a) =
        RingHom.id (Localization.Away a) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  ext r
  exact coefficientLift_algebraMap a (CommAlgCat.of R (Localization.Away a))
    (IsLocalization.Away.algebraMap_isUnit a) r

/-- An isomorphism after an identity ring map gives an isomorphism of the original laws,
even when the target algebra structure was presented by a composite. -/
def isoOfIdentityCoefficient (M : ModuleLaw O R σ) (N : ModuleLaw O R τ)
    (a : Algebra O R)
    (φ : @AlgHom O R R _ _ _ algR a)
    (hφ : @AlgHom.toRingHom O R R _ _ _ algR a φ = RingHom.id R)
    (e : @ModuleLaw.Iso O _ R _ a σ τ _ _
      (@ModuleLaw.map O _ R _ algR R _ a σ _ M φ)
      (@ModuleLaw.map O _ R _ algR R _ a τ _ N φ)) :
    @ModuleLaw.Iso O _ R _ algR σ τ _ _ M N := by
  have ha : a = algR :=
    Algebra.algebra_ext _ _ (fun r => by
      have hc := @AlgHom.commutes O R R _ _ _ algR a φ r
      exact hc.symm.trans
        (congrArg (fun g : R →+* R => g (@algebraMap O R _ _ algR r)) hφ))
  subst a
  have hp : φ = AlgHom.id O R := AlgHom.ext (RingHom.congr_fun hφ)
  subst φ
  exact (mapIdIso M).symm.trans (e.trans (mapIdIso N))

namespace OrderAction.Iso

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction A X} {E' : OrderAction A Y} {h : X.opens = Y.opens}

/-- Formal inverse atlas equations specialize to actual order-linear chart isomorphisms. -/
def onChart (f : Iso E E' h) (B : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R B b.val)) :
    ModuleLaw.OrderAction.Iso
      ((E.chart (sourceChart h b)).map (coefficientLift (O := O) b.val B hb))
      ((E'.chart b).map (coefficientLift (O := O) b.val B hb)) where
  hom := f.hom.onChart B b hb
  inv := f.inv.onChart B (sourceChart h b) hb
  inv_hom := by
    apply Subtype.ext
    exact congrArg (fun g : BasicAtlas.Hom X X rfl =>
      g.hom B (sourceChart h b) hb) (congrArg Subtype.val f.inv_hom)
  hom_inv := by
    apply Subtype.ext
    exact congrArg (fun g : BasicAtlas.Hom Y Y rfl =>
      g.hom B b hb) (congrArg Subtype.val f.hom_inv)

/-- The original local chart laws are isomorphic over their localization rings. -/
def originalChartIso (f : Iso E E' h) (b : Y.opens) :
    ModuleLaw.Iso (X.chart (sourceChart h b)) (Y.chart b) :=
  isoOfIdentityCoefficient _ _ _
    (coefficientLift (O := O) b.val (CommAlgCat.of R (Localization.Away b.val))
      (IsLocalization.Away.algebraMap_isUnit b.val))
    (coefficientLift_self b.val)
    (by
      letI := coefficientAlgebra (O := O) (CommAlgCat.of R (Localization.Away b.val))
      exact (f.onChart (CommAlgCat.of R (Localization.Away b.val)) b
        (IsLocalization.Away.algebraMap_isUnit b.val)).toModuleIso)

end OrderAction.Iso

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)
variable (R : Type v) [CommRing R] [Algebra 𝒪[K] R]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Actual local formal O_D-charts with special geometric tangent representations. -/
structure SpecialAtlas where
  atlas : BasicAtlas 𝒪[K] R (Fin (CentralSimple.reducedDegree K D))
  order : BasicAtlas.OrderAction (IntegerRing K D) atlas
  unramified : IsUnramifiedSubfieldOfReducedDegree K D ι
  tangent : ∀ b : atlas.opens,
    (order.chart b).HasGeometricTangentCharacters.{u, u, v, max u v, s}
      (subfieldIntegerInclusion K D ι).toRingHom (CentralSimple.reducedDegree K D)

namespace SpecialAtlas

variable {K D ι R} (X Y : SpecialAtlas K D ι R)

/-- Each original chart is a special coordinate module over its actual localization. -/
def chartModule (b : X.atlas.opens) : SpecialModule K D ι (Localization.Away b.val) where
  formalModule := X.atlas.chart b
  order := X.order.chart b
  unramified := X.unramified
  tangent := X.tangent b

/-- The special module on any test algebra on which a chart is defined. -/
def chartTestModule (B : CommAlgCat.{v} R) (b : X.atlas.opens)
    (hb : IsUnit (algebraMap R B b.val)) : SpecialModule K D ι B :=
  (X.chartModule b).mapSameUniverse (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb)

/-- Height d² is imposed on actual chart scalar kernels, together with the Nilp base condition. -/
def HasHeightSquared (π : 𝒪[K]) : Prop :=
  Irreducible π ∧ IsNilpotent (algebraMap 𝒪[K] R π) ∧
    ∀ b : X.atlas.opens, (X.atlas.chart b).HasPiHeight π (Nat.card 𝓀[K])
      ((CentralSimple.reducedDegree K D) ^ 2)

/-- The actual image of the uniformizer in the atlas base is nilpotent. -/
theorem base_nilpotent {π : 𝒪[K]} (h : X.HasHeightSquared π) :
    IsNilpotent (algebraMap 𝒪[K] R π) := h.2.1

/-- The original chart has the prescribed rank-based height. -/
theorem chart_height {π : 𝒪[K]} (h : X.HasHeightSquared π) (b : X.atlas.opens) :
    (X.chartModule b).HasHeightSquared π := ⟨h.1, h.2.2 b⟩

/-- Every test extension of a chart retains its specialness and actual scalar-kernel ranks. -/
theorem chartTest_height {π : 𝒪[K]} (h : X.HasHeightSquared π)
    (B : CommAlgCat.{v} R) (b : X.atlas.opens) (hb : IsUnit (algebraMap R B b.val)) :
    (X.chartTestModule B b hb).HasHeightSquared π :=
  (X.chart_height h b).map _

/-- Actual compatible families with their constructed division-order action. -/
abbrev Point (B : CommAlgCat.{v} R) := X.order.Point B

/-- The point functor constructed from actual charts and transitions. -/
abbrev pointFunctor := X.order.pointFunctor

/-- Its restriction to test algebras where pi is nilpotent. -/
abbrev nilpPointFunctor (π : R) := X.order.nilpPointFunctor π

/-- The compatible-family module is the actual special chart module wherever the chart is defined. -/
def chartPointEquiv (B : CommAlgCat.{v} R) (b : X.atlas.opens)
    (hb : IsUnit (algebraMap R B b.val)) :
    X.Point B ≃ₗ[IntegerRing K D] (X.chartTestModule B b hb).order.Point Empty :=
  X.order.chartEquiv b hb

/-- Same-cover morphisms are the actual division-order-linear atlas maps. -/
abbrev Hom (h : X.atlas.opens = Y.atlas.opens) :=
  BasicAtlas.OrderAction.Hom X.order Y.order h

/-- Same-cover isomorphisms require actual inverse formal atlas maps. -/
abbrev Iso (h : X.atlas.opens = Y.atlas.opens) :=
  BasicAtlas.OrderAction.Iso X.order Y.order h

/-- Actual inverse atlas maps preserve all chart height certificates. -/
theorem Iso.hasHeightSquared {X Y : SpecialAtlas K D ι R}
    {h : X.atlas.opens = Y.atlas.opens} (f : X.Iso Y h) {π : 𝒪[K]}
    (hX : X.HasHeightSquared π) : Y.HasHeightSquared π := by
  refine ⟨hX.1, hX.2.1, fun b => ?_⟩
  exact (f.originalChartIso b).hasPiHeight π (hX.2.2 (BasicAtlas.sourceChart h b))

/-- The height condition is invariant under actual same-cover order-linear isomorphisms. -/
theorem Iso.hasHeightSquared_iff {X Y : SpecialAtlas K D ι R}
    {h : X.atlas.opens = Y.atlas.opens} (f : X.Iso Y h) (π : 𝒪[K]) :
    X.HasHeightSquared π ↔ Y.HasHeightSquared π :=
  ⟨fun hX => SpecialAtlas.Iso.hasHeightSquared f hX,
    fun hY => SpecialAtlas.Iso.hasHeightSquared f.symm hY⟩

/-- Actual special atlases with the scalar-kernel height d² certificate. -/
def HeightSquaredAtlas (π : 𝒪[K]) := {X : SpecialAtlas K D ι R // X.HasHeightSquared π}

/-- Restrict a global special coordinate module to any actual principal-open cover. -/
def ofGlobalCover (M : SpecialModule K D ι R) (s : Set R) (hs : Ideal.span s = ⊤) :
    SpecialAtlas K D ι R where
  atlas := BasicAtlas.ofGlobalCover M.formalModule s hs
  order := BasicAtlas.ofGlobalCoverOrderAction M.order s hs
  unramified := M.unramified
  tangent b := M.tangent.map (IsScalarTower.toAlgHom 𝒪[K] R (Localization.Away b.val))

/-- Actual global scalar-kernel heights restrict to every chart. -/
theorem ofGlobalCover_height (M : SpecialModule K D ι R) {π : 𝒪[K]}
    (hM : M.HasHeightSquared π) (s : Set R) (hs : Ideal.span s = ⊤) :
    (ofGlobalCover M s hs).HasHeightSquared π :=
  ⟨hM.1, M.base_nilpotent hM, fun b => hM.2.map
    (IsScalarTower.toAlgHom 𝒪[K] R (Localization.Away b.val))⟩

/-- The singleton special atlas of a global special module. -/
def ofGlobal (M : SpecialModule K D ι R) : SpecialAtlas K D ι R :=
  ofGlobalCover M {1} (by simp)

/-- The singleton atlas has the original division-order point module. -/
def globalPointEquiv (M : SpecialModule K D ι R) (B : CommAlgCat.{v} R) :
    (ofGlobal M).Point B ≃ₗ[IntegerRing K D] M.order.AlgebraPoint B :=
  BasicAtlas.globalOrderPointEquiv M.order B

/-- The comparison is natural in coefficient algebras, after lifting the original carrier universe. -/
def globalPointFunctorIso (M : SpecialModule K D ι R) :
    (ofGlobal M).pointFunctor ≅
      M.order.algebraPointFunctor ⋙ ModuleCat.uliftFunctor.{v + 1, v} (IntegerRing K D) :=
  BasicAtlas.globalOrderPointFunctorIso M.order

/-- The same constructed comparison restricted to Nilp. -/
def globalNilpPointFunctorIso (M : SpecialModule K D ι R) (π : R) :
    (ofGlobal M).nilpPointFunctor π ≅
      M.order.nilpAlgebraPointFunctor π ⋙
        ModuleCat.uliftFunctor.{v + 1, v} (IntegerRing K D) :=
  BasicAtlas.globalOrderNilpPointFunctorIso M.order π

end SpecialAtlas

end Langlands.FormalGroup.LocalDivision
