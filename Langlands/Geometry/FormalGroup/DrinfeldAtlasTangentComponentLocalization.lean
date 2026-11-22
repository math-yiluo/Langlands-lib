import Langlands.Geometry.FormalGroup.AtlasTangentSubcover
import Langlands.Geometry.FormalGroup.DrinfeldAtlasTangentEvaluation

/-! # Localization of the actual Drinfeld atlas character components -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open IsLocalRing ValuativeRel CentralDivision CentralSimple _root_.CategoryTheory ModuleLaw
open scoped TensorProduct

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

section ImageLocalization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Submonoid R)
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
variable [Module R N] [Module S N] [IsScalarTower R S N]
variable (f : M →ₗ[R] N) (P : Module.End R M) (Q : Module.End S N)
variable (h : ∀ x : M, f (P x) = Q (f x))

private def imageMap : LinearMap.range P →ₗ[R] (LinearMap.range Q).restrictScalars R :=
  (f.comp (LinearMap.range P).subtype).codRestrict _ fun x => by
    obtain ⟨y, hy⟩ := x.property
    exact ⟨f y, (h y).symm.trans (congrArg f hy)⟩

private theorem imageMap_isLocalized [IsLocalization p S] [IsLocalizedModule p f]
    (hQ : IsIdempotentElem Q) : IsLocalizedModule p (imageMap f P Q h) where
  map_units s := by
    rw [← (Algebra.lsmul R (A := S) R ((LinearMap.range Q).restrictScalars R)).commutes]
    exact (IsLocalization.map_units S s).map _
  surj y := by
    obtain ⟨⟨x, b⟩, hx⟩ := IsLocalizedModule.surj p f y.val
    refine ⟨(⟨P x, ⟨x, rfl⟩⟩, b), ?_⟩
    apply Subtype.ext
    have hx' : (b.val : R) • y.val = f x := hx
    have hfix : Q y.val = y.val := by
      obtain ⟨v, hv⟩ := y.property
      rw [← hv]
      exact LinearMap.congr_fun hQ v
    change (b.val : R) • y.val = f (P x)
    rw [h x, ← hx', Q.map_smul_of_tower, hfix]
  exists_of_eq {x y} hxy := by
    have hf : f x.val = f y.val := congrArg Subtype.val hxy
    obtain ⟨b, hb⟩ := IsLocalizedModule.exists_of_eq (S := p) (f := f) hf
    exact ⟨b, Subtype.ext hb⟩

end ImageLocalization

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}

local instance atlasComponentLocalizationLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u,v} 𝒪[K] π} (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
variable (X : SpecialAtlas K D ι B.obj)

local notation "d" => CentralSimple.reducedDegree K D
local notation "B₀" => CommAlgCat.of B.obj B.obj
local notation "V" => X.atlas.tangentSubmodule B₀
local notation "A[" a "]" => BasicAtlas.localAlgebra X.atlas B₀ a
local notation "h[" a "]" => BasicAtlas.localUnit X.atlas B₀ a
local notation "ev[" a "]" => tangentToChart X A[a] a h[a]

/-- Evaluation on the universal test of a chart is the original compatible component. -/
@[simp]
theorem tangentToOwnChart_apply (a : X.atlas.opens) (z : V) : ev[a] z = z.val a :=
  X.atlas.tangentTestEvaluation_localTest z a

/-- The chart evaluation of the actual tangent module is its principal localization. -/
theorem tangentToOwnChart_isLocalized (a : X.atlas.opens) :
    IsLocalizedModule (Submonoid.powers a.val) ev[a] := by
  let r := algebraMap B.obj B₀ a.val
  let R := A[a]
  let k := X.atlas.localizationMap B₀ a
  let t : X.atlas.ChartTest R := ⟨R, 𝟙 R, a, h[a]⟩
  let f := X.atlas.tangentAwayMap B₀ r
  let e : (X.atlas.tangentSubmodule R).restrictScalars B.obj ≃ₗ[B.obj] (Fin d → R) :=
    (X.atlas.tangentChartEquiv R a h[a]).restrictScalars B.obj
  have h : e.toLinearMap.comp f = ev[a] := by
    apply LinearMap.ext
    intro z
    have hz := X.atlas.tangentTestEvaluation_tangentMap k z t
    let evalTest (g : B₀ ⟶ R) : Fin d → R :=
      X.atlas.tangentTestEvaluation z ⟨R, g, a, h[a]⟩
    exact hz.trans (congrArg evalTest (Category.comp_id k))
  have : IsLocalizedModule (Submonoid.powers r) f := X.atlas.tangentAwayMap_isLocalized B₀ r
  have hl : IsLocalizedModule (Submonoid.powers r) (e.toLinearMap.comp f) :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers r) f e
  exact h ▸ hl

variable (ι)

local notation "P" => tangentProjector ι χ ψ X

/-- The actual global tangent component is the image of its split coefficient projector. -/
def tangentComponent (i : Fin d) : Submodule B.obj V := LinearMap.range (P i)

section ChartTest

variable (A : CommAlgCat.{v} B.obj) (a : X.atlas.opens) (ha : IsUnit (algebraMap B.obj A a.val))

local notation "Aₙ" => tangentChartNilp (B := B) A
local notation "ψₐ" => tangentChartResidue ψ A
local notation "E" => SpecialModule.order (X.chartTestModule A a ha)
local notation "Q" => drinfeldTangentProjector (B := Aₙ) ι X.unramified χ ψₐ E
local notation "ev" => tangentToChart X A a ha

/-- The actual character component on a test in the given chart. -/
abbrev tangentTestComponent (i : Fin d) : Submodule A (Fin d → A) :=
  drinfeldTangentComponent (B := Aₙ) ι X.unramified χ ψₐ E i

local notation "W" => tangentTestComponent ι χ ψ X A a ha

/-- Evaluate the actual global character component in the corresponding chart component. -/
def tangentComponentToChart (i : Fin d) :
    tangentComponent ι χ ψ X i →ₗ[B.obj] (W i).restrictScalars B.obj := by
  letI : Algebra B.obj A := A.algebra
  let q : Module.End A (Fin d → A) := Q i
  exact imageMap (R := B.obj) (S := A) ev (P i) q (tangentToChart_projector ι χ ψ X A a ha i)

private theorem tangentComponentToChart_localization (p : Submonoid B.obj)
    [IsLocalization p A] [IsLocalizedModule p ev] (i : Fin d) :
    IsLocalizedModule p (tangentComponentToChart ι χ ψ X A a ha i) := by
  let : Algebra B.obj A := A.algebra
  let q : Module.End A (Fin d → A) := Q i
  have hQ : IsIdempotentElem q := drinfeldTangentProjector_mul_same ι X.unramified χ ψₐ E i
  exact imageMap_isLocalized (R := B.obj) (S := A) p ev (P i) q
    (tangentToChart_projector ι χ ψ X A a ha i) hQ

end ChartTest

variable (a : X.atlas.opens)

local notation "Rₐ" => A[a]
local notation "Wₐ" => tangentTestComponent ι χ ψ X Rₐ a h[a]

/-- The chart component is the principal localization of the actual global component. -/
theorem tangentComponentToChart_isLocalized (i : Fin d) :
    IsLocalizedModule (Submonoid.powers a.val) (tangentComponentToChart ι χ ψ X Rₐ a h[a] i) := by
  have : IsLocalizedModule (Submonoid.powers a.val) ev[a] := X.tangentToOwnChart_isLocalized a
  exact tangentComponentToChart_localization ι χ ψ X Rₐ a h[a] (Submonoid.powers a.val) i

/-- Scalar extension of each actual global component recovers its chart component. -/
def tangentComponentChartEquiv (i : Fin d) :
    (Rₐ ⊗[B.obj] tangentComponent ι χ ψ X i) ≃ₗ[Rₐ] Wₐ i :=
  ((isLocalizedModule_iff_isBaseChange (Submonoid.powers a.val) Rₐ
    (tangentComponentToChart ι χ ψ X Rₐ a h[a] i)).mp
    (tangentComponentToChart_isLocalized ι χ ψ X a i)).equiv

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
