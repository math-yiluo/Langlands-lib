import Langlands.Geometry.FormalGroup.DeligneAffineLineSheaf
import Langlands.Geometry.FormalGroup.DrinfeldAtlasTangentComponentLocalization
import Langlands.Geometry.FormalGroup.DrinfeldTangentStalkLine
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # The actual tangent line sheaves of a special formal atlas -/

noncomputable section

universe u v s m

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open IsLocalRing ValuativeRel CentralDivision CentralSimple _root_.CategoryTheory
  _root_.AlgebraicGeometry DeligneFormalSpace ModuleLaw
open scoped TensorProduct

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

section PrincipalCover

variable {S : Type m} [CommRing S] {E : Type m} [AddCommGroup E] [Module S E]
  (N : Submodule S E)

private theorem finiteProjective_of_chartMaps {J : Type} (s : Set S) (hs : Ideal.span s = ⊤)
    (chart : (a : s) → Submodule (Localization.Away a.val) (J → Localization.Away a.val))
    (f : (a : s) → N →ₗ[S] (chart a).restrictScalars S)
    (hf : ∀ a : s, IsLocalizedModule (Submonoid.powers a.val) (f a))
    (hfp : ∀ a : s, Module.FinitePresentation (Localization.Away a.val) (chart a))
    (hp : ∀ a : s, Module.Projective (Localization.Away a.val) (chart a)) :
    Module.FinitePresentation S N ∧ Module.Projective S N := by
  let : AddCommGroup N := N.addCommGroup
  let : ∀ a : s, IsLocalizedModule (Submonoid.powers a.val) (f a) := hf
  let : Module.FinitePresentation S N :=
    Module.FinitePresentation.of_localizationSpan' (M := N)
      (Rₚ := fun a => Localization.Away a.val) s hs f hfp
  have hFlat (a : s) : Module.Flat S ((chart a).restrictScalars S) := by
    let : Module.Projective (Localization.Away a.val) ((chart a).restrictScalars S) := hp a
    exact Module.Flat.trans S (Localization.Away a.val) ((chart a).restrictScalars S)
  let : Module.Flat S N := Module.flat_of_isLocalized_span S N s hs
    (fun a => ↥((chart a).restrictScalars S)) f hFlat
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation (R := S) (M := N)⟩

private theorem tilde_isLine_of_rankOne (hf : Module.FinitePresentation S N)
    (hp : Module.Projective S N) (hr : ∀ p : PrimeSpectrum S, Module.rankAtStalk N p = 1) :
    IsLineSheaf (Spec (CommRingCat.of S)) (tilde (ModuleCat.of S N)) := by
  let M := ModuleCat.of S N
  let : Module.FinitePresentation S N := hf
  let : Module.Finite (CommRingCat.of S) M := inferInstanceAs (Module.Finite S N)
  let : Module.Projective (CommRingCat.of S) M := hp
  exact isLineSheaf_tilde_of_rankAtStalk («R» := CommRingCat.of S) M hr

end PrincipalCover

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance atlasTangentLineLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u,max u v} 𝒪[K] π} (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
variable (X : SpecialAtlas K D ι B.obj)

local notation "d" => CentralSimple.reducedDegree K D
local notation "B₀" => CommAlgCat.of B.obj B.obj
local notation "V" => X.atlas.tangentSubmodule B₀
local notation "W" => tangentComponent ι χ ψ X
local notation "A[" a "]" => BasicAtlas.localAlgebra X.atlas B₀ a
local notation "h[" a "]" => BasicAtlas.localUnit X.atlas B₀ a
local notation "W[" a "]" => tangentTestComponent ι χ ψ X A[a] a h[a]

section LocalTest

variable (A : CommAlgCat.{max u v} B.obj) (a : X.atlas.opens) (ha : IsUnit (algebraMap B.obj A a.val))
local notation "Aₙ" => tangentChartNilp (B := B) A
local notation "ψₐ" => tangentChartResidue ψ A
local notation "Y" => X.chartTestModule A a ha
local notation "Wₐ" => tangentTestComponent ι χ ψ X A a ha

private theorem tangentTestComponent_projective (i : Fin d) : Module.Projective A (Wₐ i) :=
  drinfeldTangentComponent_projective (B := Aₙ) ι X.unramified χ ψₐ (Y).order i

private theorem tangentTestComponent_finitePresentation (i : Fin d) :
    Module.FinitePresentation A (Wₐ i) := by
  let : Module.Finite A (Wₐ i) :=
    drinfeldTangentComponent_finite (B := Aₙ) ι X.unramified χ ψₐ (Y).order i
  let : Module.Projective A (Wₐ i) := tangentTestComponent_projective ι χ ψ X A a ha i
  exact Module.finitePresentation_of_projective A (Wₐ i)

private theorem tangentTestComponent_rankAtStalk (i : Fin d) (p : PrimeSpectrum A) :
    Module.rankAtStalk (Wₐ i) p = 1 :=
  drinfeldTangentComponent_rankAtStalk (B := Aₙ) ι χ ψₐ Y i p

end LocalTest

/-- The compatible component is finitely presented and projective by localization along the atlas cover. -/
theorem tangentComponent_finiteProjective (i : Fin d) :
    Module.FinitePresentation B.obj (W i) ∧ Module.Projective B.obj (W i) := by
  let N (a : X.atlas.opens) := W[a] i
  let f (a : X.atlas.opens) : W i →ₗ[B.obj] (N a).restrictScalars B.obj :=
    tangentComponentToChart ι χ ψ X A[a] a h[a] i
  have hloc (a : X.atlas.opens) : IsLocalizedModule (Submonoid.powers a.val) (f a) :=
    tangentComponentToChart_isLocalized ι χ ψ X a i
  have hf (a : X.atlas.opens) : Module.FinitePresentation A[a] (N a) :=
    tangentTestComponent_finitePresentation ι χ ψ X A[a] a h[a] i
  have hp (a : X.atlas.opens) : Module.Projective A[a] (N a) :=
    tangentTestComponent_projective ι χ ψ X A[a] a h[a] i
  exact finiteProjective_of_chartMaps (S := B.obj) (E := V) (W i) X.atlas.opens X.atlas.covers N f hloc hf hp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
/-- The global tangent component has rank one at every prime of the test ring. -/
theorem tangentComponent_rankAtStalk (i : Fin d) (p : PrimeSpectrum B.obj) :
    Module.rankAtStalk (W i) p = 1 := by
  have hchart : ∃ a : X.atlas.opens, a.val ∉ p.asIdeal := by
    by_contra! h
    have hspan : Ideal.span X.atlas.opens ≤ p.asIdeal := Ideal.span_le.mpr fun a ha => h ⟨a, ha⟩
    rw [X.atlas.covers] at hspan
    exact p.isPrime.ne_top (top_unique hspan)
  obtain ⟨a, ha⟩ := hchart
  let A := A[a]
  have hlift : ∃ q : PrimeSpectrum A, q.comap (algebraMap B.obj A) = p := by
    change p ∈ Set.range (PrimeSpectrum.comap (algebraMap B.obj A))
    rw [PrimeSpectrum.localization_away_comap_range A a.val]
    exact (PrimeSpectrum.mem_basicOpen a.val p).mpr ha
  obtain ⟨q, hq⟩ := hlift
  let hProj := tangentComponent_finiteProjective ι χ ψ X i
  let : Module.FinitePresentation B.obj (W i) := hProj.1
  let : Module.Projective B.obj (W i) := hProj.2
  let e : A ⊗[B.obj] W i ≃ₗ[A] W[a] i := tangentComponentChartEquiv ι χ ψ X a i
  have hb := (Module.rankAtStalk_baseChange (M := W i) q).trans
    (congrArg (fun x : PrimeSpectrum B.obj => Module.rankAtStalk (W i) x) hq)
  have hr := congrFun (Module.rankAtStalk_eq_of_equiv e) q
  exact hb.symm.trans (hr.trans (tangentTestComponent_rankAtStalk ι χ ψ X A a h[a] i q))

local notation "R" => CommRingCat.of B.obj

/-- The affine sheaf associated to the actual global character component. -/
def tangentComponentSheaf (i : Fin d) : (Spec R).Modules := tilde (ModuleCat.of B.obj (W i))

set_option maxHeartbeats 900000 in
/-- Every global homogeneous tangent sheaf is a line sheaf. -/
theorem tangentComponentSheaf_isLine (i : Fin d) : IsLineSheaf (Spec R) (tangentComponentSheaf ι χ ψ X i) := by
  have hProj := tangentComponent_finiteProjective ι χ ψ X i
  have hr := tangentComponent_rankAtStalk ι χ ψ X i
  exact tilde_isLine_of_rankOne (S := B.obj) (E := V) (W i) hProj.1 hProj.2 hr

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
