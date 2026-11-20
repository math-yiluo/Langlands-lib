import Langlands.Geometry.FormalGroup.DrinfeldDivisionDegree
import Langlands.Geometry.FormalGroup.DivisionOrderAtlasRationalTwist
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderAction

/-! # Actual signed division heights on the globally coordinated frame -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u s

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision CentralSimple ModuleLaw
open scoped TensorProduct

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {k S : Type u} [Field k] [Algebra 𝒪[K] k] [CommRing S] [Algebra 𝒪[K] S]
variable {σ : Type} [Finite σ] {M : ModuleLaw 𝒪[K] S σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Restricting the actual rational order action of a global law gives the atlas action. -/
theorem atlasRationalAction_ofGlobalCover (E : OrderAction (IntegerRing K D) M)
    (s : Set S) (hs : Ideal.span s = ⊤) (d : D) :
    atlasRationalAction K D (BasicAtlas.ofGlobalCoverOrderAction E s hs) d =
      BasicAtlas.ofGlobalRationalHom s hs (rationalAction K D E d) := by
  obtain ⟨t, rfl⟩ := (integerTensorEquiv K D).surjective d
  induction t using TensorProduct.inductionOn with
  | tmul c a =>
    rw [integerTensorEquiv_tmul, map_smul, map_smul, map_smul,
      atlasRationalAction_coe, rationalAction_coe, BasicAtlas.ofGlobalRationalHom_ofHom]
    apply congrArg (fun f => c • BasicAtlas.RationalHom.ofHom (F := K) f)
    apply BasicAtlas.Hom.ext
    intro B b hb
    let e := BasicAtlas.globalOrderChartIso E b.val B hb
    symm
    change e.inv.val.comp (((E.map (IsScalarTower.toAlgHom 𝒪[K] S B)).action a).comp e.hom.val) = _
    have he : e.inv.val.comp e.hom.val = Hom.id _ := e.toModuleIso.inv_hom
    rw [← e.hom.commutes a, ← Hom.comp_assoc, he, Hom.id_comp]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add, hx, hy]

namespace DrinfeldAction

variable {τ : Type} [Finite τ] {M₀ : ModuleLaw 𝒪[K] k τ} {π : 𝒪[K]}

/-- Choose a ranked integral numerator for the actual rational division twist over a field. -/
def twistQuasiIsogenyHeightPresentation {q H : ℕ} (hq : 1 < q)
    (E : OrderAction (IntegerRing K D) M₀) (hπ : Irreducible π)
    (hM : M₀.HasPiHeight π q (H * reducedDegree K D)) (g : Dˣ) :
    {P : RationalHom.GlobalHeightPresentation π q (twistQuasiIsogeny K D E g).hom.val //
      P.index (H * reducedDegree K D) = -(H : ℤ) * (divisionUnitOrder K D g).toAdd} :=
  let h := (twistQuasiIsogeny K D E g).toModuleQuasiIsogeny.exists_globalHeight_of_fieldDegree_zpow
    hπ hq hM hM.piDivisible (twistQuasiIsogeny_fieldDegree (zero_lt_one.trans hq) E hπ hM g)
  ⟨h.choose, h.choose_spec⟩

variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}

/-- The inverse division action on the extended frame has the same signed height on every
actual chart test, including when the coefficient extension is not a field. -/
theorem frameDivision_hasConstantChartHeight
    (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := k) π)
    (ψ : k →ₐ[𝒪[K]] S) (s : Set S) (hs : Ideal.span s = ⊤) (g : Dˣ) :
    (atlasRationalAction K D (BasicAtlas.ofGlobalCoverOrderAction (Φ.val.order.map ψ) s hs)
      ((g⁻¹ : Dˣ) : D)).HasConstantChartHeight π (Nat.card 𝓀[K])
        (-(reducedDegree K D : ℤ) * (divisionUnitOrder K D g).toAdd) := by
  have hq : 1 < Nat.card 𝓀[K] := LocalField.residueCardinality_gt_one K
  have hΦ : Φ.val.formalModule.HasPiHeight π (Nat.card 𝓀[K])
      (reducedDegree K D * reducedDegree K D) := by
    simpa only [pow_two] using Φ.property.2
  let P := twistQuasiIsogenyHeightPresentation hq Φ.val.order Φ.property.1 hΦ g
  rw [atlasRationalAction_ofGlobalCover, ← rationalAction_map_apply K D Φ.val.order]
  rw [← P.property]
  exact BasicAtlas.RationalHom.hasConstantChartHeight_ofGlobal (P.val.map ψ) (hΦ.map ψ) s hs

end DrinfeldAction

end Langlands.FormalGroup.LocalDivision
