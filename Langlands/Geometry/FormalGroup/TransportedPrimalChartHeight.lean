import Langlands.Geometry.FormalGroup.PrimalChartHeightComparison
import Langlands.Geometry.FormalGroup.AtlasOrderRationalHeightIso

/-! # Integral coordinate transport of the split primal chart rank -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.RationalHom

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {X' : BasicAtlas O R υ} {Y' : BasicAtlas O R ω}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {G : OrderAction D X'} {G' : OrderAction D Y'}
variable {h : X.opens = Y.opens} {aCover : X.opens = X'.opens}
variable {bCover : Y.opens = Y'.opens}

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the transported full-order atlas tensor conjugates the evaluated
actual tensor by the corresponding integral chart isomorphisms. -/
theorem onChart_isoTransport (a : Iso E G aCover) (b : Iso E' G' bCover)
    (f : RationalHom F E E' h) (A : CommAlgCat.{v} R) (c : Y'.opens)
    (hc : IsUnit (algebraMap R A c.val)) :
    let d := sourceChart bCover c
    let x := sourceChart aCover.symm (sourceChart h d)
    ((isoTransport a b f).onChart A c hc).val =
      ModuleLaw.RationalHom.isoTransport (a.onChart A x hc).toModuleIso
        (b.onChart A c hc).toModuleIso (f.onChart A d hc).val := by
  dsimp only
  rw [ModuleLaw.RationalHom.isoTransport_eq_comp]
  let a₀ : BasicAtlas.RationalHom F X' X aCover.symm := BasicAtlas.RationalHom.ofHom a.inv.val
  let b₀ : BasicAtlas.RationalHom F Y Y' bCover := BasicAtlas.RationalHom.ofHom b.hom.val
  change BasicAtlas.RationalHom.onChart (X := X') (Y := Y')
    (h := (aCover.symm.trans h).trans bCover) A c hc
    (BasicAtlas.RationalHom.comp b₀ (BasicAtlas.RationalHom.comp f.val a₀)) = _
  rw [BasicAtlas.RationalHom.onChart_comp b₀ (BasicAtlas.RationalHom.comp f.val a₀) A c hc,
    BasicAtlas.RationalHom.onChart_comp f.val a₀ A (sourceChart bCover c) hc]
  rfl

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.RationalHom

namespace Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

open CategoryTheory TopologicalSpace BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable {F K : Type v} [Field F] [Algebra O F] [IsFractionRing O F] [Field K] [Algebra C K]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) M} {G : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) N}
variable (I : IdempotentImageCover E.divisionProjector σ')
variable (J : IdempotentImageCover G.divisionProjector τ')
variable {h : I.atlas.opens = J.atlas.opens}
variable (hE : E.HasStructuralDivisionTangent (algebraMap C D) (algebraMap C R))
variable (hG : G.HasStructuralDivisionTangent (algebraMap C D) (algebraMap C R))
variable [Finite (IsLocalRing.ResidueField O)]
variable [IsDomain C] [IsDiscreteValuationRing C] [Finite (IsLocalRing.ResidueField C)]
variable [IsFractionRing C K]

local notation "q" => Nat.card (IsLocalRing.ResidueField C)

variable {S : BasicAtlas C R σ'} {Q : BasicAtlas C R τ'}
variable {E' : BasicAtlas.OrderAction D S} {G' : BasicAtlas.OrderAction D Q}
variable {ha : I.atlas.opens = S.opens} {hb : J.atlas.opens = Q.opens}
variable (a : BasicAtlas.OrderAction.Iso
  ((I.divisionOrder E).centralAtlasOrder (I.divisionOrder_centralTangent hE)) E' ha)
variable (b : BasicAtlas.OrderAction.Iso
  ((J.divisionOrder G).centralAtlasOrder (J.divisionOrder_centralTangent hG)) G' hb)
variable (B : CommAlgCat.{v} R) (c₁ : Q.opens) (hc : IsUnit (algebraMap R B c₁.val))
variable {p : ℕ} (z : LocalQuasiIsogeny F (p : O) M N ⊤)
variable (hz : RationalSection.IsOrderLinear E G z.val) (hπ : Irreducible (p : O)) (hpK : (p : K) ≠ 0)

/-- The prime and central comparison retains its local height functions after integral
changes of both actual central atlas presentations. -/
def restrictCentralQuasiIsogeny_chartRank_transport {ϖ : C} {e l H H' : ℕ} {u : Cˣ}
    (hpO : Nat.card (IsLocalRing.ResidueField O) = p) (hp : 1 < p) (hl : 0 < l)
    (hϖ : Irreducible ϖ) (hcal : (p : C) = (u : C) * ϖ ^ e) (hq : q = p ^ l)
    (hS : ∀ i : S.opens, (S.chart i).HasPiHeight ϖ q H)
    (hQ : ∀ i : Q.opens, (Q.chart i).HasPiHeight ϖ q H') :
    let c₀ : J.atlas.opens := ⟨c₁.val, hb.symm ▸ c₁.property⟩
    let t := z.toOrderTensor hπ hz
    let g := I.restrictCentralQuasiIsogeny J (h := h) (I.divisionOrder_centralTangent hE)
      (J.divisionOrder_centralTangent hG) t hπ hpK z.source_divisible z.target_divisible
    {k : (⊤ : Opens (PrimeSpectrum B)) → ℤ //
      RationalSection.HasHeightFunction (p : O) p
        (I.restrictLocalQuasiIsogenyOnChart J (h := h) B c₀ hc z hz hπ).val k ∧
      (∀ x, (l : ℤ) ∣ k x) ∧
      RationalSection.HasHeightFunction ϖ q
        (RationalSection.ofGlobal ((g.isoTransport a b).hom.onChart B c₁ hc).val)
        (fun x => k x / (l : ℤ))} := by
  dsimp only
  let c₀ : J.atlas.opens := ⟨c₁.val, hb.symm ▸ c₁.property⟩
  let cS : S.opens := ⟨c₁.val, ha ▸ h.symm ▸ hb.symm ▸ c₁.property⟩
  let a₀ := (a.onChart B cS hc).toModuleIso
  let b₀ := (b.onChart B c₁ hc).toModuleIso
  let P := I.restrictCentralQuasiIsogeny_chartRank J (h := h) hE hG B c₀ hc z hz hπ hpK
    hpO hp hl hϖ hcal hq (a₀.symm.hasPiHeight ϖ ((hS cS).map _))
    (b₀.symm.hasPiHeight ϖ ((hQ c₁).map _))
  refine ⟨P.val, P.property.1, P.property.2.1, ?_⟩
  let g := I.restrictCentralQuasiIsogeny J (h := h) (I.divisionOrder_centralTangent hE)
    (J.divisionOrder_centralTangent hG) (z.toOrderTensor hπ hz) hπ hpK
    z.source_divisible z.target_divisible
  have he := BasicAtlas.OrderAction.RationalHom.onChart_isoTransport a b g.hom B c₁ hc
  change ((g.isoTransport a b).hom.onChart B c₁ hc).val =
    ModuleLaw.RationalHom.isoTransport a₀ b₀ (g.hom.onChart B c₀ hc).val at he
  exact he.symm ▸ P.property.2.2.ofGlobal_isoTransport a₀ b₀

end Langlands.FormalGroup.ModuleLaw.IdempotentImageCover
