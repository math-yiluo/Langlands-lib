import Langlands.Topology.Nonarchimedean.Subgroup
import Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient
import Langlands.Representation.Derivative.MirabolicProductMinusRightPhiAssembly
import Langlands.Representation.Derivative.MirabolicProductMinusRightPsi

/-!
# The identity orbit piece of the right `Φ⁻` sequence

The normalized localized orbit piece of `τ × ρ` at the identity representative is
`(Ψ⁻τ) × (ρ|P)`, naturally in both inputs. The localization of the compact induction
from the stabilizer `S` to the plus subgroup `Q` is the compact induction from
`K = P.comap plusSuccessor` of the localized coefficient (published split-stage
character comparison); `K` is the lower left mixed subgroup after a rank cast, and
the coefficient with its `Φ⁻` twist and Haar ratio is the normalized left mixed
coefficient of `(Ψ⁻τ, ρ|P)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MeasureTheory MeasureTheory.Measure
open scoped TensorProduct NNReal

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct
  GeneralLinear.Mirabolic.MixedOrbit HarmonicAnalysis

universe uF uV

section LocalizedTransport

open Induction.SplitKernelLocalization

variable {G : Type*} [Group G] {L : Type*} [Group L]
  {V W V' W' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
  (r : G →* L) (s : L →* G) (θ : r.ker →* ℂˣ) (hθ : SectionInvariant r s θ)

/-- An equivalence of representations of `G` induces an equivalence of the localized
section actions, on classes of representatives. -/
def localizedActionEquiv {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    (f : ρ.Equiv τ) : (localizedAction r s θ hθ ρ).Equiv (localizedAction r s θ hθ τ) where
  toLinearEquiv := Jacquet.Localization.representationEquiv r.ker θ f
  isIntertwining' l := by
    apply Jacquet.Localization.hom_ext
    ext v
    exact congrArg (Jacquet.Localization.mk τ r.ker θ)
      (Representation.IntertwiningMap.isIntertwining ρ τ f.toIntertwiningMap (s l) v)

@[simp] theorem localizedActionEquiv_mk {ρ : Representation ℂ G V}
    {τ : Representation ℂ G W} (f : ρ.Equiv τ) (v : V) :
    localizedActionEquiv r s θ hθ f (Jacquet.Localization.mk ρ r.ker θ v) =
      Jacquet.Localization.mk τ r.ker θ (f v) := rfl

/-- The localized equivalences commute with the class maps of compatible intertwiners. -/
theorem localizedActionEquiv_natural {ρ₁ : Representation ℂ G V} {τ₁ : Representation ℂ G W}
    {ρ₂ : Representation ℂ G V'} {τ₂ : Representation ℂ G W'}
    (f₁ : ρ₁.Equiv τ₁) (f₂ : ρ₂.Equiv τ₂) (a : ρ₁.IntertwiningMap ρ₂)
    (b : τ₁.IntertwiningMap τ₂) (h : ∀ v, f₂ (a v) = b (f₁ v))
    (z : Jacquet.Localization.Coinvariants ρ₁ r.ker θ) :
    localizedActionEquiv r s θ hθ f₂ (sectionMap r s θ hθ a z) =
      sectionMap r s θ hθ b (localizedActionEquiv r s θ hθ f₁ z) := by
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective ρ₁ r.ker θ z
  exact congrArg (Jacquet.Localization.mk τ₂ r.ker θ) (h v)

end LocalizedTransport

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The plus subgroup has a basis of compact open subgroups at the identity. -/
theorem plusSubgroup_compactOpenBasis (T : F.TopologicalData) (t : ℕ) :
    letI := T.topology
    ∀ O : Set (plusSubgroup t F.Carrier), IsOpen O → (1 : plusSubgroup t F.Carrier) ∈ O →
      ∃ U : OpenSubgroup (plusSubgroup t F.Carrier),
        IsCompact (U : Set (plusSubgroup t F.Carrier)) ∧
          (U : Set (plusSubgroup t F.Carrier)) ⊆ O := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearNonarchimedean (t + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := t + 1) (F := F.Carrier)
  let : LocallyCompactSpace (plusSubgroup t F.Carrier) := plusSubgroup_isClosed.locallyCompactSpace
  have := Langlands.subgroupNonarchimedean (mirabolic (t + 1) F.Carrier)
  have := Langlands.subgroupNonarchimedean (plusSubgroup t F.Carrier)
  intro O hO h1
  exact Langlands.compactOpenSubgroupBasis _ O (hO.mem_nhds h1)

/-! ## The rank cast to the lower left mixed product -/

section Transport

/-- The rank cast `P_(k+r+2) ≅ P_((r+1)+k+1)` as an isomorphism of topological groups. -/
def rightIdentityCast (T : F.TopologicalData) (k r : ℕ) :
    letI := T.topology
    mirabolic (k + r + 1) F.Carrier ≃ₜ* mirabolic (r + 1 + k) F.Carrier :=
  letI := T.topology
  { toMulEquiv := (rankCast (R := F.Carrier) (show r + 1 + k = k + r + 1 by omega)).symm
    continuous_toFun := continuous_rankCast_symm _
    continuous_invFun := continuous_rankCast _ }

/-- The published rank-cast pullback is pullback along the same entrywise cast. -/
theorem rightIdentityCast_toMonoidHom (T : F.TopologicalData) (k r : ℕ) :
    letI := T.topology
    (rightIdentityCast T k r).toMonoidHom =
      mirabolicCastHom (R := F.Carrier) (Nat.add_comm (r + 1) k) := by
  let := T.topology
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [mirabolicCastHom_apply]
  rfl

/-- The target `(Ψ⁻τ) × (ρ|P)` with its rank cast replaced by the explicit pullback. -/
abbrev rightIdentityTarget (T : F.TopologicalData) (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  (Mirabolic.psiMinus T (r + 1)).prod (generalLinearRestriction T k) ⋙
    T.leftMixedProductFunctor (r + 1) k ⋙
      Mirabolic.continuousPullbackFunctor (mirabolicCastHom (Nat.add_comm (r + 1) k))
        (continuous_mirabolicCastHom (Nat.add_comm (r + 1) k))

/-- Compact induction from `K` of a coefficient identified with the normalized lower
left mixed coefficient of `(Ψ⁻τ, ρ|P)` is the target, through the rank cast. -/
def rightIdentityCompactEquivOf (T : F.TopologicalData) (k r : ℕ) {W : Type*} [AddCommGroup W]
    [Module ℂ W]
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
    (κ : Representation ℂ
      ((rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) W)
    (e : letI := T.topology
      W ≃ₗ[ℂ] (Jacquet.Localization.Coinvariants X.1.representation (radical (r + 1) F.Carrier) 1 ⊗[ℂ]
        X.2))
    (he : letI := T.topology; ∀ (l : (rightStages k r F.Carrier 1).comap
        (plusSuccessor (n := k + r + 1) (F := F.Carrier))) (w : W),
      e (κ l w) = ((T.leftCharacter (r + 1) k).toMonoidHom (rightIdentityLevi k r F.Carrier l) : ℂ) •
        TensorProduct.map (((Mirabolic.psiMinus T (r + 1)).obj X.1).representation
            (leftProjection (rightIdentityLevi k r F.Carrier l)).1)
          (((generalLinearRestriction T k).obj X.2).representation
            (leftProjection (rightIdentityLevi k r F.Carrier l)).2) (e w)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1)
    letI := T.generalLinearTopologicalGroup (r + 1 + k + 1)
    (Induction.compactInduced
        ((rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier)))
        κ).Equiv
      ((rightIdentityTarget.{uF, uV} T k r).obj X).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1)
  letI := T.generalLinearTopologicalGroup (r + 1 + k + 1)
  (Induction.compactInducedTransport (rightIdentityCast T k r)
      ((rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier)))
      (leftSubgroup (r + 1) k F.Carrier) (mem_rightStages_one_comap_iff k r F.Carrier) κ
      (twist (T.leftCharacter (r + 1) k).toMonoidHom
        (leftInducingRepresentation ((Mirabolic.psiMinus T (r + 1)).obj X.1).representation
          ((generalLinearRestriction T k).obj X.2).representation)) e he).symm.trans
    (compEquivOfEq _ (rightIdentityCast_toMonoidHom T k r))

/-- The identification is natural for a coefficient intertwiner lying over a pair of
morphisms `f = (f₁, f₂)`, i.e. carried to `Ψ⁻(f₁) ⊗ f₂`. -/
theorem rightIdentityCompactEquivOf_natural (T : F.TopologicalData) (k r : ℕ)
    {W : Type*} [AddCommGroup W] [Module ℂ W] {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (κ : Representation ℂ
      ((rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) W)
    (e : letI := T.topology
      W ≃ₗ[ℂ] (Jacquet.Localization.Coinvariants X.1.representation (radical (r + 1) F.Carrier) 1 ⊗[ℂ]
        X.2))
    (he : letI := T.topology; ∀ (l : (rightStages k r F.Carrier 1).comap
        (plusSuccessor (n := k + r + 1) (F := F.Carrier))) (w : W),
      e (κ l w) = ((T.leftCharacter (r + 1) k).toMonoidHom (rightIdentityLevi k r F.Carrier l) : ℂ) •
        TensorProduct.map (((Mirabolic.psiMinus T (r + 1)).obj X.1).representation
            (leftProjection (rightIdentityLevi k r F.Carrier l)).1)
          (((generalLinearRestriction T k).obj X.2).representation
            (leftProjection (rightIdentityLevi k r F.Carrier l)).2) (e w))
    (κ' : Representation ℂ
      ((rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) W')
    (e' : letI := T.topology
      W' ≃ₗ[ℂ] (Jacquet.Localization.Coinvariants Y.1.representation (radical (r + 1) F.Carrier) 1 ⊗[ℂ]
        Y.2))
    (he' : letI := T.topology; ∀ (l : (rightStages k r F.Carrier 1).comap
        (plusSuccessor (n := k + r + 1) (F := F.Carrier))) (w : W'),
      e' (κ' l w) = ((T.leftCharacter (r + 1) k).toMonoidHom (rightIdentityLevi k r F.Carrier l) : ℂ) •
        TensorProduct.map (((Mirabolic.psiMinus T (r + 1)).obj Y.1).representation
            (leftProjection (rightIdentityLevi k r F.Carrier l)).1)
          (((generalLinearRestriction T k).obj Y.2).representation
            (leftProjection (rightIdentityLevi k r F.Carrier l)).2) (e' w))
    (t : κ.IntertwiningMap κ')
    (ht : letI := T.topology; ∀ w, e' (t w) =
      TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T (r + 1)).map f.1)).toLinearMap
        (SmoothRep.hom f.2).toLinearMap (e w))
    (u : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + r + 1 + 1)
      Induction.CompactFunctions
        ((rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) κ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1)
    letI := T.generalLinearTopologicalGroup (r + 1 + k + 1)
    rightIdentityCompactEquivOf T k r Y κ' e' he'
        (Induction.compactInducedMap
          ((rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier)))
          t u) =
      SmoothRep.hom ((rightIdentityTarget.{uF, uV} T k r).map f)
        (rightIdentityCompactEquivOf T k r X κ e he u) := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup (k + r + 1 + 1)
  let _ := T.generalLinearTopologicalGroup (r + 1 + k + 1)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change e' (t (Induction.eval
      ((rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) κ
      u.val ((rightIdentityCast T k r).symm x))) =
    TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T (r + 1)).map f.1)).toLinearMap
      (SmoothRep.hom f.2).toLinearMap
      (e (Induction.eval
        ((rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) κ
        u.val ((rightIdentityCast T k r).symm x)))
  exact ht _

end Transport

/-! ## The localization of the orbit piece -/

section Localization

variable (T : F.TopologicalData) (k r : ℕ)

/-- The restricted coefficient of the orbit piece, in the form produced by the functors. -/
abbrev rightIdentityOrbitCoefficient
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    Representation ℂ (rightIdStabilizer k r F.Carrier)
      ((Rep.resFunctor (Geometric.stabilizerToInducing (G := mirabolic (k + r + 1 + 1) F.Carrier)
          (rightInducing k r F.Carrier)
          (plusSubgroup (k + r + 1) F.Carrier) (rightRepresentative k r F.Carrier 1))).obj
        ((ObjectProperty.ι _).obj ((rightOrbitInput T k r).obj X))) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  ((Rep.resFunctor (Geometric.stabilizerToInducing (G := mirabolic (k + r + 1 + 1) F.Carrier)
      (rightInducing k r F.Carrier)
      (plusSubgroup (k + r + 1) F.Carrier) (rightRepresentative k r F.Carrier 1))).obj
    ((ObjectProperty.ι _).obj ((rightOrbitInput T k r).obj X))).ρ

/-- The functorial form of the orbit coefficient is `χ_R (τ ⊠ ρ)` through the stabilizer. -/
def rightIdentityCoefficientBridge
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    (rightIdentityOrbitCoefficient T k r X).Equiv
      (rightIdentityCoefficient T k r X.1.representation X.2.representation) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun _ => rfl)

/-- The localization of the identity orbit piece is the split-kernel localized action of
the orbit piece itself, through the identity. -/
def rightIdentityLocalizationEquiv₀
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    Representation.Equiv
      ((Mirabolic.plusPhiLocalization ψ (k + r + 1)).obj
        ((Geometric.orbitPiece (R := ℂ) (G := mirabolic (k + r + 1 + 1) F.Carrier)
          (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
          (rightRepresentative k r F.Carrier 1)).obj ((rightOrbitInput T k r).obj X))).ρ
      (Induction.SplitKernelLocalization.localizedAction
        (plusProjection (n := k + r + 1) (F := F.Carrier)) plusSuccessor
        (plusKernelThetaSmooth T ψ (k + r + 1)).toMonoidHom
        (plusKernelThetaSmooth_sectionInvariant T ψ (k + r + 1))
        ((Geometric.orbitPiece (R := ℂ) (G := mirabolic (k + r + 1 + 1) F.Carrier)
          (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
          (rightRepresentative k r F.Carrier 1)).obj ((rightOrbitInput T k r).obj X)).ρ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  Representation.Equiv.mk (LinearEquiv.refl ℂ _)
    (fun _ => LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun _ => rfl)

/-- The orbit piece is the compact induction of `χ_R (τ ⊠ ρ)` from the stabilizer. -/
def rightIdentityOrbitEquiv
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    Representation.Equiv
      ((Geometric.orbitPiece (R := ℂ) (G := mirabolic (k + r + 1 + 1) F.Carrier)
          (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
          (rightRepresentative k r F.Carrier 1)).obj ((rightOrbitInput T k r).obj X)).ρ
      (Induction.compactInduced (rightIdStabilizer k r F.Carrier)
        (rightIdentityCoefficient T k r X.1.representation X.2.representation)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  Induction.compactInducedEquiv _ (rightIdentityCoefficientBridge T k r X)

end Localization






/-! ## The identity orbit piece -/

section Piece

open Induction QuotientIntegration

/-- Naturality of a composite of five maps from the naturality of each step. -/
theorem chain_natural₅ {α₁ α₂ β₁ β₂ γ₁ γ₂ δ₁ δ₂ ε₁ ε₂ ζ₁ ζ₂ : Sort*}
    {A₁ : α₁ → β₁} {A₂ : α₂ → β₂} {B₁ : β₁ → γ₁} {B₂ : β₂ → γ₂} {C₁ : γ₁ → δ₁}
    {C₂ : γ₂ → δ₂} {D₁ : δ₁ → ε₁} {D₂ : δ₂ → ε₂} {E₁ : ε₁ → ζ₁} {E₂ : ε₂ → ζ₂}
    {a : α₁ → α₂} {b : β₁ → β₂} {c : γ₁ → γ₂} {d : δ₁ → δ₂} {e : ε₁ → ε₂} {f : ζ₁ → ζ₂}
    (x : α₁) (h₁ : A₂ (a x) = b (A₁ x)) (h₂ : B₂ (b (A₁ x)) = c (B₁ (A₁ x)))
    (h₃ : C₂ (c (B₁ (A₁ x))) = d (C₁ (B₁ (A₁ x))))
    (h₄ : D₂ (d (C₁ (B₁ (A₁ x)))) = e (D₁ (C₁ (B₁ (A₁ x)))))
    (h₅ : E₂ (e (D₁ (C₁ (B₁ (A₁ x))))) = f (E₁ (D₁ (C₁ (B₁ (A₁ x)))))) :
    E₂ (D₂ (C₂ (B₂ (A₂ (a x))))) = f (E₁ (D₁ (C₁ (B₁ (A₁ x))))) := by
  rw [h₁, h₂, h₃, h₄, h₅]

set_option maxHeartbeats 8000000 in
/-- BZ77 4.13(c), identity orbit: the normalized localized orbit piece of `τ × ρ` at the
identity representative is `(Ψ⁻τ) × (ρ|P)`, naturally in `(τ, ρ)`. -/
theorem rightPhiIdentityPiece_iso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    Nonempty (rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 1) ≅
      rightPhiQuotient.{uF, uV} T k (r + 1) ⋙
        SmoothRep.toRep (G := mirabolic (k + r + 1) F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  let := T.generalLinearTopologicalGroup (k + r + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (k + r + 1 + 1 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := k + r + 1 + 1) (F := F.Carrier)
  let : LocallyCompactSpace (plusSubgroup (k + r + 1) F.Carrier) :=
    plusSubgroup_isClosed.locallyCompactSpace
  have := isTopologicalRing_of_topologicalData F T
  -- The split-stage data on `Q = P_(k+r+2) V_(k+r+3)`.
  let P := rightStages k r F.Carrier 1
  let S := rightIdStabilizer k r F.Carrier
  let K := P.comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))
  have hker : (plusProjection (n := k + r + 1) (F := F.Carrier)).ker ≤ P :=
    plusKernel_le_stagesSubgroup _ _
  have hHP : S ≤ P := rightIdStabilizer_le_stages k r F.Carrier
  have hP : IsClosed (P : Set (plusSubgroup (k + r + 1) F.Carrier)) :=
    rightStages_isClosed k r F.Carrier 1
  have hH : IsClosed (S : Set (plusSubgroup (k + r + 1) F.Carrier)) :=
    rightIdStabilizer_isClosed k r F.Carrier
  have hsH := rightIdentity_section_mem k r F.Carrier
  have hr : Continuous (plusProjection (n := k + r + 1) (F := F.Carrier)) :=
    continuous_plusProjection
  have hs : Continuous (plusSuccessor (n := k + r + 1) (F := F.Carrier)) :=
    continuous_plusSuccessor
  let θ := plusKernelThetaSmooth T ψ (k + r + 1)
  have hθ := plusKernelThetaSmooth_sectionInvariant T ψ (k + r + 1)
  have hN : IsClosed ((plusProjection (n := k + r + 1) (F := F.Carrier)).ker :
      Set (plusSubgroup (k + r + 1) F.Carrier)) :=
    isClosed_singleton.preimage continuous_plusProjection
  have hBasis := plusSubgroup_compactOpenBasis T (k + r + 1)
  -- Measures on the kernel, its intersection with the stabilizer and the quotient.
  let rP := rightIdentityRetraction k r F.Carrier
  let eK := splitStagesKernelContinuousEquiv plusProjection plusSuccessor
    plusProjection_plusSuccessor P hker
  let : LocallyCompactSpace (plusProjection (n := k + r + 1) (F := F.Carrier)).ker :=
    hN.locallyCompactSpace
  let : LocallyCompactSpace rP.ker := eK.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hIc : IsClosed (((rightIdentityInducing k r F.Carrier).comap rP.ker.subtype :
      Subgroup rP.ker) : Set rP.ker) :=
    isClosed_splitKernelIntersection _ _ (hH.preimage continuous_subtype_val)
  let : LocallyCompactSpace ((rightIdentityInducing k r F.Carrier).comap rP.ker.subtype) :=
    hIc.locallyCompactSpace
  let : MeasurableSpace rP.ker := borel _
  have : BorelSpace rP.ker := ⟨rfl⟩
  let : MeasurableSpace ((rightIdentityInducing k r F.Carrier).comap rP.ker.subtype) := borel _
  have : BorelSpace ((rightIdentityInducing k r F.Carrier).comap rP.ker.subtype) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    ((rightIdentityInducing k r F.Carrier).comap rP.ker.subtype)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient
    ((rightIdentityInducing k r F.Carrier).comap rP.ker.subtype)) := ⟨rfl⟩
  let eR : rP.ker ≃ₜ* radical (k + r + 1 + 1) F.Carrier :=
    eK.trans (plusKernelContinuousEquiv F.Carrier)
  have hKernelBasis := compactOpenBasis_of_continuousMulEquiv eR
    (radical_compactOpenBasis T (k + r + 1))
  have hCover := compactOpenCover_of_continuousMulEquiv eR
    (radical_compactOpenCover T (k + r + 1))
  have hu := Haar.compactOpenCoverUnimodularity hCover
  let μN : Measure rP.ker := haar
  let μI : Measure ((rightIdentityInducing k r F.Carrier).comap rP.ker.subtype) := haar
  have : IsMulRightInvariant μN := hu.1 μN
  have : IsMulRightInvariant μI := hu.2 _ hIc μI
  obtain ⟨ν, hν⟩ := QuotientIntegration.compatibleMeasureExists _ hIc μN μI
  have : ν.Regular := hν.regular
  -- The coefficient `χ_R (τ ⊠ ρ)` on the stabilizer is smooth.
  have hσ : ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier),
      IsSmooth (rightIdentityCoefficient T k r X.1.representation X.2.representation) :=
    fun X => isSmooth_comp (rightIdentityInclusion k r F.Carrier)
      ((continuous_rightInducingHom k r F.Carrier).comp (continuous_stabilizerToInducing _ _))
      ((isSmooth_twist_iff _ _ (T.rightCharacter (k + 1) (r + 1)).isOpen_ker).mpr
        (isSmooth_rightInducingRepresentation X.1.isSmooth X.2.isSmooth))
  -- The localized coefficient and its character, trivial on the kernel intersection.
  let η := SplitKernelLocalization.intersectionCharacter rP
    (SplitStagesCharacter.kernelCharacter plusProjection plusSuccessor plusProjection_plusSuccessor
      P hker θ).toMonoidHom (rightIdentityInducing k r F.Carrier)
  have hη : ∀ a, η a = 1 := fun a =>
    thetaPlus_rightStabilizer_one k r F.Carrier ψ
      ⟨_, (a : rightIdentityInducing k r F.Carrier).property⟩
  let κ := fun X : SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) =>
    SplitStagesCharacter.coefficientAction plusProjection plusSuccessor
      plusProjection_plusSuccessor P S hker hHP hH hsH θ hθ
      (rightIdentityCoefficient T k r X.1.representation X.2.representation)
  let φc : SmoothCharacter ℂ (mirabolic (k + r + 1) F.Carrier) :=
    ⟨Mirabolic.phiMinusCharacter T (k + r + 1), Mirabolic.isOpen_ker_phiMinusCharacter T (k + r + 1)⟩
  -- The normalized coefficient is the normalized lower left mixed coefficient.
  have hE : ∀ (X : SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) (l : K)
      (w : Jacquet.Localization.Coinvariants
        (rightIdentityStagesCoefficient T k r X.1.representation X.2.representation)
        (rightIdentityKernelIntersection k r F.Carrier) η),
      rightIdentityCoefficientEquiv T k r X.1.representation X.2.representation η hη
          (twist (φc.toMonoidHom.comp K.subtype) (κ X) l w) =
        ((T.leftCharacter (r + 1) k).toMonoidHom (rightIdentityLevi k r F.Carrier l) : ℂ) •
          TensorProduct.map (((Mirabolic.psiMinus T (r + 1)).obj X.1).representation
              (leftProjection (rightIdentityLevi k r F.Carrier l)).1)
            (((generalLinearRestriction T k).obj X.2).representation
              (leftProjection (rightIdentityLevi k r F.Carrier l)).2)
            (rightIdentityCoefficientEquiv T k r X.1.representation X.2.representation η hη w) := by
    intro X l w
    refine localization_tensor_ext_smul
      (rightIdentityCoefficientEquiv T k r X.1.representation X.2.representation η hη)
      (twist (φc.toMonoidHom.comp K.subtype) (κ X) l) _ _ (fun a b => ?_) w
    have h₁ : twist (φc.toMonoidHom.comp K.subtype) (κ X) l
        (Jacquet.Localization.mk
          (rightIdentityStagesCoefficient T k r X.1.representation X.2.representation)
          (rightIdentityKernelIntersection k r F.Carrier) η (a ⊗ₜ b)) =
        (((φc.toMonoidHom.comp K.subtype) l : ℂ) *
          (SplitStagesCharacter.haarCharacter plusProjection plusSuccessor
            plusProjection_plusSuccessor P S hker hH hsH l : ℂ)) •
          Jacquet.Localization.mk
            (rightIdentityStagesCoefficient T k r X.1.representation X.2.representation)
            (rightIdentityKernelIntersection k r F.Carrier) η
            (rightIdentityStagesCoefficient T k r X.1.representation X.2.representation
              (SplitKernelLocalization.subgroupSection
                ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap P)
                (rightIdentityInducing k r F.Carrier)
                (rightIdentityInducing_section_mem k r F.Carrier) l) (a ⊗ₜ b)) := by
      change ((φc.toMonoidHom.comp K.subtype) l : ℂ) • (κ X) l (Jacquet.Localization.mk
          (rightIdentityStagesCoefficient T k r X.1.representation X.2.representation)
          (rightIdentityKernelIntersection k r F.Carrier) η (a ⊗ₜ b)) = _
      rw [SplitStagesCharacter.coefficientAction_mk, smul_smul]
    exact linearEquiv_smul_chain _ h₁
      (rightIdentityCoefficientEquiv_section T k r _ _ η hη l a b)
      (rightIdentity_psiMinus_tmul T k r X.1 X.2 _ _ a b) (rightIdentity_scalar_eq T k r l)
  -- The chain of identifications.
  let E : ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier),
      Representation.Equiv
        ((rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 1)).obj X).ρ
        ((rightIdentityTarget.{uF, uV} T k r).obj X).representation := fun X =>
    (twistEquiv (Mirabolic.phiMinusCharacter T (k + r + 1))
      ((rightIdentityLocalizationEquiv₀ T k r ψ X).trans
        ((localizedActionEquiv plusProjection plusSuccessor θ.toMonoidHom hθ
          (rightIdentityOrbitEquiv T k r X)).trans
          (SplitStagesCharacter.comparisonEquiv plusProjection plusSuccessor
            plusProjection_plusSuccessor hr hs P S hker hHP hP hH hsH θ hθ
            (rightIdentityCoefficient T k r X.1.representation X.2.representation) (hσ X)
            ν hKernelBasis μN μI hν hN hBasis)))).trans
    ((compactInductionTwistEquiv K φc (κ X)).trans
      (rightIdentityCompactEquivOf T k r X (twist (φc.toMonoidHom.comp K.subtype) (κ X))
        (rightIdentityCoefficientEquiv T k r X.1.representation X.2.representation η hη)
        (hE X)))
  -- Each step of the chain is natural.
  have hEnat : ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)} (φ : X ⟶ Y)
      (x : (rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 1)).obj X),
      E Y (((rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 1)).map φ).hom x) =
        SmoothRep.hom ((rightIdentityTarget.{uF, uV} T k r).map φ) (E X x) := by
    intro X Y φ x
    let orbitMap := ((Geometric.orbitPiece (R := ℂ) (G := mirabolic (k + r + 1 + 1) F.Carrier)
      (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
      (rightRepresentative k r F.Carrier 1)).map ((rightOrbitInput T k r).map φ)).hom
    let tR := Induction.restrictAlongMap (rightIdentityInclusion k r F.Carrier)
      (twistIntertwining (T.rightCharacter (k + 1) (r + 1)).toMonoidHom
        (MixedProductTensor.pullbackMap rightProjection
          (MixedProductTensor.externalMap (SmoothRep.hom φ.1) (SmoothRep.hom φ.2))))
    let cK := twistIntertwining (SplitStagesCharacter.haarCharacter plusProjection plusSuccessor
        plusProjection_plusSuccessor P S hker hH hsH)
      (SplitKernelLocalization.subgroupMap rP
        ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap P)
        (SplitStagesCharacter.kernelCharacter plusProjection plusSuccessor
          plusProjection_plusSuccessor P hker θ).toMonoidHom
        (SplitStagesCharacter.sectionInvariant plusProjection plusSuccessor
          plusProjection_plusSuccessor P hker θ hθ)
        (rightIdentityInducing k r F.Carrier)
        (SplitStagesCharacter.section_mem plusSuccessor P S hsH)
        (Induction.restrictAlongMap (Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom tR))
    have h0 : rightIdentityLocalizationEquiv₀ T k r ψ Y
        (((Mirabolic.plusPhiLocalization ψ (k + r + 1)).map
          ((Geometric.orbitPiece (R := ℂ) (G := mirabolic (k + r + 1 + 1) F.Carrier)
            (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
            (rightRepresentative k r F.Carrier 1)).map ((rightOrbitInput T k r).map φ))).hom x) =
        SplitKernelLocalization.sectionMap plusProjection plusSuccessor θ.toMonoidHom hθ orbitMap
          (rightIdentityLocalizationEquiv₀ T k r ψ X x) :=
      Submodule.Quotient.induction_on _ x fun _ => rfl
    have horb : ∀ v, rightIdentityOrbitEquiv T k r Y (orbitMap v) =
        Induction.compactInducedMap S tR (rightIdentityOrbitEquiv T k r X v) := by
      intro v
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have h1 := localizedActionEquiv_natural plusProjection plusSuccessor θ.toMonoidHom hθ
      (rightIdentityOrbitEquiv T k r X) (rightIdentityOrbitEquiv T k r Y) orbitMap
      (Induction.compactInducedMap S tR) horb (rightIdentityLocalizationEquiv₀ T k r ψ X x)
    have h2 := SplitStagesCharacter.comparisonEquiv_natural plusProjection plusSuccessor
      plusProjection_plusSuccessor hr hs P S hker hHP hP hH hsH θ hθ
      (rightIdentityCoefficient T k r X.1.representation X.2.representation) (hσ X)
      ν hKernelBasis μN μI hν hN hBasis (hσ Y) tR
      (localizedActionEquiv plusProjection plusSuccessor θ.toMonoidHom hθ
        (rightIdentityOrbitEquiv T k r X) (rightIdentityLocalizationEquiv₀ T k r ψ X x))
    have h3 := compactInductionTwistEquiv_natural K φc cK
      (SplitStagesCharacter.comparisonEquiv plusProjection plusSuccessor
        plusProjection_plusSuccessor hr hs P S hker hHP hP hH hsH θ hθ
        (rightIdentityCoefficient T k r X.1.representation X.2.representation) (hσ X)
        ν hKernelBasis μN μI hν hN hBasis
        (localizedActionEquiv plusProjection plusSuccessor θ.toMonoidHom hθ
          (rightIdentityOrbitEquiv T k r X) (rightIdentityLocalizationEquiv₀ T k r ψ X x)))
    have ht : ∀ w : Jacquet.Localization.Coinvariants
        (rightIdentityStagesCoefficient T k r X.1.representation X.2.representation)
        (rightIdentityKernelIntersection k r F.Carrier) η,
        rightIdentityCoefficientEquiv T k r Y.1.representation Y.2.representation η hη (cK w) =
        TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T (r + 1)).map φ.1)).toLinearMap
          (SmoothRep.hom φ.2).toLinearMap
          (rightIdentityCoefficientEquiv T k r X.1.representation X.2.representation η hη w) := by
      intro w
      obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
        (rightIdentityStagesCoefficient T k r X.1.representation X.2.representation)
        (rightIdentityKernelIntersection k r F.Carrier) η w
      exact rightIdentityCoefficientEquiv_natural T k r φ.1 φ.2 tR.toLinearMap (fun _ _ => rfl)
        η hη v
    have h4 := rightIdentityCompactEquivOf_natural T k r φ
      (twist (φc.toMonoidHom.comp K.subtype) (κ X))
      (rightIdentityCoefficientEquiv T k r X.1.representation X.2.representation η hη) (hE X)
      (twist (φc.toMonoidHom.comp K.subtype) (κ Y))
      (rightIdentityCoefficientEquiv T k r Y.1.representation Y.2.representation η hη) (hE Y)
      (twistIntertwining (φc.toMonoidHom.comp K.subtype) cK) ht
      (compactInductionTwistEquiv K φc (κ X)
        (SplitStagesCharacter.comparisonEquiv plusProjection plusSuccessor
          plusProjection_plusSuccessor hr hs P S hker hHP hP hH hsH θ hθ
          (rightIdentityCoefficient T k r X.1.representation X.2.representation) (hσ X)
          ν hKernelBasis μN μI hν hN hBasis
          (localizedActionEquiv plusProjection plusSuccessor θ.toMonoidHom hθ
            (rightIdentityOrbitEquiv T k r X) (rightIdentityLocalizationEquiv₀ T k r ψ X x))))
    exact chain_natural₅ x h0 h1 h2 h3 h4
  -- Assemble the natural isomorphism.
  let iso0 : rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 1) ≅
      rightIdentityTarget.{uF, uV} T k r ⋙ SmoothRep.toRep (G := mirabolic (k + r + 1) F.Carrier) :=
    NatIso.ofComponents (fun X => Rep.mkIso (E X)) (by
      intro X Y φ
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact hEnat φ x)
  exact ⟨iso0 ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerLeft
    ((Mirabolic.psiMinus T (r + 1)).prod (generalLinearRestriction T k) ⋙
      T.leftMixedProductFunctor (r + 1) k)
    (mirabolicRankCastIso.{uF, max uF uV} T (Nat.add_comm (r + 1) k)).symm) SmoothRep.toRep⟩

end Piece

end Langlands.Derivative.MirabolicProductMinus
