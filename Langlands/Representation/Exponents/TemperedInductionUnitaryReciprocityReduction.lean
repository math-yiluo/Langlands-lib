import Langlands.Representation.Exponents.TemperedInductionUnitaryReciprocityStatement
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityStatement
import Langlands.Representation.Exponents.TemperedJacquetUnitaryRestrictionStatement
import Langlands.Representation.Exponents.CasselmanUniverseLift
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof

/-! # Reduction of the VII.2.4 Proposition to its two steps

Renard 2026, VII.2.4, Proposition (printed p.229/PDF p.235) is the composite of
Frobenius reciprocity (VI.1.1, stated as `LeviFrobeniusReciprocityStatement`) and
restriction to the unitary Jacquet part (`TemperedJacquetUnitaryRestrictionStatement`).
The restriction statement takes `π` and `σ` in one carrier universe. This module
transports actual Jacquet modules, unitary parts, normalized exponents and
temperedness along cross-universe representation equivalences, and proves the
Proposition from the two statements, with the restriction step used for the lifted
carrier universe `max v w`.
-/

noncomputable section

universe u v w v' w'

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Congr

variable {H : Type*} [Monoid H] {V V' W W' : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
  {ρ : Representation ℂ H V} {ρ' : Representation ℂ H V'}
  {τ : Representation ℂ H W} {τ' : Representation ℂ H W'}

/-- Representation equivalences of source and target identify the intertwiner spaces,
across carrier universes: `f ↦ e₂ ∘ f ∘ e₁⁻¹`. -/
def intertwiningMapCongr (e₁ : ρ.Equiv ρ') (e₂ : τ.Equiv τ') :
    ρ.IntertwiningMap τ ≃ ρ'.IntertwiningMap τ' where
  toFun f := e₂.toIntertwiningMap.comp (f.comp e₁.symm.toIntertwiningMap)
  invFun f := e₂.symm.toIntertwiningMap.comp (f.comp e₁.toIntertwiningMap)
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change e₂.symm (e₂ (f (e₁.symm (e₁ x)))) = f x
    rw [Representation.Equiv.symm_apply_apply, Representation.Equiv.symm_apply_apply]
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change e₂ (e₂.symm (f (e₁ (e₁.symm x)))) = f x
    rw [Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply]

@[simp] theorem intertwiningMapCongr_apply (e₁ : ρ.Equiv ρ') (e₂ : τ.Equiv τ')
    (f : ρ.IntertwiningMap τ) (x : V') :
    intertwiningMapCongr e₁ e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl

end Congr

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance reciprocityReductionAmbientPointTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

section Jacquet

variable (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a)

/-- A representation equivalence, possibly between different carrier universes, gives an
equivalence of the actual normalized Jacquet modules over the literal Levi image. -/
def jacquetEquivOfEquiv (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (π' : SmoothRep.{0, u, w'} ℂ (rationalPoints G))
    (e : π.representation.Equiv π'.representation) :
    ((jacquetFunctor p l r hp hr hl hmul).obj π).representation.Equiv
      ((jacquetFunctor p l r hp hr hl hmul).obj π').representation :=
  normalizedJacquetRepresentationEquiv (pointImage (r ≫ p)) (pointImage (l ≫ p))
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr) π π' e

/-- The same equivalence for the Jacquet modules transported to `M(F)`. -/
def leviJacquetEquivOfEquiv (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (π' : SmoothRep.{0, u, w'} ℂ (rationalPoints G))
    (e : π.representation.Equiv π'.representation) :
    letI := leviPointTopology l hl
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.Equiv
      ((leviJacquetFunctor p l r hp hr hl hmul).obj π').representation :=
  letI := leviPointTopology l hl
  Representation.Equiv.mk (jacquetEquivOfEquiv p l r hp hl hr hmul π π' e).toLinearEquiv
    (fun m => (jacquetEquivOfEquiv p l r hp hl hr hmul π π' e).isIntertwining'
      (leviPointsEquiv p l hp hl m))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Equivalent representations have the same normalized Jacquet exponents. -/
theorem isNormalizedJacquetExponent_iff_of_equiv
    (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (π' : SmoothRep.{0, u, w'} ℂ (rationalPoints G))
    (e : π.representation.Equiv π'.representation) (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ↔
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π' χ := by
  rw [isNormalizedJacquetExponent_iff, isNormalizedJacquetExponent_iff]
  let E := jacquetEquivOfEquiv p l r hp hl hr hmul π π' e
  exact isGeneralizedEigencharacter_iff_of_equiv
    (Representation.Equiv.mk E.toLinearEquiv
      (fun t => E.isIntertwining' (splitComponentPointsMap (l ≫ p) a t))) χ

/-- Every intertwiner of actual Jacquet modules over the literal Levi image maps the
unitary part into the unitary part. -/
theorem mapsTo_unitaryJacquetPart (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (π' : SmoothRep.{0, u, w'} ℂ (rationalPoints G))
    (φ : ((jacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
      ((jacquetFunctor p l r hp hr hl hmul).obj π').representation) :
    Set.MapsTo φ
      (unitaryJacquetPart p l r hp hl hr hmul ha π :
        Set ((jacquetFunctor p l r hp hr hl hmul).obj π))
      (unitaryJacquetPart p l r hp hl hr hmul ha π' :
        Set ((jacquetFunctor p l r hp hr hl hmul).obj π')) := by
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  rw [unitaryJacquetPart_eq_iSup p l r hp hl hr hmul ha π,
    unitaryJacquetPart_eq_iSup p l r hp hl hr hmul ha π']
  refine Langlands.Subrepresentation.mapsTo_iSup φ _ _ fun χ => ?_
  refine Langlands.Subrepresentation.mapsTo_iSup φ _ _ fun h0 => ?_
  intro x hx
  have hmem : φ x ∈ normalizedJacquetWeightSpace p l r hp hl hr hmul ha π' χ :=
    map_mem_generalizedWeightSpace (splitComponentPointsMap (l ≫ p) a) χ
      (splitComponentPointsMap_mem_center (l ≫ p) ha) φ hx
  exact (le_iSup₂ (f := fun χ (_ : Plancherel.SplitTorus.normalizedRealPart
      ha.isCentralSplitTorus.1.1 χ = 0) =>
    normalizedJacquetWeightSpace p l r hp hl hr hmul ha π' χ) χ h0) hmem

/-- A representation equivalence maps the unitary part onto the unitary part. -/
theorem unitaryJacquetPart_map_jacquetEquivOfEquiv
    (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (π' : SmoothRep.{0, u, w'} ℂ (rationalPoints G))
    (e : π.representation.Equiv π'.representation) :
    (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule.map
        ((jacquetEquivOfEquiv p l r hp hl hr hmul π π' e).toLinearEquiv :
          (jacquetFunctor p l r hp hr hl hmul).obj π →ₗ[ℂ]
            (jacquetFunctor p l r hp hr hl hmul).obj π') =
      (unitaryJacquetPart p l r hp hl hr hmul ha π').toSubmodule := by
  let E := jacquetEquivOfEquiv p l r hp hl hr hmul π π' e
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mapsTo_unitaryJacquetPart p l r hp hl hr hmul ha π π' E.toIntertwiningMap hx
  · intro y hy
    exact ⟨E.symm y,
      mapsTo_unitaryJacquetPart p l r hp hl hr hmul ha π' π E.symm.toIntertwiningMap hy,
      E.apply_symm_apply y⟩

/-- A representation equivalence restricts to an equivalence of the unitary Jacquet
modules `(r_P^G π)_0` of `M(F)`. -/
def leviUnitaryJacquetModuleEquivOfEquiv (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (π' : SmoothRep.{0, u, w'} ℂ (rationalPoints G))
    (e : π.representation.Equiv π'.representation) :
    letI := leviPointTopology l hl
    (leviUnitaryJacquetModule p l r hp hl hr hmul ha π).representation.Equiv
      (leviUnitaryJacquetModule p l r hp hl hr hmul ha π').representation :=
  letI := leviPointTopology l hl
  Representation.Equiv.mk
    ((jacquetEquivOfEquiv p l r hp hl hr hmul π π' e).toLinearEquiv.ofSubmodules
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (unitaryJacquetPart p l r hp hl hr hmul ha π').toSubmodule
      (unitaryJacquetPart_map_jacquetEquivOfEquiv p l r hp hl hr hmul ha π π' e))
    (fun m => by
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      exact Representation.IntertwiningMap.isIntertwining _ _
        (jacquetEquivOfEquiv p l r hp hl hr hmul π π' e).toIntertwiningMap
        (leviPointsEquiv p l hp hl m) y.1)

/-- Restriction of Levi intertwiners along the inclusion of the unitary part, as a linear
map of actual intertwiner spaces. Carrier universes of `π` and `σ` are independent. -/
def leviUnitaryRestriction (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
        σ.representation →ₗ[ℂ]
      (leviUnitaryJacquetModule p l r hp hl hr hmul ha π).representation.IntertwiningMap
        σ.representation :=
  letI := leviPointTopology l hl
  { toFun f := f.comp (SmoothRep.hom (leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π))
    map_add' _ _ := Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
    map_smul' _ _ := Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl) }

@[simp] theorem leviUnitaryRestriction_apply (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (f : letI := leviPointTopology l hl
      ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
        σ.representation)
    (y : leviUnitaryJacquetModule p l r hp hl hr hmul ha π) :
    letI := leviPointTopology l hl
    leviUnitaryRestriction p l r hp hl hr hmul ha π σ f y =
      f (SmoothRep.hom (leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π) y) :=
  rfl

/-- Bijectivity of the restriction transfers along representation equivalences of both
`π` and `σ`, across carrier universes. -/
theorem leviUnitaryRestriction_bijective_of_equiv
    (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (π' : SmoothRep.{0, u, w'} ℂ (rationalPoints G))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (σ' : letI := leviPointTopology l hl; SmoothRep.{0, u, v'} ℂ (rationalPoints M))
    (eπ : π.representation.Equiv π'.representation)
    (eσ : letI := leviPointTopology l hl; σ.representation.Equiv σ'.representation)
    (h : letI := leviPointTopology l hl
      Function.Bijective (leviUnitaryRestriction p l r hp hl hr hmul ha π' σ')) :
    letI := leviPointTopology l hl
    Function.Bijective (leviUnitaryRestriction p l r hp hl hr hmul ha π σ) := by
  let := leviPointTopology l hl
  let Φ := intertwiningMapCongr (leviJacquetEquivOfEquiv p l r hp hl hr hmul π π' eπ) eσ
  let Ψ := intertwiningMapCongr
    (leviUnitaryJacquetModuleEquivOfEquiv p l r hp hl hr hmul ha π π' eπ) eσ
  have hcomm : (Ψ ∘ leviUnitaryRestriction p l r hp hl hr hmul ha π σ) =
      leviUnitaryRestriction p l r hp hl hr hmul ha π' σ' ∘ Φ := by
    funext f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    rfl
  rw [← Equiv.comp_bijective _ Ψ, hcomm]
  exact h.comp Φ.bijective

/-- In one carrier universe, bijectivity of the linear restriction is bijectivity of the
categorical precomposition map of `TemperedJacquetUnitaryRestrictionStatement`. -/
theorem leviUnitaryRestriction_bijective_iff (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    Function.Bijective (leviUnitaryRestriction p l r hp hl hr hmul ha π σ) ↔
      Function.Bijective
        (fun f : (leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶ σ =>
          leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π ≫ f) := by
  let := leviPointTopology l hl
  let h₁ : ((leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶ σ) ≃
      ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
        σ.representation :=
    ⟨SmoothRep.hom, SmoothRep.ofHom, fun _ => rfl, fun _ => rfl⟩
  let h₂ : (leviUnitaryJacquetModule p l r hp hl hr hmul ha π ⟶ σ) ≃
      (leviUnitaryJacquetModule p l r hp hl hr hmul ha π).representation.IntertwiningMap
        σ.representation :=
    ⟨SmoothRep.hom, SmoothRep.ofHom, fun _ => rfl, fun _ => rfl⟩
  have heq : (leviUnitaryRestriction p l r hp hl hr hmul ha π σ :
        ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
          σ.representation →
        (leviUnitaryJacquetModule p l r hp hl hr hmul ha π).representation.IntertwiningMap
          σ.representation) =
      h₂ ∘ (fun f : (leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶ σ =>
        leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π ≫ f) ∘ h₁.symm := by
    funext f
    rfl
  rw [heq, Equiv.comp_bijective, Equiv.bijective_comp]

end Jacquet

/-- Normalized-exponent temperedness is invariant under representation equivalences,
across carrier universes. -/
theorem isNormalizedExponentTempered_of_equiv {hG : IsConnectedReductive G}
    {π : SmoothRep.{0, u, w} ℂ (rationalPoints G)}
    {π' : SmoothRep.{0, u, w'} ℂ (rationalPoints G)}
    (e : π.representation.Equiv π'.representation)
    (h : IsNormalizedExponentTempered hG π) : IsNormalizedExponentTempered hG π' := by
  refine ⟨(isAdmissible_iff_of_equiv e).mp h.1, fun P M A p l a hp hl ha => ?_⟩
  obtain ⟨hne, hcone⟩ := h.2 P M A p l a hp hl ha
  exact ⟨hne, fun pres U r hr hmul χ hχ => hcone pres U r hr hmul χ
    ((isNormalizedJacquetExponent_iff_of_equiv p l r hp hl hr hmul ha π π' e χ).mpr hχ)⟩

/-- Renard VII.2.4, Proposition, from Frobenius reciprocity and the restriction step.
The restriction step is used for the carrier universe `max v w`, through universe lifts
of `π` and `σ`. -/
theorem temperedInductionUnitaryReciprocity_of
    (hF : LeviFrobeniusReciprocityStatement.{u, v, w})
    (hR : TemperedJacquetUnitaryRestrictionStatement.{u, max v w}) :
    TemperedInductionUnitaryReciprocityStatement.{u, v, w} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U A p l r a hp hl hr hmul ha
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro π σ hπ hσ
  obtain ⟨e₁, he₁⟩ := hF k G hG P M U p l r hp hl hr hmul π σ
  let π' : SmoothRep.{0, u, max v w} ℂ (rationalPoints G) := SmoothRep.universeLift.{v} π
  let σ' : SmoothRep.{0, u, max v w} ℂ (rationalPoints M) := SmoothRep.universeLift.{w} σ
  have hπ' : IsNormalizedExponentTempered hG π' :=
    isNormalizedExponentTempered_of_equiv (SmoothRep.universeLiftEquiv π) hπ
  have hσ' : IsNormalizedExponentTempered hl.isConnectedReductive σ' :=
    isNormalizedExponentTempered_of_equiv (SmoothRep.universeLiftEquiv σ) hσ
  have hbij' := (leviUnitaryRestriction_bijective_iff p l r hp hl hr hmul ha π' σ').mpr
    (hR k G hG P M U A p l r a hp hl hr hmul ha π' σ' hπ' hσ')
  have hbij := leviUnitaryRestriction_bijective_of_equiv p l r hp hl hr hmul ha π π' σ σ'
    (SmoothRep.universeLiftEquiv π) (SmoothRep.universeLiftEquiv σ) hbij'
  refine ⟨e₁.trans (LinearEquiv.ofBijective _ hbij), fun F y x hyx => ?_⟩
  change e₁ F (SmoothRep.hom (leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π) y) = _
  rw [hyx]
  exact he₁ F x

end Langlands.Aubert.General.RepresentedParabolic
