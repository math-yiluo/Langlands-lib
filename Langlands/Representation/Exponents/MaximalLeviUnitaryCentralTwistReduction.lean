import Langlands.Representation.Exponents.MaximalLeviTwistReduction
import Langlands.Representation.Exponents.PositiveUnramifiedCentralTwist
import Langlands.Representation.Aubert.General.InductionCentralCharacter
import Langlands.Representation.Classification.Essential
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.RationalCenterComparisonProof

/-! # The unitary-central-twist step of Renard VII.1.3

Renard 2026, VII.1.3 (printed p.224/PDF p.230) twists the supercuspidal `ρ` by an
unramified character of `G` so that the central character of `i_P^G ρ` becomes unitary.
This module proves `MaximalLeviUnitaryCentralTwistStatement` from Milne's theorem that
parabolic subgroups are the dynamic `P(λ)` (`ParabolicDynamicStatement`).

That theorem is used only to put the center `Z` of `G(F)` inside the parabolic points
`P(F)`. An element `z ∈ Z` then acts on `i_P^G ρ` by the scalar `ω_ρ(m_z)`, where `m_z` is
the Levi projection of `z`. The Levi projection of a represented parabolic is continuous,
so `z ↦ ω_ρ(m_z)` has open kernel, and VI.8.5 gives the twist.
-/

noncomputable section

universe u v uG uV

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section ParabolicCenter

variable {G : Type uG} [Group G] {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hZP : Subgroup.center G ≤ P)

/-- The Levi projection of a central element of `G` is central in the Levi. -/
theorem IsSemidirectDecomposition.projection_mem_center (z : Subgroup.center G) :
    h.projection ⟨z, hZP z.property⟩ ∈ Subgroup.center M := by
  rw [Subgroup.mem_center_iff]
  intro m
  have hc : (⟨m, h.levi_le m.2⟩ : P) * ⟨z, hZP z.property⟩ =
      ⟨z, hZP z.property⟩ * ⟨m, h.levi_le m.2⟩ :=
    Subtype.ext (Subgroup.mem_center_iff.mp z.property m)
  have := congrArg h.projection hc
  rwa [map_mul, map_mul, h.projection_levi] at this

/-- The Levi projection on the center of `G`, for a parabolic containing that center. -/
def parabolicCenterProjection : Subgroup.center G →* Subgroup.center M :=
  (h.projection.comp (Subgroup.inclusion hZP)).codRestrict (Subgroup.center M)
    (fun z => h.projection_mem_center hZP z)

@[simp]
theorem parabolicCenterProjection_coe (z : Subgroup.center G) :
    ((parabolicCenterProjection h hZP z : Subgroup.center M) : M) =
      h.projection ⟨z, hZP z.property⟩ :=
  rfl

theorem continuous_parabolicCenterProjection [TopologicalSpace G]
    (hproj : Continuous h.projection) : Continuous (parabolicCenterProjection h hZP) :=
  (hproj.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

end ParabolicCenter

section Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (hZP : Subgroup.center G ≤ P)

/-- A central element `z` of `G` lying in `P` acts on normalized induction by the central
character of the inducing representation at the Levi projection of `z`; the half modulus
contributes one. -/
theorem normalizedInduction_acts_of_center_le_parabolic
    (A : SmoothRep.{0, uG, uV} ℂ M) (χ : Subgroup.center M →* ℂˣ)
    (hact : ∀ (z : Subgroup.center M) (v : A),
      A.representation z v = (χ z : ℂ) • v)
    (z : Subgroup.center G) (f : (normalizedInductionFunctor h hU).obj A) :
    ((normalizedInductionFunctor h hU).obj A).representation z f =
      (χ (parabolicCenterProjection h hZP z) : ℂ) • f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change Induction.eval P (inducingRepresentation h hU A) f (x * (z : G)) =
    (χ (parabolicCenterProjection h hZP z) : ℂ) •
      Induction.eval P (inducingRepresentation h hU A) f x
  rw [Subgroup.mem_center_iff.mp z.property x]
  let q : P := ⟨z, hZP z.property⟩
  change Induction.eval P (inducingRepresentation h hU A) f ((q : G) * x) = _
  rw [normalizedInductionFunctor_covariant h hU A f q x,
    closedHalfCharacter_eq_one_of_mem_center U P hU h.le_normalizer q z.property,
    Units.val_one, one_smul]
  exact hact (parabolicCenterProjection h hZP z) _

end Induction

namespace RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

section Center

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {G P : GroupScheme (Spec (CommRingCat.of k))}

/-- Given Milne's theorem 25.1, the center of `G(F)` lies in the points of every parabolic:
a central point is in the scheme center (`rationalCenterComparison`), which lies in every
dynamic centralizer `Z_G(λ) ⊆ P_G(λ)`. -/
theorem center_le_pointImage_of_parabolicDynamic (hD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G) (p : P ⟶ G) (hp : IsParabolicSubgroup p) :
    Subgroup.center (rationalPoints G) ≤ pointImage p := by
  intro z hz
  rw [← (rationalCenterComparison k G hG : schemeCenterPoints G = _)] at hz
  obtain ⟨χ, hχ⟩ := (hD k G hG P p hp.isClosedSubgroup).mp hp
  have hzP : z ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    SubgroupFunctor.le_def.mp (Dynamic.centralizer_le_parabolic χ) _
      (SubgroupFunctor.le_def.mp (center_le_dynamicCentralizer χ) _ hz)
  rw [← hχ] at hzP
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hzP
  exact ⟨y, hy⟩

end Center

section Projection

variable {k : Type u} [Field k] {G P M U : GroupScheme (Spec (CommRingCat.of k))}

/-- The factorization `q = l(x) r(y)` of a point of `P` given by the inverse of the
multiplication isomorphism. -/
theorem pointMultiplication_inv (l : M ⟶ P) (r : U ⟶ P)
    (hmul : IsIso (subgroupMultiplication l r)) (q : rationalPoints P) :
    rationalPoints.map l (q ≫ inv (subgroupMultiplication l r) ≫ fst _ _) *
        rationalPoints.map r (q ≫ inv (subgroupMultiplication l r) ≫ snd _ _) = q := by
  rw [← lift_comp_subgroupMultiplication]
  have hlift : lift (q ≫ inv (subgroupMultiplication l r) ≫ fst _ _)
      (q ≫ inv (subgroupMultiplication l r) ≫ snd _ _) =
        q ≫ inv (subgroupMultiplication l r) := by
    ext <;> simp
  rw [hlift, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

variable [TopologicalSpace k] [IsAffineHom G.X.hom]

local instance projectionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

omit [TopologicalSpace k] [IsAffineHom G.X.hom] in
/-- The Levi projection of `p(q)` is `(l ≫ p)(x)`, where `q = l(x) r(y)`. -/
theorem pointImage_projection_coe (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsClosedSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) (x : pointImage p) (q : rationalPoints P)
    (hq : rationalPoints.map p q = x) :
    (((isSemidirectDecomposition_pointImage p l r hp hr hmul).projection x :
        pointImage (l ≫ p)) : rationalPoints G) =
      rationalPoints.map (l ≫ p) (q ≫ inv (subgroupMultiplication l r) ≫ fst _ _) := by
  have hx : (x : rationalPoints G) =
      rationalPoints.map (l ≫ p) (q ≫ inv (subgroupMultiplication l r) ≫ fst _ _) *
        rationalPoints.map (r ≫ p) (q ≫ inv (subgroupMultiplication l r) ≫ snd _ _) := by
    rw [← hq, pointMap_comp_apply, pointMap_comp_apply, ← map_mul,
      pointMultiplication_inv l r hmul q]
  have key := ((isSemidirectDecomposition_pointImage p l r hp hr hmul).projection_eq_iff x
    ⟨rationalPoints.map (l ≫ p) (q ≫ inv (subgroupMultiplication l r) ≫ fst _ _),
      ⟨_, rfl⟩⟩).mpr (by
        change (rationalPoints.map (l ≫ p)
            (q ≫ inv (subgroupMultiplication l r) ≫ fst _ _))⁻¹ * (x : rationalPoints G) ∈
          pointImage (r ≫ p)
        rw [hx, inv_mul_cancel_left]
        exact ⟨_, rfl⟩)
  rw [key]

/-- The Levi projection `P(F) → M(F)` of a represented parabolic is continuous: through the
canonical identification of `P(F)` with its point image it is the point map of the scheme
morphism `inv (subgroupMultiplication l r) ≫ fst`. -/
theorem continuous_pointImage_projection (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsClosedSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    Continuous (isSemidirectDecomposition_pointImage p l r hp hr hmul).projection := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion p.hom.hom.left := hp
  have : IsAffine P.X.left := isAffine_of_isAffineHom p.hom.hom.left
  let : TopologicalSpace (rationalPoints P) := rationalPointTopology k P.X
  let e := rationalPointSubgroupHomeomorph k (SubgroupFunctor.range p) p
    hp.isRepresentedBy_range hp
  let g : P.X ⟶ G.X :=
    inv (subgroupMultiplication l r) ≫ fst M.X U.X ≫ l.hom.hom ≫ p.hom.hom
  have hg : Continuous (fun q : rationalPoints P => q ≫ g) := continuous_rationalPointMap k g
  have he : Continuous (fun x : pointImage p =>
      e.symm ⟨(x : rationalPoints G), x.property⟩) :=
    e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  refine continuous_induced_rng.2 ((hg.comp he).congr fun x => ?_)
  have hq : rationalPoints.map p (e.symm ⟨(x : rationalPoints G), x.property⟩) = x :=
    congrArg Subtype.val (e.apply_symm_apply ⟨(x : rationalPoints G), x.property⟩)
  change e.symm ⟨(x : rationalPoints G), x.property⟩ ≫ g = _
  rw [Function.comp_apply, pointImage_projection_coe p l r hp hr hmul x _ hq]
  simp only [g, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

end Projection

/-- **The unitary-central-twist step of Renard VII.1.3**, from Milne's theorem 25.1:
`MaximalLeviUnitaryCentralTwistStatement` holds whenever `ParabolicDynamicStatement` does.

The center `Z` of `G(F)` lies in `P(F)`, and `z ∈ Z` acts on `i_P^G ρ` by
`ω_G(z) = ω_ρ(m_z)`, with `ω_ρ` the Schur central character of `ρ` and `m_z` the Levi
projection of `z`. VI.8.5 gives an unramified `χ` of `G(F)` with `|χ ω_G| = 1` on `Z`, and
`i_P^G(ρ ⊗ χ_M) ≅ (i_P^G ρ) ⊗ χ` has the unitary central character `χ ω_G`. -/
theorem maximalLeviUnitaryCentralTwist_of_parabolicDynamic
    (hD : ParabolicDynamicStatement.{u}) :
    MaximalLeviUnitaryCentralTwistStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  let := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  let := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hρ _
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  obtain ⟨ω, hact⟩ :=
    CuspidalSupport.rationalPointCentralCharacter k M hl.isConnectedReductive ρ hρ
  obtain ⟨x, hx⟩ :=
    Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible ρ.representation hρ
  have : Nontrivial ρ := ⟨⟨x, 0, hx⟩⟩
  have hω : IsOpen (ω.ker : Set (Subgroup.center (rationalPoints M))) :=
    SmoothRep.HasCentralCharacter.isOpen_ker ρ hact
  have hZP := center_le_pointImage_of_parabolicDynamic hD hG p hp
  let hd := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hU := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let e := leviPointsEquiv p l hp hl
  let ωA : Subgroup.center (pointImage (l ≫ p)) →* ℂˣ :=
    ω.comp (Subgroup.centerCongr e.symm.toMulEquiv).toMonoidHom
  let ωG : Subgroup.center (rationalPoints G) →* ℂˣ := ωA.comp (parabolicCenterProjection hd hZP)
  have hπ : Continuous (fun z : Subgroup.center (rationalPoints G) =>
      Subgroup.centerCongr e.symm.toMulEquiv (parabolicCenterProjection hd hZP z)) :=
    continuous_induced_rng.2 (e.symm.continuous.comp (continuous_subtype_val.comp
      (continuous_parabolicCenterProjection hd hZP
        (continuous_pointImage_projection p l r hp.isClosedSubgroup hr hmul))))
  have hωG : IsOpen (ωG.ker : Set (Subgroup.center (rationalPoints G))) :=
    hω.preimage hπ
  have hactA : ∀ (z : Subgroup.center (pointImage (l ≫ p))) (w : ρ),
      (SmoothRep.pullback e.symm ρ).representation z w = (ωA z : ℂ) • w :=
    fun z w => hact (Subgroup.centerCongr e.symm.toMulEquiv z) w
  have hactI : ∀ (z : Subgroup.center (rationalPoints G))
      (f : (leviInductionFunctor p l r hp hr hl hmul).obj ρ),
      ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation z f =
        (ωG z : ℂ) • f :=
    normalizedInduction_acts_of_center_le_parabolic hd hU hZP
      (SmoothRep.pullback e.symm ρ) ωA hactA
  obtain ⟨ψ, -, hnorm⟩ := exists_positive_unramifiedCharacter_norm_mul_eq_one hG ωG hωG
  let c := twistUnitaryCentralCharacter
    ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation
    (ψ : rationalPoints G →ₜ* ℂˣ).toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
    ωG hωG hactI hnorm
  exact ⟨ψ, ⟨UnitaryCentralCharacter.ofEquiv
    (ρ := (((leviInductionFunctor p l r hp hr hl hmul).obj ρ).twist
      (ψ : rationalPoints G →ₜ* ℂˣ).toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).representation) c
    (SmoothRep.equivOfIso (leviInductionUnramifiedTwistIso p l r hp hr hl hmul ψ ρ).symm)⟩⟩

end RepresentedParabolic

end Langlands.Aubert.General
