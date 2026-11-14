import Langlands.Representation.Plancherel.RationalUnitaryRegularValue
import Langlands.Representation.Plancherel.RationalOrbitBasisInvariance
import Langlands.Representation.Plancherel.RationalUnramifiedRestriction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacketDecay
import Langlands.Representation.Jacquet.StandardDynamicConstantTerm

/-! # The Plancherel weight on the orbit of a discrete series of a standard Levi

Waldspurger 2003, V.2 and Lemma V.2.1 (printed p.292): the Plancherel density `μ` is a function
on the orbit `O = {π ⊗ χ ; χ ∈ Im X(M)}` of a discrete series `π` of `M`. VI.3 (printed p.302)
integrates it in the wave packets `f_ψ(g) = ∫_O μ(ω) (E_P^G ψ_ω)(g) dω`.

In the Library the two halves live on different groups. The weight `plancherelWeight` (module
`RationalUnitaryRegularValue`) is a function on the unitary unramified characters of the
centralizer scheme `Z_G(ζ ∘ i)` (`parameterScheme`) of a cocharacter, defined from a smooth
representation of `Z_G(ζ ∘ i)(F)`. The wave packets `rationalInducedOrbitWavePacket` and their
decay bound `exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow` use the literal
standard Levi subgroup `M_I(F)`, the orbit `O` of the class of a discrete series `π` of
`M_I(F)`, and a weight on `O` smooth in the circle coordinates `leviRationalUnitaryCoordinates`.
This module connects them, for a standard cocharacter `ζ` of `I`:

* `standardLeviParameterIso`: the scheme isomorphism `Z_G(ζ ∘ i) ≅ M_I` over `G`, and
  `standardLeviDynamicHomeomorph : Z_G(ζ ∘ i)(F) ≃ₜ* M_I(F)`, the identity on points of `G(F)`;
* `standardLeviCharacterRestrict`: the restriction `z ↦ z ∘ e` from `Im X(M_I)` to
  `Im X(Z_G(ζ ∘ i))`, and the transfer of smoothness from the Library's canonical circle
  coordinates of `Im X(Z_G(ζ ∘ i))` to the coordinates `leviRationalUnitaryCoordinates`;
* `standardOrbitWeight`: a function `W` on `Im X(Z_G(ζ ∘ i))` invariant under unitary self-twists
  of `π ∘ e` gives the function `π ⊗ z ↦ W(z ∘ e)` on `O`; smoothness and continuity;
* `standardLeviPlancherelWeight`: the Plancherel weight `π ⊗ z ↦ μ(π ⊗ z)` on `O`, for `μ` the
  Plancherel density of `π ∘ e`, under the hypothesis that `j_P⁻¹` is regular at every unitary
  character. It is smooth in the coordinates of `Im X(M_I)`, continuous, and a nonnegative real
  number wherever `j_P⁻¹` has a nonnegative real value (on all of `O` if `j_P⁻¹` is nonnegative
  at every unitary character);
* `exists_norm_standardLeviPlancherelWavePacket_le_rationalXi_rpow`: the Library's decay bound
  for wave packets, applied to the Plancherel weight.

Generic sections prove that a pullback of characters is a torus monomial in circle coordinates
(`isSmoothFiniteTorusFunction_comp_pullback`), that each canonical circle coordinate is the
evaluation at a point (`exists_rationalCanonicalUnitaryCoordinate_eq_eval`), and that functions
on `Im X(M)` invariant under the stabilizer of `π` descend to the orbit
(`discreteSeriesOrbitDescend`).
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### Coordinate changes given by pullbacks are torus monomials -/

section MonomialTransfer

variable {H₁ : Type*} [Group H₁] [TopologicalSpace H₁] {H₂ : Type*} [Group H₂]
  [TopologicalSpace H₂] {I₁ I₂ : Type*} {ν₁ : I₁ → (H₁ →* ℝ≥0ˣ)} {ν₂ : I₂ → (H₂ →* ℝ≥0ˣ)}
  {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]

/-- **Smoothness along a pullback of characters.** Let `e₁` be circle coordinates on
`Im X(H₁)` each of which is the evaluation at a point of `H₁`, and `e₂` circle coordinates on
`Im X(H₂)` in which evaluation at every point is a Laurent monomial. If `T : Im X(H₂) → Im X(H₁)`
is the pullback `T z = z ∘ φ` along a map `φ : H₁ → H₂`, then `e₁ ∘ T ∘ e₂⁻¹` is an integer torus
monomial, so a function smooth in the coordinates `e₁` pulls back to a function smooth in the
coordinates `e₂`. -/
theorem isSmoothFiniteTorusFunction_comp_pullback
    (e₁ : unitaryUnramifiedCharacters ν₁ ≃* (J₁ → Circle))
    (he₁ : ∀ j, ∃ g : H₁, ∀ z, ((e₁ z j : Circle) : ℂ) = ((z.val g : ℂˣ) : ℂ))
    (e₂ : unitaryUnramifiedCharacters ν₂ ≃* (J₂ → Circle))
    (he₂ : HasLaurentUnitaryCoordinates ν₂ e₂)
    (T : unitaryUnramifiedCharacters ν₂ → unitaryUnramifiedCharacters ν₁) (φ : H₁ → H₂)
    (hT : ∀ z g, (T z).val g = z.val (φ g))
    {f : unitaryUnramifiedCharacters ν₁ → ℂ}
    (hf : IsSmoothFiniteTorusFunction fun c => f (e₁.symm c)) :
    IsSmoothFiniteTorusFunction fun y => f (T (e₂.symm y)) := by
  choose g hg using he₁
  choose n hn using fun j => he₂ (φ (g j))
  have key : ∀ y, e₁ (T (e₂.symm y)) = finiteTorusMonomial (fun j => n j) y := by
    intro y
    funext j
    apply Circle.ext
    rw [hg j, hT, hn j y]
    change ∏ k, ((y k ^ n j k : Circle) : ℂ) = ((∏ k, y k ^ n j k : Circle) : ℂ)
    exact (map_prod Circle.coeHom (fun k => y k ^ n j k) Finset.univ).symm
  have h := hf.comp_monomial (fun j => n j)
  have hfun : (fun y => f (T (e₂.symm y))) =
      (fun c => f (e₁.symm c)) ∘ finiteTorusMonomial (fun j => n j) := by
    funext y
    simp only [Function.comp_apply, ← key, MulEquiv.symm_apply_apply]
  rw [hfun]
  exact h

end MonomialTransfer

/-! ### Canonical circle coordinates are evaluations at points -/

section CanonicalEvaluation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (hG : GroupScheme.IsConnectedReductive G)

local instance standardLeviPlancherelWeightPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

omit [LocallyOfFiniteType G.X.hom] in
/-- Each of the Library's canonical circle coordinates on `Im X(G)` is the evaluation at an
actual rational point: the `j`-th coordinate is the value at any point whose valuation image
is the `j`-th vector of the chosen basis of the valuation lattice. -/
theorem exists_rationalCanonicalUnitaryCoordinate_eq_eval (j : Fin (rationalImageRank G)) :
    ∃ g : GroupScheme.rationalPoints G,
      ∀ z : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul),
        ((rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG z j : Circle) : ℂ) =
          ((z.val g : ℂˣ) : ℂ) := by
  obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G
    (Additive.toMul (rationalReductiveValuationBasis G hG j))
  refine ⟨g, fun z => ?_⟩
  have h := rationalCanonicalUnitaryUnramifiedCharacterCoordinates_symm_apply G hG
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG z) g
  rw [ContinuousMulEquiv.symm_apply_apply] at h
  rw [h, hg, ofMul_toMul, Module.Basis.repr_self]
  congr 1
  rw [Fintype.prod_eq_single j]
  · rw [Finsupp.single_eq_same, zpow_one]
  · intro k hk
    simp [Ne.symm hk]

end CanonicalEvaluation

/-! ### Functions on an orbit from stabilizer-invariant functions on `Im X(M)` -/

section OrbitDescent

variable {M : Type u} [Group M] [TopologicalSpace M] [NonarchimedeanGroup M]
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (mu : MeasureTheory.Measure (M ⧸ C)) [mu.IsHaarMeasure]
  {Ix : Type*} (νM : Ix → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

/-- A function `f` on `Im X(M)` invariant under right translation by the stabilizer `S` of the
class `ω` of `π` descends to the orbit `O = Im X(M) / S` of `ω`. -/
def discreteSeriesOrbitDescend (f : unitaryUnramifiedCharacters νM → ℂ)
    (hf : ∀ s ∈ discreteSeriesStabilizer C hC mu νM (discreteSeriesClass C hC mu π hsq),
      ∀ z, f (z * s) = f z) :
    discreteSeriesOrbit C hC mu νM (discreteSeriesClass C hC mu π hsq) → ℂ :=
  fun x => Quotient.liftOn'
    ((discreteSeriesOrbitHomeomorph C hC mu νM (discreteSeriesClass C hC mu π hsq)).symm x) f
    (fun a b hab => by
      have h := hf (a⁻¹ * b) (QuotientGroup.leftRel_apply.mp hab) a
      rw [mul_inv_cancel_left] at h
      exact h.symm)

/-- The descended function at `π ⊗ z` is `f z`. -/
theorem discreteSeriesOrbitDescend_orbitMap (f : unitaryUnramifiedCharacters νM → ℂ)
    (hf : ∀ s ∈ discreteSeriesStabilizer C hC mu νM (discreteSeriesClass C hC mu π hsq),
      ∀ z, f (z * s) = f z) (z : unitaryUnramifiedCharacters νM) :
    discreteSeriesOrbitDescend C hC mu νM π hsq f hf
        (discreteSeriesOrbitMap C hC mu νM (discreteSeriesClass C hC mu π hsq) z) = f z := by
  unfold discreteSeriesOrbitDescend discreteSeriesOrbitMap
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The descended function of a continuous function is continuous. -/
theorem continuous_discreteSeriesOrbitDescend {f : unitaryUnramifiedCharacters νM → ℂ}
    (hf : ∀ s ∈ discreteSeriesStabilizer C hC mu νM (discreteSeriesClass C hC mu π hsq),
      ∀ z, f (z * s) = f z) (hfc : Continuous f) :
    Continuous (discreteSeriesOrbitDescend C hC mu νM π hsq f hf) := by
  refine (isOpenQuotientMap_discreteSeriesOrbitMap C hC mu νM
    (discreteSeriesClass C hC mu π hsq)).isQuotientMap.continuous_iff.mpr ?_
  have h : discreteSeriesOrbitDescend C hC mu νM π hsq f hf ∘
      discreteSeriesOrbitMap C hC mu νM (discreteSeriesClass C hC mu π hsq) = f := by
    funext z
    exact discreteSeriesOrbitDescend_orbitMap C hC mu νM π hsq f hf z
  rw [h]
  exact hfc

/-- An element of the stabilizer of the class of `π` gives an actual equivalence
`π ⊗ s ≃ π`. -/
theorem nonempty_twistEquiv_of_mem_discreteSeriesStabilizer
    {s : unitaryUnramifiedCharacters νM}
    (hs : s ∈ discreteSeriesStabilizer C hC mu νM (discreteSeriesClass C hC mu π hsq)) :
    Nonempty ((π.obj.twist s.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM ⟨s.val, s.property.1⟩)).representation.Equiv
        π.obj.representation) := by
  have h : (Quotient.mk _ (IrreducibleAdmissibleRep.twist s.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM ⟨s.val, s.property.1⟩) π) :
        SmoothDualClass.{0, u, uV} (k := ℂ) (G := M)) = Quotient.mk _ π :=
    congrArg Subtype.val hs
  obtain ⟨e⟩ := Quotient.exact h
  exact ⟨SmoothRep.equivOfIso ((irreducibleAdmissibleProperty (k := ℂ) (G := M)).ι.mapIso e)⟩

end OrbitDescent

/-! ### Twists of double pullbacks -/

section PullbackTwist

variable {M : Type u} [Group M] [TopologicalSpace M] {H₁ : Type u} [Group H₁]
  [TopologicalSpace H₁] {H₂ : Type u} [Group H₂] [TopologicalSpace H₂]

/-- If `B ⊗ ψ ≃ B` and `τ = ψ ∘ e₁ ∘ e₂`, then `(B ∘ e₁ ∘ e₂) ⊗ τ ≅ B ∘ e₁ ∘ e₂`. -/
theorem nonempty_twist_pullback_pullback_iso (e₂ : H₂ ≃ₜ* H₁) (e₁ : H₁ ≃ₜ* M)
    (B : SmoothRep.{0, u, uV} ℂ M) {ψ : M →* ℂˣ} (hψ : IsOpen (ψ.ker : Set M))
    {τ : H₂ →* ℂˣ} (hτ : IsOpen (τ.ker : Set H₂)) (hτψ : ∀ h, τ h = ψ (e₁ (e₂ h)))
    (a : (B.twist ψ hψ).representation.Equiv B.representation) :
    Nonempty ((SmoothRep.pullback e₂ (SmoothRep.pullback e₁ B)).twist τ hτ ≅
      SmoothRep.pullback e₂ (SmoothRep.pullback e₁ B)) :=
  ⟨SmoothRep.mkIso (Representation.Equiv.mk a.toLinearEquiv (fun h => by
    have ha := a.isIntertwining' (e₁ (e₂ h))
    change a.toLinearMap.comp ((ψ (e₁ (e₂ h)) : ℂ) • B.representation (e₁ (e₂ h))) =
      (B.representation (e₁ (e₂ h))).comp a.toLinearMap at ha
    change a.toLinearMap.comp ((τ h : ℂ) • B.representation (e₁ (e₂ h))) =
      (B.representation (e₁ (e₂ h))).comp a.toLinearMap
    rw [hτψ]
    exact ha))⟩

end PullbackTwist

/-! ### The standard Levi `M_I` as the centralizer of a standard cocharacter -/

section Standard

open MeasureTheory
open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalDynamicSource
open RationalPlancherelDensity
open HarishChandraSchwartz
  (leviRationalUnitaryCoordinates leviRationalUnitaryCoordinates_hasLaurent)

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

local instance standardLeviPlancherelWeightLeviClosed
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPlancherelWeightLeviAffine
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left
local instance standardLeviPlancherelWeightLeviTopology
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    TopologicalSpace
      (rationalPoints (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I) ζ)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "MI" => Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "UL" => unitaryUnramifiedCharacters
  (fun ψ => (rationalNormCharacters (parameterScheme (CommGroupScheme.groupHom ζ ≫ i)) ψ).toMul)
set_option hygiene false in
local notation "UMI" =>
  unitaryUnramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I)
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ i) hG
-- `M_I(F)` as a subtype of `G(F)`, written as in the wave-packet consumers.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

/-- The actual centralizer scheme of `ζ ∘ i` and the standard Levi scheme `M_I` represent the
same subgroup functor of `G` (`standardLevi_eq_dynamic`), so they are isomorphic over `G`. -/
def standardLeviParameterIso : MS ≅ MI :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (by
      rw [← (Jacquet.standardLevi_eq_dynamic hG hi hν hζ).1]
      exact Standard.isRepresentedBy_leviHom i ν _)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The isomorphism `Z_G(ζ ∘ i) ≅ M_I` lies over `G`. -/
theorem standardLeviParameterIso_hom_comp :
    (standardLeviParameterIso hG hi hν I hζ).hom ≫
        Standard.leviHom i ν (RationalPointFamily.rootSet i ν I) =
      Dynamic.Affine.centralizerHom χ :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- `Z_G(ζ ∘ i)(F) = M_I(F)` as topological subgroups of `G(F)`. -/
def standardLeviDynamicHomeomorph : levi χ ≃ₜ* RationalPointFamily.levi i ν I where
  toMulEquiv := MulEquiv.subgroupCongr
    (congrArg (fun P : SubgroupFunctor G => P.carrier (Over.mk (𝟙 _)))
      (Jacquet.standardLevi_eq_dynamic hG hi hν hζ).1).symm
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The identification `Z_G(ζ ∘ i)(F) = M_I(F)` is the identity on points of `G(F)`. -/
@[simp] theorem standardLeviDynamicHomeomorph_apply_coe (m : levi χ) :
    ((standardLeviDynamicHomeomorph hG hi hν I hζ m : RationalPointFamily.levi i ν I) :
      RationalPoint F G.X) = (m : RationalPoint F G.X) := rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The point maps of `Z_G(ζ ∘ i) ≅ M_I` and of the two inclusions into `G` agree. -/
theorem leviRationalPointHomeomorph_map_standardLeviParameterIso
    (m : rationalPoints MS) :
    RationalPointFamily.leviRationalPointHomeomorph i ν I
        (rationalPoints.map (standardLeviParameterIso hG hi hν I hζ).hom m) =
      standardLeviDynamicHomeomorph hG hi hν I hζ (parameterHomeomorph χ m) := by
  apply Subtype.ext
  change (m ≫ (standardLeviParameterIso hG hi hν I hζ).hom.hom.hom) ≫
      (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom =
    m ≫ (Dynamic.Affine.centralizerHom χ).hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, standardLeviParameterIso_hom_comp]

/-- **Restriction `Im X(M_I) → Im X(Z_G(ζ ∘ i))`**: a unitary unramified character `z` of the
literal Levi subgroup `M_I(F)` gives the character `z ∘ e` of the centralizer scheme's points,
where `e : Z_G(ζ ∘ i)(F) ≅ M_I(F)` is the canonical identification. -/
def standardLeviCharacterRestrict : UMI →ₜ* UL :=
  (rationalUnitaryUnramifiedCharacterRestrict (standardLeviParameterIso hG hi hν I hζ).hom).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (HarishChandraSchwartz.unitaryUnramifiedCharactersHomeomorph
        (RationalPointFamily.leviRationalPointHomeomorph i ν I)
        (fun ψ => (rationalNormCharacters MI ψ).toMul)).symm)

omit [LocallyOfFiniteType G.X.hom] in
/-- The restricted character is `z ∘ e`. -/
theorem standardLeviCharacterRestrict_apply (z : UMI) (m : rationalPoints MS) :
    (standardLeviCharacterRestrict hG hi hν I hζ z).val m =
      z.val (standardLeviDynamicHomeomorph hG hi hν I hζ (parameterHomeomorph χ m)) := by
  change z.val (RationalPointFamily.leviRationalPointHomeomorph i ν I
    (rationalPoints.map (standardLeviParameterIso hG hi hν I hζ).hom m)) = _
  rw [leviRationalPointHomeomorph_map_standardLeviParameterIso]

omit [LocallyOfFiniteType G.X.hom] in
/-- **Smoothness transfers along the restriction.** A function on `Im X(Z_G(ζ ∘ i))` smooth in
the Library's canonical circle coordinates becomes, after restriction from `Im X(M_I)`, smooth in
the circle coordinates `leviRationalUnitaryCoordinates` of `Im X(M_I)`. -/
theorem isSmoothFiniteTorusFunction_comp_standardLeviCharacterRestrict {f : UL → ℂ}
    (hf : IsSmoothFiniteTorusFunction fun c =>
      f ((rationalCanonicalUnitaryUnramifiedCharacterCoordinates MS hMS).symm c)) :
    IsSmoothFiniteTorusFunction fun y =>
      f (standardLeviCharacterRestrict hG hi hν I hζ
        ((leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv.symm y)) :=
  isSmoothFiniteTorusFunction_comp_pullback
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates MS hMS).toMulEquiv
    (exists_rationalCanonicalUnitaryCoordinate_eq_eval MS hMS)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (standardLeviCharacterRestrict hG hi hν I hζ)
    (fun m => standardLeviDynamicHomeomorph hG hi hν I hζ (parameterHomeomorph χ m))
    (standardLeviCharacterRestrict_apply hG hi hν I hζ) hf

/-! ### Weights on the orbit of a discrete series of `M_I` -/

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

-- The inducing representation `π ∘ e` of `Z_G(ζ ∘ i)(F)`.
set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj
-- The orbit `O = {π ⊗ z ; z ∈ Im X(M_I)}` of the class of `π`.
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu
  (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "orbitMapπ" => discreteSeriesOrbitMap C hC mu
  (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)

/-- A unitary unramified character `s` of `M_I(F)` with `π ⊗ s ≅ π` restricts to a self-twist
of the inducing representation `π ∘ e` of `Z_G(ζ ∘ i)(F)`. -/
theorem standardLeviCharacterRestrict_mem_stabilizer {s : UMI}
    (hs : s ∈ discreteSeriesStabilizer C hC mu
      (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)) :
    (⟨(standardLeviCharacterRestrict hG hi hν I hζ s).val,
      (standardLeviCharacterRestrict hG hi hν I hζ s).property.1⟩ : unramifiedCharacters νL) ∈
      smoothRepUnramifiedTwistStabilizer νL (SmoothRep.pullback (parameterHomeomorph χ) Aπ) := by
  obtain ⟨a⟩ := nonempty_twistEquiv_of_mem_discreteSeriesStabilizer C hC mu
    (RationalPointFamily.leviRationalNormCharacters i ν I) π hsq hs
  exact (SmoothRep.isoClass_eq_iff _ _).mpr
    (nonempty_twist_pullback_pullback_iso (parameterHomeomorph χ)
      (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj
      (ψ := s.val.toMonoidHom)
      (τ := (standardLeviCharacterRestrict hG hi hν I hζ s).val.toMonoidHom) _ _
      (standardLeviCharacterRestrict_apply hG hi hν I hζ s) a)

/-- **A weight on the orbit of `π`.** A function `W` on `Im X(Z_G(ζ ∘ i))` invariant under
translation by the unitary self-twists of the inducing representation `π ∘ e` gives the function
`π ⊗ z ↦ W(z ∘ e)` on the orbit `O` of `π`. -/
def standardOrbitWeight (W : UL → ℂ)
    (hW : ∀ (τ : smoothRepUnramifiedTwistStabilizer νL
        (SmoothRep.pullback (parameterHomeomorph χ) Aπ))
      (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints MS)) (z : UL),
      W (⟨τ.val.val, τ.val.property, hτ⟩ * z) = W z) : Oπ → ℂ :=
  discreteSeriesOrbitDescend C hC mu (RationalPointFamily.leviRationalNormCharacters i ν I) π hsq
    (fun z => W (standardLeviCharacterRestrict hG hi hν I hζ z))
    (fun s hs z => by
      have h := hW ⟨_, standardLeviCharacterRestrict_mem_stabilizer hG hi hν I hζ π C hC mu hsq hs⟩
        (standardLeviCharacterRestrict hG hi hν I hζ s).property.2
        (standardLeviCharacterRestrict hG hi hν I hζ z)
      change W (standardLeviCharacterRestrict hG hi hν I hζ (z * s)) =
        W (standardLeviCharacterRestrict hG hi hν I hζ z)
      rw [map_mul, mul_comm]
      exact h)

/-- The weight at `π ⊗ z` is `W(z ∘ e)`. -/
theorem standardOrbitWeight_orbitMap (W : UL → ℂ)
    (hW : ∀ (τ : smoothRepUnramifiedTwistStabilizer νL
        (SmoothRep.pullback (parameterHomeomorph χ) Aπ))
      (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints MS)) (z : UL),
      W (⟨τ.val.val, τ.val.property, hτ⟩ * z) = W z) (z : UMI) :
    standardOrbitWeight hG hi hν I hζ π C hC mu hsq W hW (orbitMapπ z) =
      W (standardLeviCharacterRestrict hG hi hν I hζ z) :=
  discreteSeriesOrbitDescend_orbitMap C hC mu _ π hsq _ _ z

/-- **Smoothness in the circle coordinates of `Im X(M_I)`**, in the form required by the
wave-packet bound `exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow`: if `W` is
smooth in the Library's canonical circle coordinates of `Im X(Z_G(ζ ∘ i))`, the orbit weight
composed with the orbit map is smooth in the coordinates `leviRationalUnitaryCoordinates`. -/
theorem isSmoothFiniteTorusFunction_standardOrbitWeight (W : UL → ℂ)
    (hW : ∀ (τ : smoothRepUnramifiedTwistStabilizer νL
        (SmoothRep.pullback (parameterHomeomorph χ) Aπ))
      (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints MS)) (z : UL),
      W (⟨τ.val.val, τ.val.property, hτ⟩ * z) = W z)
    (hWs : IsSmoothFiniteTorusFunction fun c =>
      W ((rationalCanonicalUnitaryUnramifiedCharacterCoordinates MS hMS).symm c)) :
    IsSmoothFiniteTorusFunction fun y =>
      standardOrbitWeight hG hi hν I hζ π C hC mu hsq W hW
        (orbitMapπ ((leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv.symm
          y)) := by
  have h : (fun y => standardOrbitWeight hG hi hν I hζ π C hC mu hsq W hW
      (orbitMapπ ((leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv.symm
        y))) = fun y => W (standardLeviCharacterRestrict hG hi hν I hζ
          ((leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv.symm y)) := by
    funext y
    exact standardOrbitWeight_orbitMap hG hi hν I hζ π C hC mu hsq W hW _
  rw [h]
  exact isSmoothFiniteTorusFunction_comp_standardLeviCharacterRestrict hG hi hν I hζ hWs

/-- The orbit weight of a continuous `W` is continuous on `O`. -/
theorem continuous_standardOrbitWeight {W : UL → ℂ}
    (hW : ∀ (τ : smoothRepUnramifiedTwistStabilizer νL
        (SmoothRep.pullback (parameterHomeomorph χ) Aπ))
      (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints MS)) (z : UL),
      W (⟨τ.val.val, τ.val.property, hτ⟩ * z) = W z) (hWc : Continuous W) :
    Continuous (standardOrbitWeight hG hi hν I hζ π C hC mu hsq W hW) :=
  continuous_discreteSeriesOrbitDescend C hC mu _ π hsq _
    (hWc.comp (standardLeviCharacterRestrict hG hi hν I hζ).continuous)

/-! ### The Plancherel weight on the orbit of `π` -/

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK Aπ)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK Aπ)
  {DForward DReverse : Set (unramifiedCharacters νL)}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK Aπ)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK Aπ)
  {D : Set (unramifiedCharacters νL)}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) Aπ).IsIrreducible)

-- The canonical scalar `j_P` of the inducing representation `π ∘ e`.
set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK Aπ
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr

include hDForward hDReverse hD in
/-- **The Plancherel weight on the orbit of `π`** (Waldspurger V.2, V.2.1, printed p.292):
`π ⊗ z ↦ μ(π ⊗ z)`, where `μ` is the Plancherel density of the inducing representation
`π ∘ e` of `Z_G(ζ ∘ i)(F)` and `z ∈ Im X(M_I)` acts through the restriction `z ↦ z ∘ e`.
It is well defined because the Plancherel weight is invariant under unitary self-twists of
`π ∘ e` (`plancherelWeight_stabilizer_invariant`); it is defined under the hypothesis that `j_P⁻¹`
is regular at every unitary unramified character. -/
def standardLeviPlancherelWeight (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    Oπ → ℂ :=
  standardOrbitWeight hG hi hν I hζ π C hC mu hsq
    (plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK Aπ p q hneForward hDForwardΩ hneReverse
      hDReverseΩ hne hirr hreg)
    (plancherelWeight_stabilizer_invariant i ζ hRefl hCST hG K hK hPK hOppK Aπ p q hDForward
      hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg)

/-- The Plancherel weight at `π ⊗ z` is the Plancherel weight of `π ∘ e` at `z ∘ e`. -/
theorem standardLeviPlancherelWeight_orbitMap
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (z : UMI) :
    standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK hOppK p q
        hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
        (orbitMapπ z) =
      plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK Aπ p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hirr hreg (standardLeviCharacterRestrict hG hi hν I hζ z) :=
  standardOrbitWeight_orbitMap hG hi hν I hζ π C hC mu hsq _ _ z

/-- **Smoothness**, in the form required by the wave-packet bound
`exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow`: the Plancherel weight composed
with the orbit map is smooth in the circle coordinates `leviRationalUnitaryCoordinates` of
`Im X(M_I)`. -/
theorem isSmoothFiniteTorusFunction_standardLeviPlancherelWeight
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    IsSmoothFiniteTorusFunction fun y =>
      standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK hOppK p q
        hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
        (orbitMapπ ((leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv.symm
          y)) :=
  isSmoothFiniteTorusFunction_standardOrbitWeight hG hi hν I hζ π C hC mu hsq _ _
    (isSmoothFiniteTorusFunction_plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK Aπ p q
      hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr hreg)

/-- The Plancherel weight is continuous on the orbit `O`. -/
theorem continuous_standardLeviPlancherelWeight
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    Continuous (standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
      hreg) :=
  continuous_standardOrbitWeight hG hi hν I hζ π C hC mu hsq _
    (continuous_plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK Aπ p q hneForward hDForwardΩ
      hneReverse hDReverseΩ hne hirr hreg)

/-- **Nonnegativity.** If `j_P⁻¹` has a nonnegative real value at the unitary character
`z ∘ e`, then the Plancherel weight at `π ⊗ z` is a nonnegative real number. -/
theorem standardLeviPlancherelWeight_nonneg
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) {z : UMI}
    (hz : RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS (standardLeviCharacterRestrict hG hi hν I hζ z))) :
    ∃ r : ℝ, 0 ≤ r ∧
      standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK hOppK p q
        hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
        (orbitMapπ z) = (r : ℂ) := by
  rw [standardLeviPlancherelWeight_orbitMap]
  exact plancherelWeight_nonneg i ζ hRefl hCST hG K hK hPK hOppK Aπ p q hneForward hDForwardΩ
    hneReverse hDReverseΩ hne hirr hreg hz

/-- **Nonnegativity on the whole orbit.** If `j_P⁻¹` has a nonnegative real value at every unitary
unramified character of `Z_G(ζ ∘ i)`, then the Plancherel weight is a nonnegative real number at
every point of `O` (Lemma V.2.1, first item). -/
theorem standardLeviPlancherelWeight_nonneg_of_forall
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) (x : Oπ) :
    ∃ r : ℝ, 0 ≤ r ∧
      standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK hOppK p q
        hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg x =
        (r : ℂ) :=
  ((isOpenQuotientMap_discreteSeriesOrbitMap C hC mu _ _).surjective x).elim fun _ hz =>
    hz ▸ standardLeviPlancherelWeight_nonneg hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
      (hnn _)

/-! ### Decay of the Plancherel wave packets -/

attribute [local instance] HarishChandraSchwartz.rationalWeightsLocallyCompact
  HarishChandraSchwartz.rationalWeightsMeasurableSpace
  HarishChandraSchwartz.rationalWeightsBorelSpace

/-- **Decay of the Plancherel wave packets** (the Library's first bound toward Proposition VI.3.1,
printed p. 302–303, for the weight `μ`): for the wave packet
`f_ψ(g) = ∫_O μ(ω) (E_P^G ψ_ω)(g) dω` of a section `ψ ∈ C^∞(O, P)`, with the measure on `O`
attached to `ρ` and the Plancherel weight `μ` of the orbit `O` of `π`, and for every real `r`,
there is `c > 0` with `|f_ψ(g)| ≤ c Ξ(g) (1 + ‖n_G(g)‖)^{-r}` for all `g ∈ G(F)`. The compact
open subgroup `Kw` of the wave packet is independent of the subgroup `K` used to define `j_P`. -/
theorem exists_norm_standardLeviPlancherelWavePacket_le_rationalXi_rpow
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    {Kw : OpenSubgroup (rationalPoints G)} (hKw : IsCompact (Kw : Set (rationalPoints G)))
    (hPKw : HarishChandraSchwartz.IsIwasawaPair (standardParabolicPoints i ν ∅)
      (Kw : Subgroup (rationalPoints G)))
    (hM : HarishChandraSchwartz.IsIwasawaPair
      ((standardParabolicPoints i ν ∅).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
      ((Kw : Subgroup (rationalPoints G)).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
    [Finite (discreteSeriesStabilizer C hC mu
      (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq))]
    (ρ : Measure UMI) [IsFiniteMeasure ρ] [ρ.IsMulLeftInvariant]
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤
        c * HarishChandraSchwartz.rationalLeviXi hKw hM m)
    (s : HarishChandraSchwartz.rationalInducedSmoothOrbitSections hG hi hν I hKw hPKw π)
    (r : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : rationalPoints G,
      ‖HarishChandraSchwartz.rationalInducedOrbitWavePacket hG hi hν I hKw hPKw π C hC mu hsq ρ
          (standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK hOppK p q
            hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg)
          s g‖ ≤
        c * HarishChandraSchwartz.rationalXi hKw hPKw g *
          (1 + ‖HarishChandraSchwartz.rationalValuationCoordinates G hG g‖) ^ (-r) :=
  HarishChandraSchwartz.exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow hG hi hν I
    hKw hPKw π C hC mu hsq hM ρ _
    (isSmoothFiniteTorusFunction_standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl
      hCST K hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD
      hne hirr hreg)
    hcoeff s r

end Standard

end Langlands.Plancherel
