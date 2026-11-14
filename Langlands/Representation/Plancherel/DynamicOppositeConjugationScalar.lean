import Langlands.Representation.Plancherel.DynamicOppositeCanonicalScalar
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryScalarStatement
import Langlands.Representation.Plancherel.RationalUnramifiedRestriction
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.RepresentedSubgroupTransport
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Plancherel.RationalSourceHaarConjugation

/-! # Conjugation invariance of the scalar `j` (target)

Waldspurger 2003, IV.3 (3) (printed p.286): for `w ∈ W^G`, `j(wπ) = j(π)`, where `wπ` is a
representation of `w·M`. The proof is that left translation by `w` carries `I_P^G V` onto
`I_{w·P}^G wV` and intertwines `J_{P'|P}(π)` with `J_{w·P'|w·P}(wπ)`. Lemma V.2.1 (printed
p.292) uses it for `μ(sω) = μ(ω)`.

This module transports the rational functions on unramified characters along an
isomorphism `e : H ≅ G` of affine group schemes (`rationalUnramifiedRegularFunctionsEquiv`,
`rationalUnramifiedFunctionFieldEquiv`), with the transfer of regularity and of
nonnegative values. For a rational point `g` and a cocharacter `χ` it identifies the data
of the conjugate cocharacter `gχg⁻¹ = χ ≫ Int(g)`: the parabolics, the Levi conjugation
`leviConjugation`, the conjugate representation `conjugateRepresentation`, the isomorphism
`parameterConjugationIso` of the actual centralizer schemes, and the Iwasawa decompositions
for `gKg⁻¹`. It states IV.3 (3) for the canonical scalar `conditionalCanonicalRationalScalar`
in transport form (`ConditionalDynamicOppositeConjugationScalarStatement`), and proves the
form with any compact open subgroup equal to `gKg⁻¹`, for example `K` itself when `g ∈ K`
(`conditionalDynamicOppositeConjugationScalar_of_eq`). The target is not proved here.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped NNReal CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### Transport of regular and rational functions along group-scheme maps -/

section Transport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H K : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine H.X.left] [IsAffine K.X.left]

local instance conjugationScalarTopG : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance conjugationScalarTopH : TopologicalSpace (GroupScheme.rationalPoints H) :=
  rationalPointTopology F H.X
local instance conjugationScalarTopK : TopologicalSpace (GroupScheme.rationalPoints K) :=
  rationalPointTopology F K.X

set_option hygiene false in
local notation "RG" => unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)
set_option hygiene false in
local notation "RH" => unramifiedRegularFunctions (fun ψ => (rationalNormCharacters H ψ).toMul)
set_option hygiene false in
local notation "RK" => unramifiedRegularFunctions (fun ψ => (rationalNormCharacters K ψ).toMul)
set_option hygiene false in
local notation "XG" => unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)
set_option hygiene false in
local notation "XH" => unramifiedCharacters (fun ψ => (rationalNormCharacters H ψ).toMul)

/-- Precomposition with restriction of characters along `f`, on all complex functions. -/
private def restrictFunctionMap (f : H ⟶ G) : (XH → ℂ) →ₐ[ℂ] (XG → ℂ) where
  toFun b z := b (rationalUnramifiedCharacterRestrict f z)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [IsAffine K.X.left] in
private theorem restrictFunctionMap_evaluation (f : H ⟶ G) (h : GroupScheme.rationalPoints H) :
    restrictFunctionMap f (unramifiedEvaluation _ h) =
      unramifiedEvaluation _ (GroupScheme.rationalPoints.map f h) := rfl

omit [IsAffine K.X.left] in
private theorem restrictFunctionMap_mem (f : H ⟶ G) (b : RH) :
    restrictFunctionMap f b.val ∈ RG := by
  change b.val ∈ (RG).comap (restrictFunctionMap f)
  refine Algebra.adjoin_le (S := (RG).comap (restrictFunctionMap f)) ?_ b.property
  rintro _ ⟨h, rfl⟩
  change restrictFunctionMap f (unramifiedEvaluation _ h) ∈ RG
  rw [restrictFunctionMap_evaluation]
  exact (unramifiedEvaluationRegular _ (GroupScheme.rationalPoints.map f h)).property

/-- **Pullback of regular functions along a group-scheme map.** For `f : H ⟶ G`, the regular
function `b` on the unramified characters of `H(F)` gives `z ↦ b(z ∘ f)` on those of `G(F)`.
The evaluation at `h ∈ H(F)` goes to the evaluation at `f(h)`. -/
def rationalUnramifiedRegularFunctionsMap (f : H ⟶ G) : RH →ₐ[ℂ] RG :=
  ((restrictFunctionMap f).comp (RH).val).codRestrict RG
    (fun b => restrictFunctionMap_mem f b)

omit [IsAffine K.X.left] in
@[simp]
theorem rationalUnramifiedRegularFunctionsMap_apply (f : H ⟶ G) (b : RH) (z : XG) :
    (rationalUnramifiedRegularFunctionsMap f b).val z =
      b.val (rationalUnramifiedCharacterRestrict f z) := rfl

omit [IsAffine K.X.left] in
@[simp]
theorem rationalUnramifiedRegularFunctionsMap_evaluation (f : H ⟶ G)
    (h : GroupScheme.rationalPoints H) :
    rationalUnramifiedRegularFunctionsMap f (unramifiedEvaluationRegular _ h) =
      unramifiedEvaluationRegular _ (GroupScheme.rationalPoints.map f h) := rfl

omit [IsAffine H.X.left] [IsAffine K.X.left] in
theorem rationalUnramifiedRegularFunctionsMap_id (b : RG) :
    rationalUnramifiedRegularFunctionsMap (𝟙 G) b = b := by
  apply Subtype.ext
  funext z
  rw [rationalUnramifiedRegularFunctionsMap_apply, rationalUnramifiedCharacterRestrict_id]

/-- Pullback along a composite is the composite of the pullbacks. -/
theorem rationalUnramifiedRegularFunctionsMap_comp (f : K ⟶ H) (g : H ⟶ G) (b : RK) :
    rationalUnramifiedRegularFunctionsMap (f ≫ g) b =
      rationalUnramifiedRegularFunctionsMap g (rationalUnramifiedRegularFunctionsMap f b) := by
  apply Subtype.ext
  funext z
  rw [rationalUnramifiedRegularFunctionsMap_apply, rationalUnramifiedCharacterRestrict_comp]
  rfl

/-- **Regular functions along a group-scheme isomorphism.** For `e : H ≅ G`, pullback along
`e.hom` with inverse the pullback along `e.inv`. -/
def rationalUnramifiedRegularFunctionsEquiv (e : H ≅ G) : RH ≃ₐ[ℂ] RG :=
  AlgEquiv.ofAlgHom (rationalUnramifiedRegularFunctionsMap e.hom)
    (rationalUnramifiedRegularFunctionsMap e.inv)
    (by
      ext b : 1
      change rationalUnramifiedRegularFunctionsMap e.hom
        (rationalUnramifiedRegularFunctionsMap e.inv b) = b
      rw [← rationalUnramifiedRegularFunctionsMap_comp, Iso.inv_hom_id,
        rationalUnramifiedRegularFunctionsMap_id])
    (by
      ext b : 1
      change rationalUnramifiedRegularFunctionsMap e.inv
        (rationalUnramifiedRegularFunctionsMap e.hom b) = b
      rw [← rationalUnramifiedRegularFunctionsMap_comp, Iso.hom_inv_id,
        rationalUnramifiedRegularFunctionsMap_id])

omit [IsAffine K.X.left] in
@[simp]
theorem rationalUnramifiedRegularFunctionsEquiv_apply (e : H ≅ G) (b : RH) :
    rationalUnramifiedRegularFunctionsEquiv e b = rationalUnramifiedRegularFunctionsMap e.hom b :=
  rfl

/-- The character restriction along `e.inv`, the parameter map matching the transport of
functions: `z ↦ z ∘ e⁻¹` from characters of `H(F)` to characters of `G(F)`. -/
abbrev rationalUnramifiedCharacterTransport (e : H ≅ G) : XH →ₜ* XG :=
  rationalUnramifiedCharacterRestrict e.inv

omit [IsAffine K.X.left] in
/-- Restricting the transported character back along `e.hom` recovers the character. -/
theorem rationalUnramifiedCharacterRestrict_transport (e : H ≅ G) (z : XH) :
    rationalUnramifiedCharacterRestrict e.hom (rationalUnramifiedCharacterTransport e z) = z := by
  rw [← rationalUnramifiedCharacterRestrict_comp, Iso.hom_inv_id,
    rationalUnramifiedCharacterRestrict_id]

omit [IsAffine K.X.left] in
/-- The transported function takes at the transported character the original value. -/
theorem rationalUnramifiedRegularFunctionsEquiv_val_transport (e : H ≅ G) (b : RH) (z : XH) :
    (rationalUnramifiedRegularFunctionsEquiv e b).val (rationalUnramifiedCharacterTransport e z) =
      b.val z := by
  rw [rationalUnramifiedRegularFunctionsEquiv_apply, rationalUnramifiedRegularFunctionsMap_apply,
    rationalUnramifiedCharacterRestrict_transport]

omit [IsAffine K.X.left] in
/-- The inverse transport evaluates at `z` as the original function at the transported
character. -/
theorem rationalUnramifiedRegularFunctionsEquiv_symm_val (e : H ≅ G) (b : RG) (z : XH) :
    ((rationalUnramifiedRegularFunctionsEquiv e).symm b).val z =
      b.val (rationalUnramifiedCharacterTransport e z) := rfl

end Transport

/-! ### Transport of the actual function fields -/

section FunctionField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine H.X.left]

local instance conjugationFieldTopG : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance conjugationFieldTopH : TopologicalSpace (GroupScheme.rationalPoints H) :=
  rationalPointTopology F H.X

variable (hpH : Continuous (rationalValuationImageProjection H))
  (hH : GroupScheme.IsConnectedReductive H)
  (hpG : Continuous (rationalValuationImageProjection G))
  (hGG : GroupScheme.IsConnectedReductive G)

set_option hygiene false in
local notation "RG" => unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)
set_option hygiene false in
local notation "RH" => unramifiedRegularFunctions (fun ψ => (rationalNormCharacters H ψ).toMul)
set_option hygiene false in
local notation "XH" => unramifiedCharacters (fun ψ => (rationalNormCharacters H ψ).toMul)
set_option hygiene false in
local notation "FG" => rationalUnramifiedFunctionField G hpG hGG
set_option hygiene false in
local notation "FH" => rationalUnramifiedFunctionField H hpH hH

/-- **Rational functions along a group-scheme isomorphism.** For `e : H ≅ G`, the field
isomorphism `f ↦ (z ↦ f(z ∘ e))` from rational functions on the unramified characters of
`H(F)` to those of `G(F)`, extending `rationalUnramifiedRegularFunctionsEquiv e` to
fractions. -/
def rationalUnramifiedFunctionFieldEquiv (e : H ≅ G) : FH ≃+* FG :=
  IsFractionRing.ringEquivOfRingEquiv (rationalUnramifiedRegularFunctionsEquiv e).toRingEquiv

/-- On regular functions the field isomorphism is the transport of regular functions. -/
@[simp]
theorem rationalUnramifiedFunctionFieldEquiv_algebraMap (e : H ≅ G) (b : RH) :
    rationalUnramifiedFunctionFieldEquiv hpH hH hpG hGG e (algebraMap RH FH b) =
      algebraMap RG FG (rationalUnramifiedRegularFunctionsEquiv e b) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b

/-- The inverse field isomorphism on regular functions. -/
@[simp]
theorem rationalUnramifiedFunctionFieldEquiv_symm_algebraMap (e : H ≅ G) (b : RG) :
    (rationalUnramifiedFunctionFieldEquiv hpH hH hpG hGG e).symm (algebraMap RG FG b) =
      algebraMap RH FH ((rationalUnramifiedRegularFunctionsEquiv e).symm b) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b

/-- Complex constants are fixed. -/
theorem rationalUnramifiedFunctionFieldEquiv_constant (e : H ≅ G) (c : ℂ) :
    rationalUnramifiedFunctionFieldEquiv hpH hH hpG hGG e
        (algebraMap RH FH (algebraMap ℂ RH c)) =
      algebraMap RG FG (algebraMap ℂ RG c) := by
  rw [rationalUnramifiedFunctionFieldEquiv_algebraMap, AlgEquiv.commutes]

private theorem equiv_presentation (e : H ≅ G) {f : FH} {m n : RG}
    (hf : rationalUnramifiedFunctionFieldEquiv hpH hH hpG hGG e f =
      algebraMap RG FG m / algebraMap RG FG n) :
    f = algebraMap RH FH ((rationalUnramifiedRegularFunctionsEquiv e).symm m) /
      algebraMap RH FH ((rationalUnramifiedRegularFunctionsEquiv e).symm n) := by
  have h := congrArg (rationalUnramifiedFunctionFieldEquiv hpH hH hpG hGG e).symm hf
  rw [RingEquiv.symm_apply_apply, map_div₀,
    rationalUnramifiedFunctionFieldEquiv_symm_algebraMap,
    rationalUnramifiedFunctionFieldEquiv_symm_algebraMap] at h
  exact h

private theorem equiv_presentation' (e : H ≅ G) {f : FH} {m n : RH}
    (hf : f = algebraMap RH FH m / algebraMap RH FH n) :
    rationalUnramifiedFunctionFieldEquiv hpH hH hpG hGG e f =
      algebraMap RG FG (rationalUnramifiedRegularFunctionsEquiv e m) /
        algebraMap RG FG (rationalUnramifiedRegularFunctionsEquiv e n) := by
  rw [hf, map_div₀, rationalUnramifiedFunctionFieldEquiv_algebraMap,
    rationalUnramifiedFunctionFieldEquiv_algebraMap]

/-- A transported rational function is regular at the transported character exactly when
the original function is regular at the original character. -/
theorem rationalFunctionRegularAt_equiv_iff (e : H ≅ G) (f : FH) (z : XH) :
    RationalFunctionRegularAt G hpG hGG (rationalUnramifiedFunctionFieldEquiv hpH hH hpG hGG e f)
        (rationalUnramifiedCharacterTransport e z) ↔
      RationalFunctionRegularAt H hpH hH f z := by
  constructor
  · intro h
    obtain ⟨m, n, hn, hf⟩ := h
    exact ⟨(rationalUnramifiedRegularFunctionsEquiv e).symm m,
      (rationalUnramifiedRegularFunctionsEquiv e).symm n, hn,
      equiv_presentation hpH hH hpG hGG e hf⟩
  · intro h
    obtain ⟨m, n, hn, hf⟩ := h
    refine ⟨rationalUnramifiedRegularFunctionsEquiv e m,
      rationalUnramifiedRegularFunctionsEquiv e n, ?_,
      equiv_presentation' hpH hH hpG hGG e hf⟩
    rw [rationalUnramifiedRegularFunctionsEquiv_val_transport]
    exact hn

/-- Regularity with a nonnegative real value transfers in the same way. -/
theorem rationalFunctionNonnegAt_equiv_iff (e : H ≅ G) (f : FH) (z : XH) :
    RationalFunctionNonnegAt G hpG hGG (rationalUnramifiedFunctionFieldEquiv hpH hH hpG hGG e f)
        (rationalUnramifiedCharacterTransport e z) ↔
      RationalFunctionNonnegAt H hpH hH f z := by
  constructor
  · intro h
    obtain ⟨m, n, hn, hf, r, hr, hv⟩ := h
    exact ⟨(rationalUnramifiedRegularFunctionsEquiv e).symm m,
      (rationalUnramifiedRegularFunctionsEquiv e).symm n, hn,
      equiv_presentation hpH hH hpG hGG e hf, r, hr, hv⟩
  · intro h
    obtain ⟨m, n, hn, hf, r, hr, hv⟩ := h
    refine ⟨rationalUnramifiedRegularFunctionsEquiv e m,
      rationalUnramifiedRegularFunctionsEquiv e n, ?_,
      equiv_presentation' hpH hH hpG hGG e hf, r, hr, ?_⟩
    · rw [rationalUnramifiedRegularFunctionsEquiv_val_transport]
      exact hn
    · rw [rationalUnramifiedRegularFunctionsEquiv_val_transport,
        rationalUnramifiedRegularFunctionsEquiv_val_transport]
      exact hv

end FunctionField

/-! ### Conjugating the cocharacter by a rational point -/

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

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

section Conjugation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : RationalPoint F G.X)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] in
/-- Conjugating the cocharacter commutes with inverting it. -/
theorem inverseCocharacter_conjugate :
    Dynamic.inverseCocharacter (χ ≫ (G.innerIso g).hom) =
      Dynamic.inverseCocharacter χ ≫ (G.innerIso g).hom :=
  (Category.assoc _ _ _).symm

/-- Forward conjugation `x ↦ g x g⁻¹` carries the Levi `M(F) = Z_G(χ)(F)` onto the Levi
`Z_G(gχg⁻¹)(F)`. -/
theorem conjugateLevi_mem_iff (x : RationalPoint F G.X) :
    GroupScheme.rationalPointsConjHomeomorph G g x ∈ levi (χ ≫ (G.innerIso g).hom) ↔
      x ∈ levi χ := by
  simpa only [GroupScheme.rationalPointsConjHomeomorph_apply,
    GroupScheme.constantPoint_self] using (Dynamic.mem_centralizer_conj χ g (x := x)).symm

/-- Forward conjugation carries `P(F)` onto the parabolic of `gχg⁻¹`. -/
theorem conjugateParabolic_mem_iff (x : RationalPoint F G.X) :
    GroupScheme.rationalPointsConjHomeomorph G g x ∈ parabolic (χ ≫ (G.innerIso g).hom) ↔
      x ∈ parabolic χ :=
  RationalDynamicSource.parabolic_conjugation_mem_iff χ g x

/-- Forward conjugation carries `P̄(F)` onto the opposite parabolic of `gχg⁻¹`. -/
theorem conjugateOppositeParabolic_mem_iff (x : RationalPoint F G.X) :
    GroupScheme.rationalPointsConjHomeomorph G g x ∈
        oppositeParabolic (χ ≫ (G.innerIso g).hom) ↔
      x ∈ oppositeParabolic χ := by
  rw [oppositeParabolic, oppositeParabolic, inverseCocharacter_conjugate]
  exact conjugateParabolic_mem_iff (Dynamic.inverseCocharacter χ) g x

/-- **The conjugate Levi.** Conjugation `m ↦ g m g⁻¹` as a topological group isomorphism
from `M(F)` onto the Levi `Z_G(gχg⁻¹)(F) = g M(F) g⁻¹`. -/
def leviConjugation : levi χ ≃ₜ* levi (χ ≫ (G.innerIso g).hom) :=
  QuotientIntegration.subgroupContinuousMulEquiv (GroupScheme.rationalPointsConjHomeomorph G g)
    (levi χ) (levi (χ ≫ (G.innerIso g).hom)) (conjugateLevi_mem_iff χ g)

@[simp]
theorem leviConjugation_apply_coe (m : levi χ) :
    (leviConjugation χ g m : RationalPoint F G.X) = g * m * g⁻¹ := rfl

/-- **The conjugate representation** `gA` of `g M(F) g⁻¹`: `(gA)(g m g⁻¹) = A(m)` on the same
space. -/
abbrev conjugateRepresentation (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    SmoothRep.{0, u, uV} ℂ (levi (χ ≫ (G.innerIso g).hom)) :=
  SmoothRep.pullback (leviConjugation χ g).symm A

/-- **The conjugate parameter group.** The actual centralizer schemes of `χ` and `gχg⁻¹` are
identified by the inner automorphism `Int(g)` of `G`, compatibly with their inclusions in
`G`. -/
def parameterConjugationIso :
    parameterScheme χ ≅ parameterScheme (χ ≫ (G.innerIso g).hom) :=
  GroupScheme.SubgroupFunctor.IsRepresentedBy.isoOfComap
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (Dynamic.Affine.isRepresentedBy_centralizerHom (χ ≫ (G.innerIso g).hom))
    (G.innerIso g) (Dynamic.centralizer_eq_comap_of_iso χ (G.innerIso g)).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- On rational points, the parameter isomorphism followed by the inclusion of the
centralizer of `gχg⁻¹` is conjugation by `g` of the inclusion of the centralizer of `χ`. -/
theorem parameterConjugationIso_hom_points (y : RationalPoint F (parameterScheme χ).X) :
    (y ≫ (parameterConjugationIso χ g).hom.hom.hom) ≫
        (Dynamic.Affine.centralizerHom (χ ≫ (G.innerIso g).hom)).hom.hom =
      g * (y ≫ (Dynamic.Affine.centralizerHom χ).hom.hom) * g⁻¹ := by
  rw [parameterConjugationIso,
    GroupScheme.SubgroupFunctor.IsRepresentedBy.isoOfComap_hom_points,
    comp_innerIso_hom, GroupScheme.constantPoint_self]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The underlying ambient point of `parameterHomeomorph`. -/
theorem parameterHomeomorph_apply_coe (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (y : RationalPoint F (parameterScheme ψ).X) :
    (parameterHomeomorph ψ y : RationalPoint F G.X) =
      y ≫ (Dynamic.Affine.centralizerHom ψ).hom.hom :=
  dynamicCentralizerPointHomeomorph_apply_coe F G ψ y

/-- The parameter isomorphism and the Levi conjugation agree under the identifications
`parameterHomeomorph` of the parameter points with the literal Levis. -/
theorem parameterHomeomorph_parameterConjugationIso (y : RationalPoint F (parameterScheme χ).X) :
    parameterHomeomorph (χ ≫ (G.innerIso g).hom)
        (GroupScheme.rationalPoints.map (parameterConjugationIso χ g).hom y) =
      leviConjugation χ g (parameterHomeomorph χ y) := by
  apply Subtype.ext
  rw [leviConjugation_apply_coe, parameterHomeomorph_apply_coe,
    parameterHomeomorph_apply_coe, GroupScheme.rationalPoints.map_apply]
  exact parameterConjugationIso_hom_points χ g y

/-- The conjugate compact open `gKg⁻¹` gives the Iwasawa decomposition for the conjugate
parabolic. -/
theorem conjugate_parabolic_mul_compact (K : OpenSubgroup (RationalPoint F G.X))
    (hPK : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (x : RationalPoint F G.X) :
    ∃ p : parabolic (χ ≫ (G.innerIso g).hom), ∃ k : RationalDynamicSource.conjugateCompact g K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X) := by
  obtain ⟨p, k, h⟩ := hPK (g⁻¹ * x * g)
  refine ⟨⟨g * p * g⁻¹, (conjugateParabolic_mem_iff χ g p).2 p.2⟩,
    ⟨g * k * g⁻¹, (RationalDynamicSource.mem_conjugateCompact g k K).2 k.2⟩, ?_⟩
  change x = g * p * g⁻¹ * (g * k * g⁻¹)
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = g * (p * k) * g⁻¹ := by rw [h]
    _ = g * p * g⁻¹ * (g * k * g⁻¹) := by group

/-- The same for the opposite parabolic. -/
theorem conjugate_oppositeParabolic_mul_compact (K : OpenSubgroup (RationalPoint F G.X))
    (hOppK : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (x : RationalPoint F G.X) :
    ∃ p : oppositeParabolic (χ ≫ (G.innerIso g).hom),
      ∃ k : RationalDynamicSource.conjugateCompact g K,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X) := by
  obtain ⟨p, k, h⟩ := hOppK (g⁻¹ * x * g)
  refine ⟨⟨g * p * g⁻¹, (conjugateOppositeParabolic_mem_iff χ g p).2 p.2⟩,
    ⟨g * k * g⁻¹, (RationalDynamicSource.mem_conjugateCompact g k K).2 k.2⟩, ?_⟩
  change x = g * p * g⁻¹ * (g * k * g⁻¹)
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = g * (p * k) * g⁻¹ := by rw [h]
    _ = g * p * g⁻¹ * (g * k * g⁻¹) := by group

end Conjugation

/-! ### The target -/

set_option hygiene false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "Kg" => (RationalDynamicSource.conjugateCompact g K)
set_option hygiene false in
local notation "hKg" => (RationalDynamicSource.conjugateCompact_isCompact g K hK)
set_option hygiene false in
local notation "hPKg" => (conjugate_parabolic_mul_compact χ g K hPK)
set_option hygiene false in
local notation "hOppKg" => (conjugate_oppositeParabolic_mul_compact χ g K hOppK)
set_option hygiene false in
local notation "Ag" => (conjugateRepresentation χ g A)

/-- **Target (Waldspurger IV.3 (3), transport form).** Let `χ` be a cocharacter of `G`,
`P = P_G(χ)`, `P̄ = P_G(χ⁻¹)`, `M = Z_G(χ)`, let `K` be a compact open subgroup with
`G = P K = P̄ K`, and let `A` be a smooth representation of `M(F)`. Let `g ∈ G(F)`. Conjugation
by `g` gives the cocharacter `gχg⁻¹ = χ ≫ Int(g)`, with parabolic `gPg⁻¹`, opposite
parabolic `gP̄g⁻¹` and Levi `gMg⁻¹`; the compact open subgroup `gKg⁻¹`, which satisfies
`G = gPg⁻¹ · gKg⁻¹ = gP̄g⁻¹ · gKg⁻¹`; and the representation `gA` of `gM(F)g⁻¹`,
`(gA)(g m g⁻¹) = A(m)`. Take conditional data of the canonical scalar `j_P` of
`J_{P|P̄} J_{P̄|P}` for `A` and, independently, conditional data of `j_{gPg⁻¹}` for `gA`.
Then the scalar for `gA` is the scalar for `A` transported along the isomorphism
`Int(g) : Z_G(χ) ≅ Z_G(gχg⁻¹)` of the actual centralizer schemes:
`j_{gPg⁻¹}(gA ⊗ (z ∘ Int(g)⁻¹)) = j_P(A ⊗ z)` as rational functions of the unramified
character `z` of `M(F)`. -/
def ConditionalDynamicOppositeConjugationScalarStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (g : RationalPoint F G.X)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (_hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (_hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (_hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (p' : ForwardContinuation χg hRefl hCST hG Kg hKg hPKg hOppKg Ag)
    (q' : ReverseContinuation χg hRefl hCST hG Kg hKg hPKg hOppKg Ag)
    {DForward' DReverse' : Set (unramifiedCharacters (normCharacters χg))}
    (_hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ forwardFullDomainRegion χg Kg hKg Ag)
    (_hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ reverseFullDomainRegion χg Kg hKg Ag)
    {D' : Set (unramifiedCharacters (normCharacters χg))}
    (_hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition χg) (radical_isClosed χg)
        (leviNormCharacters χg) (parameterTransport χg z) Ag).IsIrreducible),
    conditionalCanonicalRationalScalar χg hRefl hCST hG Kg hKg hPKg hOppKg Ag
        p' q' hneForward' hDForwardΩ' hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (parameterProjection_continuous χg) (parameterScheme_isConnectedReductive χg hG)
        (parameterConjugationIso χ g)
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)

/-- **The target with any equal copy of `gKg⁻¹`.** The transport statement applies to
conditional data of `j_{gPg⁻¹}` for `gA` formed with any compact open subgroup `K₁` equal to
`gKg⁻¹`, with arbitrary proofs of its compactness and of `G = gPg⁻¹ K₁ = gP̄g⁻¹ K₁`. In
particular, if `g ∈ K` then `gKg⁻¹ = K`
(`RationalDynamicSource.conjugateCompact_eq_self`), and `K₁ = K`: the scalars of `A` and `gA`
are then formed with the same `K`, as in Waldspurger IV.3 (3) when the Weyl representative
lies in `K`. -/
theorem conditionalDynamicOppositeConjugationScalar_of_eq
    (hconj : ConditionalDynamicOppositeConjugationScalarStatement.{u, uV})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (g : RationalPoint F G.X)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (K₁ : OpenSubgroup (RationalPoint F G.X)) (hK₁ : Kg = K₁)
    (hK₁c : IsCompact (K₁ : Set (RationalPoint F G.X)))
    (hPK₁ : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χg, ∃ k : K₁, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK₁ : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χg, ∃ k : K₁,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (p' : ForwardContinuation χg hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ Ag)
    (q' : ReverseContinuation χg hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ Ag)
    {DForward' DReverse' : Set (unramifiedCharacters (normCharacters χg))}
    (hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ forwardFullDomainRegion χg K₁ hK₁c Ag)
    (hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ reverseFullDomainRegion χg K₁ hK₁c Ag)
    {D' : Set (unramifiedCharacters (normCharacters χg))}
    (hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition χg) (radical_isClosed χg)
        (leviNormCharacters χg) (parameterTransport χg z) Ag).IsIrreducible) :
    conditionalCanonicalRationalScalar χg hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ Ag
        p' q' hneForward' hDForwardΩ' hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (parameterProjection_continuous χg) (parameterScheme_isConnectedReductive χg hG)
        (parameterConjugationIso χ g)
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) := by
  subst hK₁
  exact hconj χ hRefl hCST hG g K hK hPK hOppK A p q hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hi p' q' hDForward' hneForward' hDForwardΩ'
    hDReverse' hneReverse' hDReverseΩ' hD' hne' hi'

end Langlands.Plancherel
