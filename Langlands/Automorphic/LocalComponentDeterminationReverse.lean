import Langlands.Representation.FreeMonoidGenerators
import Langlands.Automorphic.OperatorSubquotientPlaceGeneration
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Unramified.SphericalFixedLineProof
import Langlands.Global.FiniteAdelicGL.PadicComparison

/-!
# Common local components determine an automorphic representation

The reverse implication of `LocalComponentDeterminationStatement`, from
`LocalComponentExistenceStatement`: two irreducible jointly admissible operator subquotients
`Q`, `Q'` of `GL_(r+1)` that, at every place, are isotypic of the type of one irreducible local
representation are equivalent.

The place actions of an operator subquotient form a family of pairwise commuting actions of
free monoids, indexed by the places (`PlaceIndex`): at a finite place `v` the free monoid on
`GL_n(F_v)` acts through the local translations, at an infinite place the free monoid on
`K_v ⊕ (ℂ ⊗ 𝔤_v)` acts through the compact translations and the complexified Lie action. The
abstract uniqueness theorem `CommutingFamily.exists_linearEquiv_of_isotypic` then gives a linear
isomorphism intertwining all place actions, which is an equivalence of operator subquotients by
`OperatorSubquotient.equivalenceOfPlaceComm`.

* `PlaceIndex`, `PlaceGenerator`, `placeSpherical`: the places, the generators at each place, and
  the generators `GL_n(𝒪_v)` at the finite places used for the spherical condition.
* `OperatorSubquotient.placeGeneratorAction`, `OperatorSubquotient.placeRep`: the place actions
  of an operator subquotient as free-monoid representations;
  `OperatorSubquotient.placeRep_commuting` (they commute),
  `OperatorSubquotient.placeRep_eventually_fixed` (every vector is fixed by `GL_n(𝒪_v)` at almost
  every finite place), `OperatorSubquotient.isJointlyIrreducible_placeRep` (an irreducible
  subquotient is jointly irreducible for them).
* `PlaceData`: a choice of local representations at all places, with its free-monoid
  representations `PlaceData.localRep`.
* `finitePlace_isCommonType`, `realPlace_isCommonType`, `complexPlace_isCommonType`: a common
  local component of `Q` and `Q'` is a common isotypic type of the free-monoid representations
  with scalar self-intertwiners, and at a finite place its vectors fixed by `GL_n(𝒪_v)` form at
  most a line. Both facts are transported from the admissible local components supplied by
  `LocalComponentExistenceStatement`.
* `localComponentDetermination_reverse`: the reverse implication.
-/

noncomputable section

universe u

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)
open Langlands.FreeMonoidGenerators

attribute [local instance] localComponentRationalGroup localComponentContinuousGroup
  localComponentSmoothGroup localComponentFormGroup localComponentStableGroup
  localComponentRealizationGroup localComponentGeneralLinearTopology

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Places and generators -/

/-- The places of `F`: the finite places, then the real and the complex places. -/
abbrev PlaceIndex (F : Type u) [Field F] [NumberField F] : Type u :=
  FinitePlace F ⊕ ({v : NumberField.InfinitePlace F // v.IsReal} ⊕
    {v : NumberField.InfinitePlace F // v.IsComplex})

/-- The generators at a real place: the compact group `O(n)` and the complexified Lie algebra
`ℂ ⊗ 𝔤𝔩_n(ℝ)`, lifted to the universe `u`. -/
abbrev RealPlaceGenerator (n : ℕ) : Type u :=
  ULift.{u} (Matrix.unitaryGroup (Fin n) ℝ ⊕ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ))

/-- The generators at a complex place: `U(n)` and `ℂ ⊗ 𝔤𝔩_n(ℂ)`, lifted to the universe
`u`. -/
abbrev ComplexPlaceGenerator (n : ℕ) : Type u :=
  ULift.{u} (Matrix.unitaryGroup (Fin n) ℂ ⊕ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ))

/-- The generators of the place actions: `GL_n(F_v)` at a finite place, the compact group and
the complexified Lie algebra at an infinite place. -/
def PlaceGenerator (F : Type u) [Field F] [NumberField F] (n : ℕ) : PlaceIndex F → Type u
  | .inl v => FiniteLocalGL F n v
  | .inr (.inl _) => RealPlaceGenerator.{u} n
  | .inr (.inr _) => ComplexPlaceGenerator.{u} n

/-- The words in `GL_n(𝒪_v)` of length one at a finite place `v`; nothing at an infinite
place. -/
def placeSpherical (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    ∀ i : PlaceIndex F, Set (FreeMonoid (PlaceGenerator F n i))
  | .inl v => FreeMonoid.of '' (FiniteAdelicGL.localIntegral F n v : Set (FiniteLocalGL F n v))
  | .inr _ => ∅

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

theorem of_mem_placeSpherical {v : FinitePlace F} {g : FiniteLocalGL F n v}
    (hg : g ∈ FiniteAdelicGL.localIntegral F n v) :
    (FreeMonoid.of g : FreeMonoid (PlaceGenerator F n (.inl v))) ∈ placeSpherical F n (.inl v) := by
  show FreeMonoid.of g ∈
    FreeMonoid.of '' (FiniteAdelicGL.localIntegral F n v : Set (FiniteLocalGL F n v))
  exact Set.mem_image_of_mem _ hg

/-! ### The place actions of an operator subquotient -/

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

/-- The action of the generators at each place on `Q`. -/
def placeGeneratorAction : ∀ i : PlaceIndex F, PlaceGenerator F n i → Module.End ℂ Q.Space
  | .inl v => ⇑(Q.localRepresentation v)
  | .inr (.inl v) => gkGenerators ULift.down (Q.realPlaceCompactRepresentation v)
      (Q.realPlaceLieAction v)
  | .inr (.inr v) => gkGenerators ULift.down (Q.complexPlaceCompactRepresentation v)
      (Q.complexPlaceLieAction v)

/-- The place actions of `Q` as representations of the free monoids on the generators. -/
def placeRep (i : PlaceIndex F) : Representation ℂ (FreeMonoid (PlaceGenerator F n i)) Q.Space :=
  rep (Q.placeGeneratorAction i)

theorem placeGeneratorAction_comm_finite {v w : FinitePlace F} (h : v ≠ w)
    (a : PlaceGenerator F n (.inl v)) (b : PlaceGenerator F n (.inl w)) (x : Q.Space) :
    Q.placeGeneratorAction (.inl v) a (Q.placeGeneratorAction (.inl w) b x) =
      Q.placeGeneratorAction (.inl w) b (Q.placeGeneratorAction (.inl v) a x) :=
  Q.localRepresentation_comm_of_ne h a b x

theorem placeGeneratorAction_comm_finite_real (v : FinitePlace F) (w : RP)
    (a : PlaceGenerator F n (.inl v)) (b : PlaceGenerator F n (.inr (.inl w))) (x : Q.Space) :
    Q.placeGeneratorAction (.inl v) a (Q.placeGeneratorAction (.inr (.inl w)) b x) =
      Q.placeGeneratorAction (.inr (.inl w)) b (Q.placeGeneratorAction (.inl v) a x) := by
  obtain ⟨k | X⟩ := b
  · exact Q.finiteRepresentation_realPlaceCompactRepresentation
      (FiniteAdelicGL.localInclusion F n v a) w k x
  · exact Q.finiteRepresentation_realPlaceLieAction (FiniteAdelicGL.localInclusion F n v a) w X x

theorem placeGeneratorAction_comm_finite_complex (v : FinitePlace F) (w : CP)
    (a : PlaceGenerator F n (.inl v)) (b : PlaceGenerator F n (.inr (.inr w))) (x : Q.Space) :
    Q.placeGeneratorAction (.inl v) a (Q.placeGeneratorAction (.inr (.inr w)) b x) =
      Q.placeGeneratorAction (.inr (.inr w)) b (Q.placeGeneratorAction (.inl v) a x) := by
  obtain ⟨k | X⟩ := b
  · exact Q.finiteRepresentation_complexPlaceCompactRepresentation
      (FiniteAdelicGL.localInclusion F n v a) w k x
  · exact Q.finiteRepresentation_complexPlaceLieAction
      (FiniteAdelicGL.localInclusion F n v a) w X x

theorem placeGeneratorAction_comm_real {v w : RP} (h : v ≠ w)
    (a : PlaceGenerator F n (.inr (.inl v))) (b : PlaceGenerator F n (.inr (.inl w)))
    (x : Q.Space) :
    Q.placeGeneratorAction (.inr (.inl v)) a (Q.placeGeneratorAction (.inr (.inl w)) b x) =
      Q.placeGeneratorAction (.inr (.inl w)) b (Q.placeGeneratorAction (.inr (.inl v)) a x) := by
  obtain ⟨k | X⟩ := a <;> obtain ⟨l | Y⟩ := b
  · exact Q.realPlaceCompactRepresentation_comm_of_ne h l k x
  · exact Q.realPlaceCompactRepresentation_realPlaceLieAction_of_ne v w h.symm k Y x
  · exact (Q.realPlaceCompactRepresentation_realPlaceLieAction_of_ne w v h l X x).symm
  · exact Q.realPlaceLieAction_comm_of_ne h.symm X Y x

theorem placeGeneratorAction_comm_real_complex (v : RP) (w : CP)
    (a : PlaceGenerator F n (.inr (.inl v))) (b : PlaceGenerator F n (.inr (.inr w)))
    (x : Q.Space) :
    Q.placeGeneratorAction (.inr (.inl v)) a (Q.placeGeneratorAction (.inr (.inr w)) b x) =
      Q.placeGeneratorAction (.inr (.inr w)) b (Q.placeGeneratorAction (.inr (.inl v)) a x) := by
  obtain ⟨k | X⟩ := a <;> obtain ⟨l | Y⟩ := b
  · exact (Q.realPlaceCompactRepresentation_comm_complexPlace v w k l x).symm
  · exact Q.realPlaceCompactRepresentation_complexPlaceLieAction v w k Y x
  · exact (Q.complexPlaceCompactRepresentation_realPlaceLieAction w v l X x).symm
  · exact Q.realPlaceLieAction_comm_complexPlace v w X Y x

theorem placeGeneratorAction_comm_complex {v w : CP} (h : v ≠ w)
    (a : PlaceGenerator F n (.inr (.inr v))) (b : PlaceGenerator F n (.inr (.inr w)))
    (x : Q.Space) :
    Q.placeGeneratorAction (.inr (.inr v)) a (Q.placeGeneratorAction (.inr (.inr w)) b x) =
      Q.placeGeneratorAction (.inr (.inr w)) b (Q.placeGeneratorAction (.inr (.inr v)) a x) := by
  obtain ⟨k | X⟩ := a <;> obtain ⟨l | Y⟩ := b
  · exact Q.complexPlaceCompactRepresentation_comm_of_ne h l k x
  · exact Q.complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne v w h.symm k Y x
  · exact (Q.complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne w v h l X x).symm
  · exact Q.complexPlaceLieAction_comm_of_ne h.symm X Y x

/-- The generators at distinct places act by commuting operators. -/
theorem placeGeneratorAction_comm {i j : PlaceIndex F} (hij : i ≠ j)
    (a : PlaceGenerator F n i) (b : PlaceGenerator F n j) (x : Q.Space) :
    Q.placeGeneratorAction i a (Q.placeGeneratorAction j b x) =
      Q.placeGeneratorAction j b (Q.placeGeneratorAction i a x) := by
  rcases i with v | v | v <;> rcases j with w | w | w
  · exact Q.placeGeneratorAction_comm_finite (fun h => hij (by subst h; rfl)) a b x
  · exact Q.placeGeneratorAction_comm_finite_real v w a b x
  · exact Q.placeGeneratorAction_comm_finite_complex v w a b x
  · exact (Q.placeGeneratorAction_comm_finite_real w v b a x).symm
  · exact Q.placeGeneratorAction_comm_real (fun h => hij (by subst h; rfl)) a b x
  · exact Q.placeGeneratorAction_comm_real_complex v w a b x
  · exact (Q.placeGeneratorAction_comm_finite_complex w v b a x).symm
  · exact (Q.placeGeneratorAction_comm_real_complex w v b a x).symm
  · exact Q.placeGeneratorAction_comm_complex (fun h => hij (by subst h; rfl)) a b x

/-- The place actions of `Q` at distinct places commute. -/
theorem placeRep_commuting : RestrictedTensor.CyclicEvaluation.Commuting Q.placeRep :=
  fun _ _ hij g h x => rep_comm (Q.placeGeneratorAction_comm hij) g h x

/-- Every vector of `Q` is fixed by `GL_n(𝒪_v)` at almost every finite place. -/
theorem placeRep_eventually_fixed (x : Q.Space) :
    ∀ᶠ i in Filter.cofinite, ∀ h ∈ placeSpherical F n i, Q.placeRep i h x = x := by
  have hfin := FiniteAdelicGL.eventually_fixed_localIntegral Q.finiteRepresentation_isSmooth x
  rw [Filter.eventually_cofinite] at hfin ⊢
  refine ((hfin.image Sum.inl).union (Set.finite_range Sum.inr)).subset ?_
  rintro (v | w) hi
  · refine Or.inl ⟨v, fun hv => hi ?_, rfl⟩
    rintro _ ⟨g, hg, rfl⟩
    exact hv g hg
  · exact Or.inr ⟨w, rfl⟩

/-- A subspace of `Q` stable under all place actions is stable under the operator algebra. -/
theorem representation_mem_of_placeRep_stable (U : Submodule ℂ Q.Space)
    (hU : ∀ (i : PlaceIndex F) (g : FreeMonoid (PlaceGenerator F n i)), ∀ x ∈ U,
      Q.placeRep i g x ∈ U)
    (a : automorphicOperatorAlgebra F n) : ∀ x ∈ U, Q.representation a x ∈ U := by
  have hgen : ∀ i a, ∀ x ∈ U, Q.placeGeneratorAction i a x ∈ U :=
    fun i a x hx => hU i (FreeMonoid.of a) x hx
  have hfin : ∀ (v : FinitePlace F) (g : FiniteLocalGL F n v), ∀ x ∈ U,
      Q.localRepresentation v g x ∈ U := fun v g x hx => hgen (.inl v) g x hx
  have hrk : ∀ (v : RP) (k : Matrix.unitaryGroup (Fin n) ℝ), ∀ x ∈ U,
      Q.realPlaceCompactRepresentation v k x ∈ U :=
    fun v k x hx => hgen (.inr (.inl v)) (ULift.up (Sum.inl k)) x hx
  have hrl : ∀ (v : RP) (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ), ∀ x ∈ U,
      Q.realPlaceLieAction v X x ∈ U :=
    fun v X x hx => hgen (.inr (.inl v)) (ULift.up (Sum.inr X)) x hx
  have hck : ∀ (v : CP) (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ x ∈ U,
      Q.complexPlaceCompactRepresentation v k x ∈ U :=
    fun v k x hx => hgen (.inr (.inr v)) (ULift.up (Sum.inl k)) x hx
  have hcl : ∀ (v : CP) (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ x ∈ U,
      Q.complexPlaceLieAction v X x ∈ U :=
    fun v X x hx => hgen (.inr (.inr v)) (ULift.up (Sum.inr X)) x hx
  exact Q.representation_mem_of_placeStable U hfin hrk hrl hck hcl a

/-- An irreducible nonzero operator subquotient is jointly irreducible for its place actions: a
subspace stable under all place actions is stable under the operator algebra
(`representation_mem_of_placeRep_stable`). -/
theorem isJointlyIrreducible_placeRep (hQ : Q.IsIrreducible) [Nontrivial Q.Space] :
    CommutingFamily.IsJointlyIrreducible Q.placeRep := by
  refine ⟨inferInstance, fun U hU => ?_⟩
  let R : Subrepresentation Q.representation :=
    ⟨U, fun a x hx => Q.representation_mem_of_placeRep_stable U hU a x hx⟩
  rcases hQ.eq_bot_or_eq_top R with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

end OperatorSubquotient

/-! ### Local data -/

/-- A choice of local representations at all places of `F`: a representation of `GL_n(F_v)`
at every finite place `v`, and a compact action with a complexified Lie action at every real
or complex place. -/
structure PlaceData (F : Type u) [Field F] [NumberField F] (n : ℕ) where
  finiteCarrier : FinitePlace F → ModuleCat.{u} ℂ
  finiteRep : ∀ v, Representation ℂ (FiniteLocalGL F n v) (finiteCarrier v)
  realCarrier : {v : NumberField.InfinitePlace F // v.IsReal} → ModuleCat.{u} ℂ
  realRep : ∀ v, Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (realCarrier v)
  realLie : ∀ v, (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ (realCarrier v)
  complexCarrier : {v : NumberField.InfinitePlace F // v.IsComplex} → ModuleCat.{u} ℂ
  complexRep : ∀ v, Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) (complexCarrier v)
  complexLie : ∀ v, (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ (complexCarrier v)

namespace PlaceData

variable (D : PlaceData F n)

/-- The local carrier at a place. -/
def carrier : PlaceIndex F → ModuleCat.{u} ℂ
  | .inl v => D.finiteCarrier v
  | .inr (.inl v) => D.realCarrier v
  | .inr (.inr v) => D.complexCarrier v

/-- The action of the generators at a place on the local carrier. -/
def action : ∀ i : PlaceIndex F, PlaceGenerator F n i → Module.End ℂ (D.carrier i)
  | .inl v => ⇑(D.finiteRep v)
  | .inr (.inl v) => gkGenerators ULift.down (D.realRep v) (D.realLie v)
  | .inr (.inr v) => gkGenerators ULift.down (D.complexRep v) (D.complexLie v)

/-- The local representations as representations of the free monoids on the generators. -/
def localRep (i : PlaceIndex F) : Representation ℂ (FreeMonoid (PlaceGenerator F n i)) (D.carrier i) :=
  rep (D.action i)

end PlaceData

/-! ### Common local components -/

/-- Schur's lemma for an irreducible admissible representation of `GL_(r+1)(F_v)`, read as a
representation of `FiniteLocalGL F (r + 1) v`. -/
theorem automorphicObject_scalar {r : ℕ} (v : FinitePlace F)
    (A : AutomorphicObject.{u, u} (padicField v) r.succPNat)
    (φ : (A.obj.representation : Representation ℂ (FiniteLocalGL F (r + 1) v) A.obj).IntertwiningMap
      A.obj.representation) :
    ∃ c : ℂ, φ = c • Representation.IntertwiningMap.id _ :=
  (admissibleSchur_scalarEndomorphism A.obj.representation A.property.2 A.property.1 φ).exists

/-- The vectors of an irreducible admissible representation `A` of `GL_(r+1)(F_v)` fixed by
`GL_(r+1)(𝒪_v)` lie on a line (`Unramified.sphericalFixedLine`). -/
theorem automorphicObject_fixed_line {r : ℕ} (v : FinitePlace F)
    (A : AutomorphicObject.{u, u} (padicField v) r.succPNat) :
    ∃ x₀ : A.obj, ∀ x : A.obj,
      (∀ g ∈ (FiniteAdelicGL.localIntegral F (r + 1) v : Set (FiniteLocalGL F (r + 1) v)),
        A.obj.representation g x = x) → ∃ c : ℂ, x = c • x₀ := by
  have hK : ∀ g : FiniteLocalGL F (r + 1) v,
      g ∈ Correspondence.sphericalSubgroup (padicField v) r →
        g ∈ FiniteAdelicGL.localIntegral F (r + 1) v := fun g hg =>
    (congrArg (fun S : Subgroup (FiniteLocalGL F (r + 1) v) => g ∈ S)
      (FiniteAdelicGL.localIntegral_eq_sphericalSubgroup F v r)).mpr hg
  have hfix : ∀ x : A.obj,
      (∀ g ∈ (FiniteAdelicGL.localIntegral F (r + 1) v : Set (FiniteLocalGL F (r + 1) v)),
        A.obj.representation g x = x) →
      x ∈ fixedVectors A.obj.representation (Correspondence.sphericalSubgroup (padicField v) r) :=
    fun x hx g => hx g.1 (hK g.1 g.2)
  by_cases h0 : fixedVectors A.obj.representation
      (Correspondence.sphericalSubgroup (padicField v) r) = ⊥
  · refine ⟨0, fun x hx => ⟨0, ?_⟩⟩
    have hmem := hfix x hx
    rw [h0] at hmem
    rw [zero_smul]
    exact (Submodule.mem_bot ℂ).mp hmem
  · obtain ⟨a₀, -, ha₀⟩ :=
      finrank_eq_one_iff'.mp (Unramified.sphericalFixedLine _ (padicField v) r A h0)
    refine ⟨a₀, fun x hx => ?_⟩
    obtain ⟨c, hc⟩ := ha₀ ⟨x, hfix x hx⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- **Finite places.** If `ρ` is an irreducible local component of both `Q` and `Q'` at the
finite place `v`, and `Q` is also `A`-isotypic for an irreducible admissible `A`, then the
free-monoid representation of `ρ` is a common isotypic type of the place actions of `Q` and `Q'`
with scalar self-intertwiners (Schur's lemma for `A`, transported along `ρ ≃ A`), and the
vectors of `ρ` fixed by `GL_(r+1)(𝒪_v)` lie on a line (the spherical line of `A`). -/
theorem finitePlace_isCommonType {r : ℕ} (Q Q' : IrreducibleOperatorSubquotient F r)
    (v : FinitePlace F)
    (hA : ∃ A : AutomorphicObject.{u, u} (padicField v) r.succPNat,
      Q.subquotient.IsFinitePlaceIsotypic v A.obj.representation)
    {W : Type u} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (FiniteLocalGL F (r + 1) v) W) (hρ : ρ.IsIrreducible)
    (hQ : Q.subquotient.IsFinitePlaceIsotypic v ρ) (hQ' : Q'.subquotient.IsFinitePlaceIsotypic v ρ) :
    IsCommonType (rep ⇑ρ) (rep ⇑(Q.subquotient.localRepresentation v))
        (rep ⇑(Q'.subquotient.localRepresentation v)) ∧
      ∃ w₀ : W, ∀ w : W,
        (∀ g ∈ (FiniteAdelicGL.localIntegral F (r + 1) v : Set (FiniteLocalGL F (r + 1) v)),
          ρ g w = w) →
        ∃ c : ℂ, w = c • w₀ := by
  obtain ⟨A, hAQ⟩ := hA
  have := hρ
  let ρA : Representation ℂ (FiniteLocalGL F (r + 1) v) A.obj := A.obj.representation
  have hAirr : ρA.IsIrreducible := A.property.1
  have hS : ∀ φ : ρA.IntertwiningMap ρA, ∃ c : ℂ, φ = c • Representation.IntertwiningMap.id ρA :=
    automorphicObject_scalar v A
  have hτ : ⨆ f : ρA.IntertwiningMap (Q.subquotient.localRepresentation v),
      LinearMap.range f.toLinearMap = ⊤ := hAQ
  have hρQ : ⨆ f : ρ.IntertwiningMap (Q.subquotient.localRepresentation v),
      LinearMap.range f.toLinearMap = ⊤ := hQ
  have hρQ' : ⨆ f : ρ.IntertwiningMap (Q'.subquotient.localRepresentation v),
      LinearMap.range f.toLinearMap = ⊤ := hQ'
  have key := isCommonType_monoid ρ ρA hS (Q.subquotient.localRepresentation v)
    (Q'.subquotient.localRepresentation v) hτ hρQ hρQ'
  obtain ⟨hcommon, ⟨e⟩⟩ := key
  have hline := exists_fixed_line_of_equiv e
    (FiniteAdelicGL.localIntegral F (r + 1) v : Set (FiniteLocalGL F (r + 1) v))
    (automorphicObject_fixed_line v A)
  exact ⟨hcommon, hline⟩

/-- **Real places.** An irreducible `(𝔤, K)`-module that is a local component of both `Q` and
`Q'` at the real place `v` gives a common isotypic type of the place actions with scalar
self-intertwiners (Schur's lemma for the admissible component of `Q`). -/
theorem realPlace_isCommonType {r : ℕ} (Q Q' : IrreducibleOperatorSubquotient F r) (v : RP)
    (hA : ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
        (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
        Archimedean.IsRealGKModule (r + 1) ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
          Archimedean.IsAdmissibleGKModule ρ ∧ Q.subquotient.IsRealPlaceIsotypic v ρ π)
    {W : Type u} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) W)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (hirr : Archimedean.IsIrreducibleGKModule ρ π) (hQ : Q.subquotient.IsRealPlaceIsotypic v ρ π)
    (hQ' : Q'.subquotient.IsRealPlaceIsotypic v ρ π) :
    IsCommonType (gkRep (ULift.down : RealPlaceGenerator.{u} (r + 1) → _) ρ π)
      (Q.subquotient.placeRep (.inr (.inl v))) (Q'.subquotient.placeRep (.inr (.inl v))) := by
  obtain ⟨VA, ρA, πA, hreal, hirrA, hadm, hAQ⟩ := hA
  have hyp : Archimedean.GKModuleDensity.Hyp ρA πA :=
    { irreducible := hirrA
      admissible := hadm
      finite := fun x => ⟨FiniteVectors.orbitSpan ρA x, FiniteVectors.self_mem_orbitSpan _ x,
        hreal.1 x, fun g _ hw => (FiniteVectors.orbitSubrepresentation _ x).apply_mem_toSubmodule g hw⟩
      continuous := hreal.2.1 }
  exact isCommonType_gk ULift.down_surjective hirr hyp hAQ hQ hQ'

/-- **Complex places.** The analogue of `realPlace_isCommonType`. -/
theorem complexPlace_isCommonType {r : ℕ} (Q Q' : IrreducibleOperatorSubquotient F r) (v : CP)
    (hA : ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
        (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
        Archimedean.IsComplexGKModule (r + 1) ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
          Archimedean.IsAdmissibleGKModule ρ ∧ Q.subquotient.IsComplexPlaceIsotypic v ρ π)
    {W : Type u} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) W)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (hirr : Archimedean.IsIrreducibleGKModule ρ π)
    (hQ : Q.subquotient.IsComplexPlaceIsotypic v ρ π)
    (hQ' : Q'.subquotient.IsComplexPlaceIsotypic v ρ π) :
    IsCommonType (gkRep (ULift.down : ComplexPlaceGenerator.{u} (r + 1) → _) ρ π)
      (Q.subquotient.placeRep (.inr (.inr v))) (Q'.subquotient.placeRep (.inr (.inr v))) := by
  obtain ⟨VA, ρA, πA, hcpx, hirrA, hadm, hAQ⟩ := hA
  have hyp : Archimedean.GKModuleDensity.Hyp ρA πA :=
    { irreducible := hirrA
      admissible := hadm
      finite := fun x => ⟨FiniteVectors.orbitSpan ρA x, FiniteVectors.self_mem_orbitSpan _ x,
        hcpx.1 x, fun g _ hw => (FiniteVectors.orbitSubrepresentation _ x).apply_mem_toSubmodule g hw⟩
      continuous := hcpx.2.1 }
  exact isCommonType_gk ULift.down_surjective hirr hyp hAQ hQ hQ'

/-! ### The reverse implication -/

/-- **Common local components determine the representation** (the reverse implication of
`LocalComponentDeterminationStatement`), from `LocalComponentExistenceStatement`: if at every
place some irreducible local representation is a local component of both `Q` and `Q'`, then
`Q` and `Q'` are equivalent. Only the joint admissibility of `Q` is used. -/
theorem localComponentDetermination_reverse (hex : LocalComponentExistenceStatement.{u})
    (F : Type u) [Field F] [NumberField F] (r : ℕ) (Q Q' : IrreducibleOperatorSubquotient F r)
    (hQ : Q.subquotient.IsJointlyAdmissible)
    (h : (∀ v : FinitePlace F, ∃ (W : ModuleCat.{u} ℂ)
          (ρ : Representation ℂ (FiniteLocalGL F (r + 1) v) W), ρ.IsIrreducible ∧
        Q.subquotient.IsFinitePlaceIsotypic v ρ ∧ Q'.subquotient.IsFinitePlaceIsotypic v ρ) ∧
      (∀ v : {v : NumberField.InfinitePlace F // v.IsReal},
        ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
          (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
          Archimedean.IsIrreducibleGKModule ρ π ∧
            Q.subquotient.IsRealPlaceIsotypic v ρ π ∧ Q'.subquotient.IsRealPlaceIsotypic v ρ π) ∧
      ∀ v : {v : NumberField.InfinitePlace F // v.IsComplex},
        ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
          (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
          Archimedean.IsIrreducibleGKModule ρ π ∧
            Q.subquotient.IsComplexPlaceIsotypic v ρ π ∧
              Q'.subquotient.IsComplexPlaceIsotypic v ρ π) :
    Nonempty (Q.Equivalence Q') := by
  obtain ⟨hfin, hreal, hcpx⟩ := h
  obtain ⟨hAfin, hAreal, hAcpx⟩ := hex F r Q hQ
  choose Wf ρf hρf hQf hQ'f using hfin
  choose Wr ρr πr hρr hQr hQ'r using hreal
  choose Wc ρc πc hρc hQc hQ'c using hcpx
  let D : PlaceData F (r + 1) := ⟨Wf, ρf, Wr, ρr, πr, Wc, ρc, πc⟩
  have hcommon : ∀ i, IsCommonType (D.localRep i) (Q.subquotient.placeRep i)
      (Q'.subquotient.placeRep i) := by
    rintro (v | v | v)
    · exact (finitePlace_isCommonType Q Q' v (hAfin v) (ρf v) (hρf v) (hQf v) (hQ'f v)).1
    · exact realPlace_isCommonType Q Q' v (hAreal v) (ρr v) (πr v) (hρr v) (hQr v) (hQ'r v)
    · exact complexPlace_isCommonType Q Q' v (hAcpx v) (ρc v) (πc v) (hρc v) (hQc v) (hQ'c v)
  have hsph : ∀ᶠ i in Filter.cofinite, ∃ w₀ : D.carrier i, ∀ w : D.carrier i,
      (∀ h ∈ placeSpherical F (r + 1) i, D.localRep i h w = w) → ∃ c : ℂ, w = c • w₀ := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_range Sum.inr).subset ?_
    rintro (v | w) hi
    · refine absurd ?_ hi
      obtain ⟨w₀, hw₀⟩ := (finitePlace_isCommonType Q Q' v (hAfin v) (ρf v) (hρf v) (hQf v)
        (hQ'f v)).2
      refine ⟨w₀, fun w hw => hw₀ w fun g hg => hw (FreeMonoid.of g) (of_mem_placeSpherical hg)⟩
    · exact ⟨w, rfl⟩
  have : ∀ i, (D.localRep i).IsIrreducible := fun i => (hcommon i).1
  obtain ⟨Φ, hΦ⟩ := CommutingFamily.exists_linearEquiv_of_isotypic Q.subquotient.placeRep
    Q.subquotient.placeRep_commuting Q'.subquotient.placeRep Q'.subquotient.placeRep_commuting
    (Q.subquotient.isJointlyIrreducible_placeRep Q.irreducible)
    (Q'.subquotient.isJointlyIrreducible_placeRep Q'.irreducible) D.localRep
    (fun i => (hcommon i).2.1) (fun i => (hcommon i).2.2.1) (fun i => (hcommon i).2.2.2)
    (placeSpherical F (r + 1)) hsph Q.subquotient.placeRep_eventually_fixed
    Q'.subquotient.placeRep_eventually_fixed
  have hgen : ∀ i a x, Φ (Q.subquotient.placeGeneratorAction i a x) =
      Q'.subquotient.placeGeneratorAction i a (Φ x) :=
    fun i a x => hΦ i (FreeMonoid.of a) x
  exact ⟨Q.subquotient.equivalenceOfPlaceComm Q'.subquotient Φ
    (fun v g x => hgen (.inl v) g x)
    (fun v k x => hgen (.inr (.inl v)) (ULift.up (Sum.inl k)) x)
    (fun v X x => hgen (.inr (.inl v)) (ULift.up (Sum.inr X)) x)
    (fun v k x => hgen (.inr (.inr v)) (ULift.up (Sum.inl k)) x)
    (fun v X x => hgen (.inr (.inr v)) (ULift.up (Sum.inr X)) x)⟩

end Langlands.Automorphic
