import Langlands.Representation.Plancherel.ProductInducedOrbitCompactAction
import Langlands.HarmonicAnalysis.TorusFourierDecay
import Langlands.HarmonicAnalysis.TorusFourierSynthesis
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.ContinuousMap.Compact

/-! # The topology of the space `C^∞(O,P)` of smooth sections over a unitary orbit

Waldspurger, VI.3 (printed p. 301): `C^∞(Im X(M))` carries its usual topology; for every
compact open subgroup `H` of `K`, the invariants `L_K(ω,P)^{H×H}` are finite-dimensional,
`C^∞(Im X(M)) ⊗ L_K(ω,P)^{H×H}` carries the product topology, and through the description of
VI.1 its subspace `C^∞(O,P)^{H×H}` inherits a topology; `C^∞(O,P)` carries the inductive-limit
topology of these subspaces as `H` runs over the compact open subgroups of `K`.

Here `C^∞(O,P)` is `productInducedSmoothOrbitSections`, and the description of VI.1 is the
compact restriction `R = productInducedSmoothOrbitCompactRestriction`, which sends a section
`q` to the family `z ↦ R q z` in the compact picture `L_K` over the parameter torus
`J → Circle` (coordinates `e` of `Im X(M)`). For a list `l` of coordinate directions and a
linear functional `ℓ` on the compact picture, `orbitSectionSeminorm (l, ℓ)` is
`q ↦ sup_z |∂_l (ℓ ∘ R q)(z)|`. The level `C^∞(O,P)^{H×H}` (`OrbitSectionLevel`) carries the
topology of these seminorms, and `OrbitSectionSpace` carries the locally convex inductive limit
over the open subgroups `H ≤ K`, as in `HarishChandraSchwartz.Basic` for `C(G)`. The
coincidence of the level topology with Waldspurger's product topology (which uses the finite
dimensionality of `L_K(ω,P)^{H×H}`) is not formalized here.
-/

noncomputable section

open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open Langlands.HarmonicAnalysis.TorusFourier
open TopologicalSpace
open scoped NNReal

namespace Langlands.HarmonicAnalysis.TorusFourier

variable {J : Type*} [Fintype J]

/-- A finite smooth scalar family is a smooth torus function. -/
theorem isSmoothFiniteTorusFunction_of_mem_finiteSmoothFamilies {F : (J → Circle) → ℂ}
    (hF : F ∈ finiteSmoothFamilies J ℂ) : IsSmoothFiniteTorusFunction F := by
  obtain ⟨n, f, v, hF⟩ := (mem_finiteSmoothFamilies_iff J ℂ F).mp hF
  have heq : F = ((∑ i, v i • f i : smoothFiniteTorusFunctions J) : (J → Circle) → ℂ) := by
    funext z
    rw [hF z]
    simp [mul_comm]
  rw [heq]
  exact (∑ i, v i • f i).property

/-- Inclusion of smooth torus functions into the continuous functions with the sup norm. -/
def smoothTorusToContinuousMap : smoothFiniteTorusFunctions J →ₗ[ℂ] C(J → Circle, ℂ) where
  toFun f := ⟨f.val, IsSmoothFiniteTorusFunction.continuous f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem smoothTorusToContinuousMap_apply (f : smoothFiniteTorusFunctions J) (z : J → Circle) :
    smoothTorusToContinuousMap f z = f.val z :=
  rfl

variable [DecidableEq J]

theorem hasDerivAt_torusTranslate_zero {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (j : J) (z : J → Circle) :
    HasDerivAt (fun t : ℝ => f (z * finiteTorusExp (Pi.single j t)))
      (torusPartialDeriv j f z) 0 := by
  simpa only [Pi.single_zero, finiteTorusExp_zero, mul_one] using
    hasDerivAt_torusTranslate hf j z 0

theorem torusPartialDeriv_add {f g : (J → Circle) → ℂ} (hf : IsSmoothFiniteTorusFunction f)
    (hg : IsSmoothFiniteTorusFunction g) (j : J) :
    torusPartialDeriv j (f + g) = torusPartialDeriv j f + torusPartialDeriv j g := by
  funext z
  exact ((hasDerivAt_torusTranslate_zero hf j z).add (hasDerivAt_torusTranslate_zero hg j z)).deriv

theorem torusPartialDeriv_smul (c : ℂ) {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (j : J) :
    torusPartialDeriv j (c • f) = c • torusPartialDeriv j f := by
  funext z
  exact ((hasDerivAt_torusTranslate_zero hf j z).const_mul c).deriv

/-- The partial derivative `∂ⱼ` as a linear endomorphism of the smooth torus functions. -/
def torusPartialDerivLinear (j : J) :
    smoothFiniteTorusFunctions J →ₗ[ℂ] smoothFiniteTorusFunctions J where
  toFun f := ⟨torusPartialDeriv j f.val, isSmoothFiniteTorusFunction_torusPartialDeriv f.property j⟩
  map_add' f g := Subtype.ext (torusPartialDeriv_add f.property g.property j)
  map_smul' c f := Subtype.ext (torusPartialDeriv_smul c f.property j)

/-- The composite `∂_{j₁} ∘ ⋯ ∘ ∂_{jₖ}` along a list, as a linear endomorphism of the smooth
torus functions. -/
def torusPartialDerivListLinear (l : List J) :
    smoothFiniteTorusFunctions J →ₗ[ℂ] smoothFiniteTorusFunctions J :=
  l.foldr (fun j T => torusPartialDerivLinear j ∘ₗ T) LinearMap.id

@[simp]
theorem torusPartialDerivListLinear_apply (l : List J) (f : smoothFiniteTorusFunctions J) :
    (torusPartialDerivListLinear l f).val = torusPartialDerivList l f.val := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change torusPartialDeriv j (torusPartialDerivListLinear l f).val =
      torusPartialDeriv j (torusPartialDerivList l f.val)
    rw [ih]

end Langlands.HarmonicAnalysis.TorusFourier

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  {J : Type uJ} [Fintype J] [DecidableEq J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G))
  (hK : IsCompact (K : Set G)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

section Seminorms

/-- The scalar coefficient `z ↦ ℓ (R q z)` of a smooth orbit section `q` along a linear
functional `ℓ` on the compact picture, as a smooth torus function. -/
def orbitSectionCoefficient (ℓ : Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)) :
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK →ₗ[ℂ]
      smoothFiniteTorusFunctions J where
  toFun q := ⟨fun z => ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e q z),
    isSmoothFiniteTorusFunction_of_mem_finiteSmoothFamilies
      (mem_finiteSmoothFamilies_linearMap
        (F := productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e q)
        q.property.2 ℓ)⟩
  map_add' q r := by
    apply Subtype.ext
    funext z
    change ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e (q + r) z) =
      ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e q z) +
        ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e r z)
    rw [map_add, Pi.add_apply, map_add]
  map_smul' c q := by
    apply Subtype.ext
    funext z
    change ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e (c • q) z) =
      c * ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e q z)
    rw [map_smul, Pi.smul_apply, map_smul, smul_eq_mul]

omit [DecidableEq J] in
@[simp]
theorem orbitSectionCoefficient_apply
    (ℓ : Module.Dual ℂ (ProductInducedCompactPicture h K π.obj))
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (z : J → Circle) :
    (orbitSectionCoefficient ν π e h hU K hP hK hν hr hPK ℓ q).val z =
      ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e q z) :=
  rfl

/-- The derivative `∂_l (ℓ ∘ R q)` of the coefficient of a smooth orbit section, as a
continuous function on the parameter torus. -/
def orbitSectionDerivative (l : List J)
    (ℓ : Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)) :
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK →ₗ[ℂ] C(J → Circle, ℂ) :=
  smoothTorusToContinuousMap ∘ₗ torusPartialDerivListLinear l ∘ₗ
    orbitSectionCoefficient ν π e h hU K hP hK hν hr hPK ℓ

theorem orbitSectionDerivative_apply (l : List J)
    (ℓ : Module.Dual ℂ (ProductInducedCompactPicture h K π.obj))
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (z : J → Circle) :
    orbitSectionDerivative ν π e h hU K hP hK hν hr hPK l ℓ q z =
      torusPartialDerivList l
        (fun y => ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e q y))
        z := by
  change (torusPartialDerivListLinear l
    (orbitSectionCoefficient ν π e h hU K hP hK hν hr hPK ℓ q)).val z = _
  rw [torusPartialDerivListLinear_apply]
  rfl

/-- The seminorm `q ↦ sup_z |∂_l (ℓ ∘ R q)(z)|` on `C^∞(O,P)`, indexed by a list `l` of
coordinate directions and a linear functional `ℓ` on the compact picture. -/
def orbitSectionSeminorm
    (i : List J × Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)) :
    Seminorm ℂ (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :=
  (normSeminorm ℂ C(J → Circle, ℂ)).comp
    (orbitSectionDerivative ν π e h hU K hP hK hν hr hPK i.1 i.2)

theorem orbitSectionSeminorm_apply
    (i : List J × Module.Dual ℂ (ProductInducedCompactPicture h K π.obj))
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    orbitSectionSeminorm ν π e h hU K hP hK hν hr hPK i q =
      ‖orbitSectionDerivative ν π e h hU K hP hK hν hr hPK i.1 i.2 q‖ :=
  rfl

/-- Every value `|∂_l (ℓ ∘ R q)(z)|` is bounded by the seminorm. -/
theorem norm_torusPartialDerivList_le_orbitSectionSeminorm (l : List J)
    (ℓ : Module.Dual ℂ (ProductInducedCompactPicture h K π.obj))
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (z : J → Circle) :
    ‖torusPartialDerivList l
        (fun y => ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e q y))
        z‖ ≤ orbitSectionSeminorm ν π e h hU K hP hK hν hr hPK (l, ℓ) q := by
  rw [← orbitSectionDerivative_apply, orbitSectionSeminorm_apply]
  exact ContinuousMap.norm_coe_le_norm _ z

/-- The seminorm is the supremum: a nonnegative bound on every value bounds the seminorm. -/
theorem orbitSectionSeminorm_le_iff (l : List J)
    (ℓ : Module.Dual ℂ (ProductInducedCompactPicture h K π.obj))
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) {C : ℝ} (hC : 0 ≤ C) :
    orbitSectionSeminorm ν π e h hU K hP hK hν hr hPK (l, ℓ) q ≤ C ↔
      ∀ z, ‖torusPartialDerivList l
        (fun y => ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e q y))
        z‖ ≤ C := by
  rw [orbitSectionSeminorm_apply, ContinuousMap.norm_le _ hC]
  simp only [orbitSectionDerivative_apply]

/-- The seminorms with the empty list separate the sections. -/
theorem eq_zero_of_forall_orbitSectionDerivative_nil
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (hq : ∀ ℓ : Module.Dual ℂ (ProductInducedCompactPicture h K π.obj),
      orbitSectionDerivative ν π e h hU K hP hK hν hr hPK [] ℓ q = 0) : q = 0 := by
  apply productInducedSmoothOrbitCompactRestriction_injective h hU ν π K hP hK hν hr hPK e
  rw [map_zero]
  funext z
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun ℓ => ?_
  have := congrArg (fun F : C(J → Circle, ℂ) => F z) (hq ℓ)
  simpa [orbitSectionDerivative_apply, torusPartialDerivList] using this

end Seminorms

section Levels

/-- The level `C^∞(O,P)^{H×H}`: smooth orbit sections fixed by the action of `H × H`. -/
def orbitSectionLevelSubmodule (H : OpenSubgroup G) :
    Submodule ℂ (ProductInducedOrbitSections ν π h hU) :=
  productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK ⊓
    Representation.invariants
      ((productInducedOrbitRepresentation h hU ν π).comp (H.prod H).toSubgroup.subtype)

omit [DecidableEq J] in
theorem mem_orbitSectionLevelSubmodule_iff (H : OpenSubgroup G)
    (q : ProductInducedOrbitSections ν π h hU) :
    q ∈ orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H ↔
      q ∈ productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK ∧
        ∀ x : H.prod H, productInducedOrbitRepresentation h hU ν π x q = q :=
  Iff.rfl

omit [DecidableEq J] in
theorem orbitSectionLevelSubmodule_le (H : OpenSubgroup G) :
    orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H ≤
      productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK :=
  inf_le_left

omit [DecidableEq J] in
theorem orbitSectionLevelSubmodule_antitone {H H' : OpenSubgroup G} (hHH' : H' ≤ H) :
    orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H ≤
      orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H' := by
  intro q hq
  refine ⟨hq.1, fun x => ?_⟩
  exact hq.2 ⟨x.val, hHH' x.property.1, hHH' x.property.2⟩

omit [DecidableEq J] in
/-- Every smooth orbit section lies in the level of some open subgroup `H ≤ K`. -/
theorem exists_mem_orbitSectionLevelSubmodule
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    ∃ H : OpenSubgroup G, H ≤ K ∧
      q.val ∈ orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H := by
  obtain ⟨H, hHK, -, hH⟩ :=
    productInducedSmoothOrbitSections_exists_product_stabilizer h hU ν π K hP hK hν hr hPK e q
  exact ⟨H, hHK, q.property, fun x => hH x⟩

omit [DecidableEq J] in
/-- For `H ≤ K`, the compact restriction of a section of the level `C^∞(O,P)^{H×H}` takes its
values in the `H × H`-invariants of the compact picture `L_K`. -/
theorem productInducedCompactRepresentation_orbitSectionCompactRestriction
    (H : OpenSubgroup G) (hHK : H ≤ K)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (hq : q.val ∈ orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H)
    (x : H.prod H) (z : J → Circle) :
    productInducedCompactRepresentation h K π.obj
        ⟨x.val, hHK x.property.1, hHK x.property.2⟩
        (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e q z) =
      productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e q z :=
  (productInducedOrbitRepresentation_restriction h hU ν π K hP hK hν hr hPK e
    ⟨x.val, hHK x.property.1, hHK x.property.2⟩ q.val z).symm.trans
    (congrArg (fun r => productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
      (productInducedOrbitPullback ν π e h hU r) z) (hq.2 x))

/-- The level `C^∞(O,P)^{H×H}` as a type. -/
def OrbitSectionLevel (H : OpenSubgroup G) : Type _ :=
  orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H

/-- The space `C^∞(O,P)` of smooth sections over the orbit, as a type. -/
def OrbitSectionSpace : Type _ :=
  productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK

end Levels

namespace OrbitSectionLevel

variable (H : OpenSubgroup G)

instance : AddCommGroup (OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) :=
  inferInstanceAs (AddCommGroup (orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H))

instance : Module ℂ (OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) :=
  inferInstanceAs (Module ℂ (orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H))

/-- The inclusion of the level into the smooth orbit sections. -/
def toSections :
    OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H →ₗ[ℂ]
      productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK :=
  Submodule.inclusion (orbitSectionLevelSubmodule_le ν π e h hU K hP hK hν hr hPK H)

omit [DecidableEq J] in
theorem toSections_injective :
    Function.Injective (toSections ν π e h hU K hP hK hν hr hPK H) :=
  Submodule.inclusion_injective _

/-- The seminorms `sup_z |∂_l (ℓ ∘ R q)(z)|` restricted to the level. -/
def seminormFamily :
    SeminormFamily ℂ (OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H)
      (List J × Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)) :=
  fun i => (orbitSectionSeminorm ν π e h hU K hP hK hν hr hPK i).comp
    (toSections ν π e h hU K hP hK hν hr hPK H)

/-- The topology of the level `C^∞(O,P)^{H×H}` defined by the seminorms
`sup_z |∂_l (ℓ ∘ R q)(z)|` (Waldspurger VI.3). -/
instance topologicalSpace : TopologicalSpace (OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) :=
  (seminormFamily ν π e h hU K hP hK hν hr hPK H).moduleFilterBasis.topology

theorem withSeminorms : WithSeminorms (seminormFamily ν π e h hU K hP hK hν hr hPK H) :=
  ⟨rfl⟩

instance : IsTopologicalAddGroup (OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) :=
  (withSeminorms ν π e h hU K hP hK hν hr hPK H).isTopologicalAddGroup

instance : ContinuousSMul ℂ (OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) :=
  (withSeminorms ν π e h hU K hP hK hν hr hPK H).continuousSMul

instance : LocallyConvexSpace ℝ (OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) :=
  (withSeminorms ν π e h hU K hP hK hν hr hPK H).toLocallyConvexSpace

/-- Each derivative map `q ↦ ∂_l (ℓ ∘ R q)` is continuous on the level. -/
theorem continuous_orbitSectionDerivative (l : List J)
    (ℓ : Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)) :
    Continuous (orbitSectionDerivative ν π e h hU K hP hK hν hr hPK l ℓ ∘ₗ
      toSections ν π e h hU K hP hK hν hr hPK H) :=
  (norm_withSeminorms ℂ C(J → Circle, ℂ)).continuous_of_continuous_comp _ fun _ =>
    (withSeminorms ν π e h hU K hP hK hν hr hPK H).continuous_seminorm (l, ℓ)

/-- For `H' ≤ H` the inclusion `C^∞(O,P)^{H×H} → C^∞(O,P)^{H'×H'}`. -/
def inclusion {H' : OpenSubgroup G} (hHH' : H' ≤ H) :
    OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H →ₗ[ℂ]
      OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H' :=
  Submodule.inclusion (orbitSectionLevelSubmodule_antitone ν π e h hU K hP hK hν hr hPK hHH')

omit [DecidableEq J] in
theorem toSections_comp_inclusion {H' : OpenSubgroup G} (hHH' : H' ≤ H) :
    toSections ν π e h hU K hP hK hν hr hPK H' ∘ₗ inclusion ν π e h hU K hP hK hν hr hPK H hHH' =
      toSections ν π e h hU K hP hK hν hr hPK H :=
  rfl

/-- For `H' ≤ H` the inclusion `C^∞(O,P)^{H×H} → C^∞(O,P)^{H'×H'}` is continuous. -/
theorem continuous_inclusion {H' : OpenSubgroup G} (hHH' : H' ≤ H) :
    Continuous (inclusion ν π e h hU K hP hK hν hr hPK H hHH') :=
  (withSeminorms ν π e h hU K hP hK hν hr hPK H').continuous_of_continuous_comp _ fun i =>
    (withSeminorms ν π e h hU K hP hK hν hr hPK H).continuous_seminorm i

/-- The level is Hausdorff. -/
instance : T2Space (OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) := by
  let Φ : OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H →
      (Module.Dual ℂ (ProductInducedCompactPicture h K π.obj) → C(J → Circle, ℂ)) :=
    fun q ℓ => (orbitSectionDerivative ν π e h hU K hP hK hν hr hPK [] ℓ ∘ₗ
      toSections ν π e h hU K hP hK hν hr hPK H) q
  refine T2Space.of_injective_continuous (f := Φ) ?_
    (continuous_pi fun ℓ => continuous_orbitSectionDerivative ν π e h hU K hP hK hν hr hPK H [] ℓ)
  intro q r hqr
  apply toSections_injective ν π e h hU K hP hK hν hr hPK H
  rw [← sub_eq_zero, ← map_sub]
  refine eq_zero_of_forall_orbitSectionDerivative_nil ν π e h hU K hP hK hν hr hPK _ fun ℓ => ?_
  rw [map_sub, map_sub, sub_eq_zero]
  exact congrFun hqr ℓ

end OrbitSectionLevel

namespace OrbitSectionSpace

instance : AddCommGroup (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) :=
  inferInstanceAs (AddCommGroup (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK))

instance : Module ℂ (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) :=
  inferInstanceAs (Module ℂ (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK))

/-- The identification of `OrbitSectionSpace` with the smooth orbit sections. -/
def toSections :
    OrbitSectionSpace ν π e h hU K hP hK hν hr hPK →ₗ[ℂ]
      productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK :=
  LinearMap.id

/-- The inclusion `C^∞(O,P)^{H×H} → C^∞(O,P)` of a level. -/
def ofLevel (H : OpenSubgroup G) :
    OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H →ₗ[ℂ]
      OrbitSectionSpace ν π e h hU K hP hK hν hr hPK :=
  OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H

omit [DecidableEq J] in
theorem toSections_ofLevel (H : OpenSubgroup G) :
    toSections ν π e h hU K hP hK hν hr hPK ∘ₗ ofLevel ν π e h hU K hP hK hν hr hPK H =
      OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H :=
  rfl

omit [DecidableEq J] in
/-- Every element of `C^∞(O,P)` comes from the level of some open subgroup `H ≤ K`. -/
theorem exists_ofLevel (q : OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) :
    ∃ H : {H : OpenSubgroup G // H ≤ K},
      ∃ q' : OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H.1,
        ofLevel ν π e h hU K hP hK hν hr hPK H.1 q' = q := by
  obtain ⟨H, hHK, hq⟩ := exists_mem_orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK q
  exact ⟨⟨H, hHK⟩, ⟨q.val, hq⟩, rfl⟩

/-- The inductive-limit topology in the category of topological spaces: the finest topology
making every inclusion `C^∞(O,P)^{H×H} → C^∞(O,P)`, `H ≤ K` open, continuous. -/
@[instance_reducible]
def originalTop : TopologicalSpace (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) :=
  ⨆ H : {H : OpenSubgroup G // H ≤ K},
    coinduced (ofLevel ν π e h hU K hP hK hν hr hPK H.1) inferInstance

/-- The topology of `C^∞(O,P)`: the locally convex inductive limit of the topologies of the
levels `C^∞(O,P)^{H×H}`, `H` compact open in `K` (Waldspurger VI.3). It is the infimum of all
locally convex vector-space topologies coarser than `originalTop`. -/
instance topologicalSpace : TopologicalSpace (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) :=
  sInf {t : TopologicalSpace (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) |
    originalTop ν π e h hU K hP hK hν hr hPK ≤ t ∧
    @IsTopologicalAddGroup (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) t _ ∧
    @ContinuousSMul ℂ (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) _ _ t ∧
    @LocallyConvexSpace ℝ (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) _ _ _ _ t}

instance : IsTopologicalAddGroup (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) :=
  isTopologicalAddGroup_sInf fun _ ⟨_, ht, _, _⟩ ↦ ht

instance : ContinuousSMul ℂ (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) :=
  continuousSMul_sInf fun _ ⟨_, _, ht, _⟩ ↦ ht

instance : LocallyConvexSpace ℝ (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) :=
  .sInf fun _ ⟨_, _, _, ht⟩ ↦ ht

theorem originalTop_le :
    originalTop ν π e h hU K hP hK hν hr hPK ≤ topologicalSpace ν π e h hU K hP hK hν hr hPK :=
  le_sInf fun _t ⟨ht, _⟩ ↦ ht

/-- A locally convex vector-space topology on `C^∞(O,P)` is coarser than the inductive-limit
topology if and only if it is coarser than `originalTop`. -/
theorem topologicalSpace_le_iff {t : TopologicalSpace (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK)}
    [@IsTopologicalAddGroup _ t _] [@ContinuousSMul ℂ _ _ _ t]
    [@LocallyConvexSpace ℝ _ _ _ _ _ t] :
    topologicalSpace ν π e h hU K hP hK hν hr hPK ≤ t ↔
      originalTop ν π e h hU K hP hK hν hr hPK ≤ t :=
  ⟨le_trans (originalTop_le ν π e h hU K hP hK hν hr hPK),
    fun H ↦ sInf_le ⟨H, inferInstance, inferInstance, inferInstance⟩⟩

/-- Every inclusion `C^∞(O,P)^{H×H} → C^∞(O,P)`, `H ≤ K`, is continuous. -/
theorem continuous_ofLevel (H : {H : OpenSubgroup G // H ≤ K}) :
    Continuous (ofLevel ν π e h hU K hP hK hν hr hPK H.1) := by
  rw [continuous_iff_coinduced_le]
  exact le_trans (le_iSup_of_le H le_rfl) (originalTop_le ν π e h hU K hP hK hν hr hPK)

/-- The inclusion of a level as a continuous linear map. -/
def ofLevelCLM (H : {H : OpenSubgroup G // H ≤ K}) :
    OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H.1 →L[ℂ]
      OrbitSectionSpace ν π e h hU K hP hK hν hr hPK where
  toLinearMap := ofLevel ν π e h hU K hP hK hν hr hPK H.1
  cont := continuous_ofLevel ν π e h hU K hP hK hν hr hPK H

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
  [t : TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
  [LocallyConvexSpace ℝ V]

/-- The universal property of the inductive limit: a linear map from `C^∞(O,P)` to a locally
convex complex topological vector space is continuous if and only if its restriction to every
level `C^∞(O,P)^{H×H}`, `H ≤ K` open, is continuous. -/
theorem continuous_iff_continuous_comp
    (T : OrbitSectionSpace ν π e h hU K hP hK hν hr hPK →ₗ[ℂ] V) :
    Continuous T ↔ ∀ H : {H : OpenSubgroup G // H ≤ K},
      Continuous (T ∘ ofLevel ν π e h hU K hP hK hν hr hPK H.1) := by
  rw [continuous_iff_le_induced]
  have : @IsTopologicalAddGroup _ (induced T t) _ := isTopologicalAddGroup_induced T
  have : @ContinuousSMul ℂ _ _ _ (induced T t) := continuousSMul_induced T
  have : @LocallyConvexSpace ℝ _ _ _ _ _ (induced T t) :=
    LocallyConvexSpace.induced (T.restrictScalars ℝ)
  rw [topologicalSpace_le_iff, originalTop, iSup_le_iff]
  simp_rw [← continuous_iff_le_induced, continuous_coinduced_dom]

/-- Construct a continuous linear map on `C^∞(O,P)` from continuity on every level. -/
def mkCLM (T : OrbitSectionSpace ν π e h hU K hP hK hν hr hPK →ₗ[ℂ] V)
    (hT : ∀ H : {H : OpenSubgroup G // H ≤ K},
      Continuous (T ∘ ofLevel ν π e h hU K hP hK hν hr hPK H.1)) :
    OrbitSectionSpace ν π e h hU K hP hK hν hr hPK →L[ℂ] V where
  toLinearMap := T
  cont := (continuous_iff_continuous_comp ν π e h hU K hP hK hν hr hPK T).mpr hT

@[simp] theorem coe_mkCLM (T : OrbitSectionSpace ν π e h hU K hP hK hν hr hPK →ₗ[ℂ] V)
    (hT : ∀ H : {H : OpenSubgroup G // H ≤ K},
      Continuous (T ∘ ofLevel ν π e h hU K hP hK hν hr hPK H.1)) :
    (mkCLM ν π e h hU K hP hK hν hr hPK T hT : OrbitSectionSpace ν π e h hU K hP hK hν hr hPK → V) =
      T :=
  rfl

/-- Each derivative map `q ↦ ∂_l (ℓ ∘ R q)` is continuous on `C^∞(O,P)`. -/
theorem continuous_orbitSectionDerivative (l : List J)
    (ℓ : Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)) :
    Continuous (orbitSectionDerivative ν π e h hU K hP hK hν hr hPK l ℓ ∘ₗ
      toSections ν π e h hU K hP hK hν hr hPK) :=
  (continuous_iff_continuous_comp ν π e h hU K hP hK hν hr hPK _).mpr fun H =>
    OrbitSectionLevel.continuous_orbitSectionDerivative ν π e h hU K hP hK hν hr hPK H.1 l ℓ

/-- Each seminorm `q ↦ sup_z |∂_l (ℓ ∘ R q)(z)|` is continuous on `C^∞(O,P)`. -/
theorem continuous_orbitSectionSeminorm
    (i : List J × Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)) :
    Continuous fun q : OrbitSectionSpace ν π e h hU K hP hK hν hr hPK =>
      orbitSectionSeminorm ν π e h hU K hP hK hν hr hPK i (toSections ν π e h hU K hP hK hν hr hPK q) :=
  continuous_norm.comp
    (continuous_orbitSectionDerivative ν π e h hU K hP hK hν hr hPK i.1 i.2)

/-- The topology of `C^∞(O,P)` is Hausdorff. -/
instance : T2Space (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) := by
  let Φ : OrbitSectionSpace ν π e h hU K hP hK hν hr hPK →
      (Module.Dual ℂ (ProductInducedCompactPicture h K π.obj) → C(J → Circle, ℂ)) :=
    fun q ℓ => (orbitSectionDerivative ν π e h hU K hP hK hν hr hPK [] ℓ ∘ₗ
      toSections ν π e h hU K hP hK hν hr hPK) q
  refine T2Space.of_injective_continuous (f := Φ) ?_
    (continuous_pi fun ℓ => continuous_orbitSectionDerivative ν π e h hU K hP hK hν hr hPK [] ℓ)
  intro q r hqr
  change toSections ν π e h hU K hP hK hν hr hPK q = toSections ν π e h hU K hP hK hν hr hPK r
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_orbitSectionDerivative_nil ν π e h hU K hP hK hν hr hPK _ fun ℓ => ?_
  rw [map_sub, sub_eq_zero]
  exact congrFun hqr ℓ

end OrbitSectionSpace

end Langlands.HarishChandraSchwartz
