import Langlands.LocalFactor.Ramification.Herbrand.TransportProof
import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.Weil.Local.IntermediateWeil
import Langlands.VirtualRepresentation.Weil.Ramification
import Mathlib.FieldTheory.Normal.Closure

/-!
# Herbrand's theorem for finite subextensions

For a tower `K → E → L` with `L/K` Galois, an automorphism of `L` over `E` lies in
the upper group of `L/K` of index `v` exactly when it lies in the upper group of
`L/E` of index `φ_{L/E}(ψ_{L/K}(v))`. This relative index does not change when
`L` is enlarged, which defines the relative inverse Herbrand function of a finite
subextension. The absolute upper groups of the base and of the subextension are
then compared inside one algebraic closure.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace Langlands.Ramification.HerbrandBridge

open _root_.Langlands.Ramification.Padic

universe u uK uE uL uM

section FiniteSubfield

variable {p : ℕ} [Fact p.Prime] (K : Type uK) [Field K] [Algebra (Padic p) K]
  (E : Type uE) [Field E] [Algebra (Padic p) E] {L : PadicField.{uL} p}
  [Algebra K E] [Algebra E L.Carrier] [Algebra K L.Carrier]
  [IsScalarTower K E L.Carrier]
  [IsScalarTower (Padic p) K L.Carrier] [IsScalarTower (Padic p) E L.Carrier]
  (T : L.TopologicalData)

/-- Lower groups over a subfield are the restrictions of the lower groups over the base. -/
theorem restrictScalars_mem_lowerRamificationGroupInt_iff (i : ℤ) (σ : Gal(L.Carrier/E)) :
    σ.restrictScalars K ∈ Padic.lowerRamificationGroupInt T K i ↔
      σ ∈ Padic.lowerRamificationGroupInt T E i := by
  have h₁ : Padic.lowerRamificationGroupInt T K i =
      if i < 0 then ⊤ else Padic.lowerRamificationGroup T K i.toNat := rfl
  have h₂ : Padic.lowerRamificationGroupInt T E i =
      if i < 0 then ⊤ else Padic.lowerRamificationGroup T E i.toNat := rfl
  rw [h₁, h₂]
  split_ifs
  · simp
  · exact Iff.rfl

/-- Herbrand's subgroup formula in upper numbering. -/
theorem restrictScalars_mem_upperRamificationGroup_iff (v : ℝ) (σ : Gal(L.Carrier/E)) :
    σ.restrictScalars K ∈ Padic.upperRamificationGroup T K v ↔
      σ ∈ Padic.upperRamificationGroup T E
        (Padic.herbrandPhi T E (Padic.herbrandPsi T K v)) := by
  rw [Padic.upperRamificationGroup_eq_lower, Padic.upperRamificationGroup_eq_lower,
    Padic.herbrandPsi_herbrandPhi]
  exact restrictScalars_mem_lowerRamificationGroupInt_iff K E T _ σ

end FiniteSubfield

section Independence

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (E : PadicField.{uE} p)
  (M : PadicField.{uM} p) (L : PadicField.{uL} p)
  [Algebra K.Carrier M.Carrier] [Algebra K.Carrier L.Carrier]
  [Algebra E.Carrier M.Carrier] [Algebra E.Carrier L.Carrier] [Algebra M.Carrier L.Carrier]
  [IsScalarTower K.Carrier M.Carrier L.Carrier] [IsScalarTower E.Carrier M.Carrier L.Carrier]
  [IsScalarTower (Padic p) K.Carrier M.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
  [IsScalarTower (Padic p) E.Carrier M.Carrier] [IsScalarTower (Padic p) E.Carrier L.Carrier]
  [IsScalarTower (Padic p) M.Carrier L.Carrier]
  [IsGalois K.Carrier M.Carrier] [IsGalois K.Carrier L.Carrier] [IsGalois M.Carrier L.Carrier]
  [IsGalois E.Carrier M.Carrier] [IsGalois E.Carrier L.Carrier]
  (S : M.TopologicalData) (T : L.TopologicalData)

/-- The relative index `φ_{L/E} ∘ ψ_{L/K}` does not change when `M` is enlarged to `L`. -/
theorem relativeHerbrandPsi_tower (v : ℝ) :
    Padic.herbrandPhi T E.Carrier (Padic.herbrandPsi T K.Carrier v) =
      Padic.herbrandPhi S E.Carrier (Padic.herbrandPsi S K.Carrier v) := by
  rw [herbrandPsi_tower K L M T S v, herbrandPhi_tower E L M T S, Padic.herbrandPhi_herbrandPsi]

end Independence

section Cofinal

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
  {Ω : Type uL} [Field Ω] [Algebra K.Carrier Ω] [Algebra (Padic p) Ω]
  [IsScalarTower (Padic p) K.Carrier Ω]

/-- Restriction from a larger finite Galois subfield preserves upper groups. -/
theorem restrictNormalHom_mem_upper_of_le {N M : FiniteGaloisIntermediateField K.Carrier Ω}
    (h : N ≤ M) {v : ℝ} (hv : -1 ≤ v) (τ : Gal(Ω/K.Carrier))
    (hτ : AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω) M τ ∈
      canonicalUpperRamificationGroup (finiteGaloisPadicField K M) K.Carrier v) :
    AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω) N τ ∈
      canonicalUpperRamificationGroup (finiteGaloisPadicField K N) K.Carrier v := by
  let : Algebra N M := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower K.Carrier N M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (Padic p) N M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower N M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois N M := IsGalois.tower_top_of_isGalois K.Carrier N M
  have hmap := upperRestrictionCompatibility K (finiteGaloisPadicField K M)
    (finiteGaloisPadicField K N) (finiteGaloisPadicField K M).canonicalTopologicalData
    (finiteGaloisPadicField K N).canonicalTopologicalData v hv
  have heq : AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := M) N
      (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω) M τ) =
      AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω) N τ := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    have h1 := AlgEquiv.restrictNormal_commutes
      (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω) M τ) N x
    have h2 := AlgEquiv.restrictNormal_commutes τ M (algebraMap N M x)
    have h3 := AlgEquiv.restrictNormal_commutes τ N x
    have h1' := congrArg (fun y : M => (y : Ω)) h1
    rw [AlgEquiv.restrictNormalHom_apply N.toIntermediateField τ x]
    exact h1'.trans
      (AlgEquiv.restrictNormalHom_apply M.toIntermediateField τ (algebraMap N M x))
  rw [← heq]
  change _ ∈ canonicalUpperRamificationGroup (finiteGaloisPadicField K N) K.Carrier v
  rw [canonicalUpperRamificationGroup, ← hmap]
  exact Subgroup.mem_map_of_mem _ hτ

/-- Membership in `upperGroupIn` may be tested on any cofinal family of finite Galois
subfields. -/
theorem mem_upperGroupIn_iff_of_cofinal (P : FiniteGaloisIntermediateField K.Carrier Ω → Prop)
    (hP : ∀ N, ∃ M, N ≤ M ∧ P M) {v : ℝ} (hv : -1 ≤ v) (τ : Gal(Ω/K.Carrier)) :
    τ ∈ upperGroupIn K Ω v ↔ ∀ M, P M →
      AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω) M τ ∈
        canonicalUpperRamificationGroup (finiteGaloisPadicField K M) K.Carrier v := by
  rw [mem_upperGroupIn_iff]
  refine ⟨fun h M _ => h M, fun h N => ?_⟩
  obtain ⟨M, hNM, hM⟩ := hP N
  exact restrictNormalHom_mem_upper_of_le K hNM hv τ (h M hM)

end Cofinal

section Subextension

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uK} p) (K : PadicField.{uE} p)
  {Ω : Type uL} [Field Ω] [Algebra F.Carrier Ω] [Algebra K.Carrier Ω] [Algebra (Padic p) Ω]
  [Algebra F.Carrier K.Carrier] [IsScalarTower F.Carrier K.Carrier Ω]
  [IsScalarTower (Padic p) F.Carrier Ω] [IsScalarTower (Padic p) K.Carrier Ω]

variable {F K} in
/-- A finite Galois subfield over `F` containing the image of `K`, viewed over `K`. -/
def extendFiniteGalois {M : FiniteGaloisIntermediateField F.Carrier Ω}
    (h : ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M.toIntermediateField) :
    FiniteGaloisIntermediateField K.Carrier Ω :=
  have : FiniteDimensional F.Carrier (M.toIntermediateField.toSubfield.toIntermediateField h) :=
    M.finiteDimensional
  have : IsGalois F.Carrier (M.toIntermediateField.toSubfield.toIntermediateField h) :=
    M.isGalois
  { toIntermediateField := M.toIntermediateField.toSubfield.toIntermediateField h
    finiteDimensional := Module.Finite.of_restrictScalars_finite F.Carrier _ _
    isGalois := IsGalois.tower_top_of_isGalois F.Carrier K.Carrier _ }

variable {F K} in
/-- The identity of carriers, as an isomorphism over the base. -/
def extendFiniteGaloisEquiv {M : FiniteGaloisIntermediateField F.Carrier Ω}
    (h : ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M.toIntermediateField) :
    (finiteGaloisPadicField F M).Carrier ≃ₐ[F.Carrier]
      (finiteGaloisPadicField K (extendFiniteGalois h)).Carrier where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨x, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The p-adic tower through the base for a finite Galois subfield over `K`. -/
theorem extension_padicScalarTower (N : FiniteGaloisIntermediateField K.Carrier Ω) :
    IsScalarTower (Padic p) F.Carrier (finiteGaloisPadicField K N).Carrier :=
  IsScalarTower.of_algebraMap_eq fun q => Subtype.ext
    (IsScalarTower.algebraMap_apply (Padic p) F.Carrier Ω q)

attribute [local instance] extension_padicScalarTower

variable {K} in
/-- The relative index `φ_{M/K} ∘ ψ_{M/F}` computed in a finite Galois field `M ⊇ K`. -/
def relativeIndex (M : FiniteGaloisIntermediateField F.Carrier Ω)
    (h : ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M.toIntermediateField) (v : ℝ) : ℝ :=
  Padic.herbrandPhi (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData
    K.Carrier
    (Padic.herbrandPsi (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData
      F.Carrier v)

/-- Herbrand's subgroup formula inside one finite Galois field `M ⊇ K`. -/
theorem restrictNormalHom_restrictScalars_mem_upper_iff
    (M : FiniteGaloisIntermediateField F.Carrier Ω)
    (h : ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M.toIntermediateField)
    (τ : Gal(Ω/K.Carrier)) (v : ℝ) :
    AlgEquiv.restrictNormalHom (F := F.Carrier) (K₁ := Ω) M (τ.restrictScalars F.Carrier) ∈
      canonicalUpperRamificationGroup (finiteGaloisPadicField F M) F.Carrier v ↔
    AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω) (extendFiniteGalois h) τ ∈
      canonicalUpperRamificationGroup (finiteGaloisPadicField K (extendFiniteGalois h)) K.Carrier
        (relativeIndex F M h v) := by
  set f := extendFiniteGaloisEquiv h
  have key : f.autCongr (AlgEquiv.restrictNormalHom (F := F.Carrier) (K₁ := Ω) M
      (τ.restrictScalars F.Carrier)) =
      (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω) (extendFiniteGalois h)
        τ).restrictScalars F.Carrier := by
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    change (AlgEquiv.restrictNormalHom M.toIntermediateField (τ.restrictScalars F.Carrier)
      (f.symm y) : Ω) =
      (AlgEquiv.restrictNormalHom (extendFiniteGalois h).toIntermediateField τ y : Ω)
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
    rfl
  unfold canonicalUpperRamificationGroup
  rw [← autCongr_mem_upperRamificationGroup_iff
    (finiteGaloisPadicField F M).canonicalTopologicalData
    (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData
    F.Carrier f v, key]
  exact restrictScalars_mem_upperRamificationGroup_iff F.Carrier K.Carrier
    (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData v _

variable {F K} in
/-- The relative index does not change when the finite Galois field is enlarged. -/
theorem relativeIndex_eq_of_le {M₀ M : FiniteGaloisIntermediateField F.Carrier Ω} (hle : M₀ ≤ M)
    (h₀ : ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M₀.toIntermediateField)
    (h : ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M.toIntermediateField) (v : ℝ) :
    relativeIndex F M h v = relativeIndex F M₀ h₀ v := by
  set N₀ := extendFiniteGalois h₀
  set N := extendFiniteGalois h
  have hN : N₀.toIntermediateField ≤ N.toIntermediateField := fun x hx => hle hx
  let : Algebra N₀ N := (IntermediateField.inclusion hN).toRingHom.toAlgebra
  let : IsScalarTower F.Carrier N₀ N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower K.Carrier N₀ N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (Padic p) N₀ N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois F.Carrier N₀ := M₀.isGalois
  have : IsGalois F.Carrier N := M.isGalois
  have : IsGalois N₀ N := IsGalois.tower_top_of_isGalois F.Carrier N₀ N
  exact relativeHerbrandPsi_tower F K (finiteGaloisPadicField K N₀) (finiteGaloisPadicField K N)
    (finiteGaloisPadicField K N₀).canonicalTopologicalData
    (finiteGaloisPadicField K N).canonicalTopologicalData v

variable {F K} in
/-- The relative index fixes the left endpoint `-1` and is monotone. -/
theorem neg_one_le_relativeIndex {M : FiniteGaloisIntermediateField F.Carrier Ω}
    (h : ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M.toIntermediateField) {v : ℝ}
    (hv : -1 ≤ v) : -1 ≤ relativeIndex F M h v := by
  have h1 := (Padic.herbrandPsi_strictMono
    (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData F.Carrier).monotone hv
  have h2 := (Padic.herbrandPhi_strictMono
    (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData K.Carrier).monotone h1
  rw [Padic.herbrandPsi_neg_one, Padic.herbrandPhi_neg_one] at h2
  exact h2

variable {F K} in
/-- Every finite Galois subfield over `K` lies in a finite Galois subfield over `F` containing
any given one. -/
theorem exists_le_of_finiteGalois [IsGalois F.Carrier Ω]
    (M₀ : FiniteGaloisIntermediateField F.Carrier Ω)
    (N : FiniteGaloisIntermediateField K.Carrier Ω) :
    ∃ M : FiniteGaloisIntermediateField F.Carrier Ω, M₀ ≤ M ∧
      ∀ x ∈ N.toIntermediateField, x ∈ M.toIntermediateField := by
  have : IsScalarTower (Padic p) F.Carrier K.Carrier := IsScalarTower.of_algebraMap_eq fun q => by
    apply (algebraMap K.Carrier Ω).injective
    simp only [← IsScalarTower.algebraMap_apply]
  have : FiniteDimensional F.Carrier K.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) F.Carrier K.Carrier
  have : FiniteDimensional F.Carrier N := FiniteDimensional.trans F.Carrier K.Carrier N
  have : IsScalarTower F.Carrier N Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let M₁ : FiniteGaloisIntermediateField F.Carrier Ω :=
    { toIntermediateField := IntermediateField.normalClosure F.Carrier N Ω
      finiteDimensional := normalClosure.is_finiteDimensional F.Carrier N Ω
      isGalois := IsGalois.normalClosure F.Carrier N Ω }
  refine ⟨M₁ ⊔ M₀, le_sup_right, fun x hx => ?_⟩
  have h1 : x ∈ IntermediateField.normalClosure F.Carrier N Ω :=
    (IsScalarTower.toAlgHom F.Carrier N Ω).fieldRange_le_normalClosure ⟨⟨x, hx⟩, rfl⟩
  exact ((FiniteGaloisIntermediateField.le_iff M₁ (M₁ ⊔ M₀)).mp le_sup_left) h1

variable {F K} in
/-- Herbrand's theorem for a finite subextension: the upper filtration of `F` restricted to
`Gal(Ω/K)` is the upper filtration of `K`, reindexed by the relative index. -/
theorem restrictScalars_mem_upperGroupIn_iff [IsGalois F.Carrier Ω]
    {M₀ : FiniteGaloisIntermediateField F.Carrier Ω}
    (h₀ : ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M₀.toIntermediateField)
    {v : ℝ} (hv : -1 ≤ v) (τ : Gal(Ω/K.Carrier)) :
    τ.restrictScalars F.Carrier ∈ upperGroupIn F Ω v ↔
      τ ∈ upperGroupIn K Ω (relativeIndex F M₀ h₀ v) := by
  have hM : ∀ {M : FiniteGaloisIntermediateField F.Carrier Ω}, M₀ ≤ M →
      ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M.toIntermediateField :=
    fun hle x => hle (h₀ x)
  rw [mem_upperGroupIn_iff_of_cofinal F (fun M => M₀ ≤ M)
    (fun N => ⟨N ⊔ M₀, le_sup_left, le_sup_right⟩) hv, mem_upperGroupIn_iff]
  constructor
  · intro H N
    obtain ⟨M, hle, hNM⟩ := exists_le_of_finiteGalois M₀ N
    have h1 := (restrictNormalHom_restrictScalars_mem_upper_iff F K M (hM hle) τ v).mp (H M hle)
    rw [relativeIndex_eq_of_le hle h₀ (hM hle)] at h1
    exact restrictNormalHom_mem_upper_of_le K
      ((FiniteGaloisIntermediateField.le_iff _ _).mpr fun x hx => hNM x hx)
      (neg_one_le_relativeIndex h₀ hv) τ h1
  · intro H M hle
    apply (restrictNormalHom_restrictScalars_mem_upper_iff F K M (hM hle) τ v).mpr
    rw [relativeIndex_eq_of_le hle h₀ (hM hle)]
    exact H (extendFiniteGalois (hM hle))

end Subextension

section ClosureChange

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
  {Ω : Type uL} [Field Ω] [Algebra K.Carrier Ω] [Algebra (Padic p) Ω]
  [IsScalarTower (Padic p) K.Carrier Ω]

/-- The absolute upper groups, computed in another algebraic closure of the base. -/
theorem mem_absoluteUpperRamificationGroup_iff_autCongr
    (e : AlgebraicClosure K.Carrier ≃ₐ[K.Carrier] Ω) (v : ℝ)
    (τ : Field.absoluteGaloisGroup K.Carrier) :
    τ ∈ absoluteUpperRamificationGroup K v ↔ e.autCongr τ ∈ upperGroupIn K Ω v :=
  (autCongr_mem_upperGroupIn_iff K e v τ).symm

end ClosureChange

section Intermediate

open LocalClassField Weil.Local

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
  (E : FiniteIntermediateExtension F.Carrier)

/-- The p-adic scalar tower of a finite intermediate field inside the algebraic closure, for
its p-adic structure as `E.asPadicField`. -/
theorem asPadicField_isScalarTower :
    letI : Algebra (Padic p) (E.asPadicField (p := p)).Carrier := (E.asPadicField (p := p)).algebra
    IsScalarTower (Padic p) (E.asPadicField (p := p)).Carrier (AlgebraicClosure F.Carrier) :=
  letI : Algebra (Padic p) (E.asPadicField (p := p)).Carrier := (E.asPadicField (p := p)).algebra
  IsScalarTower.of_algebraMap_eq fun q =>
    IsScalarTower.algebraMap_apply (Padic p) F.Carrier (AlgebraicClosure F.Carrier) q

attribute [local instance] asPadicField_isScalarTower

/-- The Galois closure of a finite intermediate field over the base, inside the closure. -/
def galoisClosure : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  { toIntermediateField :=
      IntermediateField.normalClosure F.Carrier E.field (AlgebraicClosure F.Carrier)
    finiteDimensional := normalClosure.is_finiteDimensional F.Carrier E.field _
    isGalois := IsGalois.normalClosure F.Carrier E.field _ }

theorem algebraMap_mem_galoisClosure (x : (E.asPadicField (p := p)).Carrier) :
    algebraMap (E.asPadicField (p := p)).Carrier (AlgebraicClosure F.Carrier) x ∈
      (galoisClosure E).toIntermediateField :=
  IntermediateField.le_normalClosure E.field x.2

/-- The relative inverse Herbrand function `ψ_{E/F}` of a finite intermediate field,
computed in its Galois closure. -/
def relativeHerbrandPsi (v : ℝ) : ℝ :=
  relativeIndex F (galoisClosure E) (algebraMap_mem_galoisClosure E) v

theorem neg_one_le_relativeHerbrandPsi {v : ℝ} (hv : -1 ≤ v) :
    -1 ≤ relativeHerbrandPsi E v :=
  neg_one_le_relativeIndex _ hv

/-- Herbrand's theorem for the absolute Galois group of a finite intermediate field:
`G_F^v ∩ G_E = G_E^{ψ_{E/F}(v)}` along the prescribed Galois map. -/
theorem intermediateGaloisMap_mem_absoluteUpperRamificationGroup_iff {v : ℝ} (hv : -1 ≤ v)
    (τ : Field.absoluteGaloisGroup E.field) :
    intermediateGaloisMap F E τ ∈ absoluteUpperRamificationGroup F v ↔
      τ ∈ absoluteUpperRamificationGroup (E.asPadicField (p := p)) (relativeHerbrandPsi E v) := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  set e := intermediateClosureEquiv F E
  have key : intermediateGaloisMap F E τ =
      (e.autCongr τ).restrictScalars F.Carrier :=
    AlgEquiv.ext fun x => intermediateGaloisMap_apply F E τ x
  rw [key]
  exact (restrictScalars_mem_upperGroupIn_iff (algebraMap_mem_galoisClosure E) hv
    (e.autCongr τ)).trans
      (mem_absoluteUpperRamificationGroup_iff_autCongr (E.asPadicField (p := p)) e _ τ).symm

/-- The same statement for the actual upper groups of the local Weil groups, along the
identification of the Weil group of `E` with its fixing subgroup. -/
theorem intermediateWeilEquiv_mem_upperGroup_iff {v : ℝ} (hv : -1 ≤ v)
    (w : localWeilGroup (E.asPadicField (p := p))) :
    (intermediateWeilEquiv F E w : localWeilGroup F) ∈
        VirtualRepresentation.LocalWeil.Ramification.upperGroup F v ↔
      w ∈ VirtualRepresentation.LocalWeil.Ramification.upperGroup (E.asPadicField (p := p))
        (relativeHerbrandPsi E v) :=
  intermediateGaloisMap_mem_absoluteUpperRamificationGroup_iff E hv
    (localProjection (E.asPadicField (p := p)) w)

end Intermediate

end Langlands.Ramification.HerbrandBridge
