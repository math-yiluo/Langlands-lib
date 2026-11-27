import Langlands.BushnellKutzko.DefiningSequenceTransport
import Langlands.BushnellKutzko.SimpleCharacters

/-! # Covariance of simple characters under a linear automorphism

For an `F`-linear automorphism `f` of `V`, conjugation by `f` carries the sets of simple
characters `C(𝔄,m,β)` of BK93 (3.2.1), (3.2.3), computed from the tail of a defining
sequence, to the sets computed from the conjugated data: a character `θ` of `H^{m+1}` lies
in the old set exactly when the character `fhf⁻¹ ↦ θ(h)` of the conjugated group lies in the
new one. The inputs are the invariance of the trace and of the relative determinant
`det_{F[β]}` under conjugation, and the covariance of the groups `H^{m+1}`.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-! ### Characters of corresponding subgroups -/

section Group

variable {G : Type*} [Group G]

/-- The character `θ'` of `H'` corresponds to the character `θ` of `H` under the
automorphism `φ`: `θ'(φ x) = θ(x)`. -/
def CharacterCorresponds (φ : G ≃* G) {H H' : Subgroup G} (θ : H →* ℂˣ) (θ' : H' →* ℂˣ) :
    Prop :=
  ∀ (x : G) (hx : x ∈ H) (hx' : φ x ∈ H'), θ' ⟨φ x, hx'⟩ = θ ⟨x, hx⟩

theorem mem_map_mulEquiv_iff (φ : G ≃* G) (H : Subgroup G) (x : G) :
    φ x ∈ H.map φ.toMonoidHom ↔ x ∈ H := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem exists_characterCorresponds (φ : G ≃* G) {H H' : Subgroup G}
    (hH : H' = H.map φ.toMonoidHom) (θ : H →* ℂˣ) :
    ∃ θ' : H' →* ℂˣ, CharacterCorresponds φ θ θ' := by
  subst hH
  let e : H ≃* H.map φ.toMonoidHom := H.equivMapOfInjective φ.toMonoidHom φ.injective
  refine ⟨θ.comp e.symm.toMonoidHom, fun x hx hx' => ?_⟩
  change θ (e.symm ⟨φ x, hx'⟩) = θ ⟨x, hx⟩
  congr 1
  rw [MulEquiv.symm_apply_eq]
  rfl

theorem exists_characterCorresponds_symm (φ : G ≃* G) {H H' : Subgroup G}
    (hH : H' = H.map φ.toMonoidHom) (θ' : H' →* ℂˣ) :
    ∃ θ : H →* ℂˣ, CharacterCorresponds φ θ θ' := by
  subst hH
  let e : H ≃* H.map φ.toMonoidHom := H.equivMapOfInjective φ.toMonoidHom φ.injective
  exact ⟨θ'.comp e.toMonoidHom, fun x hx hx' => rfl⟩

/-- Universal statements over corresponding subgroups correspond. -/
theorem forall_subgroup_congr (φ : G ≃* G) {H H' : Subgroup G}
    (hH : ∀ x, φ x ∈ H' ↔ x ∈ H) {P : H → Prop} {P' : H' → Prop}
    (hP : ∀ (x : G) (hx : x ∈ H) (hx' : φ x ∈ H'), P' ⟨φ x, hx'⟩ ↔ P ⟨x, hx⟩) :
    (∀ y, P' y) ↔ ∀ y, P y := by
  constructor
  · intro h y
    exact (hP y y.2 ((hH y).2 y.2)).1 (h _)
  · intro h y
    have hy : φ.symm y ∈ H := by
      rw [← hH, MulEquiv.apply_symm_apply]
      exact y.2
    have h' := (hP (φ.symm y) hy ((hH _).2 hy)).2 (h ⟨_, hy⟩)
    have hyy : (⟨φ (φ.symm y), (hH _).2 hy⟩ : H') = y := Subtype.ext (MulEquiv.apply_symm_apply _ _)
    rwa [hyy] at h'

theorem characterAgreesOn_iff (φ : G ≃* G) {K K' H₁ H₁' H₂ H₂' : Subgroup G}
    (hK : ∀ x, φ x ∈ K' ↔ x ∈ K) (hH₁ : ∀ x, φ x ∈ H₁' ↔ x ∈ H₁)
    (hH₂ : ∀ x, φ x ∈ H₂' ↔ x ∈ H₂) {χ₁ : H₁ →* ℂˣ} {χ₁' : H₁' →* ℂˣ} {χ₂ : H₂ →* ℂˣ}
    {χ₂' : H₂' →* ℂˣ} (h₁ : CharacterCorresponds φ χ₁ χ₁')
    (h₂ : CharacterCorresponds φ χ₂ χ₂') {tw tw' : G → ℂ} (htw : ∀ x, tw' (φ x) = tw x) :
    characterAgreesOn K' χ₁' χ₂' tw' ↔ characterAgreesOn K χ₁ χ₂ tw := by
  unfold characterAgreesOn
  refine forall_subgroup_congr φ hK fun x hx hx' => ?_
  constructor
  · rintro ⟨a₁, a₂, ha⟩
    refine ⟨(hH₁ x).1 a₁, (hH₂ x).1 a₂, ?_⟩
    rw [← h₁ x _ a₁, ← h₂ x _ a₂, ← htw]
    exact ha
  · rintro ⟨a₁, a₂, ha⟩
    refine ⟨(hH₁ x).2 a₁, (hH₂ x).2 a₂, ?_⟩
    rw [h₁ x a₁, h₂ x a₂, htw]
    exact ha

theorem mem_characterNormalizer_iff (φ : G ≃* G) {H H' : Subgroup G}
    (hH : ∀ x, φ x ∈ H' ↔ x ∈ H) {θ : H →* ℂˣ} {θ' : H' →* ℂˣ}
    (hθ : CharacterCorresponds φ θ θ') (g : G) :
    φ g ∈ characterNormalizer θ' ↔ g ∈ characterNormalizer θ := by
  unfold characterNormalizer characterSelfIntertwining characterIntertwining
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_set_normalizer_iff,
    Set.mem_ofPred_eq]
  refine and_congr ?_ ?_
  · refine φ.surjective.forall.trans (forall_congr' fun h => ?_)
    rw [← map_inv, ← map_mul, ← map_mul, hH, hH]
  · refine forall_subgroup_congr φ hH fun x hx hx' => ?_
    have hmem : ∀ y, φ g * φ y * (φ g)⁻¹ = φ (g * y * g⁻¹) := fun y => by
      rw [map_mul, map_mul, map_inv]
    constructor
    · intro h hh
      have hh' : φ g * φ x * (φ g)⁻¹ ∈ H' := by rw [hmem, hH]; exact hh
      have h2 : φ (g * x * g⁻¹) ∈ H' := (hH _).2 hh
      have := h hh'
      rw [hθ x hx hx'] at this
      rw [← this, ← hθ _ hh h2]
      congr 1
      exact Subtype.ext (hmem x).symm
    · intro h hh
      have hh'' : g * x * g⁻¹ ∈ H := by rw [← hH, ← hmem]; exact hh
      rw [hθ x hx hx', ← h hh'', ← hθ _ hh'' ((hH _).2 hh'')]
      congr 1
      exact Subtype.ext (hmem x)

end Group

/-! ### The relative determinant under semilinear conjugation -/

section Determinant

variable {E E' V₁ V₂ : Type*} [Field E] [Field E'] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module E V₁] [Module E' V₂]

/-- Coordinates of `V₂` in the image under a semilinear equivalence `f` of a basis of `V₁`. -/
def semilinearCoords {ι : Type*} [Fintype ι] (b : Module.Basis ι E V₁) (σK : E ≃+* E')
    (f : V₁ ≃ₛₗ[(σK : E →+* E')] V₂) : V₂ ≃ₗ[E'] (ι → E') where
  toFun w i := σK (b.equivFun (f.symm w) i)
  invFun c := f (b.equivFun.symm (fun i => σK.symm (c i)))
  map_add' w w' := by
    ext i
    simp only [map_add, Pi.add_apply]
  map_smul' c w := by
    ext i
    simp [LinearEquiv.map_smulₛₗ]
  left_inv w := by
    simp only [RingEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]
  right_inv c := by
    ext i
    simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply]

theorem semilinearCoords_symm_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι E V₁)
    (σK : E ≃+* E') (f : V₁ ≃ₛₗ[(σK : E →+* E')] V₂) (c : ι → E') :
    (semilinearCoords b σK f).symm c = f (b.equivFun.symm (fun i => σK.symm (c i))) :=
  rfl

theorem ofEquivFun_semilinearCoords {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι E V₁) (σK : E ≃+* E') (f : V₁ ≃ₛₗ[(σK : E →+* E')] V₂) (j : ι) :
    Module.Basis.ofEquivFun (semilinearCoords b σK f) j = f (b j) := by
  rw [Module.Basis.coe_ofEquivFun]
  beta_reduce
  rw [semilinearCoords_symm_apply]
  congr 1
  have hs : (fun i => σK.symm ((Pi.single j (1 : E') : ι → E') i)) =
      (Pi.single j (1 : E) : ι → E) := by
    funext i
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hs, LinearEquiv.symm_apply_eq, Module.Basis.equivFun_apply, Module.Basis.repr_self,
    Finsupp.single_eq_pi_single]

/-- The determinant over `E'` of `f x f⁻¹` is the image under `σK` of the determinant over
`E` of `x`, for a `σK`-semilinear equivalence `f`. -/
theorem det_endConj_semilinear [FiniteDimensional E V₁] (σK : E ≃+* E')
    (f : V₁ ≃ₛₗ[(σK : E →+* E')] V₂) (x : Module.End E V₁) :
    LinearMap.det (endConj f x) = σK (LinearMap.det x) := by
  let b := Module.finBasis E V₁
  let b' := Module.Basis.ofEquivFun (semilinearCoords b σK f)
  have hmat : LinearMap.toMatrix b' b' (endConj f x) =
      (σK : E →+* E').mapMatrix (LinearMap.toMatrix b b x) := by
    ext i j
    rw [LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      LinearMap.toMatrix_apply, ofEquivFun_semilinearCoords, endConj_apply_apply,
      Module.Basis.ofEquivFun_repr_apply]
    change σK (b.equivFun (f.symm (f (x (b j)))) i) = σK (b.repr (x (b j)) i)
    rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_apply]
  rw [← LinearMap.det_toMatrix b', hmat, ← RingHom.map_det, LinearMap.det_toMatrix]
  rfl

end Determinant

/-! ### Simple characters -/

section Characters

variable {O F V : Type*} [CommRing O] [Field F] [Algebra O F] [AddCommGroup V] [Module F V]
  [Module O V] [IsScalarTower O F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- A character `χ` factors through `d.rangeRestrict`, via a character of the image `d.range`,
exactly when `χ` is constant on the fibres of `d`. -/
theorem exists_factor_rangeRestrict_iff {U D : Type*} [Group U] [Group D] (d : U →* D)
    (χ : U →* ℂˣ) :
    (∃ η : d.range →* ℂˣ, ∀ x, χ x = η (d.rangeRestrict x)) ↔
      ∀ x y, d x = d y → χ x = χ y := by
  constructor
  · rintro ⟨η, hη⟩ x y hxy
    rw [hη, hη]
    congr 1
    exact Subtype.ext hxy
  · intro h
    have hker : d.rangeRestrict.ker ≤ χ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      have hd : d x = d 1 := by
        rw [map_one]
        exact congrArg Subtype.val hx
      rw [h x 1 hd, map_one]
    refine ⟨d.rangeRestrict.liftOfRightInverse (Function.surjInv d.rangeRestrict_surjective)
      (Function.rightInverse_surjInv _) ⟨χ, hker⟩, fun x => ?_⟩
    rw [MonoidHom.liftOfRightInverse_comp_apply]

/-- `factorsThroughCentralizerDet` as constancy on the fibres of the relative determinant. -/
theorem factorsThroughCentralizerDet_iff_det_eq (β : A) {H : Subgroup G} (χ : H →* ℂˣ) :
    factorsThroughCentralizerDet β χ ↔ ∃ hE : IsField (elementAlgebra β),
      letI := hE.toField
      ∀ (x y : (Module.End (elementAlgebra β) V)ˣ)
        (hx : relativeEndUnits (elementAlgebra β) x ∈ H)
        (hy : relativeEndUnits (elementAlgebra β) y ∈ H),
        LinearMap.det (x : Module.End (elementAlgebra β) V) =
          LinearMap.det (y : Module.End (elementAlgebra β) V) →
        χ ⟨_, hx⟩ = χ ⟨_, hy⟩ := by
  unfold factorsThroughCentralizerDet
  refine exists_congr fun hE => ?_
  let := hE.toField
  let ι := relativeEndUnits (F := F) (V := V) (elementAlgebra β)
  let U := H.comap ι
  let d := (Units.map (LinearMap.det : Module.End (elementAlgebra β) V →* elementAlgebra β)).comp
    U.subtype
  let χ' : U →* ℂˣ := χ.comp ((ι.comp U.subtype).codRestrict H fun x => x.2)
  change (∃ η : d.range →* ℂˣ, ∀ x : U, χ' x = η (d.rangeRestrict x)) ↔ _
  rw [exists_factor_rangeRestrict_iff d χ']
  constructor
  · intro h x y hx hy hxy
    exact h ⟨x, hx⟩ ⟨y, hy⟩ (Units.ext hxy)
  · intro h x y hxy
    exact h x y x.2 y.2 (congrArg Units.val hxy)

theorem relativeEndUnits_unitsConj (f : V ≃ₗ[F] V) (β : A) (h : IsField (elementAlgebra β))
    (h' : IsField (elementAlgebra (endConj f β))) :
    letI := h.toField
    letI := h'.toField
    ∀ x : (Module.End (elementAlgebra β) V)ˣ,
      relativeEndUnits (elementAlgebra (endConj f β))
        (unitsConj (semilinearOfConj f (elementAlgebraConj f β) (elementAlgebraConj_smul f β)) x) =
        unitsConj f (relativeEndUnits (elementAlgebra β) x) := by
  intro x
  exact Units.ext (LinearMap.ext fun _ => rfl)

theorem factorsThroughCentralizerDet_transport [FiniteDimensional F V] (f : V ≃ₗ[F] V) (β : A)
    {H H' : Subgroup G} (hH : ∀ x, unitsConj f x ∈ H' ↔ x ∈ H) {θ : H →* ℂˣ}
    {θ' : H' →* ℂˣ} (hθ : CharacterCorresponds (unitsConj f) θ θ') :
    factorsThroughCentralizerDet (endConj f β) θ' ↔ factorsThroughCentralizerDet β θ := by
  rw [factorsThroughCentralizerDet_iff_det_eq, factorsThroughCentralizerDet_iff_det_eq]
  constructor
  · rintro ⟨hE', h'⟩
    have hE := (isField_elementAlgebra_endConj_iff f β).1 hE'
    refine ⟨hE, ?_⟩
    let := hE.toField
    let := hE'.toField
    have : FiniteDimensional (elementAlgebra β) V :=
      Module.Finite.of_restrictScalars_finite F (elementAlgebra β) V
    let fE := semilinearOfConj f (elementAlgebraConj f β) (elementAlgebraConj_smul f β)
    intro x y hx hy hxy
    have hx' : relativeEndUnits (elementAlgebra (endConj f β)) (unitsConj fE x) ∈ H' := by
      rw [relativeEndUnits_unitsConj f β hE hE', hH]
      exact hx
    have hy' : relativeEndUnits (elementAlgebra (endConj f β)) (unitsConj fE y) ∈ H' := by
      rw [relativeEndUnits_unitsConj f β hE hE', hH]
      exact hy
    have hdet : LinearMap.det ((unitsConj fE x : (Module.End (elementAlgebra (endConj f β)) V)ˣ) :
        Module.End (elementAlgebra (endConj f β)) V) =
        LinearMap.det ((unitsConj fE y : (Module.End (elementAlgebra (endConj f β)) V)ˣ) :
          Module.End (elementAlgebra (endConj f β)) V) := by
      rw [coe_unitsConj, coe_unitsConj, det_endConj_semilinear, det_endConj_semilinear, hxy]
    have key := h' _ _ hx' hy' hdet
    have ex : ∀ (z : (Module.End (elementAlgebra β) V)ˣ)
        (hz : relativeEndUnits (elementAlgebra β) z ∈ H)
        (hz' : relativeEndUnits (elementAlgebra (endConj f β)) (unitsConj fE z) ∈ H'),
        θ' ⟨_, hz'⟩ = θ ⟨_, hz⟩ := by
      intro z hz hz'
      rw [← hθ _ hz ((hH _).2 hz)]
      rfl
    rw [← ex x hx hx', ← ex y hy hy']
    exact key
  · rintro ⟨hE, h⟩
    have hE' := (isField_elementAlgebra_endConj_iff f β).2 hE
    refine ⟨hE', ?_⟩
    let := hE.toField
    let := hE'.toField
    have : FiniteDimensional (elementAlgebra β) V :=
      Module.Finite.of_restrictScalars_finite F (elementAlgebra β) V
    let fE := semilinearOfConj f (elementAlgebraConj f β) (elementAlgebraConj_smul f β)
    intro x' y' hx' hy' hxy'
    obtain ⟨x, rfl⟩ := (unitsConj fE).surjective x'
    obtain ⟨y, rfl⟩ := (unitsConj fE).surjective y'
    have hx : relativeEndUnits (elementAlgebra β) x ∈ H := by
      rw [← hH, ← relativeEndUnits_unitsConj f β hE hE']
      exact hx'
    have hy : relativeEndUnits (elementAlgebra β) y ∈ H := by
      rw [← hH, ← relativeEndUnits_unitsConj f β hE hE']
      exact hy'
    have hdet : LinearMap.det (x : Module.End (elementAlgebra β) V) =
        LinearMap.det (y : Module.End (elementAlgebra β) V) := by
      rw [coe_unitsConj, coe_unitsConj, det_endConj_semilinear, det_endConj_semilinear] at hxy'
      exact (elementAlgebraConj f β).injective hxy'
    have key := h x y hx hy hdet
    have ex : ∀ (z : (Module.End (elementAlgebra β) V)ˣ)
        (hz : relativeEndUnits (elementAlgebra β) z ∈ H)
        (hz' : relativeEndUnits (elementAlgebra (endConj f β)) (unitsConj fE z) ∈ H'),
        θ' ⟨_, hz'⟩ = θ ⟨_, hz⟩ := by
      intro z hz hz'
      rw [← hθ _ hz ((hH _).2 hz)]
      rfl
    rw [ex x hx hx', ex y hy hy']
    exact key

theorem elementCharacter_unitsConj (ψF : AddChar F ℂ) [FiniteDimensional F V]
    (f : V ≃ₗ[F] V) (β : A) (u : G) :
    elementCharacter (traceCharacter ψF) (endConj f β) (unitsConj f u) =
      elementCharacter (traceCharacter ψF) β u := by
  have h : endConj f β * (endConj f (u : A) - 1) = endConj f (β * ((u : A) - 1)) := by
    rw [map_mul, map_sub, map_one]
  simp only [elementCharacter_apply, traceCharacter_apply, coe_unitsConj, h]
  exact congrArg ψF (LinearMap.trace_conj' _ f)

theorem LatticeChain.Corresponds.mem_relativeOrderNormalizer {f : V ≃ₗ[F] V}
    {L L' : LatticeChain O F V} (hL : L.Corresponds f L') (β : A) (u : G) :
    unitsConj f u ∈ relativeOrderNormalizer L' (endConj f β) ↔ u ∈ relativeOrderNormalizer L β := by
  unfold relativeOrderNormalizer
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hL.mem_stabilizer]
  refine and_congr_left fun _ => ?_
  change endConj f β * endConj f u = endConj f u * endConj f β ↔ β * (u : A) = (u : A) * β
  rw [← map_mul, ← map_mul]
  exact (endConj f).injective.eq_iff

theorem LatticeChain.Corresponds.mem_simpleHGroup {f : V ≃ₗ[F] V}
    {L L' : LatticeChain O F V} (hL : L.Corresponds f L') (n : ℤ) (β : A) (tail : List A)
    (m : ℕ) (u : G) :
    unitsConj f u ∈ simpleHGroup L' n (endConj f β) (tail.map (endConj f)) m ↔
      u ∈ simpleHGroup L n β tail m := by
  rw [hL.simpleHGroup_eq]
  exact mem_map_mulEquiv_iff (unitsConj f) _ u

theorem LatticeChain.Corresponds.mem_simpleCharacters (ψF : AddChar F ℂ) {f : V ≃ₗ[F] V}
    {L L' : LatticeChain O F V} (hL : L.Corresponds f L') (n : ℤ) (tail : List A) :
    ∀ (β : A) (m : ℕ) (θ : simpleHGroup L n β tail (m + 1) →* ℂˣ)
      (θ' : simpleHGroup L' n (endConj f β) (tail.map (endConj f)) (m + 1) →* ℂˣ),
      CharacterCorresponds (unitsConj f) θ θ' →
        (θ' ∈ simpleCharacters ψF L' n (endConj f β) (tail.map (endConj f)) m ↔
          θ ∈ simpleCharacters ψF L n β tail m) := by
  have := L.finiteDimensional
  induction tail with
  | nil =>
    intro β m θ θ' hθ
    change θ' ∈ simpleCharacters ψF L' n (endConj f β) [] m ↔ _
    rw [simpleCharacters, simpleCharacters]
    refine and_congr ?_ (factorsThroughCentralizerDet_transport f β
      (hL.mem_simpleHGroup n β [] (m + 1)) hθ)
    refine forall_subgroup_congr (unitsConj f) (hL.mem_simpleHGroup n β [] (m + 1))
      fun x hx hx' => ?_
    rw [hL.mem_unitFiltration, hθ x hx hx', elementCharacter_unitsConj]
  | cons γ tail ih =>
    intro β m θ θ' hθ
    change θ' ∈ simpleCharacters ψF L' n (endConj f β) (endConj f γ :: tail.map (endConj f)) m ↔ _
    by_cases hm : (m : ℤ) < finiteCriticalDepth L n β
    · have hm' : (m : ℤ) < finiteCriticalDepth L' n (endConj f β) := by
        rwa [hL.finiteCriticalDepth_eq]
      have hr := hL.finiteCriticalDepth_eq n β
      simp only [simpleCharacters, ite_eq_left hm, ite_eq_left hm', Set.mem_ofPred_eq]
      generalize finiteCriticalDepth L' n (endConj f β) = r' at hr ⊢
      subst hr
      refine and_congr (factorsThroughCentralizerDet_transport f β
        (hL.mem_simpleHGroup n β (γ :: tail) (m + 1)) hθ) (and_congr ?_ ?_)
      · constructor
        · intro h u hu
          rw [← mem_characterNormalizer_iff (unitsConj f)
            (hL.mem_simpleHGroup n β (γ :: tail) (m + 1)) hθ]
          exact h ((hL.mem_relativeOrderNormalizer β u).2 hu)
        · intro h u' hu'
          obtain ⟨u, rfl⟩ := (unitsConj f).surjective u'
          rw [mem_characterNormalizer_iff (unitsConj f)
            (hL.mem_simpleHGroup n β (γ :: tail) (m + 1)) hθ]
          exact h ((hL.mem_relativeOrderNormalizer β u).1 hu')
      · let j := max m (finiteCriticalDepth L n β / 2).toNat
        constructor
        · rintro ⟨θ₀', hθ₀', hagree⟩
          obtain ⟨θ₀, h₀⟩ := exists_characterCorresponds_symm (unitsConj f)
            (hL.simpleHGroup_eq n γ tail (j + 1)) θ₀'
          refine ⟨θ₀, (ih γ j θ₀ θ₀' h₀).1 hθ₀', ?_⟩
          refine (characterAgreesOn_iff (unitsConj f)
            (hL.mem_simpleHGroup n β (γ :: tail) (j + 1))
            (hL.mem_simpleHGroup n β (γ :: tail) (m + 1)) (hL.mem_simpleHGroup n γ tail (j + 1))
            hθ h₀ (fun x => ?_)).1 hagree
          rw [← map_sub, elementCharacter_unitsConj]
        · rintro ⟨θ₀, hθ₀, hagree⟩
          obtain ⟨θ₀', h₀⟩ := exists_characterCorresponds (unitsConj f)
            (hL.simpleHGroup_eq n γ tail (j + 1)) θ₀
          refine ⟨θ₀', (ih γ j θ₀ θ₀' h₀).2 hθ₀, ?_⟩
          refine (characterAgreesOn_iff (unitsConj f)
            (hL.mem_simpleHGroup n β (γ :: tail) (j + 1))
            (hL.mem_simpleHGroup n β (γ :: tail) (m + 1)) (hL.mem_simpleHGroup n γ tail (j + 1))
            hθ h₀ (fun x => ?_)).2 hagree
          rw [← map_sub, elementCharacter_unitsConj]
    · have hm' : ¬ (m : ℤ) < finiteCriticalDepth L' n (endConj f β) := by
        rwa [hL.finiteCriticalDepth_eq]
      simp only [simpleCharacters, ite_eq_right hm, ite_eq_right hm', Set.mem_ofPred_eq]
      have hHeq : simpleHGroup L' n (endConj f β) (endConj f γ :: tail.map (endConj f)) (m + 1) =
            simpleHGroup L' n (endConj f γ) (tail.map (endConj f)) (m + 1) ↔
          simpleHGroup L n β (γ :: tail) (m + 1) = simpleHGroup L n γ tail (m + 1) := by
        rw [← List.map_cons, hL.simpleHGroup_eq, hL.simpleHGroup_eq]
        exact (Subgroup.map_injective (unitsConj f).injective).eq_iff
      constructor
      · rintro ⟨θ₀', hθ₀', hH, hagree⟩
        obtain ⟨θ₀, h₀⟩ := exists_characterCorresponds_symm (unitsConj f)
          (hL.simpleHGroup_eq n γ tail (m + 1)) θ₀'
        refine ⟨θ₀, (ih γ m θ₀ θ₀' h₀).1 hθ₀', hHeq.1 hH, ?_⟩
        exact (characterAgreesOn_iff (unitsConj f)
          (hL.mem_simpleHGroup n β (γ :: tail) (m + 1))
          (hL.mem_simpleHGroup n β (γ :: tail) (m + 1)) (hL.mem_simpleHGroup n γ tail (m + 1))
          hθ h₀ (fun _ => rfl)).1 hagree
      · rintro ⟨θ₀, hθ₀, hH, hagree⟩
        obtain ⟨θ₀', h₀⟩ := exists_characterCorresponds (unitsConj f)
          (hL.simpleHGroup_eq n γ tail (m + 1)) θ₀
        refine ⟨θ₀', (ih γ m θ₀ θ₀' h₀).2 hθ₀, hHeq.2 hH, ?_⟩
        exact (characterAgreesOn_iff (unitsConj f)
          (hL.mem_simpleHGroup n β (γ :: tail) (m + 1))
          (hL.mem_simpleHGroup n β (γ :: tail) (m + 1)) (hL.mem_simpleHGroup n γ tail (m + 1))
          hθ h₀ (fun _ => rfl)).2 hagree

end Characters

end Langlands.BushnellKutzko
