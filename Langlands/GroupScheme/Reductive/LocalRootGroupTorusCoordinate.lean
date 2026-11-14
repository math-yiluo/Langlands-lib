import Langlands.GroupScheme.Dynamic.UnipotentTorusWeights
import Langlands.GroupScheme.Reductive.LocalRootGroupAdditiveCoordinate
import Langlands.GroupScheme.Rational.TorusActionPoints
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing

/-! # Torus-equivariant root coordinates over arbitrary local rings -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- The fixed-exponent character on a general test scheme is the unit monomial. -/
theorem charValue_exponentCharacter (m : I → ℤ) (T : Over (Spec R))
    (t : T ⟶ (splitTorus (Spec R) I).X) :
    VectorGroup.charValue (splitTorus.exponentCharacter _ I m) T t =
      (splitTorus.exponentValue I (splitTorus.pointsEquiv I T t)
        (Multiplicative.ofAdd m) : Γ(T.left, ⊤)) := by
  rw [VectorGroup.charValue, splitTorus.pointsEquiv_exponentCharacter]
  rfl

/-- A homogeneous function scales through its actual character on every test scheme. -/
theorem appTop_act_of_isHomogeneous
    (b : AutomorphicAction (splitTorus (Spec R) I) (groupScheme F e))
    {m : I → ℤ} {x : B} (hx : IsHomogeneous e (TorusAction.ofAutomorphicAction e b) m x)
    (T : Over (Spec R)) (t : T ⟶ (splitTorus (Spec R) I).X)
    (y : T ⟶ (groupScheme F e).X) :
    (b.act t y).left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) =
      VectorGroup.charValue (splitTorus.exponentCharacter _ I m) T t *
        y.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) := by
  have h := coord_act_of_isHomogeneous e (TorusAction.ofAutomorphicAction e b)
    (splitTorus.pointsEquiv I T t) (pointsEquiv F e T y) hx
  rw [← pointsEquiv_act e b] at h
  simp only [coord, homEquiv_symm_pointsEquiv_apply] at h
  rw [charValue_exponentCharacter, mul_comm]
  exact h

omit [DecidableEq I] in
/-- The exponent character at prescribed affine unit coordinates. -/
theorem charValue_torusPt {A : Type u} [CommRing A] [Algebra R A]
    (m : I → ℤ) (t : I → Aˣ) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (VectorGroup.charValue (splitTorus.exponentCharacter _ I m)
          (RingCoordinates.specOver R A) (torusPt I (CommAlgCat.of R A) t)) =
      (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : A) := by
  have h := splitTorus.characterValue_exponentCharacter I m
    (torusPt I (CommAlgCat.of R A) t)
  rw [torusPt, MulEquiv.apply_symm_apply] at h
  exact congrArg (fun z : Aˣ => (z : A)) h

/-- Field-valued points distinguish integer exponent vectors, even when the
base local ring has nilpotents. -/
theorem exponent_eq_of_field_charValues [IsLocalRing R] {m n : I → ℤ}
    (h : ∀ (K : Type u) [Field K] [Algebra R K]
      (t : RingCoordinates.specOver R K ⟶ (splitTorus (Spec R) I).X),
      VectorGroup.charValue (splitTorus.exponentCharacter _ I m) _ t =
        VectorGroup.charValue (splitTorus.exponentCharacter _ I n) _ t) :
    m = n := by
  let k := IsLocalRing.ResidueField R
  let D := AddMonoidAlgebra k (I → ℤ)
  let K := FractionRing D
  let : Algebra R K :=
    ((algebraMap D K).comp ((algebraMap k D).comp (algebraMap R k))).toAlgebra
  let t : I → Kˣ := fun j =>
    Units.map (algebraMap D K).toMonoidHom (universalUnits I k j)
  have hv := congrArg (fun c => (Scheme.ΓSpecIso (CommRingCat.of K)).hom c)
    (h K (torusPt I (CommAlgCat.of R K) t))
  rw [charValue_torusPt, charValue_torusPt] at hv
  dsimp only [t] at hv
  rw [exponentValue_map, exponentValue_map, exponentValue_universalUnits,
    exponentValue_universalUnits] at hv
  change algebraMap D K (AddMonoidAlgebra.single m 1) =
    algebraMap D K (AddMonoidAlgebra.single n 1) at hv
  exact AddMonoidAlgebra.single_left_injective (one_ne_zero : (1 : k) ≠ 0)
    (IsFractionRing.injective D K hv)

end Langlands.GroupScheme.Corepresented

namespace Langlands.GroupScheme.LocalRootGroup

open Corepresented Corepresented.UnipotentPrimitive LocalSplitCell

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu : I → ℤ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The full split-torus action on the actual dynamic root group. -/
abbrev torusAction := UnipotentTorus.torusAction (torusZ i mu) nu

omit [DecidableEq I] in
/-- The scheme action on the dynamic root group agrees with conjugation in `G`. -/
theorem action_act_comp_incl {T : Over (Spec (CommRingCat.of R))}
    (t : T ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (y : T ⟶ (Uc i mu nu).X) :
    (UnipotentTorus.action (torusZ i mu) nu).act t y ≫ (incl i mu nu).hom.hom =
      (t ≫ i.hom.hom) * (y ≫ (incl i mu nu).hom.hom) * (t ≫ i.hom.hom)⁻¹ := by
  let j := jZ i mu ≫ (AffineCoordinates.groupSchemeIso G).hom
  have hj : torusZ i mu ≫ j = i := by
    change torusZ i mu ≫ jZ i mu ≫ (AffineCoordinates.groupSchemeIso G).hom = i
    rw [← Category.assoc, torusZ_comp, modelTorus, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have ht : (t ≫ (torusZ i mu).hom.hom) ≫ j.hom.hom = t ≫ i.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hj]
  change (UnipotentTorus.action (torusZ i mu) nu).act t y ≫
    (jU i mu nu ≫ j).hom.hom = _
  rw [Grp.comp_hom_hom, ← Category.assoc, UnipotentTorus.action_act_comp,
    MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, ht]
  rfl

/-- The root coordinate scales through its homogeneous weight on all scheme tests. -/
theorem coordX_act_of_isHomogeneous {a : I → ℤ} {x : coordU i mu nu}
    (hx : IsHomogeneous (unipotentCorepresentation (unipCochar i mu nu))
      (torusAction i mu nu) a x)
    (T : Over (Spec (CommRingCat.of R)))
    (t : T ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (y : T ⟶ (Uc i mu nu).X) :
    coordX i mu nu x ((UnipotentTorus.action (torusZ i mu) nu).act t y) =
      VectorGroup.charValue (splitTorus.exponentCharacter _ I a) T t *
        coordX i mu nu x y :=
  appTop_act_of_isHomogeneous (unipotentCorepresentation (unipCochar i mu nu))
    (UnipotentTorus.action (torusZ i mu) nu) hx T t y

/-- A homogeneous polynomial coordinate makes the root map torus-equivariant
over any base ring, without a reducedness hypothesis. -/
theorem rootMap_equivariant_of_isHomogeneous (x : coordU i mu nu)
    (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
    (hadd : ∀ (T : Over (Spec (CommRingCat.of R))) (y y' : T ⟶ (Uc i mu nu).X),
      coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y')
    {a : I → ℤ}
    (ha : IsHomogeneous (unipotentCorepresentation (unipCochar i mu nu))
      (torusAction i mu nu) a x)
    (T : Over (Spec (CommRingCat.of R)))
    (t : T ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(T.left, ⊤)) :
    (t ≫ i.hom.hom) * rootPoint (rootMap i mu nu x hx hadd) T c * (t ≫ i.hom.hom)⁻¹ =
      rootPoint (rootMap i mu nu x hx hadd) T
        (VectorGroup.charValue (splitTorus.exponentCharacter _ I a) T t * c) := by
  have hact : (UnipotentTorus.action (torusZ i mu) nu).act t
      (VectorGroup.scalarPoint _ T c ≫ (gaIsoU i mu nu x hx hadd).hom.hom.hom) =
      VectorGroup.scalarPoint _ T
          (VectorGroup.charValue (splitTorus.exponentCharacter _ I a) T t * c) ≫
        (gaIsoU i mu nu x hx hadd).hom.hom.hom := by
    apply (coordX_bijective i mu nu x hx T).1
    rw [coordX_act_of_isHomogeneous i mu nu ha, coordX_gaIsoU, coordX_gaIsoU]
  rw [rootPoint_rootMap, rootPoint_rootMap, ← hact, action_act_comp_incl]

set_option synthInstance.maxHeartbeats 100000 in
/-- Every field fibre of the actual dynamic root group has a parametrization
with the fixed torus exponent `a`. -/
def HasEquivariantFibres (a : I → ℤ) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra R K], ∃ Φ : Ga K ≅ UK i mu nu K,
    ∀ (Z : Over (Spec (CommRingCat.of K)))
      (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (y : Z ⟶ (Ga K).X),
      (t ≫ (tK i mu K).hom.hom) *
          (y ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map
            (jU i mu nu)).hom.hom) *
          (t ≫ (tK i mu K).hom.hom)⁻¹ =
        VectorGroup.weightPointAction (splitTorus.exponentCharacter _ I a) Z t y ≫
          (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map
            (jU i mu nu)).hom.hom

/-- The weight of a positive homogeneous coordinate is the prescribed fibre
root, over an arbitrary local ring. -/
theorem isHomogeneous_of_equivariantFibres [IsLocalRing R] {d : ℕ} (hd : 0 < d)
    {x : coordU i mu nu}
    (hxd : x ∈ CommutativeAlgebra.GradedLine.homog
      (isGrading_unipCoaction (unipCochar i mu nu)) d)
    (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
    {a : I → ℤ} (had : ∑ j, a j * nu j = d)
    (hfib : HasEquivariantFibres i mu nu a) :
    IsHomogeneous (unipotentCorepresentation (unipCochar i mu nu))
      (torusAction i mu nu) a x := by
  obtain ⟨m, hm⟩ := UnipotentTorus.exists_isHomogeneous (torusZ i mu) nu hd hxd hx
  have hadd : ∀ (T : Over (Spec (CommRingCat.of R))) (y y' : T ⟶ (Uc i mu nu).X),
      coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y' :=
    fun _ => coordX_mul_of_homogeneous i mu nu hd hxd hx.2
  have heq : m = a := by
    apply exponent_eq_of_field_charValues (R := CommRingCat.of R)
    intro K _ _ t
    obtain ⟨Φ, hΦ⟩ := hfib K
    have hline : fibreAlgHom i mu nu Φ K[X] Polynomial.X x =
        Polynomial.C ((fibreAlgHom i mu nu Φ K[X] Polynomial.X x).coeff 1) * Polynomial.X := by
      ext j
      rw [Polynomial.coeff_C_mul_X]
      split_ifs with h
      · rw [h]
      · refine CommutativeAlgebra.GradedLine.coeff_eq_zero_of_scaling hd
          (scaling_fibre i mu nu Φ _ hΦ d (by
            rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, had]))
          _ x hxd j ?_
        intro h'
        apply h
        have hd' : (0 : ℤ) < d := by exact_mod_cast hd
        have : (j : ℤ) = 1 := by nlinarith
        exact_mod_cast this
    have h₁ := rootMap_equivariant_of_isHomogeneous i mu nu x hx hadd hm _ t 1
    have h₂ := rootMap_equivariant_field i mu nu x hx hadd a Φ hΦ hline t 1
    have hc := h₁.symm.trans h₂
    have : IsClosedImmersion (rootMap i mu nu x hx hadd).hom.hom.left :=
      isClosedSubgroup_rootMap i mu nu x hx hadd
    have : Mono (rootMap i mu nu x hx hadd).hom.hom := Over.mono_of_mono_left _
    apply (scalarPoint_bijective _ _).1
    apply (cancel_mono (rootMap i mu nu x hx hadd).hom.hom).1
    simpa only [rootPoint, mul_one] using hc
  simpa only [heq] using hm

section Assembly

variable [Smooth G.X.hom] [IsLocalRing R]

/-- Root parametrizations from fixed-root field fibres, retaining nilpotents. -/
theorem exists_isRootParametrization_of_flat (a : I → ℤ)
    (ha0 : ∑ j, a j * mu j = 0) {d : ℕ} (hd : 0 < d)
    (had : ∑ j, a j * nu j = d) (hfib : HasEquivariantFibres i mu nu a) :
    ∃ u : Ga R ⟶ G, IsRootParametrization i a u := by
  obtain ⟨x, hxd, hx⟩ := exists_coordinate_of_flat i mu nu hd fun K _ _ => by
    obtain ⟨Φ, hΦ⟩ := hfib K
    exact ⟨_, Φ, hΦ, by
      rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, had]⟩
  have hadd : ∀ (T : Over (Spec (CommRingCat.of R))) (y y' : T ⟶ (Uc i mu nu).X),
      coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y' :=
    fun _ => coordX_mul_of_homogeneous i mu nu hd hxd hx.2
  have ha := isHomogeneous_of_equivariantFibres i mu nu hd hxd hx had hfib
  have hequiv := rootMap_equivariant_of_isHomogeneous i mu nu x hx hadd ha
  exact ⟨rootMap i mu nu x hx hadd,
    { represents := isRepresentedBy_rootMap i mu nu x hx hadd a hequiv ha0 hd had
      isClosedSubgroup := isClosedSubgroup_rootMap i mu nu x hx hadd
      equivariant := hequiv }⟩

/-- A chosen root parametrization over an arbitrary local ring. -/
def rootParametrizationOfFibres (a : I → ℤ)
    (ha0 : ∑ j, a j * mu j = 0) {d : ℕ} (hd : 0 < d)
    (had : ∑ j, a j * nu j = d) (hfib : HasEquivariantFibres i mu nu a) :
    Ga R ⟶ G :=
  (exists_isRootParametrization_of_flat i mu nu a ha0 hd had hfib).choose

/-- The chosen map represents the actual root subgroup and is equivariant on
every scheme test. -/
theorem isRootParametrization_rootParametrizationOfFibres (a : I → ℤ)
    (ha0 : ∑ j, a j * mu j = 0) {d : ℕ} (hd : 0 < d)
    (had : ∑ j, a j * nu j = d) (hfib : HasEquivariantFibres i mu nu a) :
    IsRootParametrization i a (rootParametrizationOfFibres i mu nu a ha0 hd had hfib) :=
  (exists_isRootParametrization_of_flat i mu nu a ha0 hd had hfib).choose_spec

end Assembly

omit [DecidableEq I] in
/-- Every root of a fibrewise root datum has an actual root parametrization
over an arbitrary local ring. -/
theorem exists_rootParametrization_of_flat [IsLocalRing R] (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (α₀ : J) :
    ∃ u : Ga R ⟶ G, IsRootParametrization i (P.root α₀) u := by
  classical
  have := hG.smooth
  have : Finite J := hP.finite
  have := hP.isReduced
  obtain ⟨mu, hmu0, hmu⟩ := exists_kernel_exponent P (IsLocalRing.ResidueField R) α₀
  have h2 : ∑ j, P.root α₀ j * P.coroot α₀ j = ((2 : ℕ) : ℤ) := by
    rw [← hP.pairing (IsLocalRing.ResidueField R), P.root_coroot_two]
    rfl
  refine exists_isRootParametrization_of_flat i mu (P.coroot α₀)
    (P.root α₀) hmu0 two_pos h2 fun K _ _ => ?_
  have hGK := hG.isConnectedReductive_baseChange (algebraBaseMap R K)
  have hmaxK := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax K
  refine exists_fibreIso i mu (P.coroot α₀) K hGK hmaxK _
    ((hP.mem_roots_iff K _).2 ⟨α₀, rfl⟩) ?_ ?_ ?_
  · intro β hβ hβ0
    obtain ⟨m, rfl⟩ : ∃ m,
        splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I m = β :=
      ⟨splitTorus.characterLatticeEquiv K I β, by
        rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
          AddEquiv.symm_apply_apply]⟩
    obtain ⟨b, rfl⟩ := (hP.mem_roots_iff K m).1 hβ
    rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter] at hβ0
    rcases hmu b hβ0 with h | h
    · exact Or.inl (by rw [h])
    · refine Or.inr ?_
      rw [h, splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
        splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, map_neg]
  · rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, hmu0]
  · rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, h2]
    norm_num

end Langlands.GroupScheme.LocalRootGroup
