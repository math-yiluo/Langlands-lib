import Langlands.GroupScheme.Reductive.GlobalRootGroupCoordinate
import Mathlib.RingTheory.Jacobson.Ideal

/-! # Global torus-equivariant root parametrizations -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.CommutativeAlgebra

/-- An idempotent scalar vanishing in every maximal residue field is zero. -/
theorem idempotent_eq_zero_of_all_maximal
    {R : Type*} [CommRing R] {r : R} (hr : r * r = r)
    (h : ∀ (p : Ideal R), p.IsMaximal → r ∈ p) : r = 0 := by
  have hj : r ∈ Ideal.jacobson (⊥ : Ideal R) :=
    Ideal.mem_sInf.mpr fun p hp => h p hp.2
  have hu : IsUnit (r * (-1) + 1) := (Ideal.mem_jacobson_bot.mp hj) (-1)
  apply hu.mul_left_inj.mp
  rw [zero_mul]
  calc
    r * (r * (-1) + 1) = (r * r) * (-1) + r := by ring
    _ = 0 := by rw [hr]; ring

end Langlands.CommutativeAlgebra

namespace Langlands.GroupScheme.LocalRootGroup

open Corepresented Corepresented.UnipotentPrimitive LocalSplitCell
  CommutativeAlgebra.GradedLine

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu : I → ℤ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

omit [DecidableEq I] in
/-- Scalar multiplication of a coordinate evaluates through the coefficient algebra. -/
theorem coordX_smul_affine (D : Type u) [CommRing D] [Algebra R D]
    (r : R) (b : coordU i mu nu)
    (y : RingCoordinates.specOver (CommRingCat.of R) D ⟶ (Uc i mu nu).X) :
    (Scheme.ΓSpecIso (CommRingCat.of D)).hom (coordX i mu nu (r • b) y) =
      algebraMap R D r *
        (Scheme.ΓSpecIso (CommRingCat.of D)).hom (coordX i mu nu b y) := by
  rw [coordX, coordX, appTop_ΓSpecIso_inv, appTop_ΓSpecIso_inv]
  simp only [Iso.inv_hom_id_apply]
  change RingCoordinates.algHom y (r • b) = _
  rw [map_smul, Algebra.smul_def]
  rfl

/-- A nonzero scalar multiple of a coordinate with weight m forces m to agree,
on field tests, with the prescribed fibre character a. -/
theorem charValue_eq_of_smul_isHomogeneous {d : ℕ} (hd : 0 < d)
    {x : coordU i mu nu}
    (hxd : x ∈ homog (isGrading_unipCoaction (unipCochar i mu nu)) d)
    (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
    (a : I → ℤ) (had : ∑ j, a j * nu j = d)
    (hfib : HasEquivariantFibres i mu nu a)
    (r : R) (m : I → ℤ)
    (hr : IsHomogeneous (unipotentCorepresentation (unipCochar i mu nu))
      (torusAction i mu nu) m (r • x))
    (K : Type u) [Field K] [Algebra R K] (hrK : algebraMap R K r ≠ 0)
    (t : RingCoordinates.specOver (CommRingCat.of R) K ⟶
      (splitTorus (Spec (CommRingCat.of R)) I).X) :
    VectorGroup.charValue (splitTorus.exponentCharacter _ I m) _ t =
      VectorGroup.charValue (splitTorus.exponentCharacter _ I a) _ t := by
  obtain ⟨Φ, hΦ⟩ := hfib K
  have hline : fibreAlgHom i mu nu Φ K[X] Polynomial.X x =
      Polynomial.C ((fibreAlgHom i mu nu Φ K[X] Polynomial.X x).coeff 1) * Polynomial.X := by
    ext j
    rw [Polynomial.coeff_C_mul_X]
    split_ifs with h
    · rw [h]
    · refine coeff_eq_zero_of_scaling hd
        (scaling_fibre i mu nu Φ _ hΦ d (by
          rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, had]))
        _ x hxd j ?_
      intro h'
      apply h
      have hd' : (0 : ℤ) < d := by exact_mod_cast hd
      have : (j : ℤ) = 1 := by nlinarith
      exact_mod_cast this
  let hadd := fun T => coordX_mul_of_homogeneous i mu nu hd hxd hx.2 (T := T)
  let y : RingCoordinates.specOver (CommRingCat.of R) K ⟶ (Uc i mu nu).X :=
    VectorGroup.scalarPoint _ _ 1 ≫ (gaIsoU i mu nu x hx hadd).hom.hom.hom
  let : Mono (jU i mu nu).hom.hom := (jU_represents i mu nu).1
  let : Mono (centralizerIncl i mu).hom.hom := (centralizerIncl_represents i mu).1
  let : Mono (incl i mu nu).hom.hom := by
    change Mono ((jU i mu nu).hom.hom ≫ (centralizerIncl i mu).hom.hom)
    infer_instance
  have hact : (UnipotentTorus.action (torusZ i mu) nu).act t y =
      VectorGroup.scalarPoint _ _
        (VectorGroup.charValue (splitTorus.exponentCharacter _ I a) _ t) ≫
          (gaIsoU i mu nu x hx hadd).hom.hom.hom := by
    apply (cancel_mono (incl i mu nu).hom.hom).mp
    rw [action_act_comp_incl]
    simpa only [y, rootPoint_rootMap, mul_one, Category.assoc] using
      rootMap_equivariant_field i mu nu x hx hadd a Φ hΦ hline t 1
  have h := coordX_act_of_isHomogeneous i mu nu hr _ t y
  rw [hact] at h
  have hv := congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of K)).hom q) h
  rw [map_mul, coordX_smul_affine i mu nu K r x,
    coordX_smul_affine i mu nu K r x] at hv
  rw [coordX_gaIsoU i mu nu x hx hadd] at hv
  have hy : coordX i mu nu x y = 1 := coordX_gaIsoU i mu nu x hx hadd _ 1
  rw [hy, map_one, mul_one] at hv
  have heq :
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom
        (VectorGroup.charValue (splitTorus.exponentCharacter _ I m) _ t) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom
        (VectorGroup.charValue (splitTorus.exponentCharacter _ I a) _ t) := by
    apply mul_left_cancel₀ hrK
    simpa only [mul_comm] using hv.symm
  simpa only [Iso.hom_inv_id_apply] using
    congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of K)).inv q) heq

/-- Fixed field-fibre characters force the full torus weight of a global
homogeneous polynomial coordinate, including over nonreduced bases. -/
theorem isHomogeneous_of_equivariantFibres_global {d : ℕ} (hd : 0 < d)
    {x : coordU i mu nu}
    (hxd : x ∈ homog (isGrading_unipCoaction (unipCochar i mu nu)) d)
    (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
    (a : I → ℤ) (had : ∑ j, a j * nu j = d)
    (hfib : HasEquivariantFibres i mu nu a) :
    IsHomogeneous (unipotentCorepresentation (unipCochar i mu nu))
      (torusAction i mu nu) a x := by
  classical
  let eu := unipotentCorepresentation (unipCochar i mu nu)
  let σ := torusAction i mu nu
  have hstable (m : I → ℤ) : comp eu σ m x ∈ Submodule.span R {x} := by
    rw [← homog_eq_span_of_aeval_surjective
      (isGrading_unipCoaction (unipCochar i mu nu)) hd hxd hx.2]
    exact UnipotentTorus.comp_mem_homog (torusZ i mu) nu hxd m
  choose r hr using fun m => Submodule.mem_span_singleton.mp (hstable m)
  have hfaithful : Function.Injective (fun s : R => s • x) :=
    smul_injective_of_aeval_injective hx.1
  have hidem (m : I → ℤ) : r m * r m = r m := by
    apply hfaithful
    simpa only [ite_eq_left rfl, ite_true, ← hr m, map_smul, smul_smul] using
      (Corepresented.comp_comp eu σ m m x)
  have hrhom (m : I → ℤ) : IsHomogeneous eu σ m (r m • x) := by
    rw [hr m]
    exact isHomogeneous_comp eu σ m x
  have hmem (m : I → ℤ) (hma : m ≠ a) (p : Ideal R) (hp : p.IsMaximal) :
      r m ∈ p := by
    by_contra hnot
    let : p.IsMaximal := hp
    let k := R ⧸ p
    let : Field k := Ideal.Quotient.field p
    let D := AddMonoidAlgebra k (I → ℤ)
    let K := FractionRing D
    let : Algebra R K :=
      ((algebraMap D K).comp ((algebraMap k D).comp (algebraMap R k))).toAlgebra
    have hrk : algebraMap R k (r m) ≠ 0 := by
      intro hz
      exact hnot (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    have hrK : algebraMap R K (r m) ≠ 0 := by
      intro hz
      change algebraMap D K (algebraMap k D (algebraMap R k (r m))) = 0 at hz
      apply hrk
      apply (algebraMap k D).injective
      apply IsFractionRing.injective D K
      simpa only [map_zero] using hz
    let tUnits : I → Kˣ := fun j =>
      Units.map (algebraMap D K).toMonoidHom (universalUnits I k j)
    let t : RingCoordinates.specOver (CommRingCat.of R) K ⟶
        (splitTorus (Spec (CommRingCat.of R)) I).X :=
      torusPt (R := CommRingCat.of R) I (CommAlgCat.of (CommRingCat.of R) K) tUnits
    have hval := charValue_eq_of_smul_isHomogeneous i mu nu hd hxd hx a had hfib
      (r m) m (hrhom m) K hrK t
    have hv := congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of K)).hom q) hval
    rw [charValue_torusPt (R := CommRingCat.of R) m tUnits,
      charValue_torusPt (R := CommRingCat.of R) a tUnits] at hv
    dsimp only [tUnits] at hv
    rw [exponentValue_map, exponentValue_map, exponentValue_universalUnits,
      exponentValue_universalUnits] at hv
    change algebraMap D K (AddMonoidAlgebra.single m 1) =
      algebraMap D K (AddMonoidAlgebra.single a 1) at hv
    exact hma (AddMonoidAlgebra.single_left_injective (one_ne_zero : (1 : k) ≠ 0)
      (IsFractionRing.injective D K hv))
  have hzero (m : I → ℤ) (hma : m ≠ a) : comp eu σ m x = 0 := by
    rw [← hr m, CommutativeAlgebra.idempotent_eq_zero_of_all_maximal
      (hidem m) (hmem m hma), zero_smul]
  have hsum : ∑ m ∈ (rho eu σ x).coeff.support, comp eu σ m x = comp eu σ a x := by
    apply Finset.sum_eq_single a
    · intro m _ hma
      exact hzero m hma
    · intro ha
      exact comp_eq_zero_of_notMem eu σ ha
  have ha : comp eu σ a x = x := hsum.symm.trans (sum_support_comp eu σ x)
  apply (isHomogeneous_iff eu σ a x).mpr
  intro m
  by_cases hma : m = a
  · subst m
    simpa only [ite_eq_left rfl, ite_true] using ha
  · simpa only [ite_eq_right hma] using hzero m hma

variable [Smooth G.X.hom]

/-- A free actual root weight and fixed equivariant field fibres yield an
actual torus-equivariant root parametrization over the original ring. -/
theorem exists_isRootParametrization_of_free_weight_of_fibres
    (a : I → ℤ) (hmu : ∑ j, a j * mu j = 0)
    {d : ℕ} (hd : 0 < d) (had : ∑ j, a j * nu j = d)
    (eW : splitTorus.exponentWeightSpace I G i a ≃ₗ[CommRingCat.of R] CommRingCat.of R)
    (hfib : HasEquivariantFibres i mu nu a) :
    ∃ u : Ga R ⟶ G, IsRootParametrization i a u := by
  obtain ⟨x, hxd, hx⟩ := exists_coordinate_of_free_weight i mu nu a hmu hd had eW hfib
  have hadd : ∀ (T : Over (Spec (CommRingCat.of R))) (y y' : T ⟶ (Uc i mu nu).X),
      coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y' :=
    fun _ => coordX_mul_of_homogeneous i mu nu hd hxd hx.2
  have ha := isHomogeneous_of_equivariantFibres_global i mu nu hd hxd hx a had hfib
  have hequiv := rootMap_equivariant_of_isHomogeneous i mu nu x hx hadd ha
  exact ⟨rootMap i mu nu x hx hadd,
    { represents := isRepresentedBy_rootMap i mu nu x hx hadd a hequiv hmu hd had
      isClosedSubgroup := isClosedSubgroup_rootMap i mu nu x hx hadd
      equivariant := hequiv }⟩

/-- The actual global root map chosen from the free weight and equivariant fibres. -/
def rootParametrizationOfFreeWeightOfFibres
    (a : I → ℤ) (hmu : ∑ j, a j * mu j = 0)
    {d : ℕ} (hd : 0 < d) (had : ∑ j, a j * nu j = d)
    (eW : splitTorus.exponentWeightSpace I G i a ≃ₗ[CommRingCat.of R] CommRingCat.of R)
    (hfib : HasEquivariantFibres i mu nu a) : Ga R ⟶ G :=
  (exists_isRootParametrization_of_free_weight_of_fibres i mu nu a hmu hd had eW hfib).choose

/-- The chosen map represents the actual root subgroup and is torus-equivariant
on all scheme tests. -/
theorem isRootParametrization_rootParametrizationOfFreeWeightOfFibres
    (a : I → ℤ) (hmu : ∑ j, a j * mu j = 0)
    {d : ℕ} (hd : 0 < d) (had : ∑ j, a j * nu j = d)
    (eW : splitTorus.exponentWeightSpace I G i a ≃ₗ[CommRingCat.of R] CommRingCat.of R)
    (hfib : HasEquivariantFibres i mu nu a) :
    IsRootParametrization i a
      (rootParametrizationOfFreeWeightOfFibres i mu nu a hmu hd had eW hfib) :=
  (exists_isRootParametrization_of_free_weight_of_fibres i mu nu a hmu hd had eW hfib).choose_spec

end Langlands.GroupScheme.LocalRootGroup
