import Langlands.GroupScheme.Reductive.CharZeroDualFixedDescent
import Langlands.GroupScheme.Rational.CharacteristicZeroInvariantIntegralVectorExtension
import Langlands.GroupScheme.Rational.InvariantIntegralCriterion
import Langlands.GroupScheme.Unipotent.CoordinateBialgebra
import Langlands.GroupScheme.CorepresentedComultiplication
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Invariant integration for reductive groups in characteristic zero -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineLinearEmbedding

/-! ### Integrals at single elements of a bialgebra -/

section Local

variable {K : Type*} [Field K] {B : Type*} [CommRing B] [Bialgebra K B]

/-- `l` integrates `y` invariantly on the left: contracting the second coproduct factor of
`y` with `l` gives the constant `l y`. -/
def IsLeftIntegralAt (l : Module.Dual K B) (y : B) : Prop :=
  rightAct l y = l y • (1 : B)

/-- `r` integrates `y` invariantly on the right: contracting the first coproduct factor of
`y` with `r` gives the constant `r y`. -/
def IsRightIntegralAt (r : Module.Dual K B) (y : B) : Prop :=
  leftAct r y = r y • (1 : B)

/-- A normalized left integral and a normalized right integral at the same element take the
same value there. -/
theorem eq_of_isLeftIntegralAt_of_isRightIntegralAt {l r : Module.Dual K B} {y : B}
    (hl : IsLeftIntegralAt l y) (hr : IsRightIntegralAt r y) (hl1 : l 1 = 1)
    (hr1 : r 1 = 1) : l y = r y := by
  have h := apply_leftAct l r y
  rw [hr, hl, map_smul, map_smul, hl1, hr1, smul_eq_mul, smul_eq_mul, mul_one,
    mul_one] at h
  exact h.symm

/-- An antipode-like map exchanging the two coproduct factors transports left contraction
with `r` into right contraction with `r ∘ S`. -/
theorem map_rightAct_comp (S : B →ₗ[K] B)
    (hS : ∀ y, Coalgebra.comul (R := K) (S y) =
      TensorProduct.map S S (TensorProduct.comm K B B (Coalgebra.comul (R := K) y)))
    (r : Module.Dual K B) (y : B) :
    S (rightAct (r ∘ₗ S) y) = leftAct r (S y) := by
  rw [rightAct_apply, leftAct_apply, hS]
  generalize Coalgebra.comul (R := K) y = t
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Composing a right integral at `S y` with an involutive antipode gives a left integral
at `y`. -/
theorem isLeftIntegralAt_comp (S : B →ₐ[K] B)
    (hS : ∀ y, Coalgebra.comul (R := K) (S y) =
      TensorProduct.map S.toLinearMap S.toLinearMap
        (TensorProduct.comm K B B (Coalgebra.comul (R := K) y)))
    (hSS : ∀ y, S (S y) = y) {r : Module.Dual K B} {y : B}
    (hr : IsRightIntegralAt r (S y)) :
    IsLeftIntegralAt (r ∘ₗ S.toLinearMap) y := by
  have h := map_rightAct_comp S.toLinearMap hS r y
  rw [AlgHom.toLinearMap_apply S y, hr] at h
  have h' := congrArg S h
  rw [AlgHom.toLinearMap_apply, hSS, map_smul, map_one] at h'
  exact h'

/-- Local normalized left integrals on finite sets, together with local normalized right
integrals at single elements, glue to a global normalized left integral. -/
theorem exists_left_integral
    (hr : ∀ y : B, ∃ r : Module.Dual K B, r 1 = 1 ∧ IsRightIntegralAt r y)
    (hl : ∀ T : Finset B, ∃ l : Module.Dual K B, l 1 = 1 ∧ ∀ y ∈ T, IsLeftIntegralAt l y) :
    ∃ ℓ : Module.Dual K B, ℓ 1 = 1 ∧ ∀ z, IsLeftIntegralAt ℓ z := by
  classical
  choose L hL1 hL using hl
  have huniq : ∀ {l l' : Module.Dual K B} {y : B}, l 1 = 1 → IsLeftIntegralAt l y →
      l' 1 = 1 → IsLeftIntegralAt l' y → l y = l' y := by
    intro l l' y h1 hy h1' hy'
    obtain ⟨r, hr1, hry⟩ := hr y
    rw [eq_of_isLeftIntegralAt_of_isRightIntegralAt hy hry h1 hr1,
      eq_of_isLeftIntegralAt_of_isRightIntegralAt hy' hry h1' hr1]
  have hf : ∀ (T : Finset B) (z : B), z ∈ T → L {z} z = L T z := fun T z hz =>
    huniq (hL1 _) (hL _ z (Finset.mem_singleton_self z)) (hL1 T) (hL T z hz)
  let ℓ : Module.Dual K B :=
    { toFun := fun z => L {z} z
      map_add' := fun x y => by
        rw [hf {x, y, x + y} (x + y) (by simp), hf {x, y, x + y} x (by simp),
          hf {x, y, x + y} y (by simp), map_add]
      map_smul' := fun c x => by
        rw [hf {x, c • x} (c • x) (by simp), hf {x, c • x} x (by simp), map_smul]
        rfl }
  have hℓ : ∀ (T : Finset B) (z : B), z ∈ T → ℓ z = L T z := hf
  refine ⟨ℓ, hL1 {1}, fun z => ?_⟩
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset (R := K) (Coalgebra.comul (R := K) z)
  let T : Finset B := insert z (s.image Prod.snd)
  have hzT : z ∈ T := Finset.mem_insert_self _ _
  have hsT : ∀ p ∈ s, p.2 ∈ T := fun p hp =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem Prod.snd hp)
  have hact : rightAct ℓ z = rightAct (L T) z := by
    rw [rightAct_apply, rightAct_apply, hs, map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    rw [hℓ T p.2 (hsT p hp)]
  change rightAct ℓ z = ℓ z • (1 : B)
  rw [hact, hL T z hzT, hℓ T z hzT]

end Local

/-! ### The antipode of a corepresented group functor -/

section Antipode

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

open Algebra.TensorProduct (includeLeft includeRight)

theorem pt_comp_antipode {A : CommAlgCat.{u} R} (f : B →ₐ[R] A) :
    pt e (f.comp (Corepresented.antipode e).hom) = (pt e f)⁻¹ := by
  have hid : e.homEquiv (𝟙 B) = pt e (AlgHom.id R B) := by
    simp only [pt, ← CommAlgCat.hom_id, CommAlgCat.ofHom_hom]
  rw [pt_comp, Corepresented.antipode, pt_homEquiv_symm, map_inv, hid, ← pt_comp,
    AlgHom.comp_id]

theorem antipode_antipode (b : B) : (Corepresented.antipode e).hom ((Corepresented.antipode e).hom b) = b := by
  have h : (Corepresented.antipode e).hom.comp (Corepresented.antipode e).hom = AlgHom.id R B := by
    apply pt_injective e
    rw [pt_comp_antipode, Corepresented.antipode, pt_homEquiv_symm, inv_inv]
    simp only [pt, ← CommAlgCat.hom_id, CommAlgCat.ofHom_hom]
  exact AlgHom.congr_fun h b

/-- The antipode reverses the order of the coproduct. -/
theorem comul_comp_antipode :
    (comul e).comp (Corepresented.antipode e).hom =
      ((Algebra.TensorProduct.map (Corepresented.antipode e).hom (Corepresented.antipode e).hom).comp
        (Algebra.TensorProduct.comm R B B).toAlgHom).comp (comul e) := by
  apply pt_injective e (A := CommAlgCat.of R (B ⊗[R] B))
  rw [pt_comp_antipode, pt_comul,
    pt_comp_comul e _ (f := includeRight.comp (Corepresented.antipode e).hom)
      (g := includeLeft.comp (Corepresented.antipode e).hom)
      (AlgHom.ext fun b => by simp) (AlgHom.ext fun b => by simp),
    pt_comp_antipode, pt_comp_antipode, mul_inv_rev]

end Antipode

/-! ### Local right integrals for reductive groups in characteristic zero -/

section Reductive

open Chevalley MatrixRepresentation

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom H.X.hom]

/-- Characteristic-zero complete reducibility gives, for every finite set of coordinates of a
connected reductive group, a normalized functional that is a right integral at each of them. -/
theorem exists_right_integral (hss : ReductiveCharZeroSemisimplicityStatement.{u}) [CharZero k]
    (hH : IsConnectedReductive H) (T : Finset (Lie.coordinateAlgebra H)) :
    letI := bialgebra (corepresentableBy H (Lie.coordinateIso H))
    ∃ r : Module.Dual k (Lie.coordinateAlgebra H), r 1 = 1 ∧
      ∀ y ∈ T, IsRightIntegralAt r y := by
  classical
  let e := corepresentableBy H (Lie.coordinateIso H)
  let := bialgebra e
  let B := Lie.coordinateAlgebra H
  let hR : IsField (CommRingCat.of k) := Field.toIsField k
  let V : Submodule k B := regularSpan (insert 1 T)
  have hV : ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V :=
    fun f _ hv => rightAct_mem_regularSpan _ f hv
  have h1V : (1 : B) ∈ V := subset_regularSpan _ (Finset.mem_insert_self _ _)
  let N := finrank k V
  let b : Basis (Fin N) k V := Module.finBasis k V
  let M := subspaceMatrix V b
  let ρ := regularRepresentation e hR V b hV
  -- The universal point of the model and its coordinates.
  let T₀ := (algSpec (CommRingCat.of k)).obj (op B)
  let φ := (Corepresented.affineSectionsIso B).inv.hom
  have hφ : Function.Injective φ := by
    intro a a' h
    have h1 := ConcreteCategory.congr_hom (Corepresented.affineSectionsIso B).inv_hom_id a
    have h2 := ConcreteCategory.congr_hom (Corepresented.affineSectionsIso B).inv_hom_id a'
    exact h1.symm.trans ((congrArg (Corepresented.affineSectionsIso B).hom.hom h).trans h2)
  let x₀ : T₀ ⟶ (Corepresented.groupScheme H.affinePointFunctor e).X := 𝟙 _
  have hM : ∀ i j, (ρ.pointMatrix T₀ x₀ : Matrix (Fin N) (Fin N) Γ(T₀.left, ⊤)) i j =
      φ (M i j) := by
    intro i j
    refine (regularRepresentation_pointMatrix e hR V b hV T₀ x₀ i j).trans ?_
    rw [Unipotent.homEquiv_symm_pointsEquiv_affine]
    have h0 : algSpec.fullyFaithful.preimage (X := op B) (Y := op B) x₀ = 𝟙 _ :=
      algSpec.fullyFaithful.preimage_id
    rw [h0, unop_id, Category.id_comp]
    rfl
  have hs : ∀ c : k, scalarMap T₀ c = φ (algebraMap k B c) := by
    intro c
    rw [φ.commutes]
    rfl
  have hsum : ∀ (w : Fin N → k) (P : Fin N → B),
      ∑ j, φ (P j) * φ (algebraMap k B (w j)) = φ (∑ j, w j • P j) := by
    intro w P
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, mul_comm]
  -- The coordinates of `1` form a fixed vector of the regular representation.
  let u : Fin N → k := fun i => extendedCoord V b i 1
  have hu1 : ∑ i, u i • (b i : B) = 1 := basis_expand V b h1V
  have hu0 : u ≠ 0 := by
    intro h
    apply Unipotent.one_ne_zero' k B
    rw [← hu1, h]
    simp
  have hrowu : ∀ i, ∑ j, u j • M i j = u i • (1 : B) := by
    intro i
    have hleft1 : leftAct (extendedCoord V b i) (1 : B) = u i • (1 : B) := by
      rw [leftAct_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    rw [← hleft1, ← hu1, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    rfl
  have hfix : ρ.IsFixedVector u := by
    rw [isFixedVector_iff_universal]
    funext i
    change ∑ j, (ρ.pointMatrix T₀ x₀ : Matrix (Fin N) (Fin N) Γ(T₀.left, ⊤)) i j *
      scalarMap T₀ (u j) = scalarMap T₀ (u i)
    simp only [hM, hs]
    exact (hsum u (M i)).trans
      (congrArg φ (by rw [hrowu i, Algebra.smul_def, mul_one]))
  -- Restrict to `H` and apply characteristic-zero complete reducibility.
  let iso := modelIso H (Lie.coordinateIso H)
  let ρH := ρ.restrict iso.inv
  have hfixH : ρH.IsFixedVector u := by
    intro T' x
    rw [pointMatrix_restrict]
    exact hfix T' _
  obtain ⟨c, hc, hcu⟩ := exists_dual_fixed_of_semisimplicity hss hH ρH u hu0 hfixH
  have hhi : iso.hom.hom.hom ≫ iso.inv.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, Iso.hom_inv_id]
    rfl
  have hcol : ∀ j, ∑ i, c i • M i j = c j • (1 : B) := by
    intro j
    apply hφ
    have h := hc T₀ (x₀ ≫ iso.hom.hom.hom)
    rw [dual_restrict, pointMatrix_restrict, Category.assoc, hhi, Category.comp_id,
      dual_pointMatrix, contragredient_mulVec_eq_iff] at h
    have hj := congrFun h j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hM, hs] at hj
    exact (hsum c fun i => M i j).symm.trans
      (hj.trans (congrArg φ (Algebra.algebraMap_eq_smul_one _)))
  -- The integral is the corresponding combination of coordinate functionals.
  let r : Module.Dual k B := ∑ i, c i • extendedCoord V b i
  have hrb : ∀ j, r (b j : B) = c j := by
    intro j
    simp [r, LinearMap.sum_apply, extendedCoord_basis, Matrix.one_apply]
  have hr1 : r 1 = 1 := by
    rw [← hcu]
    simp [r, LinearMap.sum_apply, dotProduct, u]
  have hlin : ∀ a : B, leftAct r a = ∑ i, c i • leftAct (extendedCoord V b i) a := by
    intro a
    apply Unipotent.eq_of_forall_dual k
    intro g
    rw [apply_leftAct, map_sum]
    simp only [r, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, apply_leftAct]
  have hleft : ∀ j, leftAct r (b j : B) = c j • (1 : B) := by
    intro j
    rw [hlin, ← hcol j]
    rfl
  refine ⟨r, hr1, fun y hy => ?_⟩
  have hyV : y ∈ V := subset_regularSpan _ (Finset.mem_insert_of_mem hy)
  change leftAct r y = r y • (1 : B)
  rw [← basis_expand V b hyV, map_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, hleft j, hrb j, smul_smul, smul_eq_mul]

/-- Composing local right integrals with the antipode gives, for every finite set of
coordinates, a normalized functional that is a left integral at each of them. -/
theorem exists_left_integral_finset (hss : ReductiveCharZeroSemisimplicityStatement.{u})
    [CharZero k] (hH : IsConnectedReductive H) (T : Finset (Lie.coordinateAlgebra H)) :
    letI := bialgebra (corepresentableBy H (Lie.coordinateIso H))
    ∃ l : Module.Dual k (Lie.coordinateAlgebra H), l 1 = 1 ∧
      ∀ y ∈ T, IsLeftIntegralAt l y := by
  classical
  let e := corepresentableBy H (Lie.coordinateIso H)
  let := bialgebra e
  obtain ⟨r, hr1, hr⟩ := exists_right_integral H hss hH (T.image (Corepresented.antipode e).hom)
  refine ⟨r ∘ₗ (Corepresented.antipode e).hom.toLinearMap, ?_, fun y hy => ?_⟩
  · change r ((Corepresented.antipode e).hom 1) = 1
    rw [map_one, hr1]
  · refine isLeftIntegralAt_comp (Corepresented.antipode e).hom (fun z => ?_) (antipode_antipode e)
      (hr _ (Finset.mem_image_of_mem _ hy))
    exact AlgHom.congr_fun (comul_comp_antipode e) z

/-- Characteristic-zero complete reducibility gives a global normalized left integral on the
coordinate bialgebra of a connected reductive group. -/
theorem exists_left_integral_of_semisimplicity
    (hss : ReductiveCharZeroSemisimplicityStatement.{u}) [CharZero k]
    (hH : IsConnectedReductive H) :
    letI := bialgebra (corepresentableBy H (Lie.coordinateIso H))
    ∃ ℓ : Module.Dual k (Lie.coordinateAlgebra H), ℓ 1 = 1 ∧
      ∀ z, IsLeftIntegralAt ℓ z := by
  let := bialgebra (corepresentableBy H (Lie.coordinateIso H))
  refine exists_left_integral (fun y => ?_) (exists_left_integral_finset H hss hH)
  obtain ⟨r, hr1, hr⟩ := exists_right_integral H hss hH {y}
  exact ⟨r, hr1, hr y (Finset.mem_singleton_self y)⟩

open CoordinateIntegration in
/-- The coproduct induced by actual multiplication is the comultiplication of the corepresented
coordinate bialgebra. -/
theorem coordinateCoproduct_eq_comul (z : Coord H) :
    coordinateCoproduct H z = comul (corepresentableBy H (Lie.coordinateIso H)) z := by
  have h1 := congrArg (Lie.pointCoordinates H)
    (leftTranslation_universalPoint H (A := Coord H) (Lie.universalPoint H))
  rw [Lie.pointCoordinates_naturality, universalPoint, Equiv.apply_symm_apply] at h1
  have h2 : Lie.affineMap H Algebra.TensorProduct.includeLeft (Lie.universalPoint H) =
      (Lie.pointCoordinates H).symm
        (Algebra.TensorProduct.includeLeft : Coord H →ₐ[k] Coord H ⊗[k] Coord H) := by
    apply (Lie.pointCoordinates H).injective
    rw [Lie.pointCoordinates_naturality, Lie.universalPoint, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, AlgHom.comp_id]
  rw [h2] at h1
  exact AlgHom.congr_fun h1 z

open CoordinateIntegration in
/-- Contracting the coproduct of a coordinate against `ℓ` is the right action of `ℓ`. -/
theorem contract_comul (ℓ : Module.Dual k (Coord H)) (z : Coord H) :
    letI := bialgebra (corepresentableBy H (Lie.coordinateIso H))
    contract H (Coord H) ℓ (Coalgebra.comul (R := k) z) = rightAct ℓ z := by
  let := bialgebra (corepresentableBy H (Lie.coordinateIso H))
  rw [rightAct_apply]
  generalize Coalgebra.comul (R := k) z = t
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

end Reductive

end AffineLinearEmbedding

open AffineLinearEmbedding

/-- Given characteristic-zero complete reducibility, the normalized invariant integral on the
coordinate algebra of a connected reductive group: the glued global left integral, packaged by
the universal-coordinate criterion. -/
def invariantIntegralOfSemisimplicity (hss : ReductiveCharZeroSemisimplicityStatement.{u})
    {k : Type u} [Field k] [CharZero k] (H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom H.X.hom] (hH : IsConnectedReductive H) :
    CoordinateIntegration.InvariantIntegral H :=
  let := bialgebra (corepresentableBy H (Lie.coordinateIso H))
  let h := exists_left_integral_of_semisimplicity H hss hH
  CoordinateIntegration.InvariantIntegral.ofCoordinateCoproduct H h.choose h.choose_spec.1
    fun z => by
      rw [coordinateCoproduct_eq_comul]
      change CoordinateIntegration.contract H _ _ (Coalgebra.comul (R := k) z) = _
      rw [contract_comul]
      exact (h.choose_spec.2 z).trans (Algebra.algebraMap_eq_smul_one _).symm

/-- Characteristic-zero complete reducibility of connected reductive groups implies normalized
invariant integration on their coordinate algebras. -/
theorem characteristicZeroReductiveInvariantIntegral_of_semisimplicity
    (hss : ReductiveCharZeroSemisimplicityStatement.{u}) :
    CharacteristicZeroReductiveInvariantIntegralStatement.{u} := by
  intro k _ _ H _ hH
  exact ⟨invariantIntegralOfSemisimplicity hss H hH⟩

/-- Characteristic-zero complete reducibility implies splitting of affine faithfully flat
extensions of connected reductive groups by full finite-dimensional vector kernels. -/
theorem characteristicZeroReductiveVectorExtension_of_semisimplicity
    (hss : ReductiveCharZeroSemisimplicityStatement.{u}) :
    CharacteristicZeroReductiveVectorExtensionStatement.{u} :=
  characteristicZeroReductiveVectorExtension_of_invariantIntegral
    (characteristicZeroReductiveInvariantIntegral_of_semisimplicity hss)

end Langlands.GroupScheme
