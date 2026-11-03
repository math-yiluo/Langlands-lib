import Langlands.GroupScheme.Torus.Lattice
import Mathlib.RingTheory.FiniteType

/-! # Monomorphisms of split tori over a field

A homomorphism `f : 𝔾_m^I ⟶ 𝔾_m^J` over a field `k` has an integer matrix: the row `j` is the
character `f ≫ prᵢ` in `X^*(𝔾_m^I) ≃ ℤ^I`. On points, `f` sends `(tᵢ)` to `(∏ᵢ tᵢ ^ m j i)ⱼ`.
If `f` is a monomorphism, the rows of the matrix span `ℤ^I`; this is tested on the group algebra
`k[ℤ^I ⧸ span]`. Hence `Nat.card I ≤ Nat.card J`, and when the ranks agree the matrix is invertible
over `ℤ`, so `f` is bijective on points and therefore an isomorphism.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace splitTorus

variable {k : Type u} [Field k] {I J : Type u} [Finite I] [Finite J]

local notation "𝕊" => Spec (CommRingCat.of k)

/-- The integer matrix of a homomorphism of split tori: row `j` is the character `f ≫ prⱼ` in
`X^*(𝔾_m^I) ≃ ℤ^I`. -/
def characterMatrix (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J) : J → I → ℤ := fun j =>
  characterLatticeEquiv k I
    ((Additive.ofMul f : commGroupScheme 𝕊 I ⟶ commGroupScheme 𝕊 J) ≫ proj 𝕊 J j)

/-- On points, a homomorphism of split tori is given by its integer matrix. -/
theorem pointsEquiv_comp [Fintype I] (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J) {T : Over 𝕊}
    (x : T ⟶ (splitTorus 𝕊 I).X) (j : J) :
    pointsEquiv J T (x ≫ f.hom.hom) j = ∏ i, pointsEquiv I T x i ^ characterMatrix f j i := by
  have h1 : pointsEquiv J T (x ≫ f.hom.hom) j =
      Gm.pointsEquiv 𝕊 T ((x ≫ f.hom.hom) ≫ (CommGroupScheme.groupHom (proj 𝕊 J j)).hom.hom) :=
    (comp_proj 𝕊 J (x ≫ f.hom.hom) j).symm
  have h2 : (CommGroupScheme.groupHom
      ((Additive.ofMul f : commGroupScheme 𝕊 I ⟶ commGroupScheme 𝕊 J) ≫ proj 𝕊 J j)).hom.hom =
      f.hom.hom ≫ (CommGroupScheme.groupHom (proj 𝕊 J j)).hom.hom :=
    rfl
  have h3 : (characterLatticeEquiv k I).symm (characterMatrix f j) =
      (Additive.ofMul f : commGroupScheme 𝕊 I ⟶ commGroupScheme 𝕊 J) ≫ proj 𝕊 J j :=
    AddEquiv.symm_apply_apply _ _
  have h4 := pointsEquiv_characterLatticeEquiv_symm k I (characterMatrix f j) x
  rw [h3] at h4
  rw [h1, Category.assoc, ← h2]
  exact h4

/-- The same formula for points over an affine test scheme. -/
theorem affinePointsEquiv_comp [Fintype I] (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J)
    {R : CommRingCat.{u}} (g : Spec R ⟶ 𝕊) (x : Over.mk g ⟶ (splitTorus 𝕊 I).X) (j : J) :
    affinePointsEquiv J g (x ≫ f.hom.hom) j =
      ∏ i, affinePointsEquiv I g x i ^ characterMatrix f j i := by
  let ρ : (Γ((Over.mk g).left, ⊤))ˣ ≃* Rˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv
  change ρ (pointsEquiv J (Over.mk g) (x ≫ f.hom.hom) j) =
    ∏ i, ρ (pointsEquiv I (Over.mk g) x i) ^ characterMatrix f j i
  rw [pointsEquiv_comp, map_prod]
  simp_rw [map_zpow]

/-- The rows of the integer matrix, as a `ℤ`-linear map `ℤ^J → ℤ^I`, `n ↦ ∑ⱼ nⱼ • mⱼ`. -/
abbrev characterRows (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J) : (J → ℤ) →ₗ[ℤ] (I → ℤ) :=
  let _ : Fintype J := Fintype.ofFinite J
  Fintype.linearCombination ℤ (characterMatrix f)

open Classical in
theorem characterRows_single (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J) (j : J) :
    characterRows f (Pi.single j 1) = characterMatrix f j := by
  classical
  rw [characterRows, Fintype.linearCombination_apply_single, one_smul]

section Surjective

variable (k) (I) in
/-- The group algebra over `k` of a quotient `ℤ^I ⧸ L`, used as a test algebra. -/
abbrev testAlgebra (L : Submodule ℤ (I → ℤ)) : Type u :=
  AddMonoidAlgebra k ((I → ℤ) ⧸ L)

variable (k) (I) in
/-- The units `[n]` of the test algebra attached to `n ∈ ℤ^I`. -/
def testUnit (L : Submodule ℤ (I → ℤ)) : Multiplicative (I → ℤ) →* (testAlgebra k I L)ˣ :=
  (AddMonoidAlgebra.of k ((I → ℤ) ⧸ L)).toHomUnits.comp
    (AddMonoidHom.toMultiplicative L.mkQ.toAddMonoidHom)

omit [Finite I] in
theorem testUnit_eq_one_iff (L : Submodule ℤ (I → ℤ)) (n : I → ℤ) :
    testUnit k I L (Multiplicative.ofAdd n) = 1 ↔ n ∈ L := by
  constructor
  · intro h
    have h' : AddMonoidAlgebra.of k ((I → ℤ) ⧸ L) (Multiplicative.ofAdd (L.mkQ n)) =
        AddMonoidAlgebra.of k ((I → ℤ) ⧸ L) 1 := by
      rw [map_one]
      exact congrArg Units.val h
    have h'' := AddMonoidAlgebra.of_injective h'
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff] at h''
    exact (Submodule.Quotient.mk_eq_zero L).mp h''
  · intro h
    have h' : L.mkQ n = 0 := (Submodule.Quotient.mk_eq_zero L).mpr h
    simp only [testUnit, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply,
      toAdd_ofAdd, LinearMap.toAddMonoidHom_coe, h', ofAdd_zero, map_one]

omit [Finite I] in
open Classical in
theorem prod_testUnit_zpow [Fintype I] (L : Submodule ℤ (I → ℤ)) (n : I → ℤ) :
    ∏ i, testUnit k I L (Multiplicative.ofAdd (Pi.single i 1)) ^ n i =
      testUnit k I L (Multiplicative.ofAdd n) := by
  classical
  simp_rw [← map_zpow, ← map_prod]
  congr 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_prod]
  simp_rw [toAdd_zpow, toAdd_ofAdd]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

/-- If `f` is a monomorphism, the rows of its integer matrix span `ℤ^I`. -/
theorem characterRows_surjective (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J) [Mono f.hom.hom] :
    Function.Surjective (characterRows f) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  let _ : Fintype J := Fintype.ofFinite J
  let L := LinearMap.range (characterRows f)
  let R := CommRingCat.of (testAlgebra k I L)
  let g : Spec R ⟶ 𝕊 := Spec.map (CommRingCat.ofHom (algebraMap k (testAlgebra k I L)))
  let x : Over.mk g ⟶ (splitTorus 𝕊 I).X := (affinePointsEquiv I g).symm
    fun i => testUnit k I L (Multiplicative.ofAdd (Pi.single i 1))
  have hx : affinePointsEquiv I g x = fun i => testUnit k I L (Multiplicative.ofAdd (Pi.single i 1)) :=
    MulEquiv.apply_symm_apply _ _
  have hfx : x ≫ f.hom.hom = 1 ≫ f.hom.hom := by
    rw [MonObj.one_comp]
    apply (affinePointsEquiv J g).injective
    funext j
    rw [affinePointsEquiv_comp, hx, map_one, Pi.one_apply, prod_testUnit_zpow,
      testUnit_eq_one_iff]
    exact ⟨Pi.single j 1, characterRows_single f j⟩
  have hx1 : x = 1 := (cancel_mono f.hom.hom).mp hfx
  rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun ℤ I).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply, SetLike.mem_coe, ← testUnit_eq_one_iff (k := k)]
  have h := congrFun hx i
  rw [hx1, map_one] at h
  exact h.symm

end Surjective

/-- A monomorphism `𝔾_m^I ⟶ 𝔾_m^J` of split tori over a field has `Nat.card I ≤ Nat.card J`. -/
theorem card_le_of_mono (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J) (hf : Mono f.hom.hom) :
    Nat.card I ≤ Nat.card J := by
  let _ : Fintype I := Fintype.ofFinite I
  let _ : Fintype J := Fintype.ofFinite J
  have h := LinearMap.finrank_range_le (characterRows f)
  rw [LinearMap.range_eq_top.mpr (characterRows_surjective f), finrank_top,
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

/-- If `f` is a monomorphism and `Nat.card J ≤ Nat.card I`, the rows of its integer matrix form a
basis of `ℤ^I`. -/
theorem characterRows_bijective (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J) [Mono f.hom.hom]
    (h : Nat.card J ≤ Nat.card I) : Function.Bijective (characterRows f) := by
  let _ : Fintype I := Fintype.ofFinite I
  let _ : Fintype J := Fintype.ofFinite J
  have hc : Fintype.card J = Fintype.card I := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact le_antisymm h (card_le_of_mono f inferInstance)
  let e : (J → ℤ) ≃ₗ[ℤ] (I → ℤ) := LinearEquiv.funCongrLeft ℤ ℤ (Fintype.equivOfCardEq hc).symm
  exact OrzechProperty.bijective_of_surjective_of_injective e.toLinearMap (characterRows f)
    e.injective (characterRows_surjective f)

open Classical in
/-- A monomorphism `f : 𝔾_m^I ⟶ 𝔾_m^J` with `Nat.card J ≤ Nat.card I` is surjective on points. -/
theorem comp_surjective_of_mono (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J) [Mono f.hom.hom]
    (h : Nat.card J ≤ Nat.card I) (T : Over 𝕊) :
    Function.Surjective fun x : T ⟶ (splitTorus 𝕊 I).X => x ≫ f.hom.hom := by
  let _ : Fintype I := Fintype.ofFinite I
  let _ : Fintype J := Fintype.ofFinite J
  intro y
  let M := Additive (Γ(T.left, ⊤))ˣ
  let Le : (J → ℤ) ≃ₗ[ℤ] (I → ℤ) := LinearEquiv.ofBijective _ (characterRows_bijective f h)
  let φ : (J → ℤ) →ₗ[ℤ] M :=
    (Pi.basisFun ℤ J).constr ℤ fun j => Additive.ofMul (pointsEquiv J T y j)
  let ψ : (I → ℤ) →ₗ[ℤ] M := φ ∘ₗ Le.symm.toLinearMap
  refine ⟨(pointsEquiv I T).symm fun i => (ψ (Pi.basisFun ℤ I i)).toMul, ?_⟩
  apply (pointsEquiv J T).injective
  funext j
  rw [pointsEquiv_comp, MulEquiv.apply_symm_apply]
  have key : ∑ i, characterMatrix f j i • ψ (Pi.basisFun ℤ I i) = ψ (characterMatrix f j) := by
    conv_rhs => rw [← (Pi.basisFun ℤ I).sum_repr (characterMatrix f j)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.basisFun_repr]
  have key' : ψ (characterMatrix f j) = Additive.ofMul (pointsEquiv J T y j) := by
    rw [← characterRows_single]
    change φ (Le.symm (Le (Pi.single j 1))) = _
    rw [LinearEquiv.symm_apply_apply, ← Pi.basisFun_apply, Module.Basis.constr_basis]
  have := congrArg Additive.toMul (key.trans key')
  rw [toMul_sum] at this
  exact this

/-- A monomorphism `f : 𝔾_m^I ⟶ 𝔾_m^J` of split tori over a field with
`Nat.card J ≤ Nat.card I` is an isomorphism. -/
theorem isIso_of_mono (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J) (hf : Mono f.hom.hom)
    (h : Nat.card J ≤ Nat.card I) : IsIso f := by
  let φ : ∀ T : Over 𝕊, (T ⟶ (splitTorus 𝕊 I).X) →* (T ⟶ (splitTorus 𝕊 J).X) := fun T =>
    { toFun := fun x => x ≫ f.hom.hom
      map_one' := MonObj.one_comp _
      map_mul' := fun x y => MonObj.mul_comp x y _ }
  let e : ∀ T : Over 𝕊, (T ⟶ (splitTorus 𝕊 I).X) ≃* (T ⟶ (splitTorus 𝕊 J).X) := fun T =>
    MulEquiv.ofBijective (φ T)
      ⟨fun x y hxy => (cancel_mono f.hom.hom).mp hxy, comp_surjective_of_mono f h T⟩
  have he : ∀ {T T' : Over 𝕊} (a : T' ⟶ T) (x : T ⟶ (splitTorus 𝕊 I).X),
      e T' (a ≫ x) = a ≫ e T x := fun a x =>
    show (a ≫ x) ≫ f.hom.hom = a ≫ x ≫ f.hom.hom from Category.assoc _ _ _
  have hfe : (isoOfPoints e he).hom = f :=
    hom_ext_points fun T x => comp_isoOfPoints_hom e he T x
  rw [← hfe]
  infer_instance

end splitTorus

/-! ### Transport along isomorphisms with split tori -/

section Transport

variable {k : Type u} [Field k] {I J : Type u} [Finite I] [Finite J]
  {H K : GroupScheme (Spec (CommRingCat.of k))}

/-- Conjugating a monomorphism by isomorphisms with split tori gives a monomorphism of split
tori. -/
theorem splitTorus.mono_conj_of_iso (eH : H ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (eK : K ≅ splitTorus (Spec (CommRingCat.of k)) J) (f : H ⟶ K) (hf : Mono f.hom.hom) :
    Mono (eH.inv ≫ f ≫ eK.hom).hom.hom := by
  have h1 : IsIso eH.inv.hom.hom := (inferInstance : IsIso ((Grp.forget _).mapIso eH).inv)
  have h2 : IsIso eK.hom.hom.hom := (inferInstance : IsIso ((Grp.forget _).mapIso eK).hom)
  change Mono (eH.inv.hom.hom ≫ f.hom.hom ≫ eK.hom.hom.hom)
  infer_instance

/-- A monomorphism between group schemes isomorphic to `𝔾_m^I` and `𝔾_m^J` over a field has
`Nat.card I ≤ Nat.card J`. -/
theorem splitTorus.card_le_of_mono_of_iso (eH : H ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (eK : K ≅ splitTorus (Spec (CommRingCat.of k)) J) (f : H ⟶ K) (hf : Mono f.hom.hom) :
    Nat.card I ≤ Nat.card J :=
  splitTorus.card_le_of_mono _ (splitTorus.mono_conj_of_iso eH eK f hf)

/-- A monomorphism between group schemes isomorphic to `𝔾_m^I` and `𝔾_m^J` over a field, with
`Nat.card J ≤ Nat.card I`, is an isomorphism. -/
theorem splitTorus.isIso_of_mono_of_iso (eH : H ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (eK : K ≅ splitTorus (Spec (CommRingCat.of k)) J) (f : H ⟶ K) (hf : Mono f.hom.hom)
    (h : Nat.card J ≤ Nat.card I) : IsIso f := by
  have := splitTorus.isIso_of_mono _ (splitTorus.mono_conj_of_iso eH eK f hf) h
  have hf' : f = eH.hom ≫ (eH.inv ≫ f ≫ eK.hom) ≫ eK.inv := by simp
  rw [hf']
  infer_instance

end Transport

end Langlands.GroupScheme
