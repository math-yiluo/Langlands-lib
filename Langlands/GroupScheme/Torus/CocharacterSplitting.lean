import Langlands.GroupScheme.Torus.CocharacterDatum
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Mathlib.RingTheory.Flat.Basic

/-! # Points of a torus over a splitting field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CocharacterSplitting

set_option backward.isDefEq.respectTransparency false

open CocharacterDatum

/-- Precomposition with an isomorphism of test objects, on points of a group scheme. -/
def precompEquiv {S₀ : Scheme.{u}} {G : GroupScheme S₀} {T T' : Over S₀} (ε : T' ≅ T) :
    (T ⟶ G.X) ≃* (T' ⟶ G.X) where
  toFun x := ε.hom ≫ x
  invFun y := ε.inv ≫ y
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := MonObj.comp_mul _ _ _

/-- The inverse of the pullback point equivalence is natural in the test scheme. -/
theorem baseChangePointsEquiv_symm_naturality {S₀ S₁ : Scheme.{u}} (b : S₁ ⟶ S₀)
    (G : GroupScheme S₀) {T T' : Over S₁} (a : T' ⟶ T) (y : (Over.map b).obj T ⟶ G.X) :
    (baseChangePointsEquiv b G T').symm ((Over.map b).map a ≫ y) =
      a ≫ (baseChangePointsEquiv b G T).symm y := by
  apply (baseChangePointsEquiv b G T').injective
  rw [MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality, MulEquiv.apply_symm_apply]

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]

/-- The base change morphism `Spec K ⟶ Spec k`. -/
abbrev baseMap : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

section Test

variable (S : Type u) [CommRing S] [Algebra K S] [Algebra k S] [IsScalarTower k K S]

/-- The spectrum of a `K`-algebra `S`, as a scheme over `Spec K`. -/
abbrev testScheme : Over (Spec (CommRingCat.of K)) :=
  (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of (CommRingCat.of K) S))

/-- Over `Spec k`, the spectrum of `S` is its spectrum over `Spec K` followed by the base map. -/
def testIso : (Over.map (baseMap K)).obj (testScheme K S) ≅
    (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) S)) :=
  Over.isoMk (Iso.refl _) (by
    rw [Over.map_obj_hom, algSpec_obj_hom, algSpec_obj_hom, Iso.refl_hom, Category.id_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

@[simp] theorem testIso_hom_left : (testIso (k := k) K S).hom.left = 𝟙 _ := rfl

variable {S} {S' : Type u} [CommRing S'] [Algebra K S'] [Algebra k S'] [IsScalarTower k K S']

theorem testIso_hom_comp_map (f : S →ₐ[K] S') :
    (testIso K S').hom ≫ (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (f.restrictScalars k)).op =
      (Over.map (baseMap K)).map ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom f).op) ≫
        (testIso K S).hom := by
  ext : 1
  rfl

end Test

/-! ### Points over `K`-algebras -/

section Points

variable {K} {Z : CommGroupScheme (Spec (CommRingCat.of k))} {I : Type u} [Finite I]
  (e : (GroupScheme.baseChange (baseMap K)).obj Z.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)

variable (S : Type u) [CommRing S] [Algebra K S] [Algebra k S] [IsScalarTower k K S]

/-- A splitting `Z_K ≅ 𝔾_m^I` identifies the points of `Z` over a `K`-algebra `S` with `(Sˣ)^I`. -/
def pointsEquiv : Lie.AffinePoints Z.toGrp S ≃* (I → Sˣ) :=
  (((precompEquiv (testIso K S)).trans
    (baseChangePointsEquiv (baseMap K) Z.toGrp (testScheme K S)).symm).trans
    (isoPointsEquiv e (testScheme K S))).trans (splitTorus.algebraPointsEquiv I S)

theorem pointsEquiv_apply (x : Lie.AffinePoints Z.toGrp S) :
    pointsEquiv e S x = splitTorus.algebraPointsEquiv I S
      ((baseChangePointsEquiv (baseMap K) Z.toGrp (testScheme K S)).symm
        ((testIso K S).hom ≫ x) ≫ e.hom.hom.hom) := rfl

variable {S} {S' : Type u} [CommRing S'] [Algebra K S'] [Algebra k S'] [IsScalarTower k K S']

/-- The splitting is natural in the `K`-algebra. -/
theorem pointsEquiv_naturality (f : S →ₐ[K] S') (x : Lie.AffinePoints Z.toGrp S) :
    pointsEquiv e S' (Lie.affineMap Z.toGrp (f.restrictScalars k) x) =
      fun i => Units.map f.toMonoidHom (pointsEquiv e S x i) := by
  rw [pointsEquiv_apply, pointsEquiv_apply, Lie.affineMap_apply, ← Category.assoc,
    testIso_hom_comp_map, Category.assoc, baseChangePointsEquiv_symm_naturality, Category.assoc,
    ← Lie.affineMap_apply (splitTorus (Spec (CommRingCat.of K)) I) f,
    splitTorus.algebraPointsEquiv_naturality]

end Points

/-! ### Character values -/

section Values

variable {K} {Z : CommGroupScheme (Spec (CommRingCat.of k))} {I : Type u} [Finite I]
  (e : (GroupScheme.baseChange (baseMap K)).obj Z.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)

/-- The weight of a character of `Z` in the splitting `Z_K ≅ 𝔾_m^I`. -/
def weight (χ : characterLattice Z) : I → ℤ :=
  splitTorus.characterLatticeEquiv K I
    (Additive.ofMul e.inv ≫ characterLattice.baseChange (baseMap K) Z χ)

variable [Fintype I]
variable {S : Type u} [CommRing S] [Algebra K S] [Algebra k S] [IsScalarTower k K S]

/-- In the splitting, a character takes the value `∏ tᵢ ^ mᵢ`, `m` its weight. -/
theorem characterValue_eq (χ : characterLattice Z) (x : Lie.AffinePoints Z.toGrp S) :
    Lie.characterValue χ x =
      splitTorus.exponentValue I (pointsEquiv e S x) (Multiplicative.ofAdd (weight e χ)) := by
  rw [pointsEquiv_apply, weight, ← splitTorus.characterValue_characterLatticeEquiv_symm K I,
    AddEquiv.symm_apply_apply, Lie.characterValue_comp]
  change _ = Lie.characterValue (characterLattice.baseChange (baseMap K) Z χ)
    (((baseChangePointsEquiv (baseMap K) Z.toGrp (testScheme K S)).symm
      ((testIso K S).hom ≫ x) ≫ e.hom.hom.hom) ≫ e.inv.hom.hom)
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  apply Units.ext
  rw [Lie.characterValue, Lie.characterValue, Gm.affinePointsEquiv_val, Gm.affinePointsEquiv_val]
  congr 2
  change _ = Gm.pointsEquiv _ (testScheme K S)
    ((baseChangePointsEquiv (baseMap K) Z.toGrp (testScheme K S)).symm ((testIso K S).hom ≫ x) ≫
      ((GroupScheme.baseChange (baseMap K)).map (CommGroupScheme.groupHom χ)).hom.hom ≫
        (Gm.baseChangeIso (baseMap K)).hom.hom.hom)
  rw [← Category.assoc, Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply,
    baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, Category.assoc,
    Gm.pointsEquiv_naturality (a := (testIso K S).hom), testIso_hom_left]
  rfl

/-- The value of a rational character, read through the character lattice, is its evaluation
transported along `Γ(Spec S) ≅ S`. -/
theorem characterValue_equivCharacterLattice {S : Type u} [CommRing S] [Algebra k S]
    (χ : rationalCharacters Z.toGrp) (x : Lie.AffinePoints Z.toGrp S) :
    Lie.characterValue (rationalCharacters.equivCharacterLattice Z χ) x =
      Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.toMulEquiv
        (characterEval χ _ x) :=
  rfl

/-- A rational character of weight zero in the splitting is trivial. -/
theorem eq_zero_of_weight_eq_zero [IsAffine Z.toGrp.X.left] {χ : rationalCharacters Z.toGrp}
    (h : weight e (rationalCharacters.equivCharacterLattice Z χ) = 0) : χ = 0 := by
  apply CharacterRestrictionFiniteIndex.rationalCharacters_ext_affine
  intro B y
  rw [characterEval_zero]
  have hι : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  have h1 := characterValue_eq e (rationalCharacters.equivCharacterLattice Z χ)
    (Lie.affineMap Z.toGrp (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) y)
  rw [h, ofAdd_zero, map_one, characterValue_affineMap] at h1
  have h2 : Lie.characterValue (rationalCharacters.equivCharacterLattice Z χ) y = 1 :=
    Units.map_injective hι (by rw [h1, map_one])
  rw [characterValue_equivCharacterLattice] at h2
  exact (MulEquiv.map_eq_one_iff _).mp h2

end Values

/-! ### Split points over group algebras -/

section SplitPoint

variable {K} {Z : CommGroupScheme (Spec (CommRingCat.of k))} {I : Type u} [Finite I]
  (e : (GroupScheme.baseChange (baseMap K)).obj Z.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
variable {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']

omit [Finite I] in
theorem restrictScalars_mapDomainAlgHom (g : Λ →+ Λ') :
    (AddMonoidAlgebra.mapDomainAlgHom K K g).restrictScalars k =
      AddMonoidAlgebra.mapDomainAlgHom k K g :=
  rfl

omit [Finite I] in
theorem units_map_mapDomainAlgHom_monomial (g : Λ →+ Λ') (γ : Λ) :
    Units.map (AddMonoidAlgebra.mapDomainAlgHom K K g).toMonoidHom (monomial K γ) =
      monomial K (g γ) := by
  apply Units.ext
  simp

/-- The point of `Z` over `K[Λ]` whose split coordinates are the monomials `X ^ c i`. -/
def splitPoint (c : I → Λ) : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra K Λ) :=
  (pointsEquiv e _).symm fun i => monomial K (c i)

theorem pointsEquiv_expMap_splitPoint (c : I → Λ) (g : Λ →+ Λ') :
    pointsEquiv e _ (expMap K g (splitPoint e c)) = fun i => monomial K (g (c i)) := by
  rw [expMap, ← restrictScalars_mapDomainAlgHom, pointsEquiv_naturality, splitPoint,
    MulEquiv.apply_symm_apply]
  funext i
  exact units_map_mapDomainAlgHom_monomial g (c i)

theorem isMult_splitPoint (c : I → Λ) : IsMult (splitPoint e c) := by
  apply (pointsEquiv e _).injective
  rw [map_mul, pointsEquiv_expMap_splitPoint, pointsEquiv_expMap_splitPoint,
    pointsEquiv_expMap_splitPoint]
  funext i
  rw [Pi.mul_apply, ← monomial_add]
  congr 1
  simp

variable [Fintype I]

theorem characterValue_splitPoint (χ : characterLattice Z) (c : I → Λ) :
    Lie.characterValue χ (splitPoint e c) = monomial K (∑ i, weight e χ i • c i) := by
  rw [characterValue_eq e, splitPoint, MulEquiv.apply_symm_apply]
  change ∏ i, monomial K (c i) ^ weight e χ i = _
  simp only [monomial, ← map_zpow, ← map_prod, ofAdd_sum, ofAdd_zsmul]

/-- The split point is a cocharacter datum of weight `∑ i, mᵢ • cᵢ`, `m` the weight of `χ`. -/
theorem isDatum_splitPoint (χ : characterLattice Z) (c : I → Λ) :
    IsDatum χ (∑ i, weight e χ i • c i) (splitPoint e c) where
  mult := isMult_splitPoint e c
  value := characterValue_splitPoint e χ c

include e in
/-- **Data over a splitting field.** A nonzero rational character of `Z` has a cocharacter
datum of nonzero weight over `K[ℤ]`. -/
theorem exists_isDatum [IsAffine Z.toGrp.X.left] {χ : rationalCharacters Z.toGrp} (hχ : χ ≠ 0) :
    ∃ (m : PUnit.{u+1} → ℤ) (p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra K (PUnit.{u+1} → ℤ))),
      m ≠ 0 ∧ IsDatum (rationalCharacters.equivCharacterLattice Z χ) m p := by
  classical
  have hw : weight e (rationalCharacters.equivCharacterLattice Z χ) ≠ 0 := fun h =>
    hχ (eq_zero_of_weight_eq_zero e h)
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hw
  refine ⟨_, splitPoint e (Pi.single j₀ 1), ?_, isDatum_splitPoint e _ _⟩
  rw [Finset.sum_eq_single j₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, smul_zero])
    (fun h => absurd (Finset.mem_univ j₀) h), Pi.single_eq_same]
  intro h
  exact hj₀ (by simpa using congrFun h PUnit.unit)

end SplitPoint

/-! ### Frobenius on points -/

section Frobenius

variable {K} {Z : CommGroupScheme (Spec (CommRingCat.of k))} {I : Type u} [Finite I]
  (e : (GroupScheme.baseChange (baseMap K)).obj Z.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)

include e in
/-- If a `K`-algebra map agrees with the identity after `n`-th powers, so does its action on
points of `Z`. -/
theorem pow_affineMap_eq (n : ℕ) {S : Type u} [CommRing S] [Algebra K S] [Algebra k S]
    [IsScalarTower k K S] (φ : S →ₐ[K] S) (hφ : ∀ s, s ^ n = φ s ^ n)
    (y : Lie.AffinePoints Z.toGrp S) :
    y ^ n = Lie.affineMap Z.toGrp (φ.restrictScalars k) y ^ n := by
  apply (pointsEquiv e S).injective
  rw [map_pow, map_pow, pointsEquiv_naturality]
  funext i
  apply Units.ext
  rw [Pi.pow_apply, Pi.pow_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    Units.coe_map]
  exact hφ _

include e in
/-- **Frobenius on points.** If `(id ⊗ g)` agrees with the identity on `K ⊗[k] A` after `n`-th
powers, then `u ^ n = (g_* u) ^ n` for every point `u` of `Z` over `A`. -/
theorem pow_affineMap_eq_of_tensor [IsAffine Z.toGrp.X.left] (n : ℕ) {A : Type u} [CommRing A]
    [Algebra k A] (g : A →ₐ[k] A)
    (hg : ∀ x : K ⊗[k] A, x ^ n = Algebra.TensorProduct.map (AlgHom.id K K) g x ^ n)
    (u : Lie.AffinePoints Z.toGrp A) : u ^ n = Lie.affineMap Z.toGrp g u ^ n := by
  apply affineMap_injective (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective)
  rw [map_pow, map_pow, ← Lie.affineMap_comp, ← Algebra.TensorProduct.map_restrictScalars_comp_includeRight
    (AlgHom.id K K) g, Lie.affineMap_comp]
  exact pow_affineMap_eq e n _ hg _

end Frobenius

end Langlands.GroupScheme.CocharacterSplitting
