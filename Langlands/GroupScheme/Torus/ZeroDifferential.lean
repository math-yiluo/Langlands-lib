import Langlands.GroupScheme.Rational.SplitTorusFiniteRank
import Langlands.GroupScheme.Torus.CharacterMapHom
import Langlands.GroupScheme.Torus.WeightDecomposition
import Mathlib.Algebra.CharP.Defs

/-! # Zero differentials and divisibility of split-torus character maps -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace splitTorus

variable (A : Type u) [CommRing A]

/-- Addition of infinitesimal coefficients is multiplication of the corresponding units. -/
def infinitesimalUnitAddHom : A →+ Additive (DualNumber A)ˣ where
  toFun a := Additive.ofMul (infinitesimalUnit A a)
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    ext <;> simp [infinitesimalUnit]
  map_add' a b := congrArg Additive.ofMul (infinitesimalUnit_mul A a b)

/-- Integral powers of infinitesimal units multiply their infinitesimal coefficients. -/
theorem infinitesimalUnit_zpow (a : A) (n : ℤ) :
    infinitesimalUnit A a ^ n = infinitesimalUnit A ((n : A) * a) := by
  have h := congrArg Additive.toMul ((infinitesimalUnitAddHom A).map_zsmul n a)
  change infinitesimalUnit A (n • a) = infinitesimalUnit A a ^ n at h
  simpa only [zsmul_eq_mul] using h.symm

/-- A finite product of infinitesimal units adds their coefficients. -/
theorem prod_infinitesimalUnit {I : Type u} (s : Finset I) (a : I → A) :
    ∏ i ∈ s, infinitesimalUnit A (a i) = infinitesimalUnit A (∑ i ∈ s, a i) := by
  simpa only [toMul_sum, infinitesimalUnitAddHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul] using
    (congrArg Additive.toMul (map_sum (infinitesimalUnitAddHom A) a s)).symm

variable {k : Type u} [Field k] (I : Type u) [Fintype I]
variable [Algebra k A]

/-- The value of a split-torus character on an infinitesimal point is its integral
coordinate pairing with that tangent vector. -/
theorem characterValue_infinitesimalPoint (χ : characterLattice
    (commGroupScheme (Spec (CommRingCat.of k)) I)) (v : I → A) :
    Lie.characterValue χ (infinitesimalPoint (R := CommRingCat.of k) I A v).val =
      infinitesimalUnit A (∑ i, (characterLatticeEquiv k I χ i : A) * v i) := by
  conv_lhs => rw [← (characterLatticeEquiv k I).symm_apply_apply χ]
  rw [characterValue_characterLatticeEquiv_symm]
  simp only [infinitesimalPoint, MulEquiv.apply_symm_apply, exponentValue]
  change (∏ i, infinitesimalUnit A (v i) ^ (characterLatticeEquiv k I χ i)) = _
  simp_rw [infinitesimalUnit_zpow]
  exact prod_infinitesimalUnit A Finset.univ _

/-- A split-torus character whose differential vanishes has all its exponents zero
in the base field. -/
theorem character_coordinates_cast_eq_zero (χ : characterLattice
    (commGroupScheme (Spec (CommRingCat.of k)) I))
    (hχ : ∀ X : lieKernel (splitTorus (Spec (CommRingCat.of k)) I) k,
      Lie.targetMap (CommGroupScheme.groupHom χ) k X = 1) (i : I) :
    (characterLatticeEquiv k I χ i : k) = 0 := by
  classical
  let X := infinitesimalPoint (R := CommRingCat.of k) I k (Pi.single i 1)
  have hval : Lie.characterValue χ X.val = 1 := by
    change Gm.affinePointsEquiv _ (Lie.targetMap (CommGroupScheme.groupHom χ) k X).val = 1
    rw [hχ, OneMemClass.coe_one, map_one]
  rw [characterValue_infinitesimalPoint] at hval
  have hsnd := congrArg (fun z : (DualNumber k)ˣ => z.val.snd) hval
  simpa [infinitesimalUnit, X, Pi.single_apply] using hsnd

/-- In characteristic `p`, the exponents of a character with zero differential are
divisible by `p`, including the characteristic-zero interpretation. -/
theorem characteristic_dvd_character_coordinates (p : ℕ) [CharP k p]
    (χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (hχ : ∀ X : lieKernel (splitTorus (Spec (CommRingCat.of k)) I) k,
      Lie.targetMap (CommGroupScheme.groupHom χ) k X = 1) (i : I) :
    (p : ℤ) ∣ characterLatticeEquiv k I χ i := by
  exact (CharP.intCast_eq_zero_iff k p _).mp
    (character_coordinates_cast_eq_zero I χ hχ i)

/-- Every split-torus character with zero differential is an integral multiple of
another character by the positive characteristic. -/
theorem exists_character_div_characteristic (p : ℕ) [CharP k p]
    (χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (hχ : ∀ X : lieKernel (splitTorus (Spec (CommRingCat.of k)) I) k,
      Lie.targetMap (CommGroupScheme.groupHom χ) k X = 1) :
    ∃ ψ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I),
      (p : ℤ) • ψ = χ := by
  classical
  choose m hm using characteristic_dvd_character_coordinates I p χ hχ
  refine ⟨(characterLatticeEquiv k I).symm m, ?_⟩
  apply (characterLatticeEquiv k I).injective
  ext i
  simpa only [map_zsmul, AddEquiv.apply_symm_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_id]
    using (hm i).symm

/-- A nonzero integer acts injectively on the character lattice of a split torus. -/
theorem zsmul_character_injective (n : ℤ) (hn : n ≠ 0) :
    Function.Injective (fun χ : characterLattice
      (commGroupScheme (Spec (CommRingCat.of k)) I) => n • χ) := by
  intro χ ψ h
  apply (characterLatticeEquiv k I).injective
  ext i
  have hi := congrFun (congrArg (characterLatticeEquiv k I) h) i
  simp only [map_zsmul, Pi.smul_apply, zsmul_eq_mul] at hi
  exact mul_left_cancel₀ hn hi

/-- Zero differential of a map from a standard split torus to a split torus implies
factorization through multiplication by the positive characteristic. -/
theorem exists_factor_characteristic_of_zero_differential
    {T' : CommGroupScheme (Spec (CommRingCat.of k))} (hT' : IsSplitTorus T'.toGrp)
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (f : commGroupScheme (Spec (CommRingCat.of k)) I ⟶ T')
    (hf : ∀ X : lieKernel (splitTorus (Spec (CommRingCat.of k)) I) k,
      Lie.targetMap (CommGroupScheme.groupHom f) k X = 1) :
    ∃ g : commGroupScheme (Spec (CommRingCat.of k)) I ⟶ T',
      f = ((p : ℤ) • 𝟙 _) ≫ g := by
  classical
  have hχ (χ : characterLattice T') :
      ∀ X : lieKernel (splitTorus (Spec (CommRingCat.of k)) I) k,
        Lie.targetMap (CommGroupScheme.groupHom (f ≫ χ)) k X = 1 := by
    intro X
    change Lie.targetMap (CommGroupScheme.groupHom χ) k
      (Lie.targetMap (CommGroupScheme.groupHom f) k X) = 1
    rw [hf, map_one]
  choose ψ hψ using fun χ : characterLattice T' =>
    exists_character_div_characteristic I p (f ≫ χ) (hχ χ)
  have hinj := zsmul_character_injective (k := k) I (p : ℤ) (Int.natCast_ne_zero.mpr hp)
  let F : characterLattice T' →+ characterLattice
      (commGroupScheme (Spec (CommRingCat.of k)) I) :=
    { toFun := ψ
      map_zero' := by
        apply hinj
        change (p : ℤ) • ψ 0 = (p : ℤ) • (0 : characterLattice _)
        rw [hψ, smul_zero, comp_zero]
      map_add' := fun χ ζ => by
        apply hinj
        change (p : ℤ) • ψ (χ + ζ) = (p : ℤ) • (ψ χ + ψ ζ)
        rw [smul_add, hψ, hψ, hψ, Preadditive.comp_add] }
  refine ⟨hT'.homOfCharacterMap F, ?_⟩
  apply hT'.hom_ext_of_characters
  intro χ
  rw [Category.assoc, IsSplitTorus.homOfCharacterMap_comp,
    Preadditive.zsmul_comp, Category.id_comp]
  exact (hψ χ).symm

/-- In characteristic zero, a split-torus character with zero differential is zero. -/
theorem character_eq_zero_of_zero_differential [CharZero k]
    (χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (hχ : ∀ X : lieKernel (splitTorus (Spec (CommRingCat.of k)) I) k,
      Lie.targetMap (CommGroupScheme.groupHom χ) k X = 1) : χ = 0 := by
  apply (characterLatticeEquiv k I).injective
  ext i
  simpa only [map_zero, Pi.zero_apply, Int.cast_eq_zero] using
    character_coordinates_cast_eq_zero I χ hχ i

/-- In characteristic zero, a map from a standard split torus to a split torus with
zero differential is zero. -/
theorem hom_eq_zero_of_zero_differential [CharZero k]
    {T' : CommGroupScheme (Spec (CommRingCat.of k))} (hT' : IsSplitTorus T'.toGrp)
    (f : commGroupScheme (Spec (CommRingCat.of k)) I ⟶ T')
    (hf : ∀ X : lieKernel (splitTorus (Spec (CommRingCat.of k)) I) k,
      Lie.targetMap (CommGroupScheme.groupHom f) k X = 1) : f = 0 := by
  apply hT'.hom_ext_of_characters
  intro χ
  rw [zero_comp]
  apply character_eq_zero_of_zero_differential I
  intro X
  change Lie.targetMap (CommGroupScheme.groupHom χ) k
    (Lie.targetMap (CommGroupScheme.groupHom f) k X) = 1
  rw [hf, map_one]

end splitTorus

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every homomorphism of split tori with zero differential factors through
multiplication by the positive characteristic on its source. -/
theorem IsSplitTorus.exists_factor_characteristic_of_zero_differential
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (p : ℕ) [CharP k p] (hp : p ≠ 0) (f : T ⟶ T')
    (hf : ∀ X : lieKernel T.toGrp k,
      Lie.targetMap (CommGroupScheme.groupHom f) k X = 1) :
    ∃ g : T ⟶ T', f = ((p : ℤ) • 𝟙 T) ≫ g := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso e
  obtain ⟨g, hg⟩ := splitTorus.exists_factor_characteristic_of_zero_differential I
    hT' p hp (eC.inv ≫ f) (fun X => by
      change Lie.targetMap (CommGroupScheme.groupHom f) k
        (Lie.targetMap (CommGroupScheme.groupHom eC.inv) k X) = 1
      exact hf _)
  refine ⟨eC.hom ≫ g, ?_⟩
  calc
    f = eC.hom ≫ (eC.inv ≫ f) := by simp
    _ = eC.hom ≫ (((p : ℤ) • 𝟙 _) ≫ g) := by rw [hg]
    _ = ((p : ℤ) • 𝟙 T) ≫ (eC.hom ≫ g) := by
      simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
        Category.id_comp]

/-- In characteristic zero, every homomorphism of split tori with zero differential
is zero. -/
theorem IsSplitTorus.hom_eq_zero_of_zero_differential [CharZero k]
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp) (f : T ⟶ T')
    (hf : ∀ X : lieKernel T.toGrp k,
      Lie.targetMap (CommGroupScheme.groupHom f) k X = 1) : f = 0 := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso e
  have hz := splitTorus.hom_eq_zero_of_zero_differential I hT' (eC.inv ≫ f)
    (fun X => by
      change Lie.targetMap (CommGroupScheme.groupHom f) k
        (Lie.targetMap (CommGroupScheme.groupHom eC.inv) k X) = 1
      exact hf _)
  calc f = eC.hom ≫ (eC.inv ≫ f) := by simp
       _ = 0 := by rw [hz, comp_zero]

/-- The characteristic controls homomorphisms of split tori whose actual differential
vanishes: they factor through multiplication by the positive characteristic, and vanish
in characteristic zero. -/
def SplitTorusZeroDifferentialStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → IsSplitTorus T'.toGrp → ∀ f : T ⟶ T',
    (∀ X : lieKernel T.toGrp k,
      Lie.targetMap (CommGroupScheme.groupHom f) k X = 1) →
    (∀ (p : ℕ), CharP k p → p ≠ 0 →
      ∃ g : T ⟶ T', f = ((p : ℤ) • 𝟙 T) ≫ g) ∧ (CharZero k → f = 0)

/-- The split-torus zero-differential statement holds over arbitrary fields. -/
theorem splitTorusZeroDifferential : SplitTorusZeroDifferentialStatement.{u} := by
  intro k _ T T' hT hT' f hf
  constructor
  · intro p hchar hp
    let := hchar
    exact hT.exists_factor_characteristic_of_zero_differential hT' p hp f hf
  · intro hchar
    let := hchar
    exact hT.hom_eq_zero_of_zero_differential hT' f hf

end Langlands.GroupScheme
