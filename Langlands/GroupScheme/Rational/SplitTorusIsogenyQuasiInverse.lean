import Langlands.GroupScheme.Rational.SplitTorusIsogenyCharacters
import Langlands.GroupScheme.Rational.SplitTorusIsogenyQuasiInverseLinear

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.splitTorus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] (I J : Type u)
  [Fintype I] [Fintype J] [DecidableEq I]

local notation "S" => Spec (CommRingCat.of k)
local notation "TI" => commGroupScheme S I
local notation "TJ" => commGroupScheme S J

/-- The actual torus homomorphism specified by columns of a character pullback. -/
def fromCharacterColumns (b : (I → ℤ) →ₗ[ℤ] (J → ℤ)) : TJ ⟶ TI :=
  ∑ i, (characterLatticeEquiv k J).symm (b (Pi.single i 1)) ≫ single S I i

theorem fromCharacterColumns_proj (b : (I → ℤ) →ₗ[ℤ] (J → ℤ)) (i : I) :
    fromCharacterColumns I J b ≫ proj S I i =
      (characterLatticeEquiv k J).symm (b (Pi.single i 1)) := by
  rw [fromCharacterColumns, Preadditive.sum_comp]
  simp only [Category.assoc, single_comp_proj]
  simp [comp_ite]

omit [DecidableEq I] in
private theorem commHom_ext_proj {P : CommGroupScheme S} {f g : P ⟶ TI}
    (h : ∀ i, f ≫ proj S I i = g ≫ proj S I i) : f = g := by
  apply Additive.toMul.injective
  apply Pi.hom_ext
  intro i
  exact congrArg Additive.toMul (h i)

/-- A right inverse up to an integer on characters is realized by an actual torus map. -/
theorem comp_fromCharacterColumns (f : splitTorus S I ⟶ splitTorus S J)
    (b : (I → ℤ) →ₗ[ℤ] (J → ℤ)) (n : ℤ)
    (hb : characterMap I J f ∘ₗ b = n • LinearMap.id) :
    (Additive.ofMul f : TI ⟶ TJ) ≫ fromCharacterColumns I J b = n • 𝟙 TI := by
  let a : TI ⟶ TJ := Additive.ofMul f
  change a ≫ fromCharacterColumns I J b = n • 𝟙 TI
  apply commHom_ext_proj I
  intro i
  rw [Category.assoc, fromCharacterColumns_proj]
  apply (characterLatticeEquiv k I).injective
  have h := LinearMap.congr_fun hb (Pi.single i 1)
  have hh := characterMap_equiv I J f
    ((characterLatticeEquiv k J).symm (b (Pi.single i 1)))
  rw [AddEquiv.apply_symm_apply] at hh
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Preadditive.zsmul_comp, Category.id_comp, map_zsmul, characterLatticeEquiv_proj]
    using hh.symm.trans h

/-- If the original scheme map is epimorphic, the realized inverse is two-sided. -/
theorem fromCharacterColumns_comp (f : splitTorus S I ⟶ splitTorus S J)
    [Epi f.hom.hom.left] (b : (I → ℤ) →ₗ[ℤ] (J → ℤ)) (n : ℤ)
    (hb : characterMap I J f ∘ₗ b = n • LinearMap.id) :
    fromCharacterColumns I J b ≫ (Additive.ofMul f : TI ⟶ TJ) = n • 𝟙 TJ := by
  let a : TI ⟶ TJ := Additive.ofMul f
  let g : TJ ⟶ TI := fromCharacterColumns I J b
  have hfg : a ≫ g = n • 𝟙 TI := comp_fromCharacterColumns I J f b n hb
  apply commHom_ext_proj J
  intro j
  apply (characterLatticeEquiv k J).injective
  apply characterMap_injective_of_epi I J f
  rw [characterMap_equiv, characterMap_equiv]
  change (characterLatticeEquiv k I) (a ≫ ((g ≫ a) ≫ proj S J j)) =
    (characterLatticeEquiv k I) (a ≫ ((n • 𝟙 TJ) ≫ proj S J j))
  apply congrArg (characterLatticeEquiv k I)
  calc
    a ≫ ((g ≫ a) ≫ proj S J j) = (a ≫ g) ≫ (a ≫ proj S J j) := by
      simp only [Category.assoc]
    _ = a ≫ ((n • 𝟙 TJ) ≫ proj S J j) := by
      rw [hfg]
      simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp]

omit [DecidableEq I] in
/-- A finite split-torus morphism epimorphic on schemes has an integer quasiinverse. -/
theorem exists_integer_quasiInverse (f : splitTorus S I ⟶ splitTorus S J)
    [IsFinite f.hom.hom.left] [Epi f.hom.hom.left] :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ g : TJ ⟶ TI,
      (Additive.ofMul f : TI ⟶ TJ) ≫ g = n • 𝟙 TI ∧
        g ≫ (Additive.ofMul f : TI ⟶ TJ) = n • 𝟙 TJ := by
  classical
  obtain ⟨n, hn, b, _, hb⟩ :=
    SplitTorusIsogeny.exists_quasiInverse_of_injective_finiteCokernel
      (characterMap I J f) (characterMap_injective_of_epi I J f)
      (characterMap_finite_cokernel I J f)
  exact ⟨n, hn, fromCharacterColumns I J b,
    comp_fromCharacterColumns I J f b n hb, fromCharacterColumns_comp I J f b n hb⟩

end Langlands.GroupScheme.splitTorus
