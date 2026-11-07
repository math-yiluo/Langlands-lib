import Langlands.GroupTheory.CocycleSplittingCoinvariants
import Langlands.GroupTheory.CocycleSplittingClass

noncomputable section

universe u

namespace Langlands.NormalizedTwoCocycle.SplittingModule

set_option backward.isDefEq.respectTransparency false

attribute [-instance] ULift.module

variable {G A : Type u} [Group G] [Fintype G] [CommGroup A]
  [MulDistribMulAction G A] (c : NormalizedTwoCocycle G A)

local instance abelianizationCoefficientModule : Module Scalars.{u} (Additive A) := ULift.module
local instance abelianizationTargetModule :
    Module Scalars.{u} (Additive (Abelianization c.Extension)) := ULift.module

@[simp] lemma augmentationCocycle_one : augmentationCocycle (1 : G) = 0 := by
  apply Subtype.ext
  simp [augmentationCocycle_val]

omit [Fintype G] in
@[simp] lemma sectionAbelianization_one : sectionAbelianization c 1 = 0 := rfl

lemma sectionLinear_delta (g : G) :
    sectionLinear c (delta G g) = sectionAbelianization c g⁻¹ := by
  classical
  simp [sectionLinear_apply, delta, Pi.single_apply]

lemma sectionLinear_augmentationCocycle (g : G) :
    sectionLinear c (augmentationCocycle g).val = sectionAbelianization c g := by
  rw [augmentationCocycle_val, map_sub, sectionLinear_delta, sectionLinear_delta]
  simp

omit [Group G] in
lemma delta_sum (f : G → Scalars.{u}) : ∑ g : G, f g • delta G g = f := by
  classical
  funext x
  simp [delta, Pi.single_apply]
  apply ULift.ext
  simp

lemma augmentationCocycle_sum (f : Ideal G) :
    ∑ g : G, f.val g • augmentationCocycle g⁻¹ = f := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, augmentationCocycle_val, inv_inv,
    smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [delta_sum, ← coordinateSum_apply]
  have hf : coordinateSum G f.val = 0 := f.property
  rw [hf, zero_smul, sub_zero]

/-- The extension element represented in splitting-module coinvariants. -/
def extensionCoinvariant (x : c.Extension) : (splitting c).ρ.Coinvariants :=
  Representation.Coinvariants.mk (splitting c).ρ
    ((Additive.ofMul x.left, augmentationCocycle x.right) :
      Carrier (G := G) (A := A))

lemma extensionCoinvariant_one : extensionCoinvariant c 1 = 0 := by
  change Representation.Coinvariants.mk (splitting c).ρ
    ((0, augmentationCocycle (1 : G)) : Carrier (G := G) (A := A)) = 0
  rw [augmentationCocycle_one]
  exact map_zero _

lemma extensionCoinvariant_mul (x y : c.Extension) :
    extensionCoinvariant c (x * y) =
      extensionCoinvariant c x + extensionCoinvariant c y := by
  let q : Carrier (G := G) (A := A) →ₗ[Scalars.{u}] (splitting c).ρ.Coinvariants :=
    Representation.Coinvariants.mk (splitting c).ρ
  have h := Representation.Coinvariants.mk_self_apply (splitting c).ρ x.right
    ((Additive.ofMul y.left, augmentationCocycle y.right) :
      Carrier (G := G) (A := A))
  change q (coefficientAction x.right (Additive.ofMul y.left) +
      twist c x.right (augmentationCocycle y.right).val,
      (ideal G).ρ x.right (augmentationCocycle y.right)) =
    q (Additive.ofMul y.left, augmentationCocycle y.right) at h
  rw [twist_augmentationCocycle, augmentationCocycle_action] at h
  change q (Additive.ofMul x.left +
      coefficientAction x.right (Additive.ofMul y.left) +
      Additive.ofMul (c (x.right, y.right)), augmentationCocycle (x.right * y.right)) =
    q (Additive.ofMul x.left, augmentationCocycle x.right) +
      q (Additive.ofMul y.left, augmentationCocycle y.right)
  calc
    _ = q (Additive.ofMul x.left, augmentationCocycle x.right) +
        q (coefficientAction x.right (Additive.ofMul y.left) +
            Additive.ofMul (c (x.right, y.right)),
          augmentationCocycle (x.right * y.right) - augmentationCocycle x.right) := by
      rw [← map_add]
      congr 1
      apply Prod.ext <;> dsimp <;> abel
    _ = _ := congrArg (q (Additive.ofMul x.left, augmentationCocycle x.right) + ·) h

/-- The actual homomorphism from the cocycle extension to multiplicative coinvariants. -/
def extensionToCoinvariants : c.Extension →* Multiplicative (splitting c).ρ.Coinvariants where
  toFun x := Multiplicative.ofAdd (extensionCoinvariant c x)
  map_one' := extensionCoinvariant_one c
  map_mul' := extensionCoinvariant_mul c

/-- The homomorphism induced on abelianization, in additive scalar-linear form. -/
def abelianizationToCoinvariants :
    Additive (Abelianization c.Extension) →ₗ[Scalars.{u}] (splitting c).ρ.Coinvariants where
  toFun a := (Abelianization.lift (extensionToCoinvariants c) a.toMul).toAdd
  map_add' a b := by
    change (Abelianization.lift (extensionToCoinvariants c) (a.toMul * b.toMul)).toAdd = _
    rw [map_mul]
    rfl
  map_smul' r a := by
    change (Abelianization.lift (extensionToCoinvariants c) (a.toMul ^ r.down)).toAdd =
      r.down • (Abelianization.lift (extensionToCoinvariants c) a.toMul).toAdd
    rw [map_zpow]
    rfl

lemma abelianizationToCoinvariants_of (x : c.Extension) :
    abelianizationToCoinvariants c (Additive.ofMul (Abelianization.of x)) =
      extensionCoinvariant c x := rfl

lemma coinvariantsToAbelianization_extensionCoinvariant (x : c.Extension) :
    coinvariantsToAbelianization c (extensionCoinvariant c x) =
      Additive.ofMul (Abelianization.of x) := by
  change coefficientAbelianization c (Additive.ofMul x.left) +
    sectionLinear c (augmentationCocycle x.right).val = _
  rw [sectionLinear_augmentationCocycle]
  change Additive.ofMul (Abelianization.of
    (Extension.inl c x.left * Extension.sectionMap c x.right)) = _
  rw [Extension.inl_mul_sectionMap]

lemma abelianizationToCoinvariants_coefficient (a : Additive A) :
    abelianizationToCoinvariants c (coefficientAbelianization c a) =
      Representation.Coinvariants.mk (splitting c).ρ
        ((a, 0) : Carrier (G := G) (A := A)) := by
  change extensionCoinvariant c (Extension.inl c a.toMul) = _
  change Representation.Coinvariants.mk (splitting c).ρ
    ((a, augmentationCocycle (1 : G)) : Carrier (G := G) (A := A)) = _
  rw [augmentationCocycle_one]

lemma abelianizationToCoinvariants_section (g : G) :
    abelianizationToCoinvariants c (sectionAbelianization c g) =
      Representation.Coinvariants.mk (splitting c).ρ
        ((0, augmentationCocycle g) : Carrier (G := G) (A := A)) := rfl

lemma coinvariants_abelianization_leftInverse :
    Function.LeftInverse (coinvariantsToAbelianization c) (abelianizationToCoinvariants c) := by
  intro a
  change Abelianization c.Extension at a
  refine QuotientGroup.induction_on a fun x => ?_
  change coinvariantsToAbelianization c
    (abelianizationToCoinvariants c (Additive.ofMul (Abelianization.of x))) =
    Additive.ofMul (Abelianization.of x)
  rw [abelianizationToCoinvariants_of, coinvariantsToAbelianization_extensionCoinvariant]

lemma coinvariants_abelianization_rightInverse :
    Function.RightInverse (coinvariantsToAbelianization c) (abelianizationToCoinvariants c) := by
  intro v
  induction v using Representation.Coinvariants.induction_on with
  | h x =>
    change Carrier (G := G) (A := A) at x
    change abelianizationToCoinvariants c
      (coefficientAbelianization c x.1 + sectionLinear c x.2.val) =
      Representation.Coinvariants.mk (splitting c).ρ x
    rw [map_add, sectionLinear_apply, map_sum, abelianizationToCoinvariants_coefficient]
    simp only [map_smul, abelianizationToCoinvariants_section]
    let q : Carrier (G := G) (A := A) →ₗ[Scalars.{u}] (splitting c).ρ.Coinvariants :=
      Representation.Coinvariants.mk (splitting c).ρ
    change q (x.1, 0) +
      ∑ g : G, x.2.val g • q (0, augmentationCocycle g⁻¹) = q x
    calc
      _ = q ((x.1, 0) +
          ∑ g : G, x.2.val g • ((0, augmentationCocycle g⁻¹) :
            Carrier (G := G) (A := A))) := by
        simp only [map_add, map_sum, map_smul]
      _ = q x := by
        congr 1
        apply Prod.ext
        · change x.1 + (LinearMap.fst Scalars.{u} (Additive A) (Ideal G))
            (∑ g : G, x.2.val g • ((0, augmentationCocycle g⁻¹) :
              Carrier (G := G) (A := A))) = x.1
          rw [map_sum]
          simp
        · change (0 : Ideal G) + (LinearMap.snd Scalars.{u} (Additive A) (Ideal G))
            (∑ g : G, x.2.val g • ((0, augmentationCocycle g⁻¹) :
              Carrier (G := G) (A := A))) = x.2
          rw [map_sum]
          simp only [map_smul, LinearMap.snd_apply, zero_add, augmentationCocycle_sum]

/-- The splitting-module coinvariants are the additive abelianization of the
actual cocycle extension. -/
def coinvariantsAbelianizationEquiv :
    (splitting c).ρ.Coinvariants ≃ₗ[Scalars.{u}] Additive (Abelianization c.Extension) :=
  LinearEquiv.ofLinearMap (coinvariantsToAbelianization c) (abelianizationToCoinvariants c)
    (LinearMap.ext (coinvariants_abelianization_leftInverse c))
    (LinearMap.ext (coinvariants_abelianization_rightInverse c))

end Langlands.NormalizedTwoCocycle.SplittingModule
