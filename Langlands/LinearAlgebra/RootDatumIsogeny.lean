import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Isogenies of reduced root data with characteristic-power root factors -/

noncomputable section

namespace Langlands.LinearAlgebra

/-- An isogeny of finite reduced root data in characteristic exponent `p`, in the sense of
Milne 23.1. Both lattice maps are injective; for finite perfectly paired integral lattices
this is the equivalent formulation of injectivity with finite cokernel. The root factor
is indexed by a root of the domain of `weightMap`. -/
@[ext]
structure RootDatumIsogeny (p : ℕ) {ι X Y ι₂ X₂ Y₂ : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X₂] [AddCommGroup Y₂]
    [Finite ι] [Finite ι₂]
    [Module.Finite ℤ X] [Module.Finite ℤ Y]
    [Module.Finite ℤ X₂] [Module.Finite ℤ Y₂]
    (P : RootDatum ι X Y) (Q : RootDatum ι₂ X₂ Y₂) [P.IsReduced] [Q.IsReduced] where
  /-- A characteristic exponent is one or a prime. -/
  characteristicExponent : p = 1 ∨ Nat.Prime p
  /-- The map on weight lattices. -/
  weightMap : X →ₗ[ℤ] X₂
  /-- The contravariant map on coweight lattices. -/
  coweightMap : Y₂ →ₗ[ℤ] Y
  /-- The correspondence between roots, in the direction of the weight map. -/
  indexEquiv : ι ≃ ι₂
  weightMap_injective : Function.Injective weightMap
  coweightMap_injective : Function.Injective coweightMap
  weight_coweight_transpose :
    weightMap.dualMap ∘ₗ Q.flip.toPerfPair = P.flip.toPerfPair ∘ₗ coweightMap
  /-- The root-dependent power of the characteristic exponent. -/
  rootFactor : ι → ℕ
  rootFactor_pow : ∀ i, ∃ n : ℕ, rootFactor i = p ^ n
  root_weightMap : ∀ i,
    weightMap (P.root i) = (rootFactor i : ℤ) • Q.root (indexEquiv i)
  coroot_coweightMap : ∀ i,
    coweightMap (Q.coroot (indexEquiv i)) = (rootFactor i : ℤ) • P.coroot i

namespace RootDatumIsogeny

variable {p : ℕ} {ι X Y ι₂ X₂ Y₂ : Type*}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X₂] [AddCommGroup Y₂]
  [Finite ι] [Finite ι₂]
  [Module.Finite ℤ X] [Module.Finite ℤ Y]
  [Module.Finite ℤ X₂] [Module.Finite ℤ Y₂]
  {P : RootDatum ι X Y} {Q : RootDatum ι₂ X₂ Y₂} [P.IsReduced] [Q.IsReduced]

/-- The characteristic exponent is positive. -/
theorem characteristicExponent_pos (f : RootDatumIsogeny p P Q) : 0 < p := by
  rcases f.characteristicExponent with h | h
  · simp [h]
  · exact h.pos

/-- Every root factor is positive. -/
theorem rootFactor_pos (f : RootDatumIsogeny p P Q) (i : ι) : 0 < f.rootFactor i := by
  obtain ⟨n, hn⟩ := f.rootFactor_pow i
  rw [hn]
  exact pow_pos f.characteristicExponent_pos n

/-- The transpose equation evaluated on a weight and a coweight. -/
theorem pairing_apply (f : RootDatumIsogeny p P Q) (x : X) (y : Y₂) :
    Q.toLinearMap (f.weightMap x) y = P.toLinearMap x (f.coweightMap y) := by
  exact LinearMap.congr_fun₂ f.weight_coweight_transpose y x

/-- Centrality of a root-datum isogeny means that all root factors are one (Milne 23.2). -/
def IsCentral (f : RootDatumIsogeny p P Q) : Prop :=
  ∀ i, f.rootFactor i = 1

/-- An exact root-preserving morphism with both lattice maps injective is a central
root-datum isogeny for every characteristic exponent. -/
def ofHom (hp : p = 1 ∨ Nat.Prime p) (f : RootPairing.Hom P Q)
    (hX : Function.Injective f.weightMap) (hY : Function.Injective f.coweightMap) :
    RootDatumIsogeny p P Q where
  characteristicExponent := hp
  weightMap := f.weightMap
  coweightMap := f.coweightMap
  indexEquiv := f.indexEquiv
  weightMap_injective := hX
  coweightMap_injective := hY
  weight_coweight_transpose := f.weight_coweight_transpose
  rootFactor := fun _ => 1
  rootFactor_pow := fun _ => ⟨0, by simp⟩
  root_weightMap := fun i => by simpa using f.root_weightMap_apply P Q i
  coroot_coweightMap := fun i => by
    simpa using f.coroot_coweightMap_apply P Q (f.indexEquiv i)

@[simp]
theorem ofHom_isCentral (hp : p = 1 ∨ Nat.Prime p) (f : RootPairing.Hom P Q)
    (hX : Function.Injective f.weightMap) (hY : Function.Injective f.coweightMap) :
    (ofHom hp f hX hY).IsCentral :=
  fun _ => rfl

/-- A central isogeny recovers an exact root-preserving morphism. -/
def toHom (f : RootDatumIsogeny p P Q) (hf : f.IsCentral) : RootPairing.Hom P Q where
  weightMap := f.weightMap
  coweightMap := f.coweightMap
  indexEquiv := f.indexEquiv
  weight_coweight_transpose := f.weight_coweight_transpose
  root_weightMap := funext fun i => by simpa [hf i] using f.root_weightMap i
  coroot_coweightMap := funext fun j => by
    simpa [hf (f.indexEquiv.symm j)] using f.coroot_coweightMap (f.indexEquiv.symm j)

/-- Every isogeny of root data in characteristic exponent one is central. -/
theorem isCentral_one (f : RootDatumIsogeny 1 P Q) : f.IsCentral := by
  intro i
  obtain ⟨n, hn⟩ := f.rootFactor_pow i
  simpa using hn

/-- The identity isogeny. -/
def id (hp : p = 1 ∨ Nat.Prime p) (P : RootDatum ι X Y) [P.IsReduced] :
    RootDatumIsogeny p P P :=
  ofHom hp (RootPairing.Hom.id P) Function.injective_id Function.injective_id

/-- Composition multiplies the root factors after transport along the root correspondence. -/
def comp {ι₃ X₃ Y₃ : Type*} [AddCommGroup X₃] [AddCommGroup Y₃] [Finite ι₃]
    [Module.Finite ℤ X₃] [Module.Finite ℤ Y₃]
    {R : RootDatum ι₃ X₃ Y₃} [R.IsReduced]
    (g : RootDatumIsogeny p Q R) (f : RootDatumIsogeny p P Q) :
    RootDatumIsogeny p P R where
  characteristicExponent := f.characteristicExponent
  weightMap := g.weightMap ∘ₗ f.weightMap
  coweightMap := f.coweightMap ∘ₗ g.coweightMap
  indexEquiv := f.indexEquiv.trans g.indexEquiv
  weightMap_injective := g.weightMap_injective.comp f.weightMap_injective
  coweightMap_injective := f.coweightMap_injective.comp g.coweightMap_injective
  weight_coweight_transpose := by
    ext y x
    exact (g.pairing_apply (f.weightMap x) y).trans (f.pairing_apply x (g.coweightMap y))
  rootFactor := fun i => f.rootFactor i * g.rootFactor (f.indexEquiv i)
  rootFactor_pow := fun i => by
    obtain ⟨a, ha⟩ := f.rootFactor_pow i
    obtain ⟨b, hb⟩ := g.rootFactor_pow (f.indexEquiv i)
    exact ⟨a + b, by rw [ha, hb, pow_add]⟩
  root_weightMap := fun i => by
    change g.weightMap (f.weightMap (P.root i)) = _
    rw [f.root_weightMap, map_smul, g.root_weightMap]
    simp [Nat.cast_mul, mul_smul]
  coroot_coweightMap := fun i => by
    change f.coweightMap (g.coweightMap (R.coroot (g.indexEquiv (f.indexEquiv i)))) = _
    rw [g.coroot_coweightMap, map_smul, f.coroot_coweightMap]
    simp only [Nat.cast_mul, mul_smul]
    exact smul_comm _ _ _

/-- Multiplication by `p ^ n` on both lattices is the Frobenius isogeny of root data
(Milne 23.3). This is a lattice construction, without an assertion about a group scheme. -/
def frobenius (hp : p = 1 ∨ Nat.Prime p) (P : RootDatum ι X Y) [P.IsReduced] (n : ℕ) :
    RootDatumIsogeny p P P := by
  have hp_pos : 0 < p := hp.elim (fun h => by simp [h]) Nat.Prime.pos
  have hq : (p ^ n : ℤ) ≠ 0 := by exact_mod_cast (pow_pos hp_pos n).ne'
  have : Module.IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive ℤ Y := .of_isPerfPair P.toLinearMap.flip
  exact
    { characteristicExponent := hp
      weightMap := (p ^ n : ℤ) • LinearMap.id
      coweightMap := (p ^ n : ℤ) • LinearMap.id
      indexEquiv := Equiv.refl ι
      weightMap_injective := smul_right_injective X hq
      coweightMap_injective := smul_right_injective Y hq
      weight_coweight_transpose := by
        ext y x
        change P.toLinearMap ((p ^ n : ℤ) • x) y =
          P.toLinearMap x ((p ^ n : ℤ) • y)
        simp
      rootFactor := fun _ => p ^ n
      rootFactor_pow := fun _ => ⟨n, rfl⟩
      root_weightMap := fun _ => rfl
      coroot_coweightMap := fun _ => rfl }

end RootDatumIsogeny

end Langlands.LinearAlgebra
