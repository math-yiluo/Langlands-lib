import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.CategoryTheory.Category.Basic

/-! # Complete nonarchimedean normed fields and isometric embeddings -/

universe u

namespace Langlands.Analytic

/-- The complete nonarchimedean normed fields used as analytic ground fields. -/
structure CompleteUltrametricField where
  carrier : Type u
  [normedField : NormedField carrier]
  [ultrametric : IsUltrametricDist carrier]
  [complete : CompleteSpace carrier]

attribute [instance] CompleteUltrametricField.normedField CompleteUltrametricField.ultrametric
  CompleteUltrametricField.complete

namespace CompleteUltrametricField

open CategoryTheory

instance : CoeSort CompleteUltrametricField.{u} (Type u) := ⟨carrier⟩

/-- Bundle an actual complete nonarchimedean normed field. -/
abbrev of (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    CompleteUltrametricField.{u} where
  carrier := K

/-- An isometric field embedding with its actual underlying ring homomorphism. -/
@[ext]
structure Hom (K L : CompleteUltrametricField.{u}) extends K →+* L where
  norm_eq : ∀ x, ‖toRingHom x‖ = ‖x‖

private def Hom.id (K : CompleteUltrametricField.{u}) : Hom K K :=
  ⟨RingHom.id K, fun _ => rfl⟩

private def Hom.comp {K L M : CompleteUltrametricField.{u}} (f : Hom K L) (g : Hom L M) :
    Hom K M :=
  ⟨g.toRingHom.comp f.toRingHom, fun x => (g.norm_eq (f.toRingHom x)).trans (f.norm_eq x)⟩

instance : Category CompleteUltrametricField.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext rfl
  comp_id _ := Hom.ext rfl
  assoc _ _ _ := Hom.ext rfl

variable {K L M : CompleteUltrametricField.{u}}

instance : CoeFun (K ⟶ L) (fun _ => K → L) :=
  ⟨fun f => f.toRingHom⟩

@[simp] theorem id_apply (x : K) : (𝟙 K) x = x := rfl

@[simp] theorem comp_apply (f : K ⟶ L) (g : L ⟶ M) (x : K) : (f ≫ g) x = g (f x) :=
  rfl

/-- The distance is preserved by a norm-preserving field embedding. -/
theorem Hom.isometry (f : K ⟶ L) : Isometry f := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (f.toRingHom x) (f.toRingHom y) = dist x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, f.norm_eq]

/-- The normed algebra used for extension of analytic scalars along this arrow. -/
@[instance_reducible]
def Hom.normedAlgebra (f : K ⟶ L) : NormedAlgebra K L where
  toAlgebra := f.toRingHom.toAlgebra
  norm_smul_le r x := by
    change ‖f.toRingHom r * x‖ ≤ ‖r‖ * ‖x‖
    rw [norm_mul, f.norm_eq]

/-- The chosen normed-algebra structure induces the original field embedding. -/
theorem Hom.algebraMap_normedAlgebra (f : K ⟶ L) :
    letI := f.normedAlgebra
    algebraMap K L = f.toRingHom :=
  rfl

@[simp] theorem normedAlgebra_id (K : CompleteUltrametricField.{u}) :
    (𝟙 K : K ⟶ K).normedAlgebra = NormedAlgebra.id K := rfl

/-- The scalar tower for a composable pair uses the literal composite embedding. -/
theorem Hom.isScalarTower_comp (f : K ⟶ L) (g : L ⟶ M) :
    letI := f.normedAlgebra
    letI := g.normedAlgebra
    letI := (f ≫ g).normedAlgebra
    IsScalarTower K L M := by
  let : NormedAlgebra K.carrier L.carrier := f.normedAlgebra
  let : NormedAlgebra L.carrier M.carrier := g.normedAlgebra
  let : NormedAlgebra K.carrier M.carrier := (f ≫ g).normedAlgebra
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- Every existing normed algebra structure on two such fields defines its actual isometric
ground-field arrow. -/
def ofNormedAlgebra (K L : CompleteUltrametricField.{u}) [h : NormedAlgebra K L] : K ⟶ L := by
  change Hom K L
  letI : NormedAlgebra K.carrier L.carrier := h
  exact { toRingHom := algebraMap K.carrier L.carrier
          norm_eq := fun x => norm_algebraMap' L.carrier x }

end CompleteUltrametricField

end Langlands.Analytic
